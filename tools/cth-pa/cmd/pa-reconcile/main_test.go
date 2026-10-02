package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/santhosh-tekuri/jsonschema/v6"

	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/attestation"
	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/pa"
)

// A 40-hex blob stand-in for a pinned-source sha (the v1.3 source_sha shape, the
// engine's staleness key, and — post R2 — the record's source_sha). Two distinct
// ones so staleness can be forced.
const (
	pinnedSHA = "be50573493f675d331606c3d752c3c9d15d8ffa4"
	movedSHA  = "4cd7a94f9b962ce49973d98be269ace7cc5b4387"
)

func grade(g pa.Grade) *pa.Grade { return &g }

// cleanAssistant builds an assistant the engine counts under StubV0 with
// require_signature=false: kernel-clean derived, declared matching derived, a
// reproducing non-empty hash, trust_check pass, and a source_sha equal to the
// pin (fresh). lean4 carries a whitelisted axiom; coq/agda carry none.
func cleanAssistant(name, producer, srcSHA string) pa.Assistant {
	h := "sha256:" + strings.Repeat("a", 64)
	ax := []string{}
	if name == "lean4" {
		ax = []string{"propext"}
	}
	return pa.Assistant{
		Assistant:   name,
		EvidenceRef: "proofs/QBP/Foundations/X.lean@" + srcSHA + "#lemma_" + producer,
		Producer:    producer,
		TrustCheck:  "pass",
		SourceSHA:   srcSHA,
		Declared:    pa.Declared{Mode: "decide", OutputHash: h, Axioms: ax, ExitCode: 0},
		Derived:     pa.Derived{OutputHash: h, TacticsUsed: []string{"decide"}, Axioms: ax, ExitCode: 0, KernelClean: true},
	}
}

// corrPair is a corresponding two-assistant pair checked by a non-producer (C1
// satisfied) — PA2 under StubV0/require_signature=false when both are fresh.
func corrPair(pin string) pa.Claim {
	return pa.Claim{
		ID:        "PROOF-pair",
		Consumer:  "qbp#692-ci",
		PinnedSHA: pin,
		Assistants: []pa.Assistant{
			cleanAssistant("lean4", "qbp-oppenheimer", pin),
			cleanAssistant("coq", "deming", pin),
		},
		Correspondence: pa.Correspondence{Corresponds: true, Basis: "49/49 table entries", CheckedBy: "qbp-architecture", CheckedAt: "deadbeef"},
	}
}

func baseInput(claims []pa.Claim, edges []pa.Edge, expect map[string]Expect) Input {
	return Input{
		Policy:        pa.Policy{RequireSignature: false},
		LedgerVersion: "6.14.0",
		EmittedAt:     "2026-10-02T14:00:00Z",
		Claims:        claims,
		Edges:         edges,
		Expect:        expect,
	}
}

func stubVerifier() attestation.Verifier { return attestation.StubV0{} }

// mustReconcile decodes in (honoring requireCommitted) and reconciles with StubV0,
// failing the test if decode rejects an input it should have accepted.
func mustReconcile(t *testing.T, in Input, requireCommitted bool) Output {
	t.Helper()
	b, err := json.Marshal(in)
	if err != nil {
		t.Fatalf("marshal input: %v", err)
	}
	got, err := Decode(bytes.NewReader(b), requireCommitted)
	if err != nil {
		t.Fatalf("decode rejected a valid input: %v", err)
	}
	return Reconcile(got, stubVerifier())
}

// decodeErr decodes in and returns the error (for the rejection tests).
func decodeErr(t *testing.T, in Input, requireCommitted bool) error {
	t.Helper()
	b, err := json.Marshal(in)
	if err != nil {
		t.Fatalf("marshal input: %v", err)
	}
	_, err = Decode(bytes.NewReader(b), requireCommitted)
	return err
}

// TestPA2PairNoShortfall: the synthetic two-evidence PA-2 fixture shape — a
// corresponding clean pair grades PA2, so at required_pa=2 there is no diff and no
// request. (QBP#692 coverage matrix: test_pa2_from_two_evidence_fixture.)
func TestPA2PairNoShortfall(t *testing.T) {
	c := corrPair(pinnedSHA)
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2),
			SourceRef: "JamesPagetButler/QBP@proofs/QBP/Foundations/X.lean", PinningConsumer: []string{"roms/x.hex"}},
	})
	out := mustReconcile(t, in, true)
	if len(out.Diffs) != 0 {
		t.Errorf("PA2 pair: unexpected diffs %+v", out.Diffs)
	}
	if len(out.Requests) != 0 {
		t.Errorf("PA2 pair at required 2: unexpected requests %+v", out.Requests)
	}
}

// TestEmitShortfall: a single clean assistant grades PA1; at required_pa=2 the gate
// emits one pa_shortfall stamped qbp-pa-reconcile, current_pa=1, not stale, and —
// R2 — source_sha equal to the claim's pinned_sha. (notary#3 AC1.)
func TestEmitShortfall(t *testing.T) {
	c := pa.Claim{ID: "PROOF-single", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "qbp-oppenheimer", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, SourceRef: "o/r@p", PinningConsumer: []string{"consumer-a"}},
	})
	out := mustReconcile(t, in, false) // no committed grades here -> ungraded mode
	if len(out.Requests) != 1 {
		t.Fatalf("expected 1 request, got %d (%+v)", len(out.Requests), out.Requests)
	}
	r := out.Requests[0]
	if r.Emitter != Emitter {
		t.Errorf("emitter = %q, want %q", r.Emitter, Emitter)
	}
	if r.Reason != pa.ReasonPAShortfall {
		t.Errorf("reason = %q, want pa_shortfall", r.Reason)
	}
	if r.Stale {
		t.Errorf("single fresh clean assistant should not be stale")
	}
	if r.CurrentPA == nil || *r.CurrentPA != pa.PA1 {
		t.Errorf("current_pa = %v, want 1", r.CurrentPA)
	}
	if r.SourceSHA != pinnedSHA {
		t.Errorf("R2: source_sha = %q, want the claim's pinned_sha %q", r.SourceSHA, pinnedSHA)
	}
}

// TestEmitStaleness: an assistant whose source_sha has moved off the pin is stale
// (counts 0), so the claim falls below required and the gate emits reason=staleness,
// stale=true — the stale-while-passing case notary#3 AC3 exists for.
func TestEmitStaleness(t *testing.T) {
	a := cleanAssistant("lean4", "qbp-oppenheimer", movedSHA) // source moved off the pin
	c := pa.Claim{ID: "PROOF-stale", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{a}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA1, SourceRef: "o/r@p", PinningConsumer: []string{"consumer-a"}},
	})
	out := mustReconcile(t, in, false)
	if len(out.Requests) != 1 {
		t.Fatalf("expected 1 request, got %d", len(out.Requests))
	}
	if r := out.Requests[0]; r.Reason != pa.ReasonStaleness || !r.Stale {
		t.Errorf("reason=%q stale=%v, want staleness/true", r.Reason, r.Stale)
	}
}

// TestReconcileDiffLocal: a planted hand-edit — committed pa_local=2 on a PA1 claim —
// is a diff, and Run returns errDiff (exit 3). (AC2.)
func TestReconcileDiffLocal(t *testing.T) {
	c := pa.Claim{ID: "PROOF-handedit", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA1), SourceRef: "o/r@p"},
	})
	out := mustReconcile(t, in, true)
	if len(out.Diffs) != 1 || out.Diffs[0].Field != "pa_local" {
		t.Fatalf("expected one pa_local diff, got %+v", out.Diffs)
	}
	b, _ := json.Marshal(in)
	if err := Run(bytes.NewReader(b), &bytes.Buffer{}, "", false, true); !errors.Is(err, errDiff) {
		t.Errorf("Run on a diff: err = %v, want errDiff", err)
	}
}

// TestEffectiveRecomputeIsLoadBearing (3b mutant): a head whose pa_local matches its
// committed value but whose committed pa_effective is planted stale (2, while a PA1
// derivation dependency drags the real effective to 1) must be caught. If the gate
// dropped the effective recompute, this would pass silently.
func TestEffectiveRecomputeIsLoadBearing(t *testing.T) {
	head := corrPair(pinnedSHA) // PA2 locally
	head.ID = "PROOF-head"
	dep := pa.Claim{ID: "PROOF-dep", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}} // PA1 locally
	edges := []pa.Edge{{From: head.ID, To: dep.ID, Type: pa.EdgeDerivation}}
	in := baseInput([]pa.Claim{head, dep}, edges, map[string]Expect{
		head.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2), SourceRef: "o/r@p"},
		dep.ID:  {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA1), CommittedEffective: grade(pa.PA1), SourceRef: "o/r@p"},
	})
	out := mustReconcile(t, in, true)
	var got *Diff
	for i := range out.Diffs {
		if out.Diffs[i].ClaimID == head.ID && out.Diffs[i].Field == "pa_effective" {
			got = &out.Diffs[i]
		}
	}
	if got == nil {
		t.Fatalf("effective recompute not load-bearing: no pa_effective diff on the head (diffs %+v)", out.Diffs)
	}
	if got.Committed != pa.PA2 || got.Recomputed != pa.PA1 {
		t.Errorf("effective diff = committed %d recomputed %d, want 2 -> 1", got.Committed, got.Recomputed)
	}
}

// TestPairWithoutCorrespondenceCapsAt1 (3e shape): two clean assistants but no valid
// correspondence (corresponds=false) cap the headline at PA1 — a companion cannot
// reach 2 without the correspondence block. At required 2, a shortfall.
func TestPairWithoutCorrespondenceCapsAt1(t *testing.T) {
	c := corrPair(pinnedSHA)
	c.ID = "PROOF-uncorresponded"
	c.Correspondence.Corresponds = false
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, CommittedLocal: grade(pa.PA1), CommittedEffective: grade(pa.PA1), SourceRef: "o/r@p"},
	})
	out := mustReconcile(t, in, true)
	if len(out.Diffs) != 0 {
		t.Errorf("committed pa=1 should match the capped grade, got diffs %+v", out.Diffs)
	}
	if len(out.Requests) != 1 || out.Requests[0].Reason != pa.ReasonPAShortfall {
		t.Errorf("uncorresponded pair at required 2: want one pa_shortfall, got %+v", out.Requests)
	}
}

// TestEmittedRecordConformsToSchema: a gate-emitted record validates against the
// vendored v1.3 schema (the seam) and carries the qbp-pa-reconcile emitter id.
func TestEmittedRecordConformsToSchema(t *testing.T) {
	c := pa.Claim{ID: "PROOF-single", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, SourceRef: "JamesPagetButler/QBP@proofs/QBP/Foundations/X.lean", PinningConsumer: []string{"roms/x.hex"}},
	})
	out := mustReconcile(t, in, false)
	if len(out.Requests) != 1 {
		t.Fatalf("expected 1 request, got %d", len(out.Requests))
	}
	schema := compileSchema(t)
	raw, err := json.Marshal(out.Requests[0])
	if err != nil {
		t.Fatalf("marshal request: %v", err)
	}
	var inst any
	if err := json.Unmarshal(raw, &inst); err != nil {
		t.Fatalf("parse request: %v", err)
	}
	if err := schema.Validate(inst); err != nil {
		t.Errorf("emitted record fails the v1.3 schema: %v\n%s", err, raw)
	}
	if out.Requests[0].Emitter != "qbp-pa-reconcile" {
		t.Errorf("emitter id = %q, want qbp-pa-reconcile", out.Requests[0].Emitter)
	}
}

// --- R3: committed grades required by default --------------------------------

// TestRequireCommittedRejectsNil (R3 / P3 mutant): under the default strict mode a
// claim missing a committed grade is exit 2, never a silently-skipped reconcile.
func TestRequireCommittedRejectsNil(t *testing.T) {
	c := pa.Claim{ID: "PROOF-ungraded", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}}
	for _, tc := range []struct {
		name   string
		expect Expect
	}{
		{"both nil", Expect{RequiredPA: pa.PA1, SourceRef: "o/r@p"}},
		{"effective nil", Expect{RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA1), SourceRef: "o/r@p"}},
		{"local nil", Expect{RequiredPA: pa.PA1, CommittedEffective: grade(pa.PA1), SourceRef: "o/r@p"}},
	} {
		in := baseInput([]pa.Claim{c}, nil, map[string]Expect{c.ID: tc.expect})
		if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
			t.Errorf("%s: strict decode err = %v, want errInput", tc.name, err)
		}
	}
}

// TestAllowUngradedPermitsNil (R3): the explicit ungraded mode — the fixture slice —
// accepts a nil committed grade. CI never passes it (TestWorkflowNeverAllowsUngraded).
func TestAllowUngradedPermitsNil(t *testing.T) {
	c := pa.Claim{ID: "PROOF-ungraded", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{c.ID: {RequiredPA: pa.PA1, SourceRef: "o/r@p"}})
	if err := decodeErr(t, in, false); err != nil {
		t.Errorf("ungraded mode rejected a nil committed grade: %v", err)
	}
}

// --- break-3: pinned_sha must be a real 40-hex blob --------------------------

func TestRejectNonHexPinnedSHA(t *testing.T) {
	for _, bad := range []string{"", " ", "0000", strings.Repeat("A", 40), strings.Repeat("g", 40), pinnedSHA + "0"} {
		c := pa.Claim{ID: "PROOF-x", PinnedSHA: bad, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", bad)}}
		in := baseInput([]pa.Claim{c}, nil, map[string]Expect{c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA0), CommittedEffective: grade(pa.PA0), SourceRef: "o/r@p"}})
		if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
			t.Errorf("pinned_sha %q: err = %v, want errInput", bad, err)
		}
	}
}

// --- R4: the four previously-untested decode guards --------------------------

func TestRejectMissingExpect(t *testing.T) {
	c := corrPair(pinnedSHA)
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{}) // no expect entry
	if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
		t.Errorf("missing expect: err = %v, want errInput", err)
	}
}

func TestRejectUnsuppliedEdgeEndpoint(t *testing.T) {
	c := corrPair(pinnedSHA)
	edges := []pa.Edge{{From: c.ID, To: "PROOF-ghost", Type: pa.EdgeDerivation}}
	in := baseInput([]pa.Claim{c}, edges, map[string]Expect{c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2), SourceRef: "o/r@p"}})
	if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
		t.Errorf("unsupplied edge endpoint: err = %v, want errInput", err)
	}
}

func TestRejectUnknownEdgeType(t *testing.T) {
	c := corrPair(pinnedSHA)
	edges := []pa.Edge{{From: c.ID, To: c.ID, Type: "bogus"}}
	in := baseInput([]pa.Claim{c}, edges, map[string]Expect{c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2), SourceRef: "o/r@p"}})
	if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
		t.Errorf("unknown edge type: err = %v, want errInput", err)
	}
}

func TestRejectEmptyLedgerVersion(t *testing.T) {
	c := corrPair(pinnedSHA)
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2), SourceRef: "o/r@p"}})
	in.LedgerVersion = ""
	if err := decodeErr(t, in, true); !errors.Is(err, errInput) {
		t.Errorf("empty ledger_version: err = %v, want errInput", err)
	}
}

// --- R3 guard: CI must never run the gate in ungraded mode -------------------

// TestWorkflowNeverAllowsUngraded greps the committed CI workflow: it must not pass
// -allow-ungraded, so the real-ledger gate stays strict. Dropping this guard (or
// adding the flag to CI) is a red build.
func TestWorkflowNeverAllowsUngraded(t *testing.T) {
	path := filepath.Join("..", "..", "..", "..", ".github", "workflows", "pa-reconcile.yml")
	b, err := os.ReadFile(path)
	if err != nil {
		t.Skipf("workflow not readable from here (%v); the CI-level guard runs in the repo", err)
	}
	if strings.Contains(string(b), "-allow-ungraded") {
		t.Errorf("pa-reconcile.yml must never pass -allow-ungraded (the real-ledger gate requires committed grades)")
	}
}

func compileSchema(t *testing.T) *jsonschema.Schema {
	t.Helper()
	const uri = "https://github.com/JamesPagetButler/confluent-trust/testdata/pa/notary-request.schema.json"
	b, err := os.ReadFile(filepath.Join("..", "..", "testdata", "pa", "notary-request.schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	var doc any
	if err := json.Unmarshal(b, &doc); err != nil {
		t.Fatalf("parse schema: %v", err)
	}
	cpl := jsonschema.NewCompiler()
	if err := cpl.AddResource(uri, doc); err != nil {
		t.Fatalf("register schema: %v", err)
	}
	s, err := cpl.Compile(uri)
	if err != nil {
		t.Fatalf("compile schema: %v", err)
	}
	return s
}
