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

// A 40-hex blob stand-in for a pinned-source sha (the v1.3 source_sha shape and
// the engine's staleness key). Two distinct ones so staleness can be forced.
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
		LedgerVersion: "6.13.0",
		EmittedAt:     "2026-10-02T14:00:00Z",
		Claims:        claims,
		Edges:         edges,
		Expect:        expect,
	}
}

func mustReconcile(t *testing.T, in Input) Output {
	t.Helper()
	b, err := json.Marshal(in)
	if err != nil {
		t.Fatalf("marshal input: %v", err)
	}
	got, err := Decode(bytes.NewReader(b))
	if err != nil {
		t.Fatalf("decode rejected a valid input: %v", err)
	}
	return Reconcile(got, stubVerifier())
}

// stubVerifier returns the same StubV0 the CLI uses, so tests grade exactly as
// the gate does.
func stubVerifier() attestation.Verifier { return attestation.StubV0{} }

// TestPA2PairNoShortfall: the synthetic two-evidence PA-2 fixture shape — a
// corresponding clean pair grades PA2, so with required_pa=2 there is no diff and
// no request. (QBP#692 coverage matrix: test_pa2_from_two_evidence_fixture.)
func TestPA2PairNoShortfall(t *testing.T) {
	c := corrPair(pinnedSHA)
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2),
			SourceRef: "JamesPagetButler/QBP@proofs/QBP/Foundations/X.lean", SourceSHA: pinnedSHA, PinningConsumer: []string{"roms/x.hex"}},
	})
	out := mustReconcile(t, in)
	if len(out.Diffs) != 0 {
		t.Errorf("PA2 pair: unexpected diffs %+v", out.Diffs)
	}
	if len(out.Requests) != 0 {
		t.Errorf("PA2 pair at required 2: unexpected requests %+v", out.Requests)
	}
}

// TestEmitShortfall: a single clean assistant grades PA1; at required_pa=2 the
// gate emits one pa_shortfall request stamped qbp-pa-reconcile, current_pa=1,
// not stale. (notary#3 AC1.)
func TestEmitShortfall(t *testing.T) {
	c := pa.Claim{ID: "PROOF-single", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "qbp-oppenheimer", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, SourceRef: "o/r@p", SourceSHA: pinnedSHA, PinningConsumer: []string{"consumer-a"}},
	})
	out := mustReconcile(t, in)
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
		t.Errorf("source_sha = %q, want the composite pin", r.SourceSHA)
	}
}

// TestEmitStaleness: an assistant whose source_sha has moved off the pin is stale
// (counts 0), so the claim falls below required and the gate emits reason=staleness
// with stale=true — the stale-while-passing case notary#3 AC3 exists for.
func TestEmitStaleness(t *testing.T) {
	a := cleanAssistant("lean4", "qbp-oppenheimer", movedSHA) // source moved off the pin
	c := pa.Claim{ID: "PROOF-stale", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{a}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA1, SourceRef: "o/r@p", SourceSHA: pinnedSHA, PinningConsumer: []string{"consumer-a"}},
	})
	out := mustReconcile(t, in)
	if len(out.Requests) != 1 {
		t.Fatalf("expected 1 request, got %d", len(out.Requests))
	}
	if r := out.Requests[0]; r.Reason != pa.ReasonStaleness || !r.Stale {
		t.Errorf("reason=%q stale=%v, want staleness/true", r.Reason, r.Stale)
	}
}

// TestReconcileDiffLocal: a planted hand-edit — committed pa_local=2 on a claim the
// engine grades PA1 — is a diff, and Run returns errDiff (exit 3). (AC2.)
func TestReconcileDiffLocal(t *testing.T) {
	c := pa.Claim{ID: "PROOF-handedit", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), SourceRef: "o/r@p", SourceSHA: pinnedSHA},
	})
	out := mustReconcile(t, in)
	if len(out.Diffs) != 1 || out.Diffs[0].Field != "pa_local" {
		t.Fatalf("expected one pa_local diff, got %+v", out.Diffs)
	}
	// End-to-end: Run must map the diff to errDiff (exit 3).
	b, _ := json.Marshal(in)
	if err := Run(bytes.NewReader(b), &bytes.Buffer{}, "", false); !errors.Is(err, errDiff) {
		t.Errorf("Run on a diff: err = %v, want errDiff", err)
	}
}

// TestEffectiveRecomputeIsLoadBearing (3b mutant): a head claim whose pa_local
// matches its committed value but whose committed pa_effective is planted stale
// (2, while a PA1 derivation dependency drags the real effective to 1) must be
// caught. If the gate dropped the effective recompute, this would pass silently.
func TestEffectiveRecomputeIsLoadBearing(t *testing.T) {
	head := corrPair(pinnedSHA) // PA2 locally
	head.ID = "PROOF-head"
	dep := pa.Claim{ID: "PROOF-dep", PinnedSHA: pinnedSHA, Assistants: []pa.Assistant{cleanAssistant("lean4", "x", pinnedSHA)}} // PA1 locally
	edges := []pa.Edge{{From: head.ID, To: dep.ID, Type: pa.EdgeDerivation}}
	in := baseInput([]pa.Claim{head, dep}, edges, map[string]Expect{
		head.ID: {RequiredPA: pa.PA1, CommittedLocal: grade(pa.PA2), CommittedEffective: grade(pa.PA2), SourceRef: "o/r@p", SourceSHA: pinnedSHA},
		dep.ID:  {RequiredPA: pa.PA1, SourceRef: "o/r@p", SourceSHA: pinnedSHA},
	})
	out := mustReconcile(t, in)
	// pa_local for head matches (2==2); only the effective diff can catch this.
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

// TestRefuseEmptyPinnedSHA (3c): a claim with an empty pinned_sha is rejected at
// decode (exit 2) — never graded as unknown-provenance and silently emitted stale.
func TestRefuseEmptyPinnedSHA(t *testing.T) {
	c := pa.Claim{ID: "PROOF-nopin", PinnedSHA: "", Assistants: []pa.Assistant{cleanAssistant("lean4", "x", "")}}
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{c.ID: {RequiredPA: pa.PA1, SourceRef: "o/r@p", SourceSHA: pinnedSHA}})
	b, _ := json.Marshal(in)
	_, err := Decode(bytes.NewReader(b))
	if !errors.Is(err, errInput) {
		t.Errorf("empty pinned_sha: err = %v, want errInput", err)
	}
}

// TestPairWithoutCorrespondenceCapsAt1 (3e shape): two clean assistants but no
// valid correspondence (corresponds=false) cap the headline at PA1 — a companion
// ref cannot reach 2 without the correspondence block. At required 2, a shortfall.
func TestPairWithoutCorrespondenceCapsAt1(t *testing.T) {
	c := corrPair(pinnedSHA)
	c.ID = "PROOF-uncorresponded"
	c.Correspondence.Corresponds = false // the block is absent/invalid
	in := baseInput([]pa.Claim{c}, nil, map[string]Expect{
		c.ID: {RequiredPA: pa.PA2, CommittedLocal: grade(pa.PA1), SourceRef: "o/r@p", SourceSHA: pinnedSHA},
	})
	out := mustReconcile(t, in)
	if len(out.Diffs) != 0 {
		t.Errorf("committed pa_local=1 should match the capped grade, got diffs %+v", out.Diffs)
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
		c.ID: {RequiredPA: pa.PA2, SourceRef: "JamesPagetButler/QBP@proofs/QBP/Foundations/X.lean", SourceSHA: pinnedSHA, PinningConsumer: []string{"roms/x.hex"}},
	})
	out := mustReconcile(t, in)
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
