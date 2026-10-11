// Command pa-reconcile is the QBP#692 gate over the vendored confluent-trust PA
// engine (tools/cth-pa/vendor-src/pa @ the pin in VENDOR.meta.json).
//
// It does three things and nothing else — no filing, no re-execution, no network:
//
//  1. RECOMPUTE. For every claim it grades local PA with pa.GradeClaim and folds
//     derivation edges into effective PA with pa.EffectivePA. The Derived blocks
//     it receives are the oracle of a re-execution that already happened upstream
//     (the Notary), exactly as in the engine's fixtures.
//
//  2. RECONCILE (QBP#692 AC2). When a claim carries a committed pa_local or
//     pa_effective and the recompute disagrees, that is a hard failure (exit 3):
//     a hand-typed PA, or an engine the vendor drifted from. Both committed
//     grades are checked, so a planted-stale pa_effective cannot pass while
//     pa_local matches (the effective recompute is load-bearing).
//
//  3. EMIT (notary#3 v1.3). For every claim below its required effective PA, or
//     whose evidence is stale, pa.RequestFor returns a notary-request; this CLI
//     stamps emitter=qbp-pa-reconcile and appends it to the JSON-lines artifact
//     the filer consumes (the filer is the only writer of issues). A shortfall is
//     NOT a failure: the gate stays green so the request — not red CI — carries
//     the remediation. Only a reconcile diff fails the gate.
//
// Every claim's pinned_sha is REQUIRED and must be a 40-hex blob (QBP#692 3c): a
// missing, blank or non-hex one is rejected (exit 2), never graded as
// unknown-provenance and silently emitted as stale. The emitted record's source_sha
// is this same pinned_sha (R2 — one source of truth). By default every claim must
// also carry both committed grades (R3); -allow-ungraded relaxes that for the
// fixture slice and is never passed in CI.
//
// Input (stdin), one JSON object. The claim/edge/policy fields are the engine's
// own JSON tags (pa.Claim, pa.Edge, pa.Policy); unknown fields are rejected so a
// misspelt field is never silently ignored. An `expect` map, keyed by claim id,
// carries the committed grades to reconcile against and the emit metadata:
//
//	{
//	  "policy": {"require_signature": false},
//	  "ledger_version": "6.13.0",
//	  "emitted_at": "2026-10-02T14:00:00Z",
//	  "claims": [ <pa.Claim> ... ],
//	  "edges":  [ {"from":"...","to":"...","type":"derivation"|"relevance"|"mention"} ... ],
//	  "expect": {
//	    "<claim id>": {
//	      "required_pa": 0|1|2,
//	      "committed_pa_local": 0|1|2,        // required unless -allow-ungraded (R3)
//	      "committed_pa_effective": 0|1|2,    // required unless -allow-ungraded (R3)
//	      "source_ref": "owner/repo@path",    // the record's source_sha = the claim's pinned_sha (R2)
//	      "pinning_consumer": ["..."],        // [] for an unpinned critical claim
//	      "detail": "..."                      // optional, short, human
//	    }
//	  }
//	}
//
// Output (stdout), one JSON object: the reconcile verdict and the emitted records.
//
//	{
//	  "ledger_version": "...", "engine": "...", "reconciled": n,
//	  "diffs":    [ {"claim_id":"...","field":"pa_local"|"pa_effective","committed":g,"recomputed":g} ... ],
//	  "requests": [ <notary-request v1.3> ... ]
//	}
//
// The verifier is attestation.StubV0 (the inter#149 v0 stub): every record is
// unsigned and the truth guarantee is re-execution. Flipping
// policy.require_signature to true zeroes every assistant (wrong_role) until a v1
// verifier exists — the engine's rule, not this CLI's.
//
// Exit codes: 0 reconciled clean (requests, if any, emitted); 1 usage or I/O
// failure; 2 input rejected (malformed JSON, unknown field, duplicate claim id,
// an edge whose endpoint is not a supplied claim, an unknown edge type, a
// pinned_sha that is not a 40-hex blob, an empty ledger_version, a claim with no
// expect entry, or — absent -allow-ungraded — a claim missing a committed grade);
// 3 a reconcile diff.
package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"sort"

	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/attestation"
	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/pa"
)

// EngineID names the vendored engine and its pin; it is stamped into the output
// so a downstream record can say which engine reconciled it. It matches pa-grade.
const EngineID = "confluent-trust/internal/pa@13de2f728707cd4431e0116126c530247f132158"

// Emitter is this gate's id in the notary-request schema's emitter enum.
const Emitter = "qbp-pa-reconcile"

// Expect carries, per claim, the committed grades to reconcile against and the
// metadata the emitted record needs. A nil committed grade skips that diff (a
// claim the backfill has not graded yet), so the gate is green on commit 2 and
// the diffs light up as the backfill lands.
type Expect struct {
	RequiredPA         pa.Grade  `json:"required_pa"`
	CommittedLocal     *pa.Grade `json:"committed_pa_local"`
	CommittedEffective *pa.Grade `json:"committed_pa_effective"`
	SourceRef          string    `json:"source_ref"`
	PinningConsumer    []string  `json:"pinning_consumer"`
	Detail             string    `json:"detail,omitempty"`
}

// isHexSHA reports whether s is a 40-char lowercase hex string — the shape of a
// git blob/commit sha and the v1.3 source_sha. Used to reject an empty, blank, or
// otherwise malformed pinned_sha, not just the empty string (§I4/Gemini break-3).
func isHexSHA(s string) bool {
	if len(s) != 40 {
		return false
	}
	for _, c := range s {
		if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) {
			return false
		}
	}
	return true
}

// Input is the stdin document: the engine's own types plus the expect map.
type Input struct {
	Policy        pa.Policy         `json:"policy"`
	LedgerVersion string            `json:"ledger_version"`
	EmittedAt     string            `json:"emitted_at"`
	Claims        []pa.Claim        `json:"claims"`
	Edges         []pa.Edge         `json:"edges"`
	Expect        map[string]Expect `json:"expect"`
}

// Diff is one disagreement between a committed grade and the recompute (AC2).
type Diff struct {
	ClaimID    string   `json:"claim_id"`
	Field      string   `json:"field"` // "pa_local" | "pa_effective"
	Committed  pa.Grade `json:"committed"`
	Recomputed pa.Grade `json:"recomputed"`
}

// Output is the stdout document.
type Output struct {
	LedgerVersion string             `json:"ledger_version"`
	Engine        string             `json:"engine"`
	Reconciled    int                `json:"reconciled"`
	Diffs         []Diff             `json:"diffs"`
	Requests      []pa.NotaryRequest `json:"requests"`
}

// errInput marks a rejected input (exit 2); errDiff marks a reconcile diff
// (exit 3); anything else is an I/O failure (exit 1).
var (
	errInput = errors.New("pa-reconcile: input rejected")
	errDiff  = errors.New("pa-reconcile: reconcile diff")
)

func inputErr(format string, args ...any) error {
	return fmt.Errorf("%w: %s", errInput, fmt.Sprintf(format, args...))
}

// Decode parses and fail-closed-validates the stdin document. When
// requireCommitted is true (the default; -allow-ungraded turns it off) every
// claim must carry both committed grades, so a missing one is a loud error, not
// a silently-skipped reconcile (§I4 R3 / Gemini break-1).
func Decode(r io.Reader, requireCommitted bool) (Input, error) {
	var in Input
	dec := json.NewDecoder(r)
	dec.DisallowUnknownFields()
	if err := dec.Decode(&in); err != nil {
		return in, inputErr("%v", err)
	}
	if dec.More() {
		return in, inputErr("trailing data after the input object")
	}
	if in.LedgerVersion == "" {
		return in, inputErr("empty \"ledger_version\" (R3: records must name the ledger version)")
	}
	ids := make(map[string]bool, len(in.Claims))
	for i, c := range in.Claims {
		if c.ID == "" {
			return in, inputErr("claims[%d]: empty \"claim\" id", i)
		}
		if ids[c.ID] {
			return in, inputErr("duplicate claim id %q", c.ID)
		}
		// QBP#692 3c: pinned_sha must be a real 40-hex blob, never empty/blank/
		// non-hex. An unusable pin would make the engine grade every assistant stale
		// (unknown provenance) and silently emit it; we refuse, so a bad pin is a
		// loud input error, not a quiet stale. (A bare != "" check let a space or a
		// null byte through — Gemini break-3.)
		if !isHexSHA(c.PinnedSHA) {
			return in, inputErr("claims[%d] %q: \"pinned_sha\" must be a 40-hex-lowercase blob, got %q (3c)", i, c.ID, c.PinnedSHA)
		}
		ex, ok := in.Expect[c.ID]
		if !ok {
			return in, inputErr("claim %q has no \"expect\" entry (required_pa is mandatory)", c.ID)
		}
		// R3: committed grades are required unless explicitly running ungraded. A
		// nil committed grade would skip the reconcile diff for that claim; with the
		// backfill landed, an absent grade is a deleted/never-written value, not an
		// "ungraded yet" one, so skipping it is the omission hole P3 found.
		if requireCommitted && (ex.CommittedLocal == nil || ex.CommittedEffective == nil) {
			return in, inputErr("claim %q: committed_pa_local and committed_pa_effective are required (R3); -allow-ungraded is for the fixture slice only and is never passed in CI", c.ID)
		}
		ids[c.ID] = true
	}
	for i, e := range in.Edges {
		switch e.Type {
		case pa.EdgeDerivation, "relevance", "mention":
		default:
			return in, inputErr("edges[%d]: unknown edge type %q", i, e.Type)
		}
		if !ids[e.From] {
			return in, inputErr("edges[%d]: \"from\" %q is not a supplied claim", i, e.From)
		}
		if !ids[e.To] {
			return in, inputErr("edges[%d]: \"to\" %q is not a supplied claim", i, e.To)
		}
	}
	// Every expect key must be a supplied claim — a stray expectation is a typo, not
	// something to silently ignore.
	for id := range in.Expect {
		if !ids[id] {
			return in, inputErr("expect[%q] is not a supplied claim", id)
		}
	}
	return in, nil
}

// Reconcile recomputes every claim, collects the committed-vs-recomputed diffs
// (both local and effective), and builds the notary-request records for the
// shortfalls and stale claims. It is pure: the caller decides exit behaviour.
func Reconcile(in Input, v attestation.Verifier) Output {
	grades := make(map[string]pa.Grade, len(in.Claims))
	results := make([]pa.Result, len(in.Claims))
	for i, c := range in.Claims {
		results[i] = pa.GradeClaim(c, in.Policy, v)
		grades[c.ID] = results[i].PA
	}
	deps := pa.DerivationDeps(in.Edges)

	out := Output{
		LedgerVersion: in.LedgerVersion,
		Engine:        EngineID,
		Reconciled:    len(in.Claims),
		Diffs:         []Diff{},
		Requests:      []pa.NotaryRequest{},
	}
	for i, c := range in.Claims {
		r := results[i]
		eff := pa.EffectivePA(c.ID, grades, deps)
		ex := in.Expect[c.ID]

		// AC2: a committed grade that disagrees with the recompute is a diff. Both
		// local and effective are checked — the effective recompute is not optional,
		// so a planted-stale pa_effective fails even when pa_local still matches.
		if ex.CommittedLocal != nil && *ex.CommittedLocal != r.PA {
			out.Diffs = append(out.Diffs, Diff{c.ID, "pa_local", *ex.CommittedLocal, r.PA})
		}
		if ex.CommittedEffective != nil && *ex.CommittedEffective != eff {
			out.Diffs = append(out.Diffs, Diff{c.ID, "pa_effective", *ex.CommittedEffective, eff})
		}

		// notary#3: emit a request on a shortfall or staleness. The engine decides
		// nil vs record and sets reason/stale from the grade itself; we only stamp
		// the emitter id (overwriting the engine's standalone default).
		meta := pa.RequestMeta{
			LedgerVersion: in.LedgerVersion,
			SourceRef:     ex.SourceRef,
			// R2: one source of truth for source_sha — the composite pin the gate
			// actually evaluated (c.PinnedSHA), not a second field that could name a
			// sha the staleness check never saw and wrong-key the dedupe tuple.
			SourceSHA:       c.PinnedSHA,
			EmittedAt:       in.EmittedAt,
			Detail:          ex.Detail,
			PinningConsumer: ex.PinningConsumer,
		}
		if req := pa.RequestFor(c, r, eff, ex.RequiredPA, meta); req != nil {
			req.Emitter = Emitter
			out.Requests = append(out.Requests, *req)
		}
	}
	sort.SliceStable(out.Diffs, func(i, j int) bool {
		if out.Diffs[i].ClaimID != out.Diffs[j].ClaimID {
			return out.Diffs[i].ClaimID < out.Diffs[j].ClaimID
		}
		return out.Diffs[i].Field < out.Diffs[j].Field
	})
	return out
}

// Run decodes r, reconciles with StubV0, writes the verdict to w, and — if
// emitPath is non-empty — writes the requests as JSON lines there for the filer.
// It returns errDiff when any diff was found, so the caller exits 3.
func Run(r io.Reader, w io.Writer, emitPath string, indent, requireCommitted bool) error {
	in, err := Decode(r, requireCommitted)
	if err != nil {
		return err
	}
	out := Reconcile(in, attestation.StubV0{})

	if emitPath != "" {
		if err := writeJSONLines(emitPath, out.Requests); err != nil {
			return err
		}
	}

	enc := json.NewEncoder(w)
	if indent {
		enc.SetIndent("", "  ")
	}
	if err := enc.Encode(out); err != nil {
		return err
	}
	if len(out.Diffs) > 0 {
		return fmt.Errorf("%w: %d field(s) disagree with the committed PA", errDiff, len(out.Diffs))
	}
	return nil
}

// writeJSONLines writes one notary-request per line (the filer's artifact shape).
func writeJSONLines(path string, reqs []pa.NotaryRequest) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	enc := json.NewEncoder(f)
	for _, req := range reqs {
		if err := enc.Encode(req); err != nil {
			return err
		}
	}
	return f.Close()
}

func main() {
	indent := flag.Bool("indent", false, "pretty-print the stdout verdict")
	emit := flag.String("emit", "", "write the notary-request records as JSON lines to this path")
	allowUngraded := flag.Bool("allow-ungraded", false, "permit claims with no committed PA (fixture slice only; NEVER passed in CI — the real-ledger gate requires committed grades)")
	version := flag.Bool("version", false, "print the vendored engine id and exit")
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: pa-reconcile [-indent] [-emit requests.jsonl] < input.json > verdict.json\n\n")
		fmt.Fprintf(os.Stderr, "Recomputes PA with the vendored confluent-trust engine (%s),\nfails (exit 3) on any diff from the committed PA, and emits notary-requests.\nSee the package doc for the input/output JSON contract.\n\n", EngineID)
		flag.PrintDefaults()
	}
	flag.Parse()
	if *version {
		fmt.Println(EngineID)
		return
	}
	if flag.NArg() != 0 {
		flag.Usage()
		os.Exit(1)
	}
	if err := Run(os.Stdin, os.Stdout, *emit, *indent, !*allowUngraded); err != nil {
		fmt.Fprintln(os.Stderr, err)
		switch {
		case errors.Is(err, errInput):
			os.Exit(2)
		case errors.Is(err, errDiff):
			os.Exit(3)
		default:
			os.Exit(1)
		}
	}
}
