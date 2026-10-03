// Command pa-grade is a thin CLI over the vendored confluent-trust PA engine
// (tools/cth-pa/vendor-src/pa @ the pin recorded in VENDOR.meta.json).
//
// It is the Python encoder's dependency for QBP#692: the encoder shapes the
// ledger's evidence into the engine's own input types, pa-grade grades every
// claim with pa.GradeClaim and folds derivation edges with pa.EffectivePA, and
// the encoder consumes the JSON that comes back. pa-grade does no filing, no
// re-execution and no network: the Derived blocks it receives are the oracle
// of a re-execution that already happened upstream of it, exactly as in the
// engine's own fixtures.
//
// Input (stdin), one JSON object. Field names are the engine's own JSON tags
// (pa.Policy, pa.Claim, pa.Edge); unknown fields are rejected so a misspelt
// field can never be silently ignored:
//
//	{
//	  "policy": {"require_signature": false},
//	  "claims": [ <pa.Claim> ... ],
//	  "edges":  [ {"from": "<claim>", "to": "<claim>", "type": "derivation"|"relevance"|"mention"} ... ]
//	}
//
// Output (stdout), one JSON object; per-claim fields mirror pa.Result
// (claim_id, pa, clean_count, flags) plus effective_pa from pa.EffectivePA and
// a per-assistant split of the engine's "<assistant>:<flag>" flags:
//
//	{
//	  "engine": "...", "verifier": "attestation.StubV0", "policy": {...},
//	  "claims": [
//	    {"claim_id": "...", "pa": 0|1|2, "effective_pa": 0|1|2, "clean_count": n,
//	     "flags": [<raw engine flags>],
//	     "assistants": [{"assistant": "...", "evidence_ref": "...", "counts": bool, "flags": [<bare flag types>]}]}
//	  ]
//	}
//
// The verifier is attestation.StubV0 — the inter#149 v0 stub, under which every
// record is unsigned and the truth guarantee is re-execution. Flipping
// policy.require_signature to true therefore zeroes every assistant (wrong_role)
// until a v1 verifier exists; that is the engine's rule, not this CLI's.
//
// Exit codes: 0 graded; 1 usage or I/O failure; 2 input rejected (malformed
// JSON, unknown field, duplicate claim id, or an edge whose endpoint is not one
// of the supplied claims — the engine would grade a missing dependency as PA0,
// which this CLI refuses to do silently).
package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"sort"
	"strings"

	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/attestation"
	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/pa"
)

// EngineID names the vendored engine and its pin; it is stamped into every
// output so a downstream record can say which engine graded it.
const EngineID = "confluent-trust/internal/pa@13de2f728707cd4431e0116126c530247f132158"

// Input is the stdin document. It is exactly the engine's own types.
type Input struct {
	Policy pa.Policy  `json:"policy"`
	Claims []pa.Claim `json:"claims"`
	Edges  []pa.Edge  `json:"edges"`
}

// AssistantOut is the per-assistant split of a claim's engine flags. Counts is
// true iff the engine attached no flag to this assistant — every path on which
// assistantCounts rejects an assistant appends a "<assistant>:<flag>", so the
// absence of a prefixed flag is the engine's own "this one counted". Two
// assistants on one claim sharing the same Assistant name share a prefix and
// therefore a flag set; the engine has no finer key.
type AssistantOut struct {
	Assistant   string   `json:"assistant"`
	EvidenceRef string   `json:"evidence_ref"`
	Counts      bool     `json:"counts"`
	Flags       []string `json:"flags"`
}

// ClaimOut mirrors pa.Result and adds effective_pa and the assistant split.
type ClaimOut struct {
	ClaimID     string         `json:"claim_id"`
	PA          pa.Grade       `json:"pa"`
	EffectivePA pa.Grade       `json:"effective_pa"`
	CleanCount  int            `json:"clean_count"`
	Flags       []string       `json:"flags"`
	Assistants  []AssistantOut `json:"assistants"`
}

// Output is the stdout document.
type Output struct {
	Engine   string     `json:"engine"`
	Verifier string     `json:"verifier"`
	Policy   pa.Policy  `json:"policy"`
	Claims   []ClaimOut `json:"claims"`
}

// errInput marks a rejected input (exit 2) as opposed to an I/O failure (exit 1).
var errInput = errors.New("pa-grade: input rejected")

func inputErr(format string, args ...any) error {
	return fmt.Errorf("%w: %s", errInput, fmt.Sprintf(format, args...))
}

// Decode parses and validates the stdin document.
func Decode(r io.Reader) (Input, error) {
	var in Input
	dec := json.NewDecoder(r)
	dec.DisallowUnknownFields()
	if err := dec.Decode(&in); err != nil {
		return in, inputErr("%v", err)
	}
	if dec.More() {
		return in, inputErr("trailing data after the input object")
	}
	ids := make(map[string]bool, len(in.Claims))
	for i, c := range in.Claims {
		if c.ID == "" {
			return in, inputErr("claims[%d]: empty \"claim\" id", i)
		}
		if ids[c.ID] {
			return in, inputErr("duplicate claim id %q", c.ID)
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
	return in, nil
}

// Grade runs the engine over a decoded input with the given verifier.
func Grade(in Input, v attestation.Verifier, verifierName string) Output {
	grades := make(map[string]pa.Grade, len(in.Claims))
	results := make([]pa.Result, len(in.Claims))
	for i, c := range in.Claims {
		results[i] = pa.GradeClaim(c, in.Policy, v)
		grades[c.ID] = results[i].PA
	}
	deps := pa.DerivationDeps(in.Edges)

	out := Output{Engine: EngineID, Verifier: verifierName, Policy: in.Policy, Claims: make([]ClaimOut, len(in.Claims))}
	for i, c := range in.Claims {
		r := results[i]
		flags := r.Flags
		if flags == nil {
			flags = []string{}
		}
		co := ClaimOut{
			ClaimID:     r.ClaimID,
			PA:          r.PA,
			EffectivePA: pa.EffectivePA(c.ID, grades, deps),
			CleanCount:  r.CleanCount,
			Flags:       flags,
			Assistants:  make([]AssistantOut, len(c.Assistants)),
		}
		for j, a := range c.Assistants {
			own := []string{}
			for _, f := range r.Flags {
				if rest, ok := strings.CutPrefix(f, a.Assistant+":"); ok {
					own = append(own, rest)
				}
			}
			sort.Strings(own)
			co.Assistants[j] = AssistantOut{Assistant: a.Assistant, EvidenceRef: a.EvidenceRef, Counts: len(own) == 0, Flags: own}
		}
		out.Claims[i] = co
	}
	return out
}

// Run is the CLI body: decode r, grade with StubV0, encode to w.
func Run(r io.Reader, w io.Writer, indent bool) error {
	in, err := Decode(r)
	if err != nil {
		return err
	}
	out := Grade(in, attestation.StubV0{}, "attestation.StubV0")
	enc := json.NewEncoder(w)
	if indent {
		enc.SetIndent("", "  ")
	}
	return enc.Encode(out)
}

func main() {
	indent := flag.Bool("indent", false, "pretty-print the output JSON")
	version := flag.Bool("version", false, "print the vendored engine id and exit")
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: pa-grade [-indent] < input.json > output.json\n\n")
		fmt.Fprintf(os.Stderr, "Grades claims with the vendored confluent-trust PA engine (%s).\nSee the package doc for the input/output JSON contract.\n\n", EngineID)
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
	if err := Run(os.Stdin, os.Stdout, *indent); err != nil {
		fmt.Fprintln(os.Stderr, err)
		if errors.Is(err, errInput) {
			os.Exit(2)
		}
		os.Exit(1)
	}
}
