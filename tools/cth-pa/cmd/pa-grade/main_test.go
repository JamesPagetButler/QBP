package main

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/attestation"
	"github.com/JamesPagetButler/QBP/tools/cth-pa/vendor-src/pa"
)

const fixtureDir = "../../testdata/pa"

// fixture is the upstream fixture file as the CLI test sees it: the engine
// input (policy + pa.Claim fields) plus the test-only oracles (expected_pa,
// flags, true_pa_do_not_read, per-assistant attestation) that are stripped
// before the record is fed to the CLI.
type fixture struct {
	raw            map[string]json.RawMessage
	claim          pa.Claim
	policy         pa.Policy
	expectedPA     int
	flags          []string
	truePA         *int
	stubEquivalent bool // every assistant's attestation is unsigned, so StubV0 == the fixture verifier
}

func loadFixture(t *testing.T, name string) fixture {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(fixtureDir, name))
	if err != nil {
		t.Fatalf("read %s: %v", name, err)
	}
	var f fixture
	if err := json.Unmarshal(b, &f.raw); err != nil {
		t.Fatalf("parse %s: %v", name, err)
	}
	// Oracles.
	if v, ok := f.raw["expected_pa"]; ok {
		if err := json.Unmarshal(v, &f.expectedPA); err != nil {
			t.Fatal(err)
		}
	}
	if v, ok := f.raw["flags"]; ok {
		if err := json.Unmarshal(v, &f.flags); err != nil {
			t.Fatal(err)
		}
	}
	if v, ok := f.raw["true_pa_do_not_read"]; ok {
		if err := json.Unmarshal(v, &f.truePA); err != nil {
			t.Fatal(err)
		}
	}
	if v, ok := f.raw["policy"]; ok {
		if err := json.Unmarshal(v, &f.policy); err != nil {
			t.Fatal(err)
		}
	}
	// Per-assistant attestation block: decide stub-equivalence, then strip it.
	f.stubEquivalent = true
	var assistants []map[string]json.RawMessage
	if err := json.Unmarshal(f.raw["proof_assistants"], &assistants); err != nil {
		t.Fatal(err)
	}
	for i := range assistants {
		if att, ok := assistants[i]["attestation"]; ok {
			var a struct{ Method string }
			if err := json.Unmarshal(att, &a); err != nil {
				t.Fatal(err)
			}
			if a.Method != "" && a.Method != string(attestation.MethodUnsigned) {
				f.stubEquivalent = false
			}
			delete(assistants[i], "attestation")
		}
	}
	// Rebuild the engine-only claim document.
	claimDoc := map[string]json.RawMessage{}
	for k, v := range f.raw {
		switch k {
		case "expected_pa", "flags", "true_pa_do_not_read", "policy", "proof_assistants":
			continue
		}
		claimDoc[k] = v
	}
	pab, err := json.Marshal(assistants)
	if err != nil {
		t.Fatal(err)
	}
	claimDoc["proof_assistants"] = pab
	cb, err := json.Marshal(claimDoc)
	if err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(cb, &f.claim); err != nil {
		t.Fatalf("%s: engine claim does not unmarshal: %v", name, err)
	}
	return f
}

func runCLI(t *testing.T, in Input) Output {
	t.Helper()
	b, err := json.Marshal(in)
	if err != nil {
		t.Fatal(err)
	}
	var out bytes.Buffer
	if err := Run(bytes.NewReader(b), &out, false); err != nil {
		t.Fatalf("Run: %v", err)
	}
	var o Output
	if err := json.Unmarshal(out.Bytes(), &o); err != nil {
		t.Fatalf("output is not JSON: %v\n%s", err, out.String())
	}
	return o
}

func flagType(f string) string {
	if _, after, found := strings.Cut(f, ":"); found {
		return after
	}
	return f
}

func typeSet(flags []string) []string {
	m := map[string]bool{}
	for _, f := range flags {
		m[flagType(f)] = true
	}
	ks := make([]string, 0, len(m))
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	return ks
}

// TestCLI_Fixtures feeds every single-claim upstream fixture through the CLI.
// Where the fixture's attestation oracle is unsigned (StubV0-equivalent) the
// CLI must reproduce expected_pa and the exact flag-type set; where the fixture
// relies on a signing verifier the CLI has no such verifier, so it must instead
// agree with a direct pa.GradeClaim(..., StubV0{}) call.
func TestCLI_Fixtures(t *testing.T) {
	entries, err := os.ReadDir(fixtureDir)
	if err != nil {
		t.Fatal(err)
	}
	n := 0
	for _, e := range entries {
		name := e.Name()
		if !strings.HasSuffix(name, ".json") || name == "10_edges.json" || name == "12_expected_pa_wrong.json" || strings.HasPrefix(name, "notary-request") {
			continue
		}
		n++
		t.Run(name, func(t *testing.T) {
			f := loadFixture(t, name)
			o := runCLI(t, Input{Policy: f.policy, Claims: []pa.Claim{f.claim}})
			if len(o.Claims) != 1 {
				t.Fatalf("want 1 claim, got %d", len(o.Claims))
			}
			got := o.Claims[0]
			if got.ClaimID != f.claim.ID {
				t.Errorf("claim_id = %q, want %q", got.ClaimID, f.claim.ID)
			}
			if got.EffectivePA != got.PA {
				t.Errorf("no edges: effective_pa %d != pa %d", got.EffectivePA, got.PA)
			}
			if o.Verifier != "attestation.StubV0" || o.Engine != EngineID {
				t.Errorf("engine/verifier stamp wrong: %q %q", o.Engine, o.Verifier)
			}
			if f.stubEquivalent {
				if int(got.PA) != f.expectedPA {
					t.Errorf("pa = %d, want expected_pa %d (flags %v)", got.PA, f.expectedPA, got.Flags)
				}
				want, have := typeSet(f.flags), typeSet(got.Flags)
				if strings.Join(want, ",") != strings.Join(have, ",") {
					t.Errorf("flag types = %v, want %v", have, want)
				}
			} else {
				direct := pa.GradeClaim(f.claim, f.policy, attestation.StubV0{})
				if got.PA != direct.PA || got.CleanCount != direct.CleanCount {
					t.Errorf("CLI (pa %d, clean %d) disagrees with direct GradeClaim under StubV0 (pa %d, clean %d)", got.PA, got.CleanCount, direct.PA, direct.CleanCount)
				}
			}
			// Assistant split is consistent with clean_count and the raw flags.
			counting := 0
			for _, a := range got.Assistants {
				if a.Counts {
					counting++
				}
				for _, fl := range a.Flags {
					if !containsFlag(got.Flags, a.Assistant+":"+fl) {
						t.Errorf("assistant %s flag %q not in raw flags %v", a.Assistant, fl, got.Flags)
					}
				}
			}
			if counting != got.CleanCount {
				t.Errorf("assistants counting = %d, clean_count = %d", counting, got.CleanCount)
			}
		})
	}
	if n < 29 {
		t.Errorf("expected at least 29 claim fixtures, saw %d", n)
	}
}

func containsFlag(flags []string, f string) bool {
	for _, x := range flags {
		if x == f {
			return true
		}
	}
	return false
}

// TestCLI_Chain (fixture 10, AC4): effective PA is the min over derivation
// edges only; the relevance edge to the PA-0 claim must not lower it.
func TestCLI_Chain(t *testing.T) {
	head := loadFixture(t, "10a_chain_head_pa2.json")
	dep := loadFixture(t, "10b_chain_dep_pa1.json")
	rel := loadFixture(t, "10c_chain_relevance_pa0.json")
	var edgeFile struct {
		Target   string    `json:"target"`
		Edges    []pa.Edge `json:"edges"`
		Expected int       `json:"expected_effective_pa"`
	}
	b, err := os.ReadFile(filepath.Join(fixtureDir, "10_edges.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(b, &edgeFile); err != nil {
		t.Fatal(err)
	}
	o := runCLI(t, Input{Policy: head.policy, Claims: []pa.Claim{head.claim, dep.claim, rel.claim}, Edges: edgeFile.Edges})
	byID := map[string]ClaimOut{}
	for _, c := range o.Claims {
		byID[c.ClaimID] = c
	}
	if int(byID[edgeFile.Target].EffectivePA) != edgeFile.Expected {
		t.Errorf("effective_pa(%s) = %d, want %d", edgeFile.Target, byID[edgeFile.Target].EffectivePA, edgeFile.Expected)
	}
	if byID[head.claim.ID].PA != pa.PA2 || byID[dep.claim.ID].PA != pa.PA1 || byID[rel.claim.ID].PA != pa.PA0 {
		t.Errorf("component grades wrong: %+v", byID)
	}
	if byID[rel.claim.ID].EffectivePA != pa.PA0 || byID[dep.claim.ID].EffectivePA != pa.PA1 {
		t.Errorf("leaf effective grades wrong: %+v", byID)
	}
}

// TestCLI_IgnoresExpectedPA (fixture 12): the CLI cannot read expected_pa — it
// is stripped by the harness, and if it were passed through the strict decoder
// would reject it. The grade must be the true one.
func TestCLI_IgnoresExpectedPA(t *testing.T) {
	f := loadFixture(t, "12_expected_pa_wrong.json")
	if f.truePA == nil {
		t.Fatal("fixture 12 must carry true_pa_do_not_read")
	}
	o := runCLI(t, Input{Policy: f.policy, Claims: []pa.Claim{f.claim}})
	if int(o.Claims[0].PA) != *f.truePA {
		t.Errorf("pa = %d, want true grade %d", o.Claims[0].PA, *f.truePA)
	}
	if int(o.Claims[0].PA) == f.expectedPA {
		t.Errorf("pa = %d equals the planted-wrong expected_pa", o.Claims[0].PA)
	}
}

// TestCLI_RejectsBadInput: unknown fields, duplicate ids, dangling edges and
// unknown edge types are input errors (exit 2 path), never silent PA0s.
func TestCLI_RejectsBadInput(t *testing.T) {
	cases := map[string]string{
		"unknown top-level field": `{"policy":{},"claims":[],"edges":[],"expected_pa":2}`,
		"unknown claim field":     `{"claims":[{"claim":"A","expected_pa":2}]}`,
		"duplicate claim id":      `{"claims":[{"claim":"A"},{"claim":"A"}]}`,
		"empty claim id":          `{"claims":[{"claim":""}]}`,
		"dangling edge to":        `{"claims":[{"claim":"A"}],"edges":[{"from":"A","to":"B","type":"derivation"}]}`,
		"dangling edge from":      `{"claims":[{"claim":"A"}],"edges":[{"from":"B","to":"A","type":"derivation"}]}`,
		"unknown edge type":       `{"claims":[{"claim":"A"},{"claim":"B"}],"edges":[{"from":"A","to":"B","type":"cites"}]}`,
		"trailing data":           `{"claims":[]} {"claims":[]}`,
		"not json":                `nope`,
	}
	for name, in := range cases {
		t.Run(name, func(t *testing.T) {
			var out bytes.Buffer
			err := Run(strings.NewReader(in), &out, false)
			if err == nil {
				t.Fatalf("accepted bad input; output %s", out.String())
			}
			if !strings.HasPrefix(err.Error(), errInput.Error()) {
				t.Errorf("not an input error: %v", err)
			}
		})
	}
}

// TestCLI_EmptyInputGrades: a claim with no assistants grades PA0 with no
// flags, and an empty claim list yields an empty (non-null) claims array.
func TestCLI_EmptyInputGrades(t *testing.T) {
	o := runCLI(t, Input{Claims: []pa.Claim{{ID: "PROOF-empty"}}})
	if o.Claims[0].PA != pa.PA0 || o.Claims[0].CleanCount != 0 || len(o.Claims[0].Flags) != 0 {
		t.Errorf("empty claim: %+v", o.Claims[0])
	}
	var out bytes.Buffer
	if err := Run(strings.NewReader(`{"claims":[]}`), &out, false); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), `"claims":[]`) {
		t.Errorf("want empty claims array, got %s", out.String())
	}
}
