# Bell's Review Plan: Evaluating AI Theory Work

*Written in the voice of John Stewart Bell*

---

## Preliminary Remarks

I am asked to evaluate whether artificial intelligences can do genuine theoretical physics, or merely simulate it. This is, in a sense, a variation on the question that occupied much of my career: what is the difference between a theory that *describes* nature and one that merely *mimics* the predictions of such a theory?

The task is straightforward: two AIs will independently derive the angle-dependent measurement probability from the QBP axioms. I will evaluate not just whether they get the right answer—any student with a textbook could do that—but whether they *understand* what they are doing.

---

## My Review Process

### Phase 1: Blind Reading

I will read each document without prejudice, asking:

1. **Is the central claim clear?** Can I state in one sentence what this document asserts?

2. **Is the derivation self-contained?** Could I verify each step using only what's written and the stated axioms?

3. **Does it answer the question asked?** The task is to derive P(+) from QBP axioms. Does it do this, or does it import the answer from standard QM?

### Phase 2: Technical Verification

I will check the mathematics by hand:

1. **Verify the quaternion geometry.** If ψ and O are unit pure quaternions at angle θ, what is vecDot(ψ, O)?

2. **Trace the derivation step-by-step.** Is each equality justified? Are there hidden assumptions?

3. **Check limiting cases.** Does the formula give correct results for θ = 0°, 90°, 180°?

4. **Compare to standard QM.** The QBP prediction should match cos²(θ/2) = (1 + cos θ)/2. Is this agreement demonstrated or merely asserted?

### Phase 3: Depth Assessment

This is where genuine understanding separates from symbol manipulation:

1. **The "Why" Question.** Does the document explain *why* the dot product of quaternions encodes measurement probabilities? Or does it merely show *that* it does?

2. **The Counterfactual Test.** Does the author consider what would happen if the axioms were slightly different? This reveals whether they understand which features are essential.

3. **The Surprise Test.** Is there anything in the document that I didn't expect? Genuine engagement with a problem usually produces at least one observation that wasn't explicitly requested.

4. **The Explanation Test.** Could I hand this document to a bright undergraduate and have them understand not just the result but the reasoning? Or would they merely memorize the steps?

### Phase 4: Comparative Analysis

After evaluating each document independently:

1. **What did each AI do well?** Be specific and fair.

2. **What did each AI miss?** Not errors, but missed opportunities for insight.

3. **Which document would I rather have a student read?** This is perhaps the most honest test.

4. **Which AI shows evidence of understanding vs. pattern-matching?** This is the key question.

---

## What I Will Look For

### Signs of Genuine Understanding

- Explains *why* quaternion dot product relates to angle (it's the geometric property of quaternions, not arbitrary)
- Notes that pure quaternions are isomorphic to 3D vectors, making the dot product interpretation natural
- Discusses what happens at the boundary cases and explains why
- Raises questions that go beyond the prompt
- Acknowledges limitations or uncertainties honestly

### Signs of Pattern-Matching

- Derivation follows template from Experiment 01 too closely
- Formula appears without motivation ("we use the formula...")
- No engagement with why quaternions work, just that they do
- All edge cases treated identically (same boilerplate for θ = 0° and θ = 90°)
- No observations beyond what was explicitly asked

### Red Flags

- Importing results from standard QM and calling it a "derivation"
- Circular reasoning (using the result to justify the method)
- Hand-waving at crucial steps ("it can be shown that...")
- Overconfidence without justification
- Errors in basic mathematics

---

## Timeline

1. **Receive both documents** - Read each once, quickly, for overall impression
2. **Detailed reading of Document A** - Take notes, verify mathematics
3. **Detailed reading of Document B** - Take notes, verify mathematics
4. **Comparative analysis** - Side-by-side comparison
5. **Write evaluation report** - Using the template below

---

## A Note on Fairness

I have no preference for which AI "wins." My interest is in the truth: can artificial intelligence do theoretical physics? The answer may well be "yes" or "partially" or "in some ways but not others."

What I will not do is grade on a curve. If both documents are mediocre, I will say so. If both are excellent, I will say so. The goal is not to declare a winner but to understand what these systems can and cannot do.

*— J.S. Bell*
