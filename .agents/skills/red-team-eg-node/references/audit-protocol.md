# Cumulative node red-team protocol

## Contents

1. [Objective and verdict discipline](#1-objective-and-verdict-discipline)
2. [Cumulative semantics](#2-cumulative-semantics)
3. [Phase I: exact node contract](#3-phase-i-exact-node-contract)
4. [Phase II: sentence audit](#4-phase-ii-sentence-audit)
5. [Phase III: counterexample search](#5-phase-iii-counterexample-search)
6. [Phase IV: verdict](#6-phase-iv-verdict)
7. [Phase V: smallest local repair](#7-phase-v-smallest-local-repair)
8. [Special modular-arithmetic audit](#8-special-modular-arithmetic-audit)
9. [Prohibited review behavior](#9-prohibited-review-behavior)

## 1. Objective and verdict discipline

Red-team exactly one node of a cumulative structural-exhaustion proof. Try hard
to falsify every mathematically operative sentence, but call a candidate
relevant only when it satisfies the complete state reaching that node.

Distinguish throughout:

1. a counterexample to an isolated or simplified sentence;
2. a candidate excluded by an upstream invariant;
3. a genuine counterexample on the actual residual;
4. an ambiguity whose intended correction is already supported; and
5. a real local gap requiring repair.

Do not assess the whole theorem. Seek the smallest local correction that
preserves the existing strategy and routing graph.

## 2. Cumulative semantics

### Form the exact state

For the node `v`, form

```text
F(v) = minimal-counterexample facts
     + all facts established on the selected incoming path
     + every selected branch predicate
     + every residual exclusion already made
     + every retained or transferred ledger item.
```

Read “assume” as “work on the residual already carrying `F(v)`.” Do not read the
local lemma in isolation.

### Restrict admissible facts

Use a fact only when it is:

- proved at an ancestor on the current path;
- the current diamond's selected branch predicate;
- included explicitly in the residual definition; or
- proved by the node before it is consumed.

A named destination theorem is not automatically an upstream premise. The
directed proof graph, not printed theorem order, controls ancestry and routing.

### Preserve routed residuals

“Route to Type B,” “record exit (4),” “enter periodic response,” “pass to
support dependence,” and similar phrases do not assert that a target cycle has
already been found. Verify that the routed object satisfies every entry
hypothesis of its destination.

### Respect decision semantics

When a node tests `P`, the yes arm may retain `P` and the no arm must retain the
literal logical negation of `P`. Do not demand `P` globally. Check complement,
use, retention, and routing instead.

### Separate paper and formalization status

Lean may identify the exact contract, branch key, or ledger. Missing Lean code
is not a paper counterexample. A kernel-checked downstream theorem does not
prove that every upstream producer exists. A prose/Lean mismatch is a fidelity
finding until the paper mathematics itself is evaluated.

## 3. Phase I: exact node contract

Complete this phase before searching for errors.

### Incoming residual

State the exact mathematical objects reaching the node, including as applicable:

- graph class and selected support or boundaried piece;
- packing, window, response, or finite-state data;
- degree and target-avoidance constraints;
- minimality order and tie-breakers;
- exact branch predicate;
- charge, entropy, rank, deficit, or ledger data;
- exclusions already made; and
- proper/whole-graph, connected, minimal, scale-spanning, or interface status.

### Accumulated facts

List each available fact with its source node or label. At a merge distinguish:

- facts common to every incoming path;
- facts tagged to one incoming residual; and
- ledger objects retaining the route that produced them.

Never replace an explicit tagged union by an untagged intersection.

### Exact claim

Rewrite the node as a formal implication:

```text
accumulated facts + current branch predicate
  => stated conclusion or exhaustive alternatives.
```

Preserve every quantifier, dependency, strict inequality, and finite range.

### Outgoing contracts

For each outgoing edge, state its predicate, retained facts, newly introduced
fact, destination, and every entry hypothesis required there.

For a loop, state the pre-iteration and post-iteration residuals and the
well-founded integer/order that decreases on the back edge.

## 4. Phase II: sentence audit

Number every operative sentence in the statement and proof. Use this table:

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|

Classify each sentence as one of:

- definition;
- inherited branch fact;
- finite computation;
- arithmetic implication;
- graph-realizability assertion;
- exact counting assertion;
- replacement/minimality step;
- support-localization step;
- branch exhaustiveness claim;
- routing instruction;
- termination argument; or
- external theorem invocation.

For every sentence ask:

1. Are all variables and ambient objects defined?
2. Are all quantifiers correct, and is the claim uniform or existential?
3. Is every congruence taken modulo the stated modulus?
4. Is divisibility checked before dividing or reducing a modulus?
5. Does odd-part reduction retain the missing 2-adic condition?
6. Does a modular hit lift to an integer in the stated finite interval?
7. Is the coefficient in the central range, not merely congruent to one?
8. Are bounded end ranges, transients, and equality cases handled?
9. Is every counted length realized by an actual simple cycle?
10. Does uncrossing preserve boundary degree, simplicity, target safety, and
    every exposed state?
11. Does context equivalence come with a genuinely smaller graph representative?
12. Is a target-defective quotient used only for its justified role here?
13. Is rank incorrectly promoted to a full `2^k` realized code?
14. Does an injective encoding subtract only savings charged in its baseline?
15. Are decision arms literal logical complements?
16. Is charge/deficit transferred rather than silently deleted?
17. Does every residual meet the destination's complete entry contract?
18. Does every loop have a decreasing measure?
19. Are finite, asymptotic, and sufficiently-large-`n` claims separated?
20. Does a minimality replacement preserve every hypothesis and strictly
    decrease the declared order, including equal-size exchanges?

Use sentence-row statuses such as `SUPPORTED`, `EXCLUDED UPSTREAM`,
`AMBIGUOUS`, `FAILED`, or `ROUTING ONLY`; reserve the closed verdict taxonomy
for the report as a whole.

## 5. Phase III: counterexample search

Start a new candidate whenever data change. Do not quietly repair a failed
candidate and continue under the same identifier.

### Level 1: arithmetic or finite-state abstraction

Temporarily ignore graph realization. Systematically test:

- even/odd moduli, powers of two, and zero residues;
- empty compatible residue classes and extreme allowed residues;
- degenerate gcd values and increments with a shared large power of two;
- one frequent increment;
- central intervals straddling a dyadic scale while omitting every power;
- bounded transients and exponents;
- coefficient-range endpoints; and
- equality in every strict inequality.

For `g = 2^a u` with `u` odd, verify separately

```text
2^a | L+r,
2^(k-a) = (L+r)/2^a (mod u).
```

A hit modulo `u` is not a hit modulo `g`. For a claimed central-spectrum hit,
compute `t = (2^k-L-r)/g` and check `C_sys <= t <= T_r-C_sys`.

### Level 2: abstract combinatorial object

Try to realize the arithmetic data as the serial system, response system,
support family, quotient, or ledger object immediately upstream. Check:

- increment multiplicities and residue construction;
- frequent/rare classification;
- connected and inclusion-minimal support;
- disjoint interiors and declared interfaces;
- bounded end segments; and
- scale-spanning after every allowed deletion.

### Level 3: actual residual object

Finally require an actual graph satisfying every accumulated condition:

- minimum degree and target avoidance;
- exact boundary-degree profiles;
- proper/whole-graph support status;
- absence of every earlier exit and routed handoff;
- exact packing/window conditions and support minimality;
- graph realization and simplicity of counted cycles;
- fixed vertex/edge counts when required;
- canonical choices and tie-breakers; and
- every residual exclusion.

If a candidate fails any condition, label it exactly
`NON-APPLICABLE TO THE NODE` and name the earliest upstream fact excluding it.

### Mandatory attempts

Every report must contain at least:

1. one smallest-parameter test;
2. one parity or 2-adic test;
3. one boundary or finite-range test;
4. one graph-realizability test; and
5. one branch-routing test.

For each, give explicit data, hypotheses satisfied, accumulated facts violated,
and applicability to the actual residual.

## 6. Phase IV: verdict

Choose exactly one overall verdict:

- `VALID LOCAL COUNTEREXAMPLE`: the candidate satisfies the complete incoming
  contract and falsifies the conclusion.
- `ISOLATED-STATEMENT COUNTEREXAMPLE ONLY`: it refutes a simplified sentence
  but violates an accumulated fact.
- `PROSE AMBIGUITY`: the intended statement is valid under an accumulated fact,
  but the fact or quantifier is not stated clearly.
- `NONEXHAUSTIVE BRANCH`: outgoing predicates are not complements and leave a
  residual unassigned.
- `WRONG ROUTING DESTINATION`: a real residual fails the destination contract.
- `MISSING REPRESENTATIVE`: quotient/context data exist, but no actual smaller
  replacement satisfying minimality hypotheses is constructed.
- `MISSING RANGE OR DIVISIBILITY CHECK`: an arithmetic inference omits exact
  compatibility or a finite-range condition.
- `NO ISSUE FOUND`: every candidate is excluded upstream or handled by an
  existing branch.

Do not combine verdicts. Explain subordinate observations inside the selected
verdict.

## 7. Phase V: smallest local repair

Prefer, in order of locality:

1. state an already accumulated hypothesis;
2. correct the modulus or retain the full residue/phase;
3. restrict to compatible residues;
4. check the exact finite central range;
5. move bounded exceptions into the existing finite table;
6. add one local decision subdiamond;
7. route the uncaught complement to an existing residual;
8. construct an explicit smaller representative;
9. refine the minimality order for equal-size exchanges;
10. separate quotient rank from exact code realization;
11. replace an asymptotic implication by an exact integer decision;
12. add a decreasing loop measure; or
13. split an overbroad result into correctly typed residuals.

Provide all five repair components, even when the answer is “not applicable”:

1. full corrected statement in publication-quality prose;
2. complete local proof using only facts available at the node;
3. disposition of the proposed counterexample;
4. exact graph patch `source -> predicate -> destination`, including destination
   entry facts; and
5. downstream impact on every repeated theorem, table row, caption, analogue,
   “word for word” use, and Lean contract.

The skill is report-only: specify the patch but do not apply it.

At the repaired step, do not write “standard,” “clearly,” or “by the usual
argument” in place of the missing reasoning. State whether the candidate is
caught by the corrected direct-hit condition, the finite exceptional table,
the periodic-response branch, target defect, a graph-realizable replacement,
support dependence, Type A, Type B, or route 8.

## 8. Special modular-arithmetic audit

Whenever an orbit modulo a factor of `g` is used to infer an integer power in
`L + R + gZ`, write

```text
g = 2^a u,  u odd,
R_a = {r in R : 2^a divides L+r},
R_tilde_a = {(L+r)/2^a mod u : r in R_a}.
```

The direct-hit branch is valid only if there are `r,k,t` with

```text
k >= a,
r in R_a,
2^(k-a) = (L+r)/2^a (mod u),
t = (2^k-L-r)/g,
C_sys <= t <= T_r-C_sys.
```

Route every other case explicitly:

- exact full-modulus hit -> direct target/G1;
- no exact hit but a context distinguishes the full phase -> G2/target defect;
- indistinguishable context on proper support -> G3/actual representative;
- minimal support reaching a trace interface -> route-8 entry; or
- bounded exponents/ranges -> finite cold table.

Never route a raw no-hit residual directly to contradiction.

The bundled checker accepts JSON of the form:

```json
{
  "g": 12,
  "L": 0,
  "k_min": 0,
  "k_max": 20,
  "C_sys": 1,
  "residues": [
    {"r": 4, "T_r": 20},
    {"r": 1, "T_r": 20}
  ]
}
```

Its `raw_odd_part_hit_exponents` field deliberately reports the tempting
unfiltered projection modulo `u`; `odd_part_hit_exponents` reports only the
normalized congruence after `2^a | L+r` has been checked. Compare both fields
when auditing a proof that may have projected away the 2-adic phase.

## 9. Prohibited review behavior

Do not:

- read the lemma in isolation;
- treat a later theorem as an ancestor because it is cited or numbered later;
- demand independence globally when the graph tests it;
- treat routing, target defect, or a named exit as an automatic cycle;
- use missing Lean code as a paper counterexample;
- use kernel checking as proof of an unstated manuscript lemma;
- discard 2-adic compatibility, coefficient ranges, or end segments;
- call an abstract equivalent quotient a graph replacement;
- infer global theorem failure from a local issue; or
- invent a new branch before checking existing destination contracts.
