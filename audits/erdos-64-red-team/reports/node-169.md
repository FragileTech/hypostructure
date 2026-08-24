<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 169,
  "node_label": "trivial neutral-configuration residual: dense packing, every corridor terminal and neutral, \\(Q=E\\); every window is blocked at every dyadic scale",
  "panel": "fig:proof-diagram-part-xii",
  "contract_sha256": "3ffb4989b31dfd6d5aa61f1a65e534eb83f7d4bcce1d5846c22182f7072fe540",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "NO ISSUE FOUND",
  "audited_at": "2026-08-24T21:30:23Z"
}
-->

# Red-team audit: node [169]

## 1. Executive verdict

Verdict: **NO ISSUE FOUND**

Node [169] correctly packages the selected graph into the blocked class.  The incoming residual already supplies the fixed induced-(P_{13}) packing, the vertex and edge counts, minimum degree at least three, and global avoidance of every power-of-two cycle.  Those facts imply that the transported labelled copy of (G) contains every fixed window at its position and that no target cycle passes through any window.  The stronger terminal/neutral/(Q=E) facts are retained for the outgoing decision but are not needed for this membership inference.  All attempted counterexamples either violate the global counterexample condition or an earlier dense-residual fact.

## 2. Exact node contract

### Incoming residual

The sole immediate edge is [166] (	o) [169].  It carries the dense-packing residual in which every selected return corridor is terminal and neutral and is its own canonical representative, (Q=E).  The fixed maximal vertex-disjoint induced-(P_{13}) packing (mathcal P), its labelled window positions, the vertex set (V(G)), and the fixed edge count (m) are retained.

### Accumulated facts

- [1]--[6]: (G) is a finite simple counterexample, with (delta(G)\ge3) and no power-of-two cycle anywhere in (G); node [4] selected the counterexample and node [5] records the equivalent target-return exclusion.
- [8]--[14]: the minimal-counterexample consequences, boundary profiles, context universality, replacement, and hereditary target-uncompressibility remain available.  Node [169]'s membership claim consumes only the baseline and target-avoidance portion.
- [15], [17]--[21]: (G) contains induced (P_{13})'s; (mathcal P) is the fixed maximal disjoint induced-(P_{13}) packing with its label/window data; and the surviving spine carries the fixed labelled skeleton budget and near-cubic edge count.
- [158]--[160], [162]: the joint window package is unrealized, giving the dense inequality; the (	au(\theta)<1/4) arm did not fire; and the dense hot/cold pass leaves only its explicitly named residuals.
- [163], [165], [166]: on this incoming route, every selected configuration under consideration is terminal, equal-length, context-neutral, and satisfies the retained equality (Q=E).  The genuine-second-strand route [167]--[168] is a sibling terminal route and is not merged into [169].

### Current predicate and exact claim

Let (mathcal G^{\delta\ge3}_{n,m}) be the labelled graphs on (V(G)) with (m) edges and minimum degree at least three.  With (mathcal P)'s positions fixed, define

[
mathcal B(mathcal P)=\{H\inmathcal G^{\delta\ge3}_{n,m}:
  H[V(P)]\cong P_{13}\text{ at every }P\inmathcal P,
  \text{ and no power-of-two cycle of }H\text{ meets a window}\}.
]

A window is blocked at scale (2^j) when no cycle of length (2^j) passes through it.  The exact assertion is

[
  G\inmathcal B(mathcal P)
  \quad\text{and}\quad
  \forall P\inmathcal P\;\forall j,
  \text{(P) is blocked at scale (2^j)}.
]

The introductory residual sentence additionally retains that every selected corridor is terminal, neutral, and equal to its canonical representative.

### Outgoing contracts

The only immediate edge is [169] (	o) [170].  Node [170] is the literal decision whether the conditional barrier-state savings add at every fixed separated scale.  It retains the fixed class (mathcal B(mathcal P)), the fact that the selected graph is a member, the dense-packing overflow, the fixed packing/window labels, and the terminal neutral (Q=E) residual.  Its yes arm goes to compression [171]; its logical negation goes to the overlap-system route [172].  Node [169] supplies every entry datum needed to pose that decision.  The validity of the two later closure arguments is outside this single-node verdict.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| 1 | The incoming residual has every selected corridor terminal, neutral, and (Q=E). | Nodes [162], [163], and the selected [166] route. | Do not merge the sibling genuine-strand route [167]--[168]. | Inspect the live edge set: [166] is the sole predecessor of [169]. | SUPPORTED |
| 2 | Fix (V(G)), (m), and the maximal packing (mathcal P) with its positions. | Nodes [1], [17], and the inherited edge-count branch. | These data must remain fixed across the class being counted. | Relabel (G) onto the fixed labelled carrier and keep the transported window subsets. | SUPPORTED |
| 3 | (mathcal B(mathcal P)) consists exactly of fixed-((n,m)), minimum-degree-three labelled graphs containing the fixed induced windows and having no target cycle through a window. | Definition at node [169]. | “Through a window” means meeting at least one window vertex; it does not assert global target avoidance for every member (H). | Insert a target cycle disjoint from all windows: this does not contradict the definition, which intentionally blocks only window-meeting cycles. | SUPPORTED |
| 4 | A window is blocked at scale (2^j) iff no (2^j)-cycle passes through it. | Definition at node [169]. | Scales (1) and (2), if included linguistically, must be harmless in a simple graph. | Simple graphs have no cycles of length one or two; scales (2^j\ge4) are target lengths. | SUPPORTED |
| 5 | (G\inmathcal B(mathcal P)). | Fixed (V(G)), (m), (delta(G)\ge3), the induced-window packing, and global target avoidance. | Labelling must preserve edges, degrees, induced subgraphs, and cycle lengths. | Transport along an arbitrary vertex bijection; all four properties are isomorphism-invariant. | SUPPORTED |
| 6 | Every window of (G) is blocked at every dyadic scale. | Node [2]'s absence of every power-of-two cycle in (G), plus simplicity for lengths one and two. | The quantifier must cover every fixed window and every used scale. | A target cycle through any one window would already be a target cycle of (G). | SUPPORTED |
| 7 | The minimum-degree clause is essential for the later blocked-class counting setup. | The class is a subset of the near-cubic fixed-edge skeletons; `rem:blocked-class-checks` explains the intended baseline. | This is motivation for later entropy estimates, not a closure proved at node [169]. | Remove the clause: isolated induced paths give the large family described in the later check. | ROUTING ONLY |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take (n=13), (p_{13}=1), and let the single window occupy all vertices.  Requiring it to be induced makes the whole graph exactly (P_{13}), with two vertices of degree one and eleven of degree two.
- **Hypotheses satisfied:** The vertex set has the smallest possible order for one induced (P_{13}), and the window-position and induced-path clauses hold.
- **Accumulated facts violated:** The graph fails (delta(G)\ge3), first imposed at node [2], and therefore is not in (mathcal G^{\delta\ge3}_{n,m}).
- **Applicability:** **NON-APPLICABLE TO THE NODE**; node [2] excludes the smallest-order attempt.

### Parity or 2-adic test

- **Explicit data:** Test (j=0,1,2), giving proposed blocked lengths (1,2,4), and then arbitrary (j\ge2), giving (2^j\in\{4,8,16,\ldots\}).
- **Hypotheses satisfied:** These exhaust the low 2-adic boundary and all target scales.  The graph is finite and simple.
- **Accumulated facts violated:** None.  A simple graph has no cycles of length one or two, while node [2] excludes every cycle of length (2^j\ge4).
- **Applicability:** Applicable and non-falsifying.  The phrase “every dyadic scale” is valid whether it starts with the manuscript's target range (j\ge2) or includes the two vacuous simple-graph scales.

### Boundary or range test

- **Explicit data:** Set (p_{13}=0), so (mathcal P=\varnothing).  Then the window clauses and “every window is blocked” statement are vacuous, and (mathcal B(\varnothing)=mathcal G^{\delta\ge3}_{n,m}).
- **Hypotheses satisfied:** The blocked-class definition itself permits the empty packing and remains internally consistent.
- **Accumulated facts violated:** On the actual route, node [159] requires (2^{c_{13}p_{13}\log_2 n}>|\mathcal G_{n,m}|).  With (p_{13}=0), the left side is (1), while the selected labelled copy of (G) makes the fixed-((n,m)) skeleton class nonempty.  The strict inequality cannot hold.
- **Applicability:** **NON-APPLICABLE TO THE NODE**; node [159]'s dense-packing predicate excludes the empty-range case.

### Graph-realizability test

- **Explicit data:** Let the vertices be (v_0,\ldots,v_{12},a,b,c,d).  Put the path edges (v_iv_{i+1}), all six edges of the (K_4) on (a,b,c,d), all edges (av_i), and the two edges (bv_0,bv_{12}).  The set ({v_0,\ldots,v_{12}}) induces (P_{13}), and every vertex has degree at least three.  But (v_0,a,v_2,v_1,v_0) is a (4)-cycle through the window.
- **Hypotheses satisfied:** Finite simplicity, a labelled induced-(P_{13}) at the fixed position, a fixed edge count, and minimum degree at least three.
- **Accumulated facts violated:** The displayed (4)-cycle violates the target-avoidance condition first imposed at node [2], and hence violates the blocked clause itself.
- **Applicability:** **NON-APPLICABLE TO THE NODE**; node [2] excludes this strongest explicit graph challenge.

### Branch-routing test

- **Explicit data:** Keep a finite simple target-avoiding (G), its fixed packing, edge count, and minimum degree, but posit one selected terminal neutral corridor with (E\ne Q).  The blocked-class membership inference still goes through, but the retained branch tag does not.
- **Hypotheses satisfied:** Every fact used solely to prove (G\inmathcal B(mathcal P)).
- **Accumulated facts violated:** The unique incoming route [166] retains (Q=E) for the trivial neutral residual.
- **Applicability:** **NON-APPLICABLE TO THE NODE**; node [166] is the earliest selected-route fact excluding this handoff candidate.  This also confirms that node [169] does not silently merge the sibling [167]--[168] route.

## 5. Strongest valid counterexample

No candidate reaches the actual residual.  The strongest explicit graph attempt has the correct induced window, edge-count type, and minimum-degree condition, but its concrete (4)-cycle through the window violates node [2].  The empty-packing and nontrivial-neutral attempts are separately excluded by nodes [159] and [166].  The low-scale 2-adic test produces no counterexample because lengths one and two are impossible in a simple graph and every larger dyadic length is globally excluded.

## 6. Local repair

### Corrected statement

No proof-source change required.  A fully explicit restatement is: with (V(G)), (m), and the labelled positions of the fixed maximal induced-(P_{13}) packing (mathcal P) held fixed, let (mathcal B(mathcal P)) be the class of labelled (n)-vertex, (m)-edge graphs of minimum degree at least three that induce (P_{13}) on every prescribed window and contain no target cycle meeting a prescribed window.  Then the labelled copy of the selected counterexample (G) belongs to (mathcal B(mathcal P)), and every prescribed window is blocked at every target scale.

### Complete local proof

Choose any bijection from (V(G)) to the fixed labelled carrier.  Transporting (G) along it preserves simplicity, the number of edges, vertex degrees, induced subgraphs, and cycle lengths.  Hence the labelled copy has (m) edges and minimum degree at least three.  Because (mathcal P) is a packing of induced (P_{13})'s in (G), each transported window position induces (P_{13}).  If an accepted cycle passed through a transported window, applying the inverse labelling would give a power-of-two cycle in (G), contradicting the counterexample condition at node [2].  Thus the labelled copy is in (mathcal B(mathcal P)).  The same argument for each window and each target length (2^j) gives blockedness at every target scale; lengths one and two are vacuous in a simple graph if the phrase is read to include them.

### Counterexample disposition

The explicit 17-vertex candidate is caught directly by the target condition: its (4)-cycle is a power-of-two hit through the window.  The (n=13) candidate is caught by the baseline, the empty packing by the dense strict inequality, and the (E\ne Q) handoff by the selected [166] route.  No finite table, replacement, Type A/Type B, or route-8 routing is needed at node [169].

### Graph patch

No graph patch required.  The existing typed handoff is

```text
[166] -- terminal neutral residual with Q = E --> [169]
[169] -- fixed blocked class and G in B(P) --> [170]
```

Node [170] receives the selected member, fixed packing/window positions, dense overflow, minimum-degree baseline, global blockedness of (G), and retained neutral-corridor data.  Its yes/no branches are a literal proposition and its negation.

### Downstream impact

No theorem, table, caption, analogue, or Lean contract requires a node-[169] correction.  The later claims that conditional savings hold throughout (mathcal B(mathcal P)), that a nonadditive fibre produces a closable serial system, and that the resulting encoding is injective are substantive obligations of nodes [170]--[172]; this report neither imports them as support for node [169] nor certifies them.

## 7. Regression audit

The manuscript search

```text
rg -n -C 3 'def:blocked-class|trivial neutral-configuration residual|blocked at every|every window.*blocked' to_formalize/erdos_64_proof.tex
```

inspected:

- the Part XII labels, edge [169] (	o) [170], and caption at lines 1149--1172;
- detailed dependency-table row 53 at line 1231;
- the source-ledger entry for `def:blocked-class` and `lem:blocked-graphs-compress` at line 1564;
- the definition and membership assertion at lines 7714--7736;
- the use of the node-[169] residual in `lem:window-system-realizability` and `lem:system-increment-arithmetic`;
- `lem:scale-additivity` and `lem:blocked-graphs-compress`, which consume the class and its selected member;
- `rem:blocked-class-checks` at line 8068 and `rem:entropy-lives-here`.

The dossier's item-level occurrence search for `def:blocked-class` found lines 1231, 1564, 7723, and 8068 and no declared reverse-item dependency.  The broader phrase search found the expected prose and theorem uses above but no second definition or conflicting membership criterion.

The formalization search

```text
rg -n -C 3 'IsBlocked|blockedClassRow|blockedClassMember|blockedClassAt|objectSkeleton_blocked' hypostructure proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean Assembly_node_audit.md web/data/eg_node_audit.json
```

verified the actual declarations in `Graph/BlockedClass.lean`, the `Holds` proposition in `SpineVocabulary.lean`, and `blockedClassRow` in `ColdCorridorRows.lean`.  The row reads the selected target avoidance and the fixed packing, proves transported minimum degree and blockedness, and records the elementary cardinal domination of the class by the skeleton budget.  That cardinal conjunct is not used to prove membership and contributes no stronger window claim.  `BlockedCompressionRows.lean` consumes the member only after node [170]'s separate additivity decision.

## 8. Residual uncertainty

No uncertainty remains in node [169]'s definition or selected-graph membership inference.  This audit did not validate the universal conditional-fibre bound, overlap uncrossing, modular arithmetic, or injective compression at nodes [170]--[172], and it does not treat their later statements as evidence for node [169].  Lean's cardinal bound for the raw blocked class is a general subtype bound rather than the later compression estimate, but this is faithful to the limited contract audited here.
