<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 178,
  "node_label": "pair-code unrealized residual: the entropy count of [131] or of the free side of [137] fails; \\cref{lem:pair-failure-overlap} gives a minimal pair overlap obstruction",
  "panel": "fig:proof-diagram-part-x",
  "contract_sha256": "99bb56f52d746efe11b4a73f13581a0e4d3d72782b54ed5723608833099d1a4b",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "NONEXHAUSTIVE BRANCH",
  "audited_at": "2026-08-24T21:51:17Z"
}
-->

# Red-team audit: node [178]

## 1. Executive verdict

Verdict: **NONEXHAUSTIVE BRANCH**

The two incoming count-failure arms do not imply the “pair overlap
obstruction” defined at node [178].  Failure to realize one binary bit per pair
means that, after some prefix assignment, a pair coordinate has at most one
realized continuation.  The definition uses the opposite condition: it calls
(\mathcal U) an obstruction when *no* ordering makes *every* pair coordinate
have conditional cardinality at most one.  Thus a one-coordinate constant
fibre is a count-failure residual but has no obstruction, whereas the full
binary product satisfies the displayed obstruction predicate.  The proof also
changes one pair response without constructing a graph in the current
fixed-((n,m)) conditional fibre, so disconnected support components need not
factor.  Consequently the unconditional edge to [179] leaves the
code-unrealized-but-determined residual unassigned.  The smallest repair is to
retain an actual minimal *binary code defect*, reverse the conditional-fibre
inequality, and either prove a boundary-profile- and edge-count-preserving
factorization lemma for disconnected supports or route its failure separately.

## 2. Exact node contract

### Incoming residual

Node [178] is a merge of two tagged routes on the same selected
lexicographically minimal counterexample (G):

1. `[131] -- count fails --> [178]`.  Node [130]'s blocker-free arm carries
   the full active surplus family
   (mathcal A_0=mathcal P_{\rm exc}), the full pair schedule
   (Pi=\binom{\mathcal A_0}{2}), the baseline spine demand
   (mathcal I_{\rm spine}), and the literal failure of the mixed full-code
   count.
2. `[137] -- count fails on the free side --> [178]`.  This route carries the
   canonical blocker and capacity-token ledgers from [132]--[136], the same
   baseline spine demand, the presentation-specific free pair set
   (Pi=\Pi_{\rm free}), and the literal failure of the corresponding mixed
   full-code count.  The token presentation and its free side must remain
   tagged to this route; they are not facts on the [131] route.

Common to both routes are the finite simple graph, minimum degree at least
three, absence of power-of-two cycles, lexicographic minimality, no proper
minimum-degree-three core, high-degree independence, boundary-profile and
context-universality rules, replacement/uncompressibility, the fixed maximal
induced-(P_{13}) packing, and the strict non-near-cubic surplus branch.  Nodes
[125]--[129] retain the sparse-exit survivor, full active surplus demands with
(|\mathcal A_0|=\sigma(G)), canonical port returns and response supports,
and an independently target-testable baseline family with deficit
(E_{\rm spine}(n)\le C_E n).

The selected branch fact is not an abstract rank failure.  It is the failure
of graph realization of the mixed code among the labelled skeletons of the
current fixed-((n,m)) class.  The manuscript explicitly says this is a
genuine residual because the pair response coordinates are functions of the
graph and their supports share spine routes; abstract label-injectivity alone
does not realize all response combinations.

### Accumulated facts

The common facts available at [178] are:

- `[2]`, `[4]`--`[14]`: the selected target-free minimal counterexample,
  target algebra, degree and boundary facts, context universality,
  replacement, and hereditary uncompressibility.
- `[17]`, `[18]`: the canonical window packing and the declared target
  coordinate algebra.
- `[19] -- yes`, `[20]`, `[125]`: strict non-near-cubic surplus and survival
  of all named sparse surplus exits.
- `[126]`--`[129]`: the exact sparse envelope, full excess-port activation,
  canonical returns (R_p), port supports (T(p)), response supports
  (Gamma(p)), and the baseline demand (mathcal I_{\rm spine}).
- `def:sparse-pair-response`: for every pair (pi), the canonical connected
  response support (X_\pi) and declared exact response coordinate (r_\pi).
- `lem:sparse-pair-dependence-exit`: an admissible rank dependence of the
  pair coordinates yields a sparse exit or a type-(d)/(e) blocker.  This is a
  statement about quotient dependence, not a graph-realizing switch between
  values inside the current conditional fibre.
- The selected incoming negation: the mixed baseline-plus-pair family does
  not realize the asserted full binary code in the labelled skeleton budget.

On the [137] route only, the canonical blocked/free partition, one blocker and
capacity token per blocked pair, exact token no-overcounting, and the literal
free set of that presentation are retained.  No common or route-specific fact
at [178] supplies a nonempty subfamily (mathcal U), its realized joint state
set (mathcal S(\mathcal U)), a missing binary extension, connected overlap
support, or a gluing representative for changing one support while fixing the
other exposed data.

The Lean branch values match that limitation.  `FreePairCodeUnrealizedStatement`
and `BlockedPairCodeUnrealizedStatement` retain the appropriate baseline and
presentation witnesses plus the numerical negation of the code inequality.
They contain no pair-overlap family or connected support.  There is no fact key
or producer for the manuscript's node-[178] obstruction, and the assembly
hands either negation directly to the unresolved
`selectedSparsePairSerialSystem` obligation.

### Current predicate and exact claim

For a finite (mathcal U\subseteqPi), the manuscript defines
(mathcal S(\mathcal U)) as the joint pair-response values realized by
graphs in the current conditional fibre.  It then defines a pair overlap
obstruction as a nonempty (mathcal U) for which no ordering
(pi_1,\ldots,pi_t) has

\[
|\mathcal S(\pi_i\mid\pi_1,\ldots,pi_{i-1})|\le1
\qquad(1\le i\le t)
\]

in every nonempty conditional fibre.  In words, no order makes every
coordinate determined by the previously exposed coordinates.

The node claims the implication

\[
\begin{split}
&\text{the mixed baseline/pair full code is not realized}\\
&\qquad\Longrightarrow
\exists\,\varnothing\ne\mathcal U\subseteq\Pi
\text{ minimal with the displayed no-determining-order property,}\\
&\hspace{14em}\text{and }\bigcup_{\pi\in\mathcal U}X_\pi
\text{ is connected.}
\end{split}
\]

The conditional inequality has the wrong polarity.  For binary coordinates,
full product realization requires two continuations in every nonempty prefix
fibre along a suitable exposure order.  Failure is witnessed by a prefix fibre
with at most one continuation.  A minimal defect should therefore say that no
ordering keeps *at least two* continuations at every step, not that no ordering
makes *all* steps have at most one.

The connectivity conclusion has a second missing premise.  Minimality of a
code defect on two disconnected support components does not by itself imply
that the component state sets multiply.  One needs an actual gluing theorem
showing that compatible graph-realized states on the components combine to a
graph in the same conditional fibre while preserving vertex and edge counts,
boundary degrees, all earlier exposed coordinates, canonical choices, and
target safety.  `lem:sparse-pair-dependence-exit` supplies no such graph
representative.

### Outgoing contracts

The sole edge is `[178] -> [179]`.  Node [179], through
`lem:pair-system-realizability`, requires an actual minimal pair overlap
obstruction on the strict branch with connected overlap support.  It then
chooses overlapping response supports, uncrosses their first/last common
vertices, and claims one of a target hit, sparse exit, smaller representative,
Type B bottleneck, or a scale-spanning serial demand system.

Neither incoming count-failure record contains the object required for that
construction.  In particular:

- a constant one-coordinate pair fibre has failed the pair bit but admits the
  determining order and hence is not an obstruction under the current
  definition;
- a failure contributed entirely by the baseline, especially when the [137]
  free pair set is empty, has no nonempty pair subfamily at all; and
- even a correctly defined minimal code defect can have disconnected support
  unless conditional graph states factor over the components.

These residuals have no alternative edge.  The route to [179] is therefore
not exhaustive.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | The count at [131] and the free-side count at [137] are literal branch tests. | The two exact numerical decisions. | Each false arm must retain its own pair set and baseline presentation. | Compare the full pair schedule with the token-ledger free side. | SUPPORTED |
| S2 | Abstract pair-coordinate label-injectivity does not itself realize the full graph code. | Definition of graph-realized states and canonical pair supports. | Do not reuse rank independence as a graph-switching lemma. | A coordinate is abstractly testable but constant on the current graph fibre. | SUPPORTED |
| S3 | A pair overlap obstruction is a family with no order making every conditional cardinality at most one. | `def:pair-overlap-system`. | This predicate must have the same polarity as failure of a lower product-code bound. | A constant singleton versus a full binary singleton. | DEFINITION, BUT WRONG POLARITY |
| S4 | Pairwise disjoint response supports allow the response of one pair to be changed while every other support is fixed. | Disjointness and `lem:sparse-pair-dependence-exit`. | Need an actual graph in the current fixed-((n,m)) conditional fibre, with boundary degrees and exact profiles preserved. | Two disjoint supports whose permitted local states have incompatible total edge counts. | FAILED |
| S5 | Quotient independence after conditioning realizes the product code. | `lem:sparse-pair-dependence-exit`. | Rank/target testability must be promoted to simultaneous graph realization by a canonical injection. | A binary target state has a tester context but only one value occurs among current skeletons. | FAILED |
| S6 | Count failure is witnessed by a finite family for which no exposure order “works” in the sense of S3. | S3--S5. | Failure of (2^{|\Pi|}) requires a missing continuation, not the absence of a fully determining order. | (Pi=\{\pi\}), (mathcal S(\pi)=\{0\}). | FAILED |
| S7 | A minimal obstruction exists by cardinality. | Finiteness of (Pi). | There must first be a nonempty witness satisfying the obstruction predicate. | Constant singleton has count failure and no witness. | FAILED |
| S8 | If the minimal witness were disconnected, admissible component orders could be concatenated. | Minimality and disjoint supports. | Conditional state sets of disconnected components must factor, with actual compatible graph representatives. | Two components coupled only by the fixed global edge count. | FAILED |
| S9 | The overlap support is connected. | S8. | Need the missing conditional gluing/factorization theorem. | A cross-component parity or edge-count relation. | FAILED |
| S10 | The same argument applies to the full [131] schedule and the [137] free side. | Tagged definition of (Pi). | The [137] free side may be empty and carries capacity-ledger data absent at [131]. | (Pi_{\rm free}=\varnothing). | FAILED WITHOUT A NONEMPTY PAIR-DEFECT PREMISE |
| S11 | The resulting object meets [179]'s entry contract. | S7--S9. | Must retain actual supports, overlap incidences, minimality, and connectedness. | Inspect the Lean false-arm values field by field. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Let (Pi=\{\pi\}) and let the current nonempty
  conditional fibre realize only (r_\pi=0).  Thus
  (mathcal S(\{\pi\})=\{0\}): the expected binary factor (2) is absent,
  but the only exposure order has conditional cardinality (1\le1).
- **Hypotheses satisfied:** This is a finite graph-response fibre, its pair
  code is unrealized, and the unique response support (X_\pi) can be
  connected exactly as `def:sparse-pair-response` requires.
- **Accumulated facts violated:** On the full [131] schedule, a singleton pair
  set would mean (|\mathcal A_0|=2), which is incompatible with the strict
  non-near-cubic surplus lower bound for the orders relevant to node [19].  No
  actual [137] graph with exactly one free pair and every earlier canonical
  ledger fact was constructed.
- **Applicability:** **NON-APPLICABLE TO THE NODE** as a full [131] residual;
  the earliest exclusion is node [19], the strict non-near-cubic surplus test.
  It is nevertheless an exact finite-state counterexample to the implication
  used in `lem:pair-failure-overlap`: the only nonempty subfamily is not an
  obstruction under the stated definition.

### Parity or 2-adic test

- **Explicit data:** For two binary pair coordinates take first
  (mathcal S=\{(0,0),(1,1)\}), a parity-correlated code of size (2<4).
  For comparison take the full product
  (mathcal S'=\{0,1\}^2).  Under either ordering, the first coordinate has
  two possibilities.  Therefore no ordering makes *every* conditional size at
  most one, so both (mathcal S) and the fully realized (mathcal S')
  satisfy the manuscript's obstruction predicate.
- **Hypotheses satisfied:** The first state set has a genuine one-bit code
  deficit; the second is the exact binary product.  Both are legitimate finite
  conditional-state abstractions.
- **Accumulated facts violated:** Neither abstraction was realized by an actual
  target-free minimal graph with the active-port family and canonical supports
  of nodes [125]--[137].  The full product also violates the selected incoming
  count-failure predicate.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  For the full product, the
  earliest exclusion is the selected `[131]/[137] -- count fails` predicate;
  for the parity code, graph realization is first unverified at node [2].  The
  test shows that the error is already Boolean and is not repaired by any
  2-adic phase or divisibility condition.

### Boundary or range test

- **Explicit data:** On the [137] tagged route let the concrete token ledger
  assign every scheduled pair to a blocker, so
  (Pi_{\rm free}=\varnothing).  Let the selected numerical false arm be
  [
  2^{|\mathcal I_{\rm spine}|}>
  |\mathcal G_{n,m}|.
  ]
  The current Lean `BlockedPairCodeUnrealizedStatement` permits precisely this
  shape: it records the concrete capacity presentation and the negated mixed
  inequality but no nonemptiness of the free side.
- **Hypotheses satisfied:** The canonical pair partition and capacity-token
  presentation can have an empty free side; the displayed inequality is the
  literal count-failure predicate after substituting (|\Pi_{\rm free}|=0).
- **Accumulated facts violated:** If the baseline demand has already been
  canonically realized by graphs in the current skeleton class, independent
  target entropy excludes the displayed inequality.  The manuscript treats
  graph realization itself as a branch test, and no actual graph satisfying
  all upstream facts and this baseline-only failure was supplied.
- **Applicability:** Applicable to the written [137] false-arm contract and to
  the current Lean proposition, but not established as an actual graph
  residual.  It exposes a missing range check: node [178] requires a nonempty
  pair family although neither incoming failure statement proves one.

### Graph-realizability test

- **Explicit data:** Take a finite simple high-surplus graph and freeze all
  edges outside two disjoint pair-response supports as well as the previous
  canonical exposure data.  Restrict the conditional fibre to one graph, so
  every pair response is constant.  Complete the local port supports with
  cubic neighbours and high-degree centres so the active-demand geometry is
  present.
- **Hypotheses satisfied:** The conditional fibre is nonempty; each
  (X_\pi) is a finite connected support; every conditional response set has
  size one; hence any claimed extra pair bit is not graph-realized.
- **Accumulated facts violated:** The trial completion was not shown to avoid
  (C_4,C_8,C_{16},\ldots), be lexicographically minimal, carry the canonical
  maximal (P_{13}) packing, or survive all sparse exits.  Dense elementary
  completions generally contain a 4-cycle.
- **Applicability:** **NON-APPLICABLE TO THE NODE.**  The earliest unverified
  accumulated condition is node [2], absence of power-of-two cycles.  The test
  isolates the missing operation in the proof: disjoint local supports do not
  create alternative graphs in the conditional fibre merely because their
  response labels are abstractly distinct.

### Branch-routing test

- **Explicit data:** On either incoming false arm retain only what the branch
  actually supplies: the appropriate pair set (Pi), baseline family and
  deficit, route-specific capacity data if present, and the negated numerical
  full-code inequality.  Instantiate its realized pair-state projection by a
  constant nonempty fibre.  Then every ordering determines every pair
  coordinate, so no nonempty (mathcal U) satisfies the current obstruction
  predicate.
- **Hypotheses satisfied:** The literal code failure and every field of
  `FreePairCodeUnrealizedStatement` or
  `BlockedPairCodeUnrealizedStatement` are retained.  No accumulated fact
  asserts a graph-realized binary extension or an overlap family.
- **Accumulated facts violated:** None at the level of the stated node-[178]
  handoff.  Realization by a complete minimal-counterexample graph remains
  unproved, but that is exactly the realization residual selected by the node.
- **Applicability:** Applicable to the proof-flow contract.  The destination
  asks for an actual minimal connected obstruction, while the source contains
  only a numerical negation.  The constant/determined complement has no edge,
  so the branch is nonexhaustive.

## 5. Strongest valid counterexample

No explicit graph was found that satisfies the entire minimal-counterexample,
canonical-packing, active-port, sparse-exit-survivor, and count-failure state.
The strongest candidate is the exact finite conditional-fibre pattern selected
by the node: the mixed pair code lacks one binary factor because a pair
coordinate is constant after a realized prefix.  For the smallest witness,
(mathcal S(\{\pi\})=\{0\}).  This satisfies the intended meaning of
“pair-code unrealized,” but the sole order has conditional cardinality one and
therefore disproves the asserted obstruction conclusion.  The [137] empty-free
boundary is stronger at the typed-contract level: the current false-arm
proposition can hold with no nonempty pair subfamily from which an obstruction
could be chosen.  These are valid counterexamples to the local finite-state
implication and routing contract, not counterexamples to the graph theorem.

## 6. Local repair

### Corrected statement

Replace `def:pair-overlap-system` and the operative node-[178] claim by the
following graph-realized version.

> First condition on one already graph-realized baseline state.  Let
> (Pi\ne\varnothing) be the route-specific pair set, and for
> (mathcal U\subseteqPi) let
> (mathcal S(\mathcal U)\subseteq\{0,1\}^{\mathcal U}) be the projection of
> the current nonempty conditional graph fibre to the designated binary pair
> truths.  A pair code defect is a nonempty (mathcal U) for which
> (mathcal S(\mathcal U)\ne\{0,1\}^{\mathcal U}).  It is minimal when every
> proper nonempty subfamily has full binary projection.  Equivalently, for
> every exposure order of a minimal defect, some nonempty prefix fibre has at
> most one continuation for the next coordinate.  If the mixed code fails
> after the baseline code has been realized, such a minimal defect exists.
> If, in addition, graph-realized response states factor over support
> components with disjoint declared interfaces, its overlap support is
> connected.

The factorization premise must be a proved lemma, not an informal change of a
response label.  It must preserve fixed (n,m), the boundary-degree profile,
previously exposed coordinates, canonical packing/port data, and exact target
response under gluing.

### Complete local proof

Condition on a graph-realized baseline value (b).  If every pair truth vector
in ({0,1}^{\Pi}) occurs in the resulting nonempty graph fibre, then the
baseline state together with the pair vectors realizes the full mixed code.
On the selected pair-extension failure arm this is false.  Thus for some
realized (b),

\[
\mathcal S_b(\Pi)\ne\{0,1\}^{\Pi}.
\]

This also proves (Pi\ne\varnothing): for (Pi=\varnothing), the only
vector is the empty vector and it occurs in every nonempty fibre.  Since
(Pi) is finite, choose an inclusion-minimal nonempty
(mathcal U\subseteqPi) with
(mathcal S_b(\mathcal U)\ne\{0,1\}^{\mathcal U}).  Every proper subfamily
has full binary projection.

Fix an ordering (pi_1,\ldots,pi_t) of (mathcal U).  Its prefix of length
(t-1) is proper, hence realizes every binary prefix.  Since the full
(mathcal U)-cube is not realized, choose a prefix assignment for which at
least one of the two values of (pi_t) has no extension.  The corresponding
nonempty prefix conditional fibre therefore has at most one realized value of
(pi_t).  This proves the corrected exposure formulation and shows why the
manuscript's `\le1` condition belongs in the *witness of failure*, not under a
negation saying that no fully determining order exists.

For connectivity, let the overlap graph of (mathcal U) have components
(mathcal U_1,\ldots,mathcal U_s).  Assume the required conditional
factorization theorem:

\[
\mathcal S_b(\mathcal U)
=\prod_{j=1}^s\mathcal S_b(\mathcal U_j).
\]

If (s\ge2), each (mathcal U_j) is proper, so minimality makes every factor
the full binary cube.  Their product is then the full cube on (mathcal U),
a contradiction.  Hence (s=1), and the overlap support is connected.  This
is the exact object that may be sent to [179].  Without the displayed
factorization theorem, the proof stops at the minimal code defect and its
disconnected complement must remain a named residual.

### Counterexample disposition

The constant singleton fibre becomes the smallest corrected pair code defect:
its missing second value witnesses the required conditional cardinality at
most one.  It no longer falls through the branch.  The full product is not a
defect.  The empty [137] free side cannot enter the repaired pair-extension
failure arm after the baseline state has been realized; a failure before that
conditioning is a baseline-code realization residual and must be routed
separately.  A disconnected parity or edge-count coupling is either ruled out
by the new factorization theorem or retained on the explicit
separated-support realization-defect arm.

### Graph patch

Replace the unconditional handoff by the typed split

```text
[131]/[137] -- baseline code realized; pair extension count holds --> existing route
[131]/[137] -- baseline code unrealized --> baseline-realization residual
[131]/[137] -- baseline realized; pair extension code unrealized --> [178]
[178] -- minimal binary code defect + conditional factorization -->
          connected pair-overlap defect --> [179]
[178] -- minimal binary code defect + factorization fails -->
          separated-support graph-realization defect
```

The first [178] edge must retain the route tag, the realized baseline value,
the nonempty (Pi), the actual nonempty conditional fibre, the minimal
(mathcal U), its missing binary extension, all (X_\pi), and the proved
connected overlap graph.  The separated-support arm must test the exact
failure: a context-visible incompatibility may route to sparse exit (b), a
target-complete proper-support relation with an actual smaller representative
may route to exit (c), and a purely fixed-((n,m)) compatibility obstruction
must remain in the encoding ledger.  It may not be sent to [179] without a
graph-realized gluing representative.

### Downstream impact

Synchronize the Part-X node [178] label, its incoming edge descriptions,
caption and summary, overview row 54, the constraint-ledger row,
`def:pair-overlap-system`, `lem:pair-failure-overlap`, and
`lem:pair-count-or-arithmetic`.  Node [179]'s
`lem:pair-system-realizability` must consume the corrected minimal binary code
defect and the actual connected overlap data; every appeal to “minimality” or
to changing one response must use the new factorization/gluing lemma.  Node
[180] is downstream of that repaired producer and cannot be reached from a
bare count negation.  The analogous barrier system at [170] uses an upper
conditional-state bound (F_{a,b}) and therefore has a different inequality
direction; it must not be altered word for word.

In Lean, strengthen both unrealized statements to distinguish baseline
realization from pair-extension failure, add semantic types and keys for the
actual conditional fibre, minimal code defect, support overlap graph, and
connectedness proof, and add a producer before any serial-system consumer.
`freePairEntropyDichotomy` and `blockedPairEntropyDichotomy` currently publish
only the numerical false arms; `selectedSparsePairSerialSystem` must not accept
those facts directly.

## 7. Regression audit

The audit inspected:

- the Part-X nodes [125]--[144] and [178]--[180], including both incoming
  edges to [178], the Part-X caption/summary, overview rows 45--54, and the
  constraint-ledger entries;
- `def:active-surplus-demands`, `lem:surviving-active-family`,
  `def:baseline-spine-demand`, `def:sparse-pair-response`,
  `lem:sparse-pair-dependence-exit`, `prop:sparse-entropy-sandwich`, and
  `prop:sparse-entropy-sandwich-with-blockers`;
- the full statements and proofs of `def:pair-overlap-system`,
  `lem:pair-failure-overlap`, `lem:pair-system-realizability`,
  `lem:pair-system-increment-arithmetic`, and
  `lem:pair-count-or-arithmetic`;
- the [170] analogue `def:barrier-overlap-system` and
  `lem:barrier-failure-overlap`.  Its upper product-bound failure correctly
  uses “no exposure order has conditional size at most (F_{a,b})”; that
  polarity cannot be copied to the lower binary-code realization at [178];
- Lean's `FreePairEntropySandwichStatement`,
  `FreePairCodeUnrealizedStatement`,
  `BlockedPairEntropySandwichStatement`,
  `BlockedPairCodeUnrealizedStatement`, `freePairEntropyDichotomy`,
  `blockedPairEntropyDichotomy`, and both calls to
  `selectedSparsePairSerialSystem` in `selectedStrictSurplusBranch`;
- `Assembly_node_audit.md` and `web/data/eg_node_audit.json` as locators,
  followed by the actual declarations.  They likewise record that no pair
  overlap key, producer, or serial-system handoff exists.
- review-postmortem entries E04 and E32.  Those entries correctly reject the
  generic claim that pair-code failure has no structural branch.  This report
  tests the branch that is present and finds the opposite conditional-fibre
  inequality in its defining predicate; it does not demand independence on
  both arms.

Search patterns included

```text
rg -n 'pair-failure-overlap|pair-system-realizability|pair-system-increment-arithmetic|pair-count-or-arithmetic|pair-overlap-system|pair-code unrealized|count fails' to_formalize/erdos_64_proof.tex
rg -n 'FreePairCodeUnrealizedStatement|BlockedPairCodeUnrealizedStatement|freePairEntropyDichotomy|blockedPairEntropyDichotomy|PairOverlap|pairOverlap|selectedSparsePairSerialSystem' hypostructure proofs Assembly_node_audit.md web/data/eg_node_audit.json
rg -n 'barrier-overlap-system|barrier-failure-overlap|conditional fibre|product code|graph-realiz|gluing|word for word|analog' to_formalize/erdos_64_proof.tex
```

Negative searches found no manuscript or Lean lemma that factors current
fixed-((n,m)) conditional graph fibres over disconnected pair-response
supports, no nonemptiness proof for the [137] free side on the false arm, no
semantic representation of (mathcal S(\mathcal U)) in Lean, and no producer
of a minimal connected pair overlap obstruction.  The only closely analogous
conditional-fibre lemma is the barrier *upper-bound* product argument, whose
inequality has the opposite role.

## 8. Residual uncertainty

No actual minimal target-free graph realizing the constant or empty-free
conditional-fibre candidates was constructed.  The exact alphabet of each
pair response may contain more than the designated obstructing/nonobstructing
bit; the repaired statement deliberately projects to the binary coordinate
that is charged by the (2^{|\Pi|}) count.  I did not prove the required
fixed-edge-count conditional gluing theorem, and it may fail without exposing
additional per-component edge counts and boundary profiles; that failure is
why the separated-support arm is retained.  I did not audit the uncrossing or
doubling-orbit mathematics of nodes [179] and [180] beyond checking their
entry dependency on node [178].  No manuscript, proof-flow, Lean, diagram,
audit-source, or coverage-ledger file was changed.
