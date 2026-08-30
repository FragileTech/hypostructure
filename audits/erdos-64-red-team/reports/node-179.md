<!-- red-team-audit
{
  "schema_version": 1,
  "proof": "erdos-gyarfas",
  "node": 179,
  "node_label": "serial demand system: uncrossing yields a scale-spanning chain of interfaces with bounded system increments (\\cref{lem:pair-system-realizability})",
  "panel": "fig:proof-diagram-part-x",
  "contract_sha256": "36e4029de5935fb9a16438109fed7f114ead0597fa0dab8ea10eb841b58ebef6",
  "manuscript_sha256": "106a8205a1718fbf90e1686a107b2143b9edca574e2b0c11415e7f44aee2c0f9",
  "graph_sha256": "dc67fae178f947a9607c167e383d85919633341bdd423e4c4a45e4c317b3a765",
  "lean_audit_sha256": "50324ef5594d635a52d83aeb297f2ca3f3d30ef58de4ce3602816c7e78365b12",
  "verdict": "NONEXHAUSTIVE BRANCH",
  "audited_at": "2026-08-24T21:55:04Z"
}
-->

# Red-team audit: node [179]

## 1. Executive verdict

Verdict: **NONEXHAUSTIVE BRANCH**

The current definition forces every minimal pair overlap obstruction consumed
by node [179] to be a singleton: if a coordinate has two possible values, that
singleton is already an obstruction, while if every singleton has at most one
value, every ordering determines the whole family.  The proof nevertheless
starts by choosing two intersecting response supports.  The incoming count
failure is compatible with this omitted case, for example on the state set
`{(0,0),(1,0)}`.  Even after adding a two-support premise, connected
minimum-vertex response supports are not paths, generic high-degree
intersections do not satisfy the same-token bottleneck entry contract, and no
registered uniform port-return bound supplies the displayed constant
$D_{\rm sp}$.  Thus alternatives (i)--(v) do not exhaust the stated input and
the sole edge to [180] is unjustified.  This is a local contract failure; no
complete minimal-counterexample graph is claimed.

## 2. Exact node contract

### Incoming residual

The only diagram edge is `[178] -> [179]`.  Node [178] is reached by one of two
tagged false arms:

- the full free-pair entropy count at [131] fails; or
- after the blocker and capacity-token route [132]--[137], the entropy count
  on the free side of [137] fails.

The common manuscript handoff retains the selected finite simple graph $G$,
the strict non-near-cubic branch, the surviving active surplus demands and
their canonical data $T(p),R_p,\Gamma(p)$, the route-specific pair set $\Pi$,
the already exposed encoding coordinates, and the exact numerical count
failure.  Node [178] then claims to supply a minimal pair overlap obstruction
$\mathcal U\subseteq\Pi$ with connected overlap support.  Each pair
$\pi=\{p,q\}$ has the response support $X_\pi$, defined only as the
lexicographically first minimum-vertex connected subgraph containing the two
demand supports.

Under the literal `def:pair-overlap-system`, $\mathcal U\ne\varnothing$ is an
obstruction when no ordering makes every next conditional response set have
cardinality at most one in every nonempty conditional fibre.  Minimality says
that every proper nonempty subfamily does admit such an ordering.  This
definition, not a corrected binary-code-defect definition, is the object
actually consumed at [179].

The Lean continuation is weaker still.  The two false arms append only
`K .freePairCodeUnrealized` or `K .blockedPairCodeUnrealized` and immediately
call the undefined `selectedSparsePairSerialSystem`.  There is no key, row,
producer, or semantic object for $\mathcal U$, its overlap graph, an
uncrossing, or a pair serial system.

### Accumulated facts

- Nodes [1]--[18] supply the finite simple target-avoiding graph, the
  lexicographic minimal-counterexample order, return algebra,
  bridgelessness/no-proper-core consequences, high-degree independence,
  boundary profiles, context universality, replacement exclusions, and the
  canonical $P_{13}$ packing.
- Nodes [19]--[20] select the strict surplus branch.  Nodes [125]--[130]
  retain the full active surplus family, canonical port returns and response
  supports, the fact that all named sparse exits are absent, the baseline
  spine family, and the canonical pair partition.
- On the [131] route, the ledger retains the free-pair set and the literal
  failure of its mixed code count.  On the [137] route it instead retains the
  blocker partition, exact token capacities, role fibres, and the literal
  failure of the free-side mixed count.  These are tagged alternatives, not a
  union of sibling facts.
- Node [178] purports to add a minimal connected pair overlap obstruction.
  Nothing on the incoming path states $|\mathcal U|\ge2$, that any $X_\pi$ is
  a path, that two supports have two ordered common vertices, that an
  intersection carries a common token and role, or that a canonical return
  has uniformly bounded length.
- Node [166] is not an ancestor of [179].  Its dense-residual neutral
  conclusion cannot be imported as a global identification of pair-response
  pieces.  The Type A absorption and Type B bottleneck results are also typed
  destination lemmas, not unconditional facts about every pair-support
  intersection.

### Current predicate and exact claim

With $F(179)$ denoting the accumulated state above, the stated lemma asserts

\[
 F(179)+\text{``$\mathcal U$ is a minimal pair overlap obstruction''}
 \Longrightarrow (i)\vee(ii)\vee(iii)\vee(iv)\vee(v),
\]

where (i) is an actual power-of-two cycle, (ii) is a context-distinguished
sparse exit, (iii) is a context-equivalent smaller proper representative,
(iv) is a same-token routed bottleneck with a high-degree first separator,
and (v) is a scale-spanning serial demand system.  The serial outcome must
contain ordered interfaces, nonempty internally disjoint corridor families,
two closing port-return pieces meeting the system only at its endpoints,
nonzero increments bounded by

\[
 D_{\rm sp}=2M_{\rm cold}+2\ell_{\rm ret},
\]

and an actual simple cycle for every choice of one piece per cell.

Because the strict branch already excludes (i)--(iv), the operative node label
uses the stronger implication $F(179)\Rightarrow(v)$.  That implication is
not proved.  In fact, under the literal obstruction definition every minimal
obstruction is a singleton.  If a singleton coordinate has more than one
value in a nonempty fibre, it is itself an obstruction.  If no singleton is
an obstruction, each unconditional coordinate range has size at most one;
conditioning can only shrink it, so every ordering works for the whole
family.  Hence a minimal obstruction cannot contain two supports for the
first uncrossing step.

### Outgoing contracts

The only edge is `[179] -> [180]`.  It has no branch label and therefore
asserts that the entire surviving input carries the serial-system alternative.
Node [180] needs more than connected support: it needs a genuine graph-realized
spectrum with at least one frequent nonzero increment, a defined gcd, exact
residue classes, central scale-spanning ranges, and the proof that every
counted length is a simple cycle of $G$.

A singleton obstruction, a branching minimum connected support, a generic
intersection without a same-token certificate, and an unbounded closing
return satisfy no outgoing edge.  Lean confirms the missing handoff rather
than repairing it: `SerialSystem.Spectrum` is graph-free and is never
instantiated from this branch, and `selectedSparsePairSerialSystem` has no
live declaration.

## 3. Sentence audit

| Sentence | Exact assertion | Facts used | Hidden obligation | Adversarial test | Status |
|---|---|---|---|---|---|
| S1 | A minimal pair overlap obstruction satisfies exactly one of (i)--(v). | `def:pair-overlap-system`; strict branch. | The five alternatives must cover singleton and non-path obstructions. | A two-coordinate fibre `{(0,0),(1,0)}` selects the singleton varying coordinate. | FAILED |
| S2 | The obstruction can be chosen with fewest support edges and intersections. | Finiteness of $G$ and $\mathcal U$. | Secondary minimization does not create two members or new geometry. | Minimize a singleton obstruction. | SUPPORTED BUT INSUFFICIENT |
| S3 | Every response support can be oriented from its first demand. | $X_\pi$ is connected and contains two demand supports. | A canonical start, end, and path order must be defined for a connected subgraph that may branch. | A minimum Steiner tree with three arms. | FAILED |
| S4 | Two intersecting supports have first and last common vertices. | An asserted pair of overlapping $X_\pi$. | There must be two supports and their intersection must carry compatible linear orders. | The actual minimal obstruction is a singleton; alternatively two trees meet at one articulation. | FAILED |
| S5 | Between those vertices the union contains two internally disjoint strands. | S3--S4. | The common vertices must be distinct and the union must have two disjoint routes. | Two supports meet in one vertex or share a branching subtree. | FAILED |
| S6 | Uncrossing preserves boundary degrees and every exposed coordinate. | Boundary-profile formalism; claimed analogy. | Both switched graphs must be simple members of the same fixed conditional fibre, with all canonical data unchanged. | A cross-edge after switching or a changed canonical $X_\rho$. | FAILED |
| S7 | A target hit, distinguishing context, or smaller representative gives (i)--(iii). | Target avoidance; context universality; replacement. | The uncrossed object must be an actual graph; (iii) needs a strictly smaller target-complete representative. | Keep only abstract response labels without a switched graph. | SUPPORTED ONLY WITH THE MISSING REALIZATION |
| S8 | Any high-degree first separator is the same-token routed bottleneck. | `lem:same-token-bottleneck-routing`. | Need a token $t$, role $r$, and role-homogeneous matching or star in $H_{t,r}$ with more than $Q_{\rm geom}$ edges. | A single generic overlap at a high-degree vertex. | FAILED; WRONG DESTINATION AS A SUBORDINATE DEFECT |
| S9 | Any ambient-cubic first separator is closed by Type A cubic-switch absorption. | `lem:typeA-cubic-switch-absorption`. | The pair residual must meet the Type A-specific switch and ledger entry contract. | A free pair-response support through an unrelated cubic vertex. | FAILED |
| S10 | Otherwise the strands are equal-length neutral pieces. | Exhaustion of earlier cases. | Length change, context equivalence, and exact target neutrality must be proved for every surviving strand. | Two unequal abstract pieces for which no graph switch exists. | FAILED |
| S11 | Node [166] identifies the neutral pieces. | Dense-residual refined minimality. | [166] must be an ancestor or a separately stated universally applicable lemma with matching inputs. | Check the directed ancestor list and the dense branch tag. | FAILED |
| S12 | Repeated uncrossing makes the intersection graph a path. | S3--S11; secondary minimality. | Cycles and branching must be removed while preserving the obstruction and conditional fibre. | A branching intersection with no typed Type A/Type B entry. | FAILED |
| S13 | Every long cell can be read from both ends using cold cut-states. | `def:cold-corridor-first-failure`. | Each pair-system cell must lie on a selected cold corridor with the same registered interfaces. | A cell internal to a generic $X_\pi$. | FAILED |
| S14 | Every nonzero increment is at most $D_{\rm sp}$. | S13; displayed $\ell_{\rm ret}$. | A declared uniform bound on canonical $R_p$ must exist. | Canonical returns of arbitrarily large length in bridgeless graphs. | FAILED |
| S15 | Every selection of cell pieces and the two returns is a simple cycle. | Disjoint cell interiors; distinct incidences. | Returns must avoid all cell interiors and each other except at the declared endpoints. | A port return re-enters an internal cell vertex. | FAILED |
| S16 | The resulting system is scale-spanning. | Absence of a bounded F5 dependence. | A precise map from pair-system end dependence to an actual cold F5 row is needed. | All variation remains in a bounded end segment not registered as a cold corridor. | FAILED |

## 4. Counterexample attempts

### Smallest-parameter test

- **Explicit data:** Take $\Pi=\{\pi,\rho\}$ and let the current nonempty
  pair-response fibre be
  $\mathcal S(\Pi)=\{(0,0),(1,0)\}$.  The binary pair code has size two
  rather than four.  For $\mathcal U=\{\pi\}$, the only exposure order has a
  conditional response set of size two, so it is an obstruction; it is
  minimal because it has no proper nonempty subfamily.  Let $X_\pi$ be any
  connected response support.
- **Hypotheses satisfied:** The finite fibre is nonempty, the mixed pair code
  fails, $\mathcal U$ satisfies the literal obstruction predicate and its
  literal minimality clause, and its overlap support is connected.
- **Accumulated facts violated:** No finite-state clause of the [178] to [179]
  handoff is violated.  An actual target-free lexicographically minimal graph
  realizing this response fibre was not constructed.
- **Applicability:** Applicable to the local logical contract.  There are not
  two supports to uncross, and no listed alternative assigns the singleton
  nonserial complement.

### Parity or 2-adic test

- **Explicit data:** Use the same fibre.  It provides no corridor cell, no
  positive system increment, and hence no integer
  $g=2^a u$ or realizable residue set $\mathcal R$ for node [180].  For
  comparison, assigning a hypothetical sole increment $6=2\cdot3$ still does
  not make a graph-realized spectrum: there is no verified base length or
  central coefficient interval.
- **Hypotheses satisfied:** The singleton is an admitted minimal obstruction,
  and no incoming fact requires a nonzero increment or defines $g$.
- **Accumulated facts violated:** None by the singleton finite-state datum.
  The hypothetical increment 6 is merely an arithmetic probe and is not
  asserted to be realized by $G$.
- **Applicability:** Applicable as an outgoing-contract test.  The 2-adic
  arithmetic is unavailable because node [179] has not constructed the object
  on which it operates; it cannot close the omitted structural case.

### Boundary or range test

- **Explicit data:** For any proposed constant $B$, take a bridgeless cubic
  graph with girth greater than $B+1$, choose an edge $hx$, and take the
  canonical simple $x$--$h$ return in $G-hx$.  Every such return has length
  greater than $B$.  `lem:sparse-port-activation` makes exactly this
  bridgelessness construction and states no uniform length bound.
- **Hypotheses satisfied:** The test satisfies the local simplicity,
  bridgelessness, degree-three endpoint, and canonical-return mechanism used
  to define $R_p$ and $\Gamma(p)$.
- **Accumulated facts violated:** No member of the family was proved to avoid
  every power-of-two cycle, be the selected lexicographically minimal
  counterexample, or survive all sparse exits.  Those global conditions are
  unverified rather than contradicted.
- **Applicability:** Applicable to the claimed inference of a registered
  uniform $\ell_{\rm ret}$.  It is not a complete node-[179] residual.  The
  manuscript contains no declaration of $\ell_{\rm ret}$ outside the sentence
  defining $D_{\rm sp}$.

### Graph-realizability test

- **Explicit data:** Realize one response support $X_\pi$ locally as the
  minimum connected tree joining the four connected marked subgraphs
  $T(p),\Gamma(p),T(q),\Gamma(q)$, with three of its connecting arms meeting
  at a vertex $c$.  Attach outside boundary stubs without adding vertices to
  the chosen connector.  Choose labels so this branching tree is the
  lexicographically first minimum-vertex connector.
- **Hypotheses satisfied:** The local object is a finite simple graph and
  satisfies the exact definition of $X_\pi$: it is connected, canonical after
  labels are fixed, and minimum in vertex count among connectors of the
  marked supports.  Connectedness does not make it a path.
- **Accumulated facts violated:** The local completion was not shown to have
  minimum degree three everywhere, avoid all target cycles, be globally
  minimal, or realize the exact entropy-failure fibre.  It is not offered as a
  complete counterexample graph.
- **Applicability:** Applicable to the graph-geometric inference used at S3.
  The definition permits branching response supports and provides neither an
  orientation order nor two closing pieces disjoint from their interiors.

### Branch-routing test

- **Explicit data:** Retain the smallest-parameter fibre and its singleton
  obstruction.  On the [131] tag it carries only the free-pair count failure;
  on the [137] tag it may additionally carry capacity-ledger data, but
  membership of $\pi$ in a role-homogeneous same-token matching or star of
  size greater than $Q_{\rm geom}$ is not part of either handoff.
- **Hypotheses satisfied:** All fields asserted by the manuscript's [178]
  output are present: a minimal obstruction and a connected overlap support,
  with its source tag retained.
- **Accumulated facts violated:** No accumulated fact is contradicted at the
  typed handoff level.  Full graph realization remains open.
- **Applicability:** Applicable.  The singleton is neither assigned to an
  explicit residual nor eligible for [180].  It also cannot be sent to
  `lem:same-token-bottleneck-routing`, whose token, role, homogeneous
  matching/star, and size hypotheses are absent.

## 5. Strongest valid counterexample

No complete graph satisfying every minimal-counterexample, target-avoidance,
canonical-packing, sparse-exit-survivor, and count-failure fact was
constructed.  The strongest candidate is the exact finite conditional fibre

\[
 \Pi=\{\pi,\rho\},\qquad
 \mathcal S(\Pi)=\{(0,0),(1,0)\},\qquad
 \mathcal U=\{\pi\}.
\]

It simultaneously has a failed binary product code and a minimal connected
obstruction under the manuscript's literal definition.  It reaches the
abstract [179] contract but supplies only one response support, so the proof's
first operation and all later serial geometry are undefined.  Giving
$X_\pi$ the locally graph-realizable branching connector above strengthens
the candidate against the possible reply that a singleton support is already
a serial path.  The missing global graph realization is why the verdict is a
nonexhaustive branch rather than `VALID LOCAL COUNTEREXAMPLE`.

## 6. Local repair

### Corrected statement

Replace the unconditional serial-realizability assertion by a typed
exhaustive split.  A **pair uncrossing certificate** for $\mathcal U$ must
record:

1. at least two response supports and an explicit chosen intersection with
   ordered distinct common vertices and two internally disjoint strands;
2. actual switched simple graphs in the same conditional fibre, preserving
   the boundary-degree profile, all exposed coordinates, canonical demand
   data, and target safety;
3. for every routed branching case, the full destination witness: either the
   Type A-specific switch entry data or a token $t$, role $r$, and
   role-homogeneous matching/star in $H_{t,r}$ of size greater than
   $Q_{\rm geom}$;
4. localization of every retained cell to the cold-corridor state system and
   an explicitly declared finite return bound $L_{\rm ret}$; and
5. ordered interfaces, disjoint cell interiors, closing pieces disjoint from
   the system except at the endpoints, simple-cycle realization for every
   selection, and the exact central scale-spanning interval.

Then the corrected local theorem is:

> For a minimal pair overlap obstruction on the strict branch, either an
> existing outcome (i)--(iv) occurs with its complete typed witness, or a pair
> uncrossing certificate yields the serial system sent to [180], or the object
> is retained as a **nonserial pair-geometry residual**.  The last residual
> includes singleton obstructions, supports without the required linear
> intersection, untyped branching intersections, cells not localized to a
> cold corridor, and unbounded or intersecting closing returns.

To make the intended route nonvacuous, node [178] must separately replace the
current obstruction predicate by a correctly polarized minimal missing-code
predicate and prove $|\mathcal U|\ge2$ or explicitly route its singleton
case.  Connectedness alone is not a substitute for the certificate above.

### Complete local proof

All data are finite.  Test outcomes (i), (ii), (iii), and (iv) sequentially,
requiring the complete witness named in each statement.  If one succeeds,
publish that typed outcome.  On their common complement, test the finite
predicate `PairUncrossingCertificate(\mathcal U)`.  If it succeeds, project
the ordered interfaces, corridor families, closing pieces, increment bound,
simple-cycle realization, and scale-spanning field from the certificate; this
is precisely the entry object of [180].  If it fails, retain

\[
 \operatorname{PairGeometryResidual}(\mathcal U)
 :=\neg(i)\wedge\neg(ii)\wedge\neg(iii)\wedge\neg(iv)
   \wedge\neg\operatorname{PairUncrossingCertificate}(\mathcal U).
\]

These sequential predicates are pairwise disjoint by construction and their
union is exhaustive by finite excluded middle.  No unproved graph surgery is
hidden in the proof.  For the current literal obstruction definition, a
separate elementary argument shows that every minimal obstruction is a
singleton: if some coordinate has range greater than one, its singleton is an
obstruction; if all singleton ranges are at most one, conditioning only
shrinks them and every order determines the entire family.  Therefore the
present producer always enters the new residual until node [178]'s definition
is repaired.

### Counterexample disposition

The fibre `{(0,0),(1,0)}` enters the singleton subtype of
`PairGeometryResidual`; it is no longer silently sent to [180].  The branching
connector enters the nonlinear-support subtype.  A high-degree intersection
enters outcome (iv) only after the token/role/matching-or-star certificate is
present; otherwise it remains in the untyped-branching subtype.  Long or
intersecting returns remain on the closing-geometry subtype until an actual
uniform bound and disjointness proof are supplied.

### Graph patch

Replace the unconditional edge by the following local subdiamond:

```text
[178] -> [179]
[179] -- typed dyadic/context/replacement/Type-B witness --> existing closure
[179] -- verified PairUncrossingCertificate --> [180]
[179] -- singleton or nonserial geometry --> new pair-geometry residual
```

The first edge must retain the [131]/[137] source tag, the actual conditional
fibre, $\mathcal U$, every $X_\pi$, and its overlap incidences.  The new
residual must not be labelled a sparse exit or Type B handoff unless it later
constructs that destination's exact witness.

### Downstream impact

Synchronize the Part-X [178]--[180] labels and caption, overview row 54, the
constraint-ledger row, `def:pair-overlap-system`,
`lem:pair-failure-overlap`, `lem:pair-system-realizability`, and
`lem:pair-count-or-arithmetic`.  Node [180] may consume only the certified
serial arm.  Its arithmetic still needs an independent audit of the exact
finite spectrum and periodic alternative; it cannot repair missing graph
realization at [179].

In Lean, introduce semantic types for the corrected code defect, overlap
support, typed exits, pair-uncrossing certificate, and nonserial complement.
Only a row producing the serial certificate may call the node-[180]
arithmetic.  The current calls to undefined
`selectedSparsePairSerialSystem` from bare count-negation histories must be
replaced by this split.

## 7. Regression audit

The audit inspected:

- the Part-X nodes [125]--[144] and [178]--[180], both tagged paths into
  [178], the single edges [178] -> [179] -> [180], the panel caption and
  summary, overview row 54, and the detailed dependency/constraint rows;
- `def:active-surplus-demands`, `lem:sparse-port-activation`,
  `def:sparse-pair-response`, `lem:sparse-pair-dependence-exit`,
  `def:pair-overlap-system`, `lem:pair-failure-overlap`, the full statement
  and proof of `lem:pair-system-realizability`, and the outgoing
  `lem:pair-system-increment-arithmetic` and
  `lem:pair-count-or-arithmetic`;
- the full base analogue `def:serial-window-system`,
  `lem:window-system-realizability`, `lem:serial-system-sumset`, and
  `lem:system-increment-arithmetic`.  Its completion supports, window
  offsets, fixed-scale barrier data, and Type A handoffs do not automatically
  transfer to pair-response supports;
- `def:cold-corridor-first-failure`,
  `lem:typeA-cubic-switch-absorption`, and the full entry contract and proof of
  `lem:same-token-bottleneck-routing`;
- the directed ancestor set in the fresh dossier, which excludes node [166],
  and the requirements to preserve branch facts and to treat residual routing
  as routing rather than an automatic
  contradiction;
- `Assembly.lean` on both entropy-failure arms,
  `HomogeneousBottleneckRows.lean`,
  `Graph/SerialSystemArithmetic.lean`, `Assembly_node_audit.md`, and
  `web/data/eg_node_audit.json` as formalization locators, followed by the
  live declarations.

Search patterns included

```text
rg -n 'pair-overlap-system|pair-failure-overlap|pair-system-realizability|pair-system-increment-arithmetic|pair-count-or-arithmetic' to_formalize/erdos_64_proof.tex
rg -n 'same-token-bottleneck-routing|typeA-cubic-switch-absorption|cold-corridor-first-failure|window-system-realizability|serial-window-system' to_formalize/erdos_64_proof.tex
rg -F '\ell_{\rm ret}' to_formalize/erdos_64_proof.tex
rg -F 'D_{\rm sp}' to_formalize/erdos_64_proof.tex
rg -n 'selectedSparsePairSerialSystem|PairSerial|SerialSystem' proofs hypostructure Assembly_node_audit.md web/data/eg_node_audit.json
```

The fixed-string search found $\ell_{\rm ret}$ only in the definition sentence
for $D_{\rm sp}$ and found $D_{\rm sp}$ only in the [179] statement/proof and
[180] statement.  No manuscript declaration supplies the claimed registered
return bound.  The Lean search found no pair serial-system key or producer, no
$D_{\rm sp}$ or $\ell_{\rm ret}$ declaration, and no graph instantiation of
`SerialSystem.Spectrum` on this branch.

## 8. Residual uncertainty

No actual minimal target-free graph realizing the two-state conditional fibre
or the branching response support together with every upstream ledger fact
was constructed.  The audit therefore establishes a finite-state and typed
routing defect, not a counterexample to the Erdős--Gyárfás theorem.  It remains
possible that additional, currently unstated geometry of active port supports
could rule out some branching connectors, but neither
`def:sparse-pair-response` nor an ancestor lemma supplies it.  No proof was
found that canonical port returns have a uniform length bound on the strict
residual.  The proposed repair deliberately retains the nonserial complement;
closing that new residual requires new mathematics.  Node [180]'s separate
doubling-orbit and finite-range validity was inspected only as an outgoing
contract, not re-audited here.  No manuscript, diagram, Lean,
implementation-audit, or coverage-ledger source was changed.
