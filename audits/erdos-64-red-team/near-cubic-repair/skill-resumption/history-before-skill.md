# Execution record: strict-surplus handoff and homogeneous caps

Target: Node [144], `thm:homogeneous-overload-geometric-closure`.
Date: 2026-09-21. Status: **partial mathematical progress; branch not closed**.

This record follows the stages of `ExecutionRecipe.tsx` and
`recipe-reference.ts`. It distinguishes performed constructions from candidate
moves. It must not be read as a proof of the requested closure.

## 1. Establish the branch

The first unsupported assertion is the consequence in
`thm:homogeneous-overload-geometric-closure`: after Type B handoffs have been
routed, every token satisfies the fixed homogeneous cap. The preceding
assertion gives an exit or an envelope, not this cap.

The requested endpoint is to justify the near-cubic continuation without
adding an assumption or an extra open endpoint. The positive capped argument
must remain valid. The offending strict-surplus history must not borrow its
sibling's `surplusAtOrBelow` fact.

`incoming-144.txt` copies the complete incoming constraints and returned key
index of `selectedBottleneckDischarge`. The canonical history includes the
selection/minimality, target avoidance, degree and normal-form facts, maximal
packing, active surplus demands, exact capacity presentation, canonical
blocker assignment, entropy sandwich, baseline demand, role-fibre partition,
quantitative overload, and the selected homogeneous pattern. All earlier
keys in `known` remain retained. Its actual output is

`[typeBFanEntry, bottleneckRouting, typeBHandoff] ++ known`.

The selected graph, packing, port selector, token, role, source class, and
connector data are fixed. The graph has not been replaced or reselected.

Owner for any eventual formal repair: the existing sealed same-token rows
in `Graph/Strategy/HomogeneousBottleneckRows.lean`; no detached proof wrapper
or extra input supplying the desired conclusion is authorized. This attempt
has not changed a Lean mathematical declaration.

The initial audit table called the routed prefix an exact match to the whole
theorem. That is too strong: the prefix's output does not include the disputed
cap consequence. The live `Holds` definitions and row bodies, rather than that
green cell, determine what has been established.

## 2. Structural inventory

| Observable | Present and already accounted | Aspect still unaccounted | Candidate and prerequisites |
|---|---|---|---|
| Target avoidance | No power-of-two cycle in the selected graph | Cycles potentially created by a modification | Actual cycle restoration is required before minimality can close the modified graph. |
| Minimality and cubic neighbours | Every edge has a cubic endpoint; high centres are independent | A modification at a high separator | Check degrees, boundary profile, target transfer and strict size decrease separately. |
| Role-fibre loads | Canonical pairs partition by token and role; token supply at most `8n+s` | Pairs discarded when a fibre is handed off | Retain the exact discarded set and its cardinality. |
| Entropy | Free pairs bounded by `C_E n+(s/2+1)log₂n` | The extra pair demand after the handoff | Same-currency assignment to actual payers, not an assertion that routing removes demand. |
| Type B envelope | Actual high centre, first neighbours, arms, core and fan-safety | How many original pair demands one envelope can receive | A total map with a proved fibre capacity and multiplicity bound. |
| Type B mass | Negative vertex charge bounded by centre surplus on the appropriate canonical support family | Relation between this charge and pair cardinality | This conversion is not one of the inspected mass inequalities. |
| Source history | Original overload pattern is still in the ledger | Aggregate family of all routed fibres | Enumerate deterministically, preserve original indices and count each pair once. |

No fixed upper bound on the number of pair demands using a centre is supplied
merely by its degree, its surplus weight, or the existence of a fan envelope.
No near-cubic estimate was inserted into this inventory.

## 3. Candidate admission and minimality checks

### Constraint and compression candidates checked

- **Delete an edge at the high separator.** Its other endpoint is cubic.
  Deletion lowers that endpoint to degree two. The required baseline does not
  survive this operation; this is not an admissible closure.
- **Delete the separator.** Its cubic neighbours fall below the baseline.
  A further reconstruction, not deletion alone, would be required.
- **Contract an edge or triangle.** Strict size decrease is available, but
  power-of-two cycle preservation is not automatic. A cycle can shorten to
  an accepted length. In particular, a six-cycle with a chord completing a
  triangle has cycles of lengths 3, 5 and 6; contracting that triangle creates
  a four-cycle. This is a local obstruction to the proposed preservation
  argument, not a counterexample satisfying the complete EG residual.
- **Fold two neighbours of a high separator.** With no four-cycle, their
  only common neighbour is that separator. Its degree can absorb the loss
  of one incidence; the other degree calculations are favourable. However,
  if the separator is on the boundary, its boundary degree profile changes.
  Enlarging the support to internalize it needs a proved transport of the
  declared coordinate family and its realization map. Even after that,
  target preservation or an admissible declared target-defect witness is
  required. A graph fold by itself does not establish those fields.
- **Use an arbitrary context distinction.** Rejected as a closure move:
  hypothetical context paths are not paths in the selected graph. In
  particular, the inspected `attemptedResponseQuotient` helper mentions
  adjoining a disjoint accepted quadrilateral to a realization. That is not
  evidence that the desired actual handoff contraction preserves its response
  coordinates. This attempt does not use that construction as a shortcut.

These checks reject the automatic applications, not all possible repaired
versions of the operations. The unmet construction fields remain recorded.

### Quantitative candidate selected for local execution

Keep every pair demand in the account. Split the canonical blocked-pair
fibres into a fixed bounded part and the exact excess. This move requires
only the existing pair partition and a finite order. Those prerequisites are
present. Its counting identity is proved below. The further claim that Type B
pays the excess is a separate obligation; it has not been admitted as a
proved transition.

## 4–5. Executed construction: retain the handoff pair count

Write `s=σ(G)=|A₀|`, and let `Π_{t,r}` be the canonically assigned blocked
pair fibre. These fibres are disjoint: a pair has one assigned token and one
role. Put

`L=L_geom`, `b=(L−1)(2L−3)`, `M=Q_st b`.

Order the actual pairs by the fixed graph/port order. In each fibre retain its
first `min(b,|Π_{t,r}|)` pairs, and put all later pairs into `E_{t,r}`. Define

`E = ⋃_{t,r} E_{t,r}`,
`H = |E| = Σ_{t,r} max(0,|Π_{t,r}|−b)`.

The equality follows from the disjoint fibre partition; tagged copies do not
increase the count because the tag is a function of the original pair.
There is no graph change and no change of packing, selector, token assignment,
role, return, or boundary state. Every removed pair remains an element of the
explicit set `E`.

The bounded parts contain at most `Q_st b` pairs per token. Consequently

`|Π_blk| ≤ M |T_cap| + H ≤ M(8n+s)+H`.

Combining with the inherited free-pair estimate gives the exact corrected
counting inequality

`s(s−1)/2 ≤ (C_E+8M)n + M s + (s/2+1)log₂n + H`.       (1)

Unlike the disputed inference, (1) does not declare a handoff absent. It
charges its pair excess explicitly. It holds with all the original source
facts retained, including the strict-surplus condition when applicable.

### A proved sufficient estimate, with explicit finite constants

If fixed nonnegative constants `K,D` satisfy

`H ≤ K n + D s`,                                      (2)

then (1) implies near-cubicity for every `n≥1`, not merely an unspecified
large-order range. Put

`A=C_E+8M+K`, `B=M+D`,
`C=2B+3+sqrt(2A+4)`.

For `n≥1`, `log₂n≤2sqrt(n)`. Multiplying (1) by two, substituting (2), and
writing `x=s/sqrt(n)` therefore gives

`x² ≤ 2A+(2B+1)x/sqrt(n)+2x+4/sqrt(n)`
`   ≤ (2B+3)x+(2A+4)`.

If `x>C`, both `x>sqrt(2A+4)` and `x−(2B+3)>sqrt(2A+4)` hold, so
`x(x−(2B+3))>2A+4`, a contradiction. Hence

`s ≤ C sqrt(n)`.

This is a complete local proof **conditional on the explicit pair-count
bound (2)**. It is not a proof that (2) holds. If used in the application, the
owning surplus threshold must be checked against this `C`; deriving a larger
constant does not contradict a split made at a smaller one.

## 6. Consumer audit and complementary outcome

The existing `M_B≤16σ(G)` estimate, where applicable, bounds the sum of
negative support charges. It does not bound `H`. The former is a vertex/edge
charge; the latter counts original unordered port pairs. No equality or
injection between them has been established in this attempt.

A genuine sufficient construction would assign each pair in `E` to a payer,
with at most `Kn+Ds` aggregate capacity and no double counting. For the
centre-surplus version, let `U={(h,i): h high, 1≤i≤d(h)−3}`, so `|U|=s`.
A map `π:E→U` with `|π⁻¹(u)|≤D` would prove (2) with `K=0`.
Choosing a centre is not enough to prove the fibre bound.

Here is the exact failure exposed by trying that assignment. Suppose an
actual assignment `a:E→V_{≥4}` has been constructed. Then

`H=Σ_h |a⁻¹(h)|`, `s=Σ_h(d(h)−3)`.

Thus `H>D s` implies an actual high centre with

`|a⁻¹(h)|>D(d(h)−3)`.

The proof is summation and contrapositive: if every summand satisfied the
opposite inequality, their sums would too. This locates a concrete overload
once the assignment exists. It does **not** prove that the overloaded centre
has a new target cycle or a compressible response. The original handoff
retains only finitely many separated arms and does not make their reuse
injective across all source pair demands.

The scalar data cannot fill this hole. For any integer `N>D`, a set of `N`
pair-demand tags can all be assigned to a single centre-surplus unit. The
assignment exists, but its capacity claim fails. This is a countermodel to
that inference about assignments, not an EG graph counterexample.

### Second inventory pass: repair the assignment's source interface

The initial truncation set `E` has the clean exact formula above, but selecting
an arbitrary excess edge does not ensure it is in the particular homogeneous
pattern used by the handoff proof. Assigning all excess edges to one
independently chosen envelope would discard that source relation. The plan
is therefore refined to actual pattern extraction. The graph, fibres, roles
and port data stay fixed; only the pending subset of pair records changes.

For each fibre, start with `F=Π_{t,r}`. If `F` contains an `L`-matching or an
`L`-star, choose the first such pattern `P` in the fixed finite order, record
the handoff witness supplied for this particular pattern by the routing
lemma, and replace `F` by `F\P`. The sparse-exit alternative contradicts the
retained survivor fact. Because `|P|=L≥1`, the measure `|F|` decreases exactly
by `L`. At the empty set the process stops; if it stops earlier, it stops
precisely because neither pattern exists. The inherited matching–star bound
then gives `|F|≤b`. This proves termination, including the base case, without
changing the graph or losing any removed record. The handoff production here
uses the preceding routing lemma as a mathematical input; its implementation
fidelity is not established by this combinatorial argument.

Let `J` be the number of recorded extraction events over all fibres and let
`E*` be the union of their source patterns. These patterns are disjoint as
pair sets: each is removed before the next choice, and the original fibres
are disjoint. Thus

`|E*|=LJ`,
`|Π_blk|=|bounded remainder|+LJ≤M(8n+s)+LJ`.

Every pair in `E*` has a unique event tag. That event carries its actual source
pattern, token, role and envelope. This is a source assignment, unlike
assigning arbitrary excess pairs to an unrelated fan. The original truncation
excess satisfies `H≤LJ` because each final fibre has at most `b` pairs. The
quantitative proof above works with `H` replaced by `LJ`.

**This closes the extraction/partition construction and its termination. It
does not close payment of the events.** Selecting the least decoration of each
recorded envelope makes a total map from events to high centres. It does not
prove that a centre receives only a bounded number of events. The patterns
are pair-disjoint, but their port endpoints, connector arms, core vertices,
and fan incidences need not be disjoint. The Type B at-most-twice convention
applies to its canonical support roles; it cannot be transferred to these
event tags without a multiplicity proof.

The sufficient next bound is now `LJ≤Kn+Ds`. For `K=0`, failure gives an
actual centre `h` with

`L·#{events assigned to h}>D(d(h)−3)`.

This follows by summing the opposite inequalities. The remaining geometric
task is on this event family, including every repeated incidence. No geometric
consumer for this overload has been proved here, so it is not installed as a
new live branch.

### Third inventory pass: test whether overlap routing supplies the capacity

Candidate: capacitated Hall assignment on the **actual extraction events**.
For each event, eligible centres are the decorations in its recorded envelope;
this is a nonempty finite set, not an invented geometric witness. Give each
centre a positive integer capacity `c(h)`. Replace it by `c(h)` labelled slots.
The finite marriage theorem gives an event-to-slot injection if every event
subset `S` satisfies `|S|≤Σ_{h∈N(S)}c(h)`. If all events are injected, this
proves `J≤Σ_h c(h)`. Choosing a capacity comparable to `d(h)−3` would give
the required aggregate bound, provided the Hall inequalities are proved.

If Hall fails, choose an inclusion-minimal deficient event set `S`. This is
well-defined in the finite event family. It has the following **proved**
properties:

1. `|S|=Σ_{h∈N(S)}c(h)+1`. Deleting any event gives a proper subset with
   cardinality `|S|−1`, at most its neighbour capacity, which is at most
   `Σ_{N(S)}c`. Deficiency gives the reverse strict inequality.
2. Deleting any one event does not change `N(S)`. Otherwise the positive
   capacity of a lost centre would make its remaining capacity strictly less
   than `|S|−1`, contradicting minimality.
3. Every centre in `N(S)` is incident with at least two events, by property 2.
4. The bipartite incidence graph on `S∪N(S)` is connected. If it had two
   components, deficiency of the sum would make one proper component's event
   set deficient, contradicting minimality. Nonempty eligibility rules out
   isolated event components.
5. For each `e∈S`, the events `S\{e}` can be injected into the centre slots
   in `N(S)`: all their subsets are proper subsets of `S` and satisfy Hall.
   The injection fills every slot by property 1.

This constructs a minimal connected **incidence** obstruction with exact
unit deficit. It does not yet construct serial response paths in the original
graph. In particular, a single centre of capacity `k`, adjacent to `k+1`
events, satisfies all five properties. Its incidence graph is a tree; it has
no alternating cycle to interpret as a graph cycle. Repeated envelope arms
can also represent different event tags. Thus connectedness and minimal
deficiency alone cannot justify the serial-path/arithmetic continuation.

Outcome: the Hall construction and both abstract alternatives are explicit.
The deficient alternative has no proved graph-level consumer here. Therefore
this is recorded as a tested candidate and a more precise obstruction, not
an admitted exhaustive closure of Node [144]. The next required construction
must evaluate the shared physical arms/response coordinates, not merely
repeat matching on these event tags.

### Fourth inventory pass: repair the fold's support, then compare history

The construction and proof are in `proper-fold.md`. At a high centre h of
degree d, cubic neighbours and absence of a four-cycle imply `n≥2d+1`.
Enlarging the fold support to `N[h]∪N(a)∪N(b)` internalizes h,a,b without
swallowing G: its size is at most d+5, and n≥13 handles d=4. Folding a,b
preserves minimum degree and the boundary degree profile, and strictly reduces
the number of vertices. Minimality produces a target defect witnessed by the
actual outside, not an artificially augmented realization.

The missing quotient-reading field was then checked against the exact source
signature. Boundary-degree equality does not supply it. Moreover, the adjacent
fold is exactly the already consumed open-port suppression move, whose newly
created cycle is retained as port-activation data, not a contradiction. This
rules out declaring the fold argument a closure merely from that target defect.
The nonadjacent fold remains a candidate requiring a declared-coordinate
reading preserved by the identification.

### Fifth inventory pass: lift the fold's cycle on the retained residual

Instruction retained: no new assumptions; all existing branch facts stay in
force. The new observable is the precise location and lift of a target cycle
in the nonadjacent fold, rather than its already established existence.

`proper-fold.md` now proves the exhaustive lift: the cycle uses the merged
vertex, avoids its edge to the high centre, and splits to a simple path
between the two original neighbours of the same dyadic length. If the centre
is absent from the path, closure adds two edges; if it is present, the path
splits into two cycles with lengths summing to the dyadic length plus two.
Neither arithmetic alternative alone forces an original target cycle.

The shortest internal-centre case is explicit: two triangles through the
centre become a four-cycle upon folding neighbours from different triangles.
These are open ports in the manuscript's terminology, not its triangular
ports. The distinction was checked against the actual port definition.
Consequently this case cannot be assigned to the triangular-port theorem by
name or treated as a new sparse exit. The existing open-pair Type B routing
does not remove the outstanding consumer obligation.

This is a written mathematical consequence on the same residual, not a
kernel-certified new ledger entry. It is not an admitted closure transition:
the exact coordinate-reading equality and event-capacity obligations remain
on the queue. No hypothesis, sibling fact, new endpoint or graph replacement
has been added to the live proof.

### Sixth inventory pass: source retention and local smoothing

Scope remains exclusively Node [144]. A broader search for degree estimates
was abandoned: no external degree theorem was imported, and neither the main
reduction nor another node was edited to evade this obligation.

The live handoff schema retains the active family and certified source pattern
alongside an existential envelope. It does not publish an indexed assignment
from all removed source pairs to envelope arms with bounded fibres. In
particular, `SameTokenTypeBHandoffStatement` ends in a conjunction with
`SameTokenTypeBHandoffEnvelopeStatement data object`; the latter does not take
the source pattern or capacity presentation as an index. The construction in
the owner does use actual separating configurations, but that construction is
not itself the missing multiplicity theorem. This distinction does not erase
the earlier source facts from the exact ledger.

The proposed local degree cap was checked against `lem:fan-certificate` and
`def:marked-typeB-fan`. The bound eight requires a compatible certificate map
on every neighbour of the centre. A two-arm decorated handoff does not supply
that map. Its absence cannot be treated as a contradiction: the manuscript
explicitly retains fan-certificate residual centres. No degree cap was assumed.

`split-off.md` supplies the next actual local construction. At a heavy centre,
a nonedge pair can be split off while preserving minimum degree and reducing
edge count. Minimality forces an actual Mersenne-length path between that pair
in the original graph. At a degree-four centre, at least two full smoothings
preserve minimum degree and reduce vertex count. Their target cycles give the
explicit one-chord/two-chord path alternatives recorded there.

The arithmetic was checked against the already retained fold witness. Even
internally disjoint paths of lengths 2, 2^i, and 2^j−1 yield no dyadic cycle.
That local theta disproves the length-only shortcut, not the requested theorem
on the full residual. Consequently neither smoothing is claimed as a closed
or decreasing residual transition. The unresolved coordinate/multiplicity
consumer remains the same specific gap; this is not a proof of impossibility.

## 7. Verification, remaining queue, and exact status

Performed: read the complete recipe, copy the incoming history, compare the
actual row output with the theorem, inventory existing budgets, check the
cheap minimality operations, construct the disjoint excess pair set, prove
(1), prove the explicit implication (2) ⇒ near-cubicity, and audit the proposed
Type B consumer in the same currency; construct the terminating pattern-extraction
loop; analyze the capacitated Hall alternative and its minimal connected
defect; and prove the proper-fold geometry, checking it against the already
consumed suppression move.

Not performed/proved: a capacity-bounded assignment of `E`, a declared
response-preserving fold closing its failure, or exhaustive closure of the
strict-surplus handoff. No new diamond has been inserted in the live graph
because its negative consumer has not been proved. No new open leaf has been
hidden among the existing three. No conditional result here is presented as
an unconditional repair of the manuscript.

The exact unfinished queue is:

1. The pair-to-event assignment is constructed. Prove the required capacity
   for these actual events, or close the minimal deficient event family using
   its shared physical arms and retained response data.
2. For the nonadjacent proper fold, construct the permitted declared-coordinate
   quotient and prove `Identifies original folded` from its actual reading.
   The adjacent suppression case cannot reuse its old activation witness as
   a new contradiction.
3. Consume each resulting outcome on the exact sparse-survivor ledger.
4. Only after closure, publish the unconditional near-cubic conclusion, check
   the owning threshold and connect the branch. If the quantitative route
   succeeds, replace the false original-fibre cap inference by its proved
   accounted-pair bound; bounded remainder fibres are not caps on the original
   fibres.

This record is intentionally a partial execution, not a claim to have
completed all prescribed outcomes. The unresolved capacity/construction is
mathematics still to be proved, not permission to insert it as a Lean premise.

## Check results and source stability

- Canonical ledger/execution fixtures: build passed, 8573 jobs.
- Table synchronization check: passed after correcting the partial-match
  verdict for this label and Node [144].
- API catalog: drift detected; no refresh or new plumbing was introduced.
- Extraction checker: 2,198 small fibre instances passed. This checks the
  record-partition algorithm, not EG geometry or the actual large L parameter.
- Fold checker: 2,430 folds in explicit C4-free minimum-degree-three frames
  passed the degree, boundary and strict-size checks. These frames are not
  claimed to avoid all power-of-two cycles or to be minimal counterexamples.
- The owning Lean module rebuild completed successfully (8,744 jobs), as
  recorded in `/tmp/eg-surplus-repair-owner.log`. This builds the existing
  routing implementation; no new Lean proof of closure has been claimed.
  The local mathematical results above are written proofs, not newly
  kernel-certified declarations.
- `SpineVocabulary.lean` changed externally during the attempt. The relevant
  handoff and bottleneck definitions were reread and had the same content.
  Initial and final source hashes are retained separately.
