# Node [185]: inventory before move selection

This follows `repair_and_closure.md` §§4.7–4.8. The inventory concerns the
complete live node-[185] state, including its implemented continuation to
[186]. It does not replace that state by a graph class or a density inequality.
The earlier theta experiment is excluded from move selection.

## Fixed object

Retain the original graph and every incoming ledger key. In particular keep:

- The canonical packing and remainder, near-cubic baseline, target avoidance,
  obstruction rank, hot-branch state count, relabelling cap, and all earlier
  exit outcomes.
- The entire unified entry family with receivers, traces, basins, essential
  carriers and deletion witnesses; the committed demand and absorption
  assignments, open units, blockers, peel chain and failed stage-rate test.
- The all-visible ownership fact, visible-four packages at the original
  entry receivers, and the simultaneous balances appended at [186].
- The *selected history* in `Route8UnifiedVisibleHistoryStatement`: its
  particular support (X), receiver (w), current peeling set (P), actual
  visible-four package, original no-exit-(4) statement for its selected loads,
  and target-completeness of precisely its Q1 response pairs.

The empty-peeling packages attached to all unified receivers and the package
at the selected history's current peeling set are different indexed data.
Their exit-(4) hypotheses are not interchanged.

For the selected history only, write (A=\{u_1,u_2,u_3,u_4\}) for its four
distinct selected loads and

\[
 B_X=\{v\in X:d_X(v)<3\}.
\]

The set (B_X) is the original receiver set, not a newly declared demand
supply. Each (u_i) is an internal-degree-three vertex. Its actual selected
return carries a channel between (w) and another member of (B_X), with
its canonical trace as a suffix. Each vertex of (X) has ambient degree three.

## What earlier moves actually accounted for

The full A–I ledger is listed in `node_181_structure.md` §2. The rows below
distinguish an accounted *observable* from other structure in the same object.
An accounted fact remains available as a premise.

| Property | Present as | Accounted upstream? | Enabled technique and output |
|---|---|---|---|
| A01–A07, A09–A14 | Order, exact cubicity in (X), surplus, degree sums, wedge and cut counts, empty internal 3-core | The spine, charge, rank and entropy rows evaluate these quantities. [183] also uses exact cubicity pointwise on a selected trace. | Use these facts as constraints; do not repeat their counts as a closing move. |
| A08/E04 | Maximal degree-two chains and exact subdivision lengths | Theorem 0.9 of the structural note already develops leaf stripping and weighted suppression. This is not a fresh direction, regardless of its separate implementation status. | No further normalization proposal on that observable. |
| B01/D08 | Connected canonical supports, fixed selection orders | Canonical decomposition and trace/ledger choices | Keep the selected (X,w,P,A) fixed. |
| B02/B03 | Cuts and vertex separators between the **four actual selected loads and the original receiver set** | Bridgelessness is known. No inspected live row computes the minimum separator for these terminal sets. The retired two-mark argument did not do this either. | T04/T14: a minimum separator on (X), with actual incidence counts on its marked side. |
| B04/C13 | Maximum number of mutually vertex-disjoint paths from (A) to distinct members of (B_X) | Each load has its own visible channel. Separate visibility does not evaluate joint disjointness. No demand matching proves this graph linkage. | T14: vertex Menger gives a linkage or its minimum separator. |
| B05–B08/E05–E06 | Original boundary types, exact Q1 response comparisons, basin minimality and replacement exclusion | Already constructed and retained. The internal fold is not a Q1 comparison. | These are exact constraints on any later construction, not permission to identify arbitrary pieces. |
| B09/H06/H07 on the demand relation | Committed 2/3 assignment and absorber relation | One-entry augmentation, private-carrier bounds, global demand and absorption, and proposed Hall localization are already recorded. | Do not run another matching on the entry–essential-incidence graph. That graph is distinct from the vertex-linkage network below. |
| C01–C03/C05–C08 | Actual channels, forbidden target cycles, theta identities, induced-(P_{13}) exclusion | The original exit chain and the rejected trace–ear/theta work already used these tests. | Retain simplicity and the induced-path bound when proving properties of newly constructed paths. Do not extract another unmarked theta. |
| C04/F08 | Joint exact length behaviour of selected channels | Individual connector-plus-channel exclusions are retained. A serial increment system on these four channels has not been produced. | T09 requires that actual serial system first; the cold-branch system cannot be imported. |
| C09 | Maximum cardinality of the original packing | Remainder exclusion and global density accounted; a profitable exchange through this package is not exhibited. | T06 needs actual compatible induced paths before an exchange can be selected. |
| D05 | Joint intersection pattern of the four selected channels and their canonical traces | Individual visibility and trace suffix containment are retained. Their boundary-linkage number and minimum separating set are not evaluated. | T14 evaluates separation; T10 would require the resulting actual overlap data, not hypothetical witness cycles. |
| D07 | Equality among actual channel and connector data | Q1 response equivalence is retained. The former common-channel closure was withdrawn; equality of graph channels has not been proved from response equivalence. | T16 cannot start by assuming that equality or by repeating the fold. |
| D09 | Graph realization of the response readings at a selected connector separator | Rootability and structural first separation exist in the supporting files; the full registered reading remains a separate construction. | T05/T15 requires the actual reading and its degree fibre. A raw first separator is not already a Q4 certificate. |
| F01–F07 | Full rank, response-support cores and declared deletion witnesses | Ancestor rank/dependence rows and unified census | Retain these facts at their original entries; graph paths newly selected by Menger are not automatically declared response coordinates. |
| G01–G09/H01–H06/H08–H10 | Hot count, relabelling cap, net deficit, load capacities, exact peel/demand/absorption identities | Upstream budgets and the simultaneous [186] calculation | No new payer is introduced; all quantitative facts remain attached to every structural outcome. |
| I01–I05 | Existing finite tables, canonical orders and registered constants | Accounted for their declared inputs | No enumeration of all supports and no table of unlabelled shapes substituted for the complete state. |
| I06 | Fixed external inputs | The induced-path/3-core consequence is already retained; two-terminal textbook inputs need their literal degree hypotheses | A small separator must first produce the required actual terminal configuration. |

The former Menger attempt is specifically at `node_181_structure.md` §8 and
its correction at §12.3: it tried to obtain a single separating vertex from
failure of a path avoiding an existing common segment. That inference fails.
The observable selected here instead uses all four visible origins against
the original receiver set. Its separator is allowed to have size two or
three. Neither one-vertex separation nor silence is assumed.

## Selection from the unaccounted rows

Select **T14, vertex-capacitated Menger on the original support (X)**.
It jointly evaluates B02/B03/B04, C13 and the separating aspect of D05.
The preconditions are present: (X) is a finite actual graph, (A) has four
distinct interior vertices, (B_X\cap A=\varnothing), and all four actual
visible channels are retained. No new response realization, serial system,
packing exchange or unproved one-vertex cut is needed to execute this move.

The currency is structural constraint. This choice does not claim that a
linkage is a payer or that its separator is already an exit-(4) witness.

## Executed step: exact linkage and separator alternatives

Let κ be the maximum number of mutually vertex-disjoint (A\)-to-(B_X)
paths, counting their endpoints in the disjointness condition. Then

\[
                         2\le\kappa\le4.                 \tag{1}
\]

More precisely the complete incoming state supplies one of these outcomes:

1. **κ = 4.** Four mutually vertex-disjoint induced paths in (X), one
   from each original (u_i), ending at four distinct original receivers.
   Each has at most eleven edges, and its interior misses (B_X).
2. **κ = 2 or 3.** A minimum (A\)-to-(B_X) vertex separator (C\subset X)
   with (|C|=\kappa). Let (S) be the union of components of (X-C)
   containing a member of (A\setminus C). Then

   \[
   \begin{gathered}
   S\cap B_X=\varnothing,\qquad A\setminus C\subseteq S,
      \qquad |A\cap S|=4-|A\cap C|\ge4-\kappa,\\
   \delta_G(S)\subseteq E_G(S,C),\qquad
   2\le|\delta_G(S)|\le2\kappa\le6.                    \tag{2}
   \end{gathered}
   \]

   There are at most κ components of (S), each a proper connected
   ambient-cubic shore with at least two actual cut edges. Every original
   selected trace starting in (S) meets (C) before reaching (w).

**Proof of the linkage–separator identity.** Split each vertex of (X)
into an input and output joined by an arc of capacity one. Give the two
directed arcs for each graph edge capacity five. Connect a source to the
inputs of (A) and the outputs of (B_X) to a sink, also with capacity five.
Cutting the four input-output arcs at (A) bounds the minimum cut by four.
The integral augmenting-path algorithm either increases the flow or, when
no residual source–sink path exists, returns its reachable-side cut with
capacity equal to the flow. Thus it terminates with an integral maximum
flow and minimum cut of the same value.

No arc of capacity five can occur in a minimum cut. The cut therefore
consists of vertex arcs; their original vertices separate (A) from (B_X).
Conversely any such separator cuts the network by its vertex arcs. An
integral flow, after deleting circulations, gives vertex-disjoint graph
paths: a vertex arc's unit capacity forbids sharing, including at either
terminal set. This proves the stated min–max identity and κ ≤ 4.

**Why κ is at least two.** Each original selected load (u_i) lies on its
actual simple channel between two distinct original receivers. The two
directions of that channel give two paths from (u_i) to (B_X), intersecting
only at (u_i). They can be stopped at their first receiver. No single
vertex other than (u_i) blocks both. Since (A) has four members, for
any proposed singleton separator one can choose (u_i) different from it.
That singleton does not separate (A) from (B_X). There is also an
(A\)-to-(B_X) path, so the empty set is not a separator. Menger now gives
the lower bound in (1).

**The four-path outcome.** Trim each path at its first receiver, and choose
a four-path linkage minimizing its total number of edges. A chord of one
path would shorten it without meeting another path; hence each is induced.
The original (X) is induced-(P_{13})-free, so every path has at most
eleven edges. Unit capacities give distinct initial and terminal vertices.
These paths are additional graph data; the original scheduled traces and
returns are kept, not replaced by them.

**The separator outcome.** Choose a minimum separator (C), breaking ties
by the existing order. Its deletion separates every vertex of (A\setminus C)
from (B_X\setminus C). Thus (S) has the first two properties in (2).
Every vertex of (S) has degree three already inside the original (X),
because (S\cap B_X=\varnothing). It has no neighbour outside (X).
Every edge from (S) to (X\setminus S) meets (C), by the definition of
components of (X-C). This proves the asserted cut containment.

Each (c\in C) has at most two neighbours in (S). If (c\in B_X), this
follows from its original internal degree being at most two. If (c\notin B_X),
minimal cardinality of (C) says that (C\setminus\{c\}) is not a separator.
Take an (A\)-to-(B_X) path avoiding that smaller set. It uses (c), and
its part after (c) reaches (B_X) without another vertex of (C).
The first neighbour on that part cannot belong to (S), since otherwise
its component in (X-C) would meet (B_X). Thus (c) has a neighbour outside
(S), and exact ambient cubicity gives at most two neighbours in (S).
Summing over (C) proves the upper bound (2\kappa).

There is at least one selected load outside (C), so (S) is nonempty.
Each of its components is a proper shore of connected bridgeless (G), and
therefore has at least two cut edges. Their cuts are disjoint and sum to
(\delta_G(S)), so there are at most κ components. Finally (w\in B_X)
and each original selected trace lies in (X); a trace from (S) must
leave through (C). This proves all assertions. □

## Exact accounting after the move

The full branch state remains the first coordinate. In the separator case,
the four selected origins have the exhaustive recorded partition

\[
                  A=(A\cap S)\mathbin{\dot\cup}(A\cap C).
\]

Both sets keep their original witnesses and assignments. No origin in (C)
is declared paid or removed. The cut edges of (S) are actual *internal*
edges of (X); they are not members of the original boundary supply.
No receiver, demand, absorber or essential-core definition is transferred
from (X) to (S) without a separate proof.

The B04 observable is now evaluated exactly by κ. On its lower arm, the
previously unevaluated marked separation has a quantitative certificate:
two or three separator vertices, at most six actual cut incidences, at
most three shores, and at least (4-\kappa) original visible origins inside.
On its upper arm, simultaneous realizability is an actual four-path linkage,
rather than an assumption about separately existing channels.

The next inventory is consequently on these *same indexed data*: the
four-path linkage together with its original trace/return intersections, or
the marked shores and their at most six incidences together with the original
Q1/peel/core records. It must retain the origins in the separator as well as
those inside. No cold-branch theorem or silent-load premise is imported.

**Proof status.** The displayed local implication is proved above. Its two
outcomes do not yet have complete closure continuations, so no new node,
recursive reduction, demand payment, or closed status is asserted. The
methodology's admission requirement for a proof-DAG transition remains to be
satisfied; recording κ alone is not reported as closing node [185].
