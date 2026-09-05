# Node [181]: structural accounting through [185]

This document lists every fact that holds for the minimal counterexample $G$
when the proof reaches node [181], the arm taken at every diamond on the way,
the technique (register T01–T19) that produced each fact and the register
property (A01–I06) it evaluated, and the exact typed data at the leaf. Nothing
is projected, summarized, or dropped. Section 0 records the implemented
strict transition from [181] to [124] or [183], followed by the strict
shortest-trace boundary-support reduction from [183] to [184] and the strict
visible-first prefix exhaustion from [184] to [185]. The existing exit-(4)
producer now also retains target-completeness for each selected Q1 response
pair, at its original receiver and peeling set. This does not identify an
internal vertex fold with a Q1 response-coordinate identification. The fold
calculation below is retained, but its former closure claim is withdrawn.
Sections
6–12 retain the earlier
trace--ear attempt and its audit because several of its local identities are
correct and useful. They are not used in the implemented transition. Sections
13–20 retain a superseded block--cut draft for audit history only. That draft
incorrectly treated every unpaid unified entry as silent, whereas the live
`route8UnifiedEntries` family contains both visible-first and silent-excess
loads. No assertion from §§13–20 is part of the proof DAG.

Sources: `to_formalize/erdos_64_proof.tex` (labels in backticks; node numbers
in brackets), `closure_proofs.md` (Theorems 1.3–1.5, 3.1–3.4), the live
statement types in `HypostructureErdos64EG/StrategyDag.lean` and
`Graph/Strategy/SpineVocabulary.lean`, and the register
`web/frontend/src/structural-survey/data.ts`.

---

## 0. Implemented reductions and retained Q1 semantics through [185]

The first new textbook move on the literal node-[181] residual is a
**one-entry augmentation of a lexicographically maximal finite packing**. It
uses no silence assumption, does not rerun the demand construction, and does
not pass to another graph or another support.

Let `entries` be the retained unified entry family, let
`core(ξ)` be its canonical essential-carrier set, and let

\[
  \operatorname{priv}(\xi)
   :=\{c\in\operatorname{core}(\xi):
       c\notin\operatorname{core}(\eta)
       \text{ for every }\eta\in\texttt{entries},\ \eta\ne\xi\}.
\]

The incoming demand fact supplies a partition

\[
       P=(\Xi_3(P),\Xi_2(P),\Xi_{\rm res}(P);A_P)
\]

which is lexicographically maximal in
\((|\Xi_3(P)|,|\Xi_2(P)|)\), subject to the pinned-entry condition. Put

\[
       \Xi_{\rm un}(P):=\Xi_2(P)\mathbin{\dot\cup}\Xi_{\rm res}(P).
\]

### Theorem 0.1 (unpaid entries have at most two private carriers)

For every \(\xi\in\Xi_{\rm un}(P)\),

\[
                         |\operatorname{priv}(\xi)|\le2. \tag{0.1}
\]

#### Proof

Suppose instead that some unpaid \(\xi\) has at least three private carriers,
and choose a three-element set
\(D\subseteq\operatorname{priv}(\xi)\). Define a new ledger \(Q\) by

\[
 \Xi_3(Q)=\Xi_3(P)\cup\{\xi\},\qquad
 \Xi_2(Q)=\Xi_2(P)\setminus\{\xi\},\qquad
 \Xi_{\rm res}(Q)=\Xi_{\rm res}(P)\setminus\{\xi\},
\]

set \(A_Q(\xi)=D\), and leave every other assignment unchanged. The three
classes still form a disjoint partition of `entries`. The new assignment is
available because \(D\subseteq\operatorname{core}(\xi)\), and has cardinality
three. Every old size-two or size-three assignment is unchanged.

For disjointness, if \(\eta\ne\xi\), then the old assignment
\(A_P(\eta)\) lies in \(\operatorname{core}(\eta)\). Privacy of every
\(c\in D\) therefore gives \(c\notin A_P(\eta)\). Thus \(D\) is disjoint
from every old assignment, while old assignments remain pairwise disjoint.
Finally, a pinned entry different from \(\xi\) keeps its assignment. The
entry \(\xi\) itself cannot be pinned: every pinned entry already belongs to
\(\Xi_3(P)\), whereas \(\xi\in\Xi_2(P)\cup\Xi_{\rm res}(P)\). Hence \(Q\)
is an admissible pinned ledger and

\[
                    |\Xi_3(Q)|=|\Xi_3(P)|+1,
\]

contradicting the first coordinate of maximality. This proves (0.1). ∎

In Lean this exchange is proved anonymously inside
`route8UnpaidExitFourDichotomy`. The decision reads the incoming demand
partition, constructs the comparison partition \(Q\), verifies every
partition, availability, disjointness, cardinality, and pinned-assignment
clause there, and contradicts the first coordinate of the retained
maximality statement. No detached helper theorem or stronger intermediate
API is introduced.

### Theorem 0.2 (exhaustive exit-(4) split)

Exactly one of the following occurs.

1. Some \(\xi\in\Xi_{\rm un}(P)\) has no exit-(4) witness. Then the retained
   unified census makes \(\xi\) target-complete-minimal, gives
   \(\alpha(\xi)\ge2\), and Theorem 0.1 gives its two-carrier bound. These are
   exactly the inputs of the existing node-[124] proposition, so this arm
   closes there.
2. Every \(\xi\in\Xi_{\rm un}(P)\) has an exit-(4) witness. Together with
   Theorem 0.1 this is the exact intermediate residual fact at node [183].

#### Proof

Choose an unpaid entry with no witness if one exists. The unified census says
that its basin is either target-complete-minimal, or target-defective together
with an exit-(4) witness for the same indexed load. The second alternative
contradicts the choice. Thus the entry is target-complete-minimal. The census
also supplies \(\alpha\ge2\), and (0.1) supplies the two-carrier condition.
The retained no-witness statement is therefore literally
`route8UnifiedTrueTwoCarrierEntry`; its unique existing consumer
`route8UnifiedTerminalNoGoRow` closes node [124].

If no such entry exists, classical negation gives a witness for every unpaid
entry, and (0.1) holds for each of them. This is precisely
`Route8UnpaidExitFourResidualStatement`. ∎

For quantitative accounting define

\[
 H_{181}(P)=\{\xi\in\Xi_{\rm un}(P):
                   |\operatorname{priv}(\xi)|\ge3\},\qquad
 N_{181}(P)=\{\xi\in\Xi_{\rm un}(P):
                   \xi\text{ has no exit-(4) witness}\}.
\]

Theorem 0.1 proves \(|H_{181}(P)|=0\) on both arms. A positive value of
\(|N_{181}(P)|\) closes at [124]; the only surviving arm [183] has

\[
              (|H_{181}(P)|,|N_{181}(P)|)=(0,0). \tag{0.2}
\]

Thus the residual predicate has strictly fewer admissible structural profiles,
while the entry family, demand units, assignments, peel chain, absorption,
window blockers, unified census, and every earlier ledger key are retained.

The Lean decision is `route8UnpaidExitFourDichotomy`; the Assembly consumer is
`selectedRouteEightUnpaidExitFourReduction`. On its right arm the fact
`route8UnpaidExitFourResidual` is appended to the unchanged `ExactLedger`.

### Theorem 0.3 (shortest-trace visible-ownership reduction)

Let `entries := route8UnifiedEntries data object` be the same broad unified
family retained from [123]. It contains both visible-first and silent-excess
loads; it is not replaced by a silent subfamily. Define only the residual
coordinate

\[
 S_{184}:=
 \{\xi=(X,w,u)\in\texttt{entries}:
       u\notin\operatorname{visibleLoads}(X,w)\}.             \tag{0.3}
\]

On the literal node-[183] state,

\[
       \forall\xi=(X,w,u)\in\texttt{entries},\quad
       u\in\operatorname{visibleLoads}(X,w),
 \qquad S_{184}=\varnothing,
 \qquad |S_{184}|=0.                                         \tag{0.4}
\]

#### Proof

Fix an actual retained entry \(\xi=(X,w,u)\), and suppose that its load is
silent. Let \(P:u\leadsto w\) be its canonical path selected by `tracePath?`,
and let \(T\) be the vertex set of \(P\). Every object in this sentence is
already determined by the incoming entry and its fixed path schedule.

**1. Exact cubicity on the incoming support.** Membership of \(X\) in the
unified negative collection gives ambient surplus zero. The incoming
minimum-degree baseline gives \(d_G(x)\ge3\) for every \(x\), while ambient
surplus is the sum over \(X\) of the nonnegative terms \(d_G(x)-3\). Hence

\[
                         d_G(x)=3\qquad(x\in X).              \tag{0.5}
\]

**2. The selected trace is induced.** The path schedule used by `tracePath?`
is ordered first by length. Consequently the selected trace is no longer
than any other trace-shaped \(u\)--\(w\) path. Take a shortest
\(u\)--\(w\) path in the induced graph on \(T\). Its vertices are vertices of
the original trace, so it inherits the original trace-shape conditions; it is
therefore one of the candidates in the same schedule. The selected trace is
no longer than it, while shortestness gives the reverse inequality. Thus the
selected trace is itself shortest in the induced graph on \(T\), and the
standard chord-shortening argument makes it induced.

The source and target are distinct: the routed-load clause makes \(u\)
internally cubic in \(X\), whereas the receiver clause makes \(w\) internally
deficient. Every vertex of an induced nontrivial path has at most two
neighbours in its vertex set. Equation (0.5) therefore gives an edge leaving
\(T\) at every trace vertex. In the exact boundary notation,

\[
                              T\subseteq\partial_VT.          \tag{0.6}
\]

**3. Silence makes the trace support complete.** For each supported D1--D4
coordinate, the retained coordinate census has two exhaustive readings. It
either meets the selected trace at a vertex declared in its support, or its
declared support is owned by an actual scheduled receiver-entry return for
\(u\). The second reading contradicts the assumed silence of \(u\). In the
first reading the declared vertex belongs to \(\partial_VT\) by (0.6).
The trace itself supplies containment and connectedness. Thus \(T\) satisfies
every clause of `TraceComplete` for this same entry.

**4. Basin minimality identifies the basin with the trace.** The selected
basin \(B_u\) contains the selected trace. Since \(T\) is now a complete
candidate, the minimum-cardinality selection rule gives \(|B_u|\le|T|\).
Therefore

\[
                              B_u=T.                           \tag{0.7}
\]

**5. A boundary-only basin has empty essential core.** Equations
(0.6)--(0.7) put every basin vertex on the basin boundary. In the literal
definition of `retainedBasinPiece`, a retained coordinate set can alter only
an edge whose two decoded endpoints are interior vertices. A boundary-only
basin has no such endpoints. Hence every retained coordinate set produces
the same boundaried piece and the same response state. In particular the
empty coordinate set is complete. The canonical essential core has minimum
complete cardinality, so

\[
                 \alpha(\xi)=|\mathcal C_{\rm ess}(\xi)|=0.   \tag{0.8}
\]

The incoming unified census, on this same index, says
\(\alpha(\xi)\ge2\). This contradiction eliminates the silent assumption.
Since the entry was arbitrary, every entry is visible and (0.4) follows. ∎

This is the first new structural move after [183]: shortest-path chord
elimination followed by boundary-support collapse. It does not rerun visible
routing, demand packing, or exit-(4) peeling. The anonymous proof lives inside
the Type-A atomic row `route8UnifiedVisibleResidualRow`; that row reads
`route8UnifiedEntryCensus`, appends
`route8UnifiedVisibleResidual`, and retains the complete incoming key list.
Assembly enforces the literal predecessor by running it only on a ledger that
already contains `route8UnpaidExitFourResidual`; its consumer is
`selectedRouteEightVisibleResidual`.

For quantitative accounting, append the third coordinate to (0.2):

\[
       \bigl(|H_{181}(P)|,|N_{181}(P)|,|S_{184}|\bigr)
                              =(0,0,0).                        \tag{0.9}
\]

The transition [183]→[184] removes the entire silent structural profile, not
any entry. The exact entry family, the partition
\(\Xi_3\mathbin{\dot\cup}\Xi_2\mathbin{\dot\cup}\Xi_{\rm res}\), every demand
assignment, every exit-(4) witness, the peel chain, both absorption classes,
the unique-window blocker map, the unified census, and every earlier
`ExactLedger` key remain attached. Node [184] is therefore a strict residual:
all retained entries have actual return ownership, and no claim that this
remaining all-visible overlap structure is empty has been inserted.

### Theorem 0.4 (visible-first prefix exhaustion)

Keep the same broad family
route8UnifiedEntries and write \(s\) for the retained discharge scale. For an
entry \(\xi=(X,w,u)\), let \(\mathcal P_X(w)\) be the actual completion ports
of \(w\), and let \(\mathcal L_{\rm vis}(X,w;h)\) be the visible loads owned
through port \(wh\). Define the remaining non-overload coordinate

\[
 O_{185}:=
 \left\{\xi=(X,w,u)\in\texttt{entries}:
   \forall h\in\mathcal P_X(w),\quad
   |\mathcal L_{\rm vis}(X,w;h)|<s\right\}.             \tag{0.10}
\]

On the literal node-[184] state,

\[
 O_{185}=\varnothing,
 \qquad |O_{185}|=0,                                    \tag{0.11}
\]

and every retained entry has an actual canonical package consisting of an
overloaded port, \(s\) distinct visible loads owned through that port, and the
first scheduled actual receiver-entry return for each selected load.

#### Proof

Fix \(\xi=(X,w,u)\in\texttt{entries}\). Literal membership in the incoming
family gives

\[
 u\in E_X(w):=\mathcal L_X(w)\setminus A_X(w),           \tag{0.12}
\]

where \(A_X(w)\) is the visible-first payable prefix of length
\(s q_X(w)-1\), and \(q_X(w)=3-d_X(w)\). Node [184] gives the additional
fact \(u\in\mathcal L_{\rm vis}(X,w)\) for this same entry. Nothing is
reselected.

Suppose \(\xi\in O_{185}\). The zero ambient-surplus and minimum-degree facts
already used in Theorem 0.3 give \(d_G(x)=3\) for every \(x\in X\). Hence
\(w\) has exactly \(q_X(w)\) completion ports. Since \(w\) is a receiver,
\(d_X(w)<3\), so \(q_X(w)\ge1\). The defining inequality of \(O_{185}\)
gives at most \(s-1\) visible loads at each port. Counting every visible load
at one of its actual owning ports yields the retained port-cap estimate

\[
 |\mathcal L_{\rm vis}(X,w)|+q_X(w)
       \le s q_X(w),
 \qquad
 |\mathcal L_{\rm vis}(X,w)|\le s q_X(w)-1.             \tag{0.13}
\]

The second inequality says that the entire visible block fits inside the
visible-first prefix. Thus
\(\mathcal L_{\rm vis}(X,w)\subseteq A_X(w)\), and the node-[184] ownership
of \(u\) gives \(u\in A_X(w)\). This contradicts (0.12). Therefore every
entry lies outside \(O_{185}\), proving (0.11).

For each entry, the negation of membership in \(O_{185}\) supplies an actual
completion port carrying at least \(s\) distinct visible loads. The already
fixed finite orders choose the first such port, the first \(s\) loads at that
port, and the first scheduled visible return for each load. These choices
form VisibleFourUnpeeledPackage at the empty peeling set. They are all paths
and vertices of the selected graph, not profile-context data. ∎

The anonymous Lean proof is the Type-A atomic row
route8UnifiedVisibleOverloadRow. It reads only
route8UnifiedVisibleResidual, appends route8UnifiedVisibleOverload, and leaves
every incoming key queryable. Its Assembly consumer is
selectedRouteEightVisibleOverload; all three selected route-8 continuations
run it immediately after selectedRouteEightVisibleResidual.

Appending the fourth exact coordinate to (0.9) gives

\[
 \bigl(|H_{181}(P)|,|N_{181}(P)|,|S_{184}|,|O_{185}|\bigr)
                         =(0,0,0,0).                     \tag{0.14}
\]

This is not another peel and does not reconstruct the payable order. It
consumes the all-visible ownership fact that first becomes available at
[184] and eliminates the complete non-overloaded ownership profile. The
entry family, demand partition and assignments, exit-(4) witnesses, peel
chain, absorbers, blockers, basins, essential cores, and all prior
ExactLedger keys remain unchanged. The exact [185] frontier therefore
consists entirely of entries whose receivers carry canonical actual
visible-four packages.

<!-- RETAINED DIAGNOSTIC: the joint-balance calculation below is the earlier
accounting draft. The live Lean DAG still carries the joint-balance row at
[186]; Theorem 0.7 does not replace it with a closure.

### Theorem 0.5 (the simultaneous node-[185] balance)

The preceding reductions must now be read together with the quantitative
facts that entered [181]. Use denominator-cleared notation throughout:

\[
\begin{array}{c|l}
r&=|R|,\\
b&=|\partial_E R|=|\operatorname{supply}|,\\
h&=\text{the retained Type B/near-cubic exceptional allowance},\\
D&=\displaystyle\sum_{X\in\widetilde{\mathcal X}}
       (|X|-4\defp(X)),\\
N&=|\widetilde\Xi|,\\
p&=|P_4|=|\text{the recorded peel-chain set}|,\\
O&=|\mathcal U_{\rm press}\setminus\mathcal U_{\rm abs}|
     =\mathsf P_{\rm open}.
\end{array}                                                   \tag{0.15}
\]

Here \(h=o(r)\), the threshold is \(3\), the discharge scale is \(4\), and
the failed-stage slack is \(2h\). For the committed maximal demand partition
write

\[
 N=N_3+N_2+N_{\rm res},\qquad
 a=3N_3+2N_2,\qquad
 d=N_2+3N_{\rm res}.                                        \tag{0.16}
\]

Let \(B\) be the number of type-(A1) absorbed units. The type-(A2) units have
already routed to the proper-compression or support-dependence exits on this
branch, so their surviving count is zero. Concretely, the witness stored by
the live `route8DemandAbsorptionRow` has dependence set `∅`. Its type-(A1)
absorber is an unused incidence of the **same support as the owning entry**:
for every absorbed unit \(\upsilon\), the retained typed clause is
\[
 A(\upsilon)\in\operatorname{cutEdges}
       (\operatorname{owner}(\upsilon)).                    \tag{0.16a}
\]
The assignment is globally injective and disjoint from every base assignment.
Thus it may be partitioned by owner support without changing any assignment or
discarding any unit. Every calculation below uses this full correlation.

Then all of the following hold simultaneously:

\[
\boxed{N=D+U}\quad(U\ge0),                                  \tag{0.17}
\]

\[
\boxed{r\le D+4b+h},                                        \tag{0.18}
\]

\[
\boxed{3N\le b+O},                                          \tag{0.19}
\]

\[
\boxed{3r\le13b+6h+3p}.                                    \tag{0.20}
\]

Moreover every routed load at a saturated receiver of a member of
\(\widetilde{\mathcal X}\) is visible, not merely every load that happens to
index an excess entry.

#### Proof

Fix \(X\in\widetilde{\mathcal X}\). Every vertex of \(X\) has ambient degree
three. As already proved at the node-[181] leaf, a connected negative support
has no internal-degree-zero receiver. Hence every receiver \(w\) has

\[
 q(w)=3-d_X(w)\in\{1,2\}.                                   \tag{0.21}
\]

Write \(L(w)\) for its routed-load count. If \(w\) is saturated, its
visible-first payable prefix has exactly \(4q(w)-1\) members, and hence its
excess-entry count is

\[
 e(w)=L(w)-(4q(w)-1).                                       \tag{0.22}
\]

If \(w\) is unsaturated, put

\[
 u(w)=(4q(w)-1)-L(w)\ge0.                                   \tag{0.23}
\]

Every internal-degree-three vertex is routed exactly once. Summing \(L(w)\)
over the receivers of \(X\), and separating saturated and unsaturated
receivers, gives

\[
\begin{aligned}
 N_X-U_X
 &=\sum_{w\ {\rm sat}}e(w)-\sum_{w\ {\rm unsat}}u(w)\\
 &=n_3(X)-3n_2(X)-7n_1(X)\\
 &=|X|-4\defp(X)=D_X,                                      \tag{0.24}
\end{aligned}
\]

where \(N_X=\sum_{w\ {\rm sat}}e(w)\) and
\(U_X=\sum_{w\ {\rm unsat}}u(w)\). The supports are disjoint and their
entry families are disjoint, so summing (0.24) proves (0.17).

Node [184] upgrades the same calculation. Suppose a saturated receiver had a
silent routed load. If it had at least \(4q(w)-1\) visible loads, the
visible-first prefix would consist entirely of visible loads and every silent
load would lie in the excess. If it had fewer than \(4q(w)-1\) visible loads,
the prefix would contain all visible loads; since saturation gives at least
one load beyond the prefix, some silent load would again lie in the excess.
Either way the unified family would contain a silent entry, contradicting
Theorem 0.3. Thus every saturated routed load is visible. Theorem 0.4
consequently supplies a canonical actual visible-four package at every
saturated receiver that contributes to \(N\).

Equation (0.18) is the retained unified-deficit fact with threshold \(3\),
scale \(4\), and exceptional allowance \(h\). The demand partition has the
exact identity

\[
                         3N=a+d.                             \tag{0.25}
\]

The demand units split into \(B\) type-(A1) absorbed units and \(O\) open
units, because the type-(A2) count is zero:

\[
                         d=B+O.                              \tag{0.26}
\]

The \(a\) base incidences and the \(B\) absorber incidences are actual
single-use members of the same boundary supply, and the two families are
disjoint. Therefore

\[
                         a+B\le b.                           \tag{0.27}
\]

Substitution of (0.26)--(0.27) into (0.25) proves (0.19). Finally, the
literal failed StageRate assertion is the negation of

\[
                         13b+6h+3p<3r.
\]

All quantities are natural numbers, so its negation is exactly (0.20). No
asymptotic replacement or discarded peel is involved. \(\square\)

The four displayed relations are not independent estimates. Eliminating
\(D\) and \(N\) between (0.17)--(0.19) gives the single coupled pressure
bound

\[
                  O\ge3r-13b-3h.                            \tag{0.28}
\]

Likewise (0.20) gives the exact peel lower bound

\[
                  3p\ge3r-13b-6h.                           \tag{0.29}
\]

These are the two sides of the same obstruction: the mass which the failed
stage could not leave in the reduced ledger is still present both as recorded
peels and as unabsorbed demand.

This theorem is implemented as the anonymous atomic row
`route8JointBalanceRow`.  Its output is the canonical key
`route8JointBalance` (index 506).  The row retrieves
`route8UnifiedVisibleResidual`, `route8UnifiedVisibleOverload`,
`route8PeeledDemandResidual`, and `route8UnifiedDeficit` from the same
`ExactLedger`; proves the saturated-load visibility statement directly from
the visible-first order; reuses the committed peel chain, maximal partition,
and empty-dependence absorption witnesses; and appends all exact identities
and the subtraction-free form of (0.28).  The Assembly consumer
`selectedRouteEightJointBalance` is run on every route-8 continuation, so the
implemented boundary after [185] is [186].

### Theorem 0.6 (the silent unpeeled terminal is empty)

On the literal node-[186] state, fix any retained unified component (X),
any saturated receiver (w) of (X), and any recorded peeling set (P).
Then

\[
 \mathcal L^{P}_{\rm un}(w)\setminus
 \mathcal L_{\rm vis}(w)=\varnothing.                       \tag{0.30s}
\]

#### Proof

Assume the set is nonempty and choose a load (u) in it. By the definition
of `unpeeledLoads`, (u) is a member of the routed-load family
(mathcal L(w)). The universal saturated-load visibility clause already
proved in Theorem 0.5 therefore puts (u) in
(mathcal L_{\rm vis}(w)). But membership in the displayed set also says
(u\notinmathcal L_{\rm vis}(w)), a contradiction. Hence the set is empty.
(square)

This is the exact quantitative decrease: for every triple ((X,w,P)), the
number of admissible silent-unpeeled loads falls to zero. The proof does not
reselect a component, rebuild a demand partition, or alter the peel history.
It is proved inside `route8JointBalanceRow` and stored as a conjunct of
`route8JointBalance` (key 506) in the same `ExactLedger`. Thus [186] performs
one strict reduction: it closes the silent terminal profile quantitatively.
The distinct visible-entry history is not used in this elimination and remains
the next object to audit separately.

-->

### Theorem 0.7 (target-completeness of the retained Q1 response pairs)

Take the selected history at [185], including its original no-exit-(4)
statement. Let \(P\) be its `VisibleFourUnpeeledPackage`, at its actual
receiver \(w\) and current peeling set \(P_4(w)\). For every
\(p:P.\texttt{Q1OriginPair}\), put

\[
 A_p=\texttt{visibleResponsePiece}(p.\texttt{leftResponseCoordinate}),
 \qquad
 B_p=\texttt{visibleResponsePiece}(p.\texttt{rightResponseCoordinate}).
\]

The two pieces have the same boundary-degree profile and are context-equivalent
for the retained target predicate. Consequently the set of target-defective
Q1 origin pairs in this package is empty.

#### Proof

Both profiles are the profile of the same selected support, by
`visibleResponsePiece_boundaryDegreeProfile`. Fix an origin pair \(p\).
Context universality gives context equivalence or a target defect between
exactly \(A_p\) and \(B_p\). In the second case, the original Q1 constructor
gives `P.witnessOfPairTargetDefect p`: its load is the selected left load,
which belongs to the current unpeeled selected list. It is therefore a witness
excluded by the no-exit-(4) statement for this very package and peeling set.
This contradiction excludes the second alternative and proves context
equivalence. Together with equality of profiles this is `TargetComplete`.
Since the argument holds for every origin pair, none is target-defective. ∎

The proof is published by the original exit-(4) decisions, including their
terminal retests, in the visible conjunct of `ExitFourFreeAt`. Both the
no-witness statement and the pairwise conclusion are retained through
`typeAExitFiveFree`, `typeAExitSixFree`, and the selected no-handoff state.
The node-[185] atomic row reads that state and publishes the conclusion for
the same package under `route8UnifiedVisibleHistory`. All existing keys and
their ancestry remain in `ExactLedger`; no new key, hypothesis, or node is
introduced. This is the explicit retention of an upstream consequence, not
a new residual reduction or a proof of `False` at [181].

### The internal-fold calculation and its exact semantic consequence

Work on the literal selected history retained at [185]. Its
`VisibleFourUnpeeledPackage` contains four distinct selected loads

\[
                         U=\{u_1,u_2,u_3,u_4\}.               \tag{0.31}
\]

No equality of channels, nesting of traces, or additional comparison
hypothesis is used. There is a pair (u,v\in U) for which one of the
following alternatives holds.

1. (u) and (v) have no common neighbour.
2. (u) and (v) have a unique common neighbour (x), and there is
   (c\in U-\{u,v\}) with (c\ne x) and (xc\notin E(G)).

Identifying (u) and (v), and in the second alternative adding the edge
(xc), gives a canonical boundaried piece (X^{\rm fold}) inside the same
selected Type A support (X) such that

\[
 \mathbf d_\partial(X^{\rm fold})=\mathbf d_\partial(X),
 \qquad
 \delta\bigl(X^{\rm fold}\oplus_\partial(G-X)\bigr)\ge3,
 \qquad
 |V(X^{\rm fold}\oplus_\partial(G-X))|=|V(G)|-1.             \tag{0.32}
\]

The comparison of this fold with the original piece is target-defective:
context equivalence would contradict the incoming replacement exclusion.
This statement concerns the original support and its fold, not the two
response pieces in Theorem 0.7.

#### Proof

**1. The four selected vertices are full interior cubic vertices.** The
presentation facts retained by `cubicBaseline` give (delta=3) and (s=4).
The package's selected list has length (s) and is repetition-free, proving
(0.31). Every selected load lies in `unpeeledLoads`, hence in the selected
support (X), and `mem_routedLoads` gives

\[
                         d_X(u_i)=3.                          \tag{0.33}
\]

The selected Type A support has ambient surplus zero. Since the incoming
baseline gives (d_G(y)\ge3) for every vertex, the defining nonnegative
surplus sum forces (d_G(y)=3) for every (y\in X). Combining this with
(0.33) shows that every neighbour of every (u_i) belongs to (X). Thus all
four selected vertices are full interior vertices of the actual boundaried
piece; none is a boundary label.

**2. A foldable pair always exists.** Any two distinct vertices of (G)
have at most one common neighbour. Otherwise two distinct common neighbours
(a,b) give the simple four-cycle (uavbu), contrary to the retained target
avoidance and `quadrilateralAccepted`.

Choose two vertices (u,v\in U). If they have no common neighbour, the first
alternative holds. Otherwise let (x) be their unique common neighbour. If
(x\notin U), then (x) already uses two of its three incident edges on
(u,v); among the two members of (U-\{u,v\}), at least one, say (c), is
not adjacent to (x). This is the second alternative. If (x\in U), let
(c) be the fourth member of (U). Again the second alternative holds
unless (xc\in E(G)).

It remains to treat (x\in U) and (N_G(x)=\{u,v,c\}). If one of the three
pairs (xu,xv,xc) has no common neighbour, use that pair and the first
alternative holds. Suppose instead that each has a common neighbour. A common
neighbour of (x) and a member of ({u,v,c}) must itself be one of the
other two members of this set. Therefore the graph induced by
({u,v,c}) has minimum degree at least one and hence at least two edges.
Two such edges share one of these three vertices; together with the two
corresponding edges incident with (x), they form a simple four-cycle. This
contradiction exhausts the last case and proves the asserted dichotomy.

**3. The local fold preserves the baseline and the exact boundary fibre.**
Identify (u) and (v) to a new vertex (z), delete the resulting loop if
(uv\in E(G)), and merge duplicate incidences, as required for a simple
graph.

If (u,v) have no common neighbour, no other vertex loses degree. The new
vertex has degree six when (uv\notin E(G)), and degree four when
(uv\in E(G)). Thus the ambient minimum degree remains at least three.

Suppose (x) is the unique common neighbour and (c) is supplied by the
second alternative. After the identification, (x) is the only vertex whose
degree decreases: its two incidences (xu,xv) merge to (xz), so its degree
is two. The vertex (z) has degree five if (uv\notin E(G)), and degree
three if (uv\in E(G)). Add the missing edge (xc). This restores the
degree of (x) to three, raises the degree of the full interior vertex (c)
from three to four, and changes no other degree. The repaired graph again has
minimum degree at least three.

The boundary accounting is exact in both cases. The removed vertices
(u,v), the optional repair endpoint (c), and the folded vertex (z) are
interior. Every retained boundary vertex other than (x) merely replaces an
incident edge to (u) or (v) by one incident edge to (z), so its internal
degree is unchanged. If (x) is a boundary vertex, the fold removes exactly
one internal incidence and the repair adds exactly one internal incidence.
All outside edges and all boundary labels are untouched. Hence the identity
on the original boundary gives the first equality in (0.32). Finally, two
internal vertices have been replaced by one and the repair adds no vertex, so
the glued realization has exactly one fewer vertex. This proves (0.32), with
no remaining construction arm.

**4. Replacement exclusion forces target defect of the fold.** Apply
`Response.contextEquivalent_or_targetDefect` to \(X^{\rm fold}\) and
the original piece \(X\). If they are context-equivalent, the one-way target
implication holds for every compatible outside context. The selected support
is connected and proper, and (0.32) supplies the unchanged boundary profile,
the minimum-degree bound, and strict lexicographic decrease. These are the
fields of `InterfaceReplacement.ReplacementSupport`, contradicting the
retained `replacementExclusion` fact. Thus the fold is target-defective. ∎

There is no contradiction with Theorem 0.7: its pieces are \(A_p,B_p\), whereas
this comparison uses \(X,X^{\rm fold}\). The first assertion is
\(\operatorname{TargetComplete}(A_p,B_p)\); the second is
\(\operatorname{TargetDefect}(X,X^{\rm fold})\). Their arguments are different.
The original Q1 record fixes the former response pieces definitionally.
Adding an `originFold` constructor to that record changes the exit family;
it does not prove that the latter comparison was excluded upstream.

The counts in (0.32) concern a comparison graph with one fewer vertex. They
do not decrease the incoming residual: the target-defective fold is not a
permitted target-complete replacement. In particular, neither
\(X^{\rm fold}\) nor an assumed equivalence with it is appended as a successor
state. The earlier claim \(\mathcal B_{185}\Rightarrow\bot\), equation
(0.34), and its alleged closure-key producer were incorrect and are removed.
The valid degree and boundary accounting of steps 1–3 is preserved above.

<!-- RETIRED: the previous common-channel specialization is preserved below
for audit history. It is not an active theorem and is not used by the proof.

### Retired common-channel specialization

Work on the literal visible-history state retained at [185].  The distinct
response-coordinate arm has already passed through the existing continuation
routing: target defect is exit (4), a nontrivial target-complete
identification is exit (5), support enlargement is exit (6), and separated
outside continuations give the decorated handoff (7).  The inherited
no-exit-(4), no-exit-(5), no-exit-(6), and no-handoff clauses close those four
outcomes.  The only active arm considered here is therefore the equality arm
of that same finite comparison: the four selected returns have one common
actual connector and one common actual channel $C$.  No graph, support,
load, or response coordinate is reselected.

On this arm the four distinct selected loads cannot survive.  More precisely,
let

\[
                 u_1,u_2,u_3,u_4                              \tag{0.31}
\]

be the selected loads in their retained order.  There is a canonical
boundaried piece $X^{\rm fold}$, obtained inside the same selected Type A
support $X$, such that

\[
 \mathbf d_\partial(X^{\rm fold})=\mathbf d_\partial(X),
 \qquad
 \delta\bigl(X^{\rm fold}\oplus_\partial(G-X)\bigr)\ge3,
 \qquad
 |V(X^{\rm fold}\oplus_\partial(G-X))|=|V(G)|-1.             \tag{0.32}
\]

The Q1 comparison between $X^{\rm fold}$ and $X$ is either
target-defective, contradicting the retained no-exit-(4) clause, or
target-complete, contradicting the retained no-exit-(5) clause and, directly,
the minimality and target-avoidance clauses.  Hence the duplicate arm has no
member.

#### Proof

**1. Four actual nested traces.**  The presentation identities give
$s=4$ and $\delta=3$.  The selected-load list in the retained
`VisibleFourUnpeeledPackage` has length $s$ and has no repetition, so
(0.31) consists of four distinct vertices.  For each $u_i$, the package
contains its selected canonical trace

\[
                         T_i:u_i\leadsto w.
\]

The repaired graph-owned `VisibleFor` certificate says literally that the
vertex list of $T_i$ is a suffix of the vertex list of its selected channel.
On the present equality arm all four selected channels are $C$.  Suffixes
of one finite list are linearly ordered by suffix inclusion.  Since their
first vertices $u_i$ are distinct, the four suffixes are distinct.  Let
$T^-$ be the longest and $T^+$ the shortest, with respective first
vertices $u$ and $v$.  Then $T^+$ is a proper suffix of $T^-$, and
the $u$--$v$ segment $P$ of $T^-$ contains the four distinct first
vertices in their suffix order.  Consequently

\[
                         |P|\ge3.                             \tag{0.33}
\]

The canonical trace schedule is ordered first by length.  The
shortest-path argument already used in Theorem 0.3 therefore applies to
$T^-$: a chord would shorten it inside its own vertex set while preserving
the trace shape.  Thus $T^-$, and hence $P$, is induced.

Every nonterminal vertex of a trace has internal degree at least $\delta$.
The selected support has ambient surplus zero and the ambient graph has
minimum degree at least $\delta=3$; hence every support vertex has ambient
degree exactly three.  It follows that every nonterminal trace vertex has
internal degree exactly three.  In particular $u,v$, and the vertices
$a,b$ immediately following $u$ and immediately preceding $v$ on
$P$, are full interior vertices of $X$.  By (0.33), $a\ne b$.

**2. The internal fold.**  Identify $u$ and $v$ to one new interior
vertex $z$, retaining all other vertices and taking the resulting simple
graph.  The vertices $u,v$ are nonadjacent because $P$ is induced and
has length at least three.

There is at most one common neighbour of $u$ and $v$.  Indeed, two
distinct common neighbours $x,y$ would give the simple cycle

\[
                         u x v y u
\]

of length four, contradicting the retained target avoidance together with
the registered fact that length four is accepted.

If $u,v$ have no common neighbour, their six incident neighbours remain
distinct after the identification.  The new vertex $z$ has degree six,
every other vertex keeps its degree, and the quotient is simple.  In this
case this quotient is $X^{\rm fold}\oplus_\partial(G-X)$.

Suppose instead that $x$ is their unique common neighbour.  The vertex
$x$ is not on $P$: an interior occurrence on the induced $u$--$v$
path of length at least three cannot be adjacent to both ends.  Write $y$
for the third neighbour of $x$.  After identifying $u,v$, the two edges
$xu,xv$ become the single edge $xz$, so $x$ is the only vertex whose
degree has fallen, and its degree is two.  The vertices $a,b$ are distinct
full interior vertices.  Since $x$ has exactly the three neighbours
$u,v,y$, at most one of $a,b$ equals $y$.  Let $c$ be the first of
$a,b$, in the retained order, which is not $y$.  Then

\[
                   c\in X-\partial_VX,qquad xc\notin E(G).  \tag{0.34}
\]

Add the single edge $xc$ after the identification.  This is a simple edge
by (0.34).  It restores the degree of $x$ from two to three, raises the
degree of the interior vertex $c$ from three to four, and changes no other
degree.  The identified vertex $z$ has degree five.  Thus the resulting
graph has minimum degree at least three.

This repair also preserves the boundary fibre exactly.  The deleted vertices
$u,v$ and the repair endpoint $c$ are full interior vertices, hence none
is a boundary label.  The vertex $z$ is again interior.  At $x$, the
identification removes one internal incidence and the new edge $xc$ adds
one internal incidence.  Therefore the internal degree of every retained
boundary label is unchanged, including $x$ when its third edge $xy$
leaves $X$.  Every cut edge and every outside vertex is untouched.  The
identity on the old boundary labels consequently gives

\[
                  \mathbf d_\partial(X^{\rm fold})
                    =\mathbf d_\partial(X).                  \tag{0.35}
\]

In both common-neighbour cases exactly the two vertices $u,v$ are replaced
by the one vertex $z$; the optional edge repair adds no vertex.  This proves
all three assertions in (0.32).  In particular the comparison object is
strictly smaller in the first coordinate of the retained lexicographic
minimality order.

**3. Exhaustion of the response comparison.**  The fold is the graph-owned
Q1 identification of the two extreme selected response origins.  Its two
readings have the common labelled boundary and the common degree profile
(0.35).  Context universality gives exactly two outcomes.

* If a compatible context distinguishes the fold from the original reading,
  the distinguishing data are a Q1 target-defect record whose declared
  origin contains $u$ and $v$.  Both are selected unpeeled loads of the
  retained package.  It is therefore an exit-(4) witness at the current peel
  state, contradicting the no-exit-(4) conjunct of
  `Route8UnifiedVisibleHistoryStatement`.
* Otherwise the two readings are target-complete against every compatible
  context.  The identification is nontrivial because $u\ne v$, and (0.32)
  supplies its strictly smaller minimum-degree-three realization.  This is
  precisely exit (5), contradicting the inherited no-exit-(5) clause.  The
  same contradiction can be read without the exit name: minimality supplies
  an accepted cycle in
  $X^{\rm fold}\oplus_\partial(G-X)$, target-completeness transfers it to
  $X\oplus_\partial(G-X)\cong G$, and the retained selection fact says that
  $G$ has no accepted cycle.

Both exhaustive outcomes close.  Hence the cardinality of the duplicate
visible-history residual is exactly zero.  The fold is used only as the
strictly smaller comparison realization inside the closing argument; it is
not installed as a child residual.  The complete incoming `ExactLedger`,
including the peel chain, demand partition, absorbers, blockers, essential
cores, density cap, Type B allowance, and every earlier exit exclusion,
remains the first coordinate of the state throughout. \(\square\)

The exact producer repaired by this lemma is the graph-owned Q1 clause of
`lem:typeA-unpeeled-visible-routing`: its response coordinate includes the
originating canonical trace, and identification means the normalized internal
fold constructed above.  It is not the erasure of a formal trace tag.  The
target-defective outcome publishes the existing Q1 exit-(4) witness; the
target-complete outcome publishes the existing nontrivial exit-(5)
compression.  Thus the theorem adds no hypothesis and leaves no third
``duplicate coordinate'' alternative.

#### Exact exhaustion map and owning Lean payload

The visible-history comparison has the following exhaustive arms.  Each row
acts on the selected package already present in
`Route8UnifiedVisibleHistoryStatement`; it neither forms a new package nor
forgets the current peeling set.

| Exact arm of the selected four-return comparison | Existing consumer | Residual after the consumer |
|---|---|---|
| One selected anchored return has Mersenne length | `return-equivalence` | empty by target avoidance |
| Two selected anchored returns are internally disjoint and their lengths sum to a power of two | `typeA-common-port-return-cycle` | empty by target avoidance |
| Two selected traces in one packed window violate their registered relation $C_s$ | `WindowLabelCollision.hasCycleWithLength_of_labelCollision` | empty by target avoidance |
| A compatible context distinguishes two distinct response coordinates | Q1 witness in the current `Graph.ExitFour.Witness` family | empty by the retained no-exit-(4) conjunct |
| Their identification is target-complete on its present response support | `ExitFiveAt` | empty by the retained no-exit-(5) conjunct |
| Target-completeness first appears on a larger connected support | `ExitSixDelocalizes` | empty by the retained no-exit-(6) conjunct |
| The actual outside continuations remain separated | `HandoffProduced` | empty by the retained no-handoff conjunct |
| The four graph-owned coordinates have the same connector and channel | the internal fold of Theorem 0.7 | target defect closes at exit (4), and target completeness closes at exit (5) |

The last row itself has only the two common-neighbour construction arms.  In
the zero-common-neighbour arm, identification produces a simple graph and
changes the degree multiset by replacing two degree-three vertices by one
degree-six vertex.  In the one-common-neighbour arm, identification produces
one degree-two vertex $x$ and one degree-five vertex $z$; adding the uniquely
specified missing internal edge $xc$ changes their degrees to three and five
and changes the degree of $c$ from three to four.  Thus both arms produce the
same exact terminal data

\[
  \Delta |V|=-1,\qquad \delta\ge3,\qquad
  \Delta\mathbf d_\partial=0.                                \tag{0.36}
\]

There is no negative construction arm and hence no child residual.  If
$D_{185}$ denotes the finite set of duplicate visible-history packages in the
literal incoming state, Theorem 0.7 proves

\[
                         |D_{185}|=0.                         \tag{0.37}
\]

The atomic producer for this conclusion reads the existing keys
`route8UnifiedVisibleHistory`, `selection`, `replacementExclusion`, and
`cubicBaseline`, together with the already retained exit-(1)--(3) and
handoff exclusions.  Inside that producer the following data are kept in one
dependent record:

1. the `VisibleFourUnpeeledPackage`, its current `peeled`, `loadCount`, and
   `loadNodup` fields;
2. for every selected load, its scheduled `ReceiverEntryReturn`, its
   `VisibleFor` proof, and `traceSuffix_of_visibleFor`;
3. the equality or first-separation comparison of the graph-owned response
   coordinates, including the originating selected load and canonical trace;
4. the longest and shortest suffix origins $u,v$, the induced trace segment
   $P$, the full-interior proofs for $u,v,a,b$, and the no-$C_4$ proof that
   $u,v$ have at most one common neighbour;
5. the normalized folded piece, the identity of its labelled boundary, the
   equality of boundary-degree profiles, its minimum-degree-three proof, and
   the exact vertex-count equality in (0.36);
6. the `Response.contextEquivalent_or_targetDefect` result for that very
   fold, with the target-defect arm mapped to a Q1 witness supported on
   $\{u,v\}$ and the target-complete arm mapped to the nontrivial exit-(5)
   compression; and
7. in the target-complete arm, the smaller-object cycle supplied by
   `selection`, its transfer through the actual outside context, and its
   transport along the owned-decomposition reconstruction isomorphism to the
   forbidden target predicate on the original object.

The live Lean schema presently represents Q1 by two channel-support pieces
and represents exit (5) only by a single trace-basin retained-coordinate
compression.  Those types cannot state the fold just proved.  The producer
repair is therefore made at `lem:typeA-unpeeled-visible-routing`: its Q1 datum
stores the originating traces and its target-complete case stores the
graph-owned normalized fold.  This is an upstream representation repair, not
an added premise.  The repaired node-[185] consumer is the direct elimination
described in the table; it appends `False` while retaining the complete
incoming key list.

-->

<!--
RETIRED LOCALIZATION/MATCHING DRAFT.  This source block is preserved only so
the earlier work is not destroyed.  It is excluded from the rendered proof:
the live argument begins after the closing comment and uses neither a
same-support absorber nor a Q1-only matching.

### Corollary 0.6 (forced concentration on one retained support)

On the large node-[185] branch one has, as exact integer inequalities,

\[
                         p>3b,\qquad O>9b.                   \tag{0.30}
\]

More precisely, the complete incoming state canonically selects one support
\(X_\star\in\widetilde{\mathcal X}\). Put

\[
 b_\star=|\partial_E X_\star|,\quad
 N_\star=|\widetilde\Xi(X_\star)|,\quad
 p_\star=|P_4\cap\widetilde\Xi(X_\star)|,
\]

and let \(O_\star\) be the open units owned by entries of \(X_\star\). Let
\(J_\star\) be the entries of \(X_\star\) which are simultaneously peeled,
unpaid in \(\Xi_2\cup\Xi_{\rm res}\), and owners of an open unit. Then

\[
\boxed{
 2\le b_\star\le1535,\qquad
 3b_\star+1\le p_\star\le N_\star\le|X_\star|\le6142,
}                                                            \tag{0.31}
\]

\[
\boxed{
 |J_\star|\ge2b_\star+1,qquad
 O_\star=3N_\star-b_\star\ge8b_\star+3.
}                                                            \tag{0.32}
\]

Every incidence of \(\partial_E X_\star\) is occupied exactly once by the
base demand assignment or by a type-(A1) absorber. On this same support the
following four concentrations hold.

1. Some receiver owns at least three distinct entries of \(J_\star\).
2. Some actual canonical blocker incidence owns at least nine open units,
   hence units of at least three distinct unpaid entries.
3. Some incidence \(c_\star\in\partial_E X_\star\) belongs to the essential
   cores of five distinct entries
   \(\xi_1,\ldots,\xi_5\in J_\star\). For every \(i\),

   \[
   \begin{gathered}
   \xi_i\text{ occurs in the recorded peel chain},\qquad
   \xi_i\in\Xi_2\cup\Xi_{\rm res},\\
   \xi_i\text{ owns an open demand unit},\qquad
   c_\star\in\mathcal C_{\rm ess}(\xi_i),\\
   |\operatorname{priv}(\xi_i)|\le2,\qquad
   |\mathcal C_{\rm ess}(\xi_i)|\ge2,                        \tag{0.33}\\
   \xi_i\text{ has its recorded exit-(4) witness, is actually visible, and}\\
   \text{its receiver carries the canonical actual visible-four package.}
   \end{gathered}
   \]
4. Some incidence \(c_\dagger\in\partial_E X_\star\) belongs to the
   essential cores of seven distinct peeled entries. Each of the seven keeps
   its own peel-stage two-carrier certificate and exit-(4) witness, and all
   seven are visible and have the node-[185] visible-four package.

In particular, \(c_\star\) and \(c_\dagger\) are already occupied exactly
once. They are physical cut edges reused by five or seven simultaneous
response records, not five or seven units of boundary capacity.

#### Proof

The retained stub identity and orbit calculation give

\[
 \frac b r\le\tau^\ast+o(1),\qquad
 \tau^\ast=\frac{45}{4c_{13}-138},\qquad \frac h r=o(1).     \tag{0.34}
\]

Indeed
\[
 b+2e_\times(W)=15p_{13}+\sigma_W
\]
and \(\sigma_W\le\sigma(G)=o(r)\), while
\(\theta=p_{13}/n\le\theta^\ast+o(1)\) and
\(r=(1-13\theta)n\). Thus
\[
 \frac br\le\frac{15\theta^\ast}{1-13\theta^\ast}+o(1)
            =\tau^\ast+o(1).
\]

The numerical margin is already determined by the registered window
constant:

\[
 3-22\tau^\ast
  =\frac{12c_{13}-1404}{4c_{13}-138}>0,                     \tag{0.35}
\]

because \(c_{13}=118.108581006\ldots>117\). Write the two error terms in
(0.34) as \(\varepsilon_r,\eta_r\to0\). On the literal large-\(r\) arm,
eventually
\[
 22\varepsilon_r+6\eta_r<3-22\tau^\ast.
\]
Multiplication by \(r\) then gives the exact integer inequality

\[
                         3r>22b+6h.                          \tag{0.36}
\]

This is a consequence of the incoming density and near-cubic keys, not a new
rate assumption. Combining (0.36) with (0.29) yields \(p>3b\). Combining
(0.36) with (0.28) yields

\[
 O\ge3r-13b-3h>9b+3h\ge9b,
\]

which proves (0.30).

Decompose every quantity by its unique owner support:

\[
 b=\sum_Xb_X,\quad N=\sum_XN_X,\quad p=\sum_Xp_X,
 \quad O=\sum_XO_X.                                         \tag{0.37}
\]

Because \(p>3b\), some support satisfies \(p_X>3b_X\); choose the first one
and call it \(X_\star\). This is localization of the strict global excess,
not passage to a different object: the whole [185] ledger remains the first
coordinate of the state, and \(X_\star\) is a selected member of its retained
support family.

For each support \(X\), let \(J_X\) be the set of distinct entries which
occur in the peel-chain set, lie in \(\Xi_2\cup\Xi_{\rm res}\), and own at
least one open demand unit. A peeled entry outside \(J_X\) is either in
\(\Xi_3(X)\), or is unpaid and has all of its demand units absorbed. In the
second case choose its first absorbed unit. Distinct entries give distinct
demand units, so this choice injects those entries into the \(B_X\) absorbed
units of the same support. Hence

\[
                         p_X\le |J_X|+N_{3,X}+B_X.            \tag{0.38}
\]

The same no-overcount ledger used in (0.27), now partitioned by owner support,
gives

\[
                         3N_{3,X}+B_X\le b_X,
 \qquad\text{hence}\qquad N_{3,X}+B_X\le b_X.               \tag{0.39}
\]

For \(X=X_\star\), (0.38)--(0.39) and the integrality of
\(p_\star>3b_\star\) give

\[
                    |J_\star|\ge p_\star-b_\star
                                      \ge2b_\star+1.          \tag{0.40}
\]

In particular \(O_\star>0\). If one incidence of
\(\partial_E X_\star\) were unused by both the base assignment and the
type-(A1) absorber assignment, assigning it to any open unit of this same
support would enlarge the committed absorption. Maximality forbids this.
Thus, with the evident support-local notation,

\[
 a_\star+B_\star=b_\star,qquad
 3N_\star=a_\star+B_\star+O_\star,qquad
 O_\star=3N_\star-b_\star.                                 \tag{0.41}
\]

The peel set is a subset of the entry family, so
\(N_\star\ge p_\star\ge3b_\star+1\). Equation (0.41) gives
\(O_\star\ge8b_\star+3\). Ambient cubicity gives
\(b_\star=\sum_wq(w)\), with \(q(w)\in\{1,2\}\), so the number of
receivers is at most \(b_\star\). Assigning each member of \(J_\star\) to
its retained receiver and using (0.40) forces a receiver with at least three
distinct members of \(J_\star\). Assigning each of the \(O_\star\) open
units to its owner receiver forces a receiver with at least nine open units.

The manuscript's blocker producer already chooses, for each open unit, the
first incidence in its demand token and then the unique packed window at the
other endpoint. Retaining that incidence coordinate gives a map from the
\(O_\star\) units to the \(b_\star\) actual cut incidences of
\(X_\star\). Equation (0.32) forces a fibre of at least nine units. Since an
unpaid entry owns at most three demand units, that fibre has at least three
distinct owners. The current Lean blocker schema stores only the window
projection of this already constructed pair; the prose ledger retains the
full producer output for the later port.

Every member of \(J_\star\) is still an entry of the unchanged unified census, so
its essential core has at least two actual boundary incidences. Count the
incidence relation

\[
 \mathcal I_{J_\star}=\{(\xi,c):\xi\in J_\star,
                         c\in\mathcal C_{\rm ess}(\xi)\}.
\]

Then

\[
 |\mathcal I_{J_\star}|
   =\sum_{\xi\in J_\star}|\mathcal C_{\rm ess}(\xi)|
   \ge2|J_\star|\ge4b_\star+2.                             \tag{0.42}
\]

If every carrier occurred in at most four of these cores, the right side
would be at most \(4b_\star\). Thus some \(c_\star\) occurs in at least five
distinct cores; selecting the first five gives (0.33).

Apply the same count to all \(p_\star\) peeled entries. They are distinct
members of the unchanged census, so

\[
 \sum_{\xi\in P_4(X_\star)}|\mathcal C_{\rm ess}(\xi)|
   \ge2p_\star\ge6b_\star+2.                                \tag{0.43}
\]

Some incidence \(c_\dagger\) therefore belongs to at least seven peeled
cores. The `PeelChain` record gives each of those entries its two-carrier
certificate relative to the then-unpeeled family and its stage-local
exit-(4) witness; Theorems 0.3--0.4 give visibility and the actual
visible-four package on the same indices. Finally, (0.41) says every boundary
incidence of \(X_\star\), including \(c_\star\) and \(c_\dagger\), is used
once by the disjoint base/absorber assignment.

Connectedness and bridgelessness give \(b_\star\ge2\). Since
\(X_\star\) is negative and ambient-cubic,
\(4b_\star<|X_\star|\); the retained component bound
\(|X_\star|\le6142\) gives \(b_\star\le1535\). This proves (0.31) and
all four concentrations. \(\square\)

### 0.7 The exact node-[186] residual and the strict decrease

Corollary 0.6 is a structural-exhaustion transition. Its first negative arm
closes arithmetically:

\[
 \bigl(\forall X,\ p_X\le3b_X\bigr)
       \Longrightarrow p=\sum_Xp_X\le3\sum_Xb_X=3b,
                                                               \tag{0.44}
\]

contradicting (0.30). Once \(X_\star\) is selected, each remaining diffuse
arm closes on that same support:

\[
\begin{array}{rcl}
|J_\star|\le2b_\star&\Longrightarrow&p_\star\le3b_\star,\\
O_\star\le8b_\star+2&\Longrightarrow&N_\star\le p_\star-1,\\
\max_c|\{\xi\in J_\star:c\in\mathcal C_{\rm ess}(\xi)\}|\le4
 &\Longrightarrow&2|J_\star|\le4b_\star,\\
\max_c|\{\xi\in P_4(X_\star):c\in\mathcal C_{\rm ess}(\xi)\}|\le6
 &\Longrightarrow&2p_\star\le6b_\star,\\
\max_w|J_\star(w)|\le2&\Longrightarrow&|J_\star|\le2b_\star,\\
\max_c|c^{-1}_{\rm block}(c)|\le8&\Longrightarrow&O_\star\le8b_\star.
\end{array}                                                   \tag{0.45}
\]

Here the second line uses \(O_\star=3N_\star-b_\star\) and
\(p_\star\ge3b_\star+1\); the receiver line uses that there are at most
\(b_\star\) receivers. Thus every failure of the displayed node-[186]
profile returns an inequality contradicting the already selected
\(p_\star>3b_\star\). The surviving child keeps the whole [185] ledger and
appends \(X_\star\), its local ledgers, and all selected fibres. No entry,
peel, absorber, window, path, basin, carrier, or earlier key is projected
away.

The active region selected inside the unchanged state is one bounded,
connected, \(P_{13}\)-free,
ambient-cubic Type A support attached to a fixed packed window through
the canonical blocker fibre. Five distinct loads in that support are at once
two-private-carrier, actually peeled, still demand-open, actually visible,
and receiver-overloaded, while the same physical incidence on which all five
response cores depend has already been spent once. Seven peeled entries share
an occupied essential carrier, one receiver owns three peeled/open entries,
and one blocker incidence carries nine open units. These are simultaneous
coordinates of one retained support, not four independently selected hard
cases.

This also identifies exactly why the earlier one-coordinate moves leave the
residual alive. The demand ledger counts a physical incidence at most once,
whereas response essentiality, exit-(4) records, and actual visibility may
reuse it with multiplicity. The visible-first step sees actual return
ownership but permits several loads to use the same canonical channel for one
terminal trace edge. The window-signature test sees pairs of distinct
boundary incidences; units in the repeated-incidence fibre have the same
incidence and supply no such pair. A profile/deletion witness records response
dependence but is not itself an additional path of \(G\). Independent
application of the path, demand, window, or response rows therefore counts
different projections of the same records. Equations (0.17)--(0.43) are the
first account which forces those projections to meet on the same incoming
indices.

Node [186] is consequently not a generic graph problem and not a renewed
Hall, peeling, trace-ear, or visible-four test. Its literal residual is the
complete [185] ledger plus the **locally capacity-saturated repeated-carrier
support** (0.31)--(0.45). The next local move must act on the correlation
between the same support's peel order, actual visible-return packages,
receiver fibres, and occupied response carriers. Recounting any one of those
projections separately returns an upstream inequality and cannot decrease
this residual.

### 0.8 One state carrying every inherited restriction

The concentration statement is not used as a projection of the branch.  The
literal state after [186] is

\[
 \mathcal B_{186}:=
 \bigl(\mathcal B_{185};X_\star,P_\star,J_\star,
       a_\star,B_\star,O_\star,c_\star,c_\dagger,
       w_\star,c_{\rm block}\bigr),                         \tag{0.46}
\]

where \(\mathcal B_{185}\) is the complete immutable `ExactLedger`,
\(P_\star=P_4\cap\widetilde\Xi(X_\star)\), and the last four coordinates
are the canonically first witnesses of the four concentrations in Corollary
0.6.  Thus every fact in §§1--4 remains attached to every selected entry.
The following table records their simultaneous effect on this one state; it
is a cross-index of the complete A--I ledger, not a replacement for it.

| Retained block | Its exact restriction on the same state \(\mathcal B_{186}\) | Quantitative or routing effect |
|---|---|---|
| A-1--A-10 | The selected support is induced, ambient-cubic and zero-surplus; \(b_\star=\defp(X_\star)=\sum_wq(w)\), \(q(w)\in\{1,2\}\), and \(4b_\star<|X_\star|\le6142\). | \(2\le b_\star\le1535\); there are at most \(b_\star\) receivers and exactly \(b_\star\) physical completion ports. |
| B-1--B-11 | \(X_\star\) is one actual connected component of \(R\); its cut is an actual cut of bridgeless \(G\).  The base and same-support absorber assignments are disjoint and exhaust this cut. | \(a_\star+B_\star=b_\star\) and no unused incidence can absorb an open unit. |
| C-1--C-11 | \(G\) and \(X_\star\) are target-free; every retained visible return is an actual scheduled simple path through its recorded physical port.  Mersenne returns, target-sum theta pairs, and illegal shared-window pairs are absent. | Every four actual visible returns through one port pass directly to the response part of `lem:typeA-visible-entry`; exits (1)--(3) cannot consume them. |
| D-1--D-5 | Supports, receivers, ports, traces, returns, peel stages, assignments, absorbers, blockers and all selected fibres use the fixed global order. | Every selection below is a function of the incoming labelled object; no new choice of graph, support, or context is made. |
| E-1--E-7 | Proper target-complete compression and proper/global support dependence are excluded; the support has no handoff; every peel step is a recorded strict descent and remains in its original stage. | Exits (5)--(7) are unavailable for a four-return family.  A surviving response identification is therefore exit (4), and an empty-stage witness transports to any original peel stage at which its selected load is still fresh. |
| F-1--F-5 | Every selected entry keeps its basin, response algebra, essential core of size at least two, declared deletion witnesses, and at most two private essential incidences when unpaid. | The same physical cut incidence occurs in at least five \(J_\star\)-cores and another in at least seven peeled cores; these multiplicities do not create extra boundary capacity. |
| G-1--G-7 | The realized window entropy, relabelling-orbit cap, exact support partition, and all no-overcount identities remain live. | They give (0.34)--(0.36), hence \(p>3b\) and \(O>9b\), without importing the cold branch or [173]. |
| H-1--H-8 | Negative charge, visible-first capacities, the unified burden, the maximal 2/3 ledger, absorption, blockers and the full peel identity are read together. | On \(X_\star\), \(p_\star\ge3b_\star+1\), \(|J_\star|\ge2b_\star+1\), and \(O_\star=3N_\star-b_\star\ge8b_\star+3\). |
| I-1--I-4 | \(X_\star\) is \(P_{13}\)-free, has diameter at most eleven and order at most 6142; the registered finite constants and earlier exact tests remain available. | These facts bound the selected residual but are not substituted for its actual paths or response data. |
| Type B and the rest of \(R\) | The other canonical supports, every surplus unit, and the exceptional allowance \(h=o(r)\) remain in \(\mathcal B_{185}\). | They occur explicitly in (0.18), (0.20), and (0.28)--(0.36); selecting \(X_\star\) does not discard their mass. |

The remaining freedom left by these simultaneous accounts is one joint
overlap tensor: how different peeled entries reuse physical ports, actual
channels, trace segments, occupied response carriers and blocker incidences.
All degree, cut, charge, demand, peeling, path, quotient, window, entropy,
rank, and finite-size restrictions constrain that same tensor in the single
state (0.46); none is now being analysed on a detached projection.

### Theorem 0.7 (maximal matching in the actual Q1-defect graph)

The peeled entries of \(X_\star\) admit a canonical partition

\[
 P_\star=Q_\star\mathbin{\dot\cup}Z_\star                 \tag{0.47}
\]

with the following properties.

1. \(Q_\star\) is partitioned into pairs.  The two entries of every pair are
   visible through one common actual completion port and their two selected
   receiver-entry response coordinates form a target-defective Q1
   identification.  Both entries retain a Q1 exit-(4) witness valid at their
   own original peel stage.
2. At most three members of \(Z_\star\) choose any one completion port.  Hence

   \[
       |Z_\star|\le3b_\star,
       \qquad |Q_\star|=p_\star-|Z_\star|
                    \ge p_\star-3b_\star>0.                \tag{0.48}
   \]

In particular \(|Q_\star|\ge2\), and the unresolved peel-mechanism count
strictly decreases from \(p_\star\) at [186] to at most \(3b_\star\) at
[187].

#### Proof

For each \(\xi=(X_\star,w,u)\in P_\star\), Theorem 0.3 gives at least one
actual completion port through which \(u\) is visible.  Choose the first such
port \(e(\xi)=(w,h)\), and then the first scheduled visible return
\(R_\xi\) through it.  The fibres

\[
                P_e:=\{\xi\in P_\star:e(\xi)=e\}
\]

partition \(P_\star\), and the possible \(e\)'s are precisely among the
\(b_\star\) actual cut incidences of \(X_\star\).

On each fibre form the finite simple graph \(H_e\) with vertex set \(P_e\).
Join distinct entries \(\xi,\eta\) when the Q1 identification of the response
coordinates determined by \(R_\xi,R_\eta\) is target-defective.  This is a
relation on data already present in \(\mathcal B_{186}\): both returns are
actual, their response pieces have the same boundary-degree profile, and
context universality decides target-completeness versus target-defect.

We claim

\[
                         \alpha(H_e)\le3.                    \tag{0.49}
\]

Indeed, four independent vertices would give four distinct actual visible
receiver-entry returns through the same port.  Apply the already proved local
argument of `lem:typeA-visible-entry` to these four specified returns.  Exits
(1)--(3) contradict the retained target, theta, and label tests.  If every
pairwise Q1 identification were target-complete, the response argument would
give exit (5), exit (6), or the separated-continuation handoff (7); all three
are excluded in the same incoming ledger.  Therefore one pair is
target-defective of type Q1, which is an edge of \(H_e\), contrary to
independence.  This proves (0.49).  Notice that this does not repeat the
node-[93] case split: its proved four-return implication is used as the edge
certificate for a new matching move.

Choose the lexicographically first maximal matching \(M_e\) in each \(H_e\).
The vertices missed by a maximal matching are independent: an edge between
two missed vertices could be added to the matching.  By (0.49), at most three
vertices of \(P_e\) are missed.  Let \(Z_\star\) be the union of these missed
sets and let \(Q_\star=P_\star\setminus Z_\star\).  The matching endpoints
give the required pair partition, and summing over the at most \(b_\star\)
port fibres gives

\[
 p_\star=2\sum_e|M_e|+|Z_\star|,qquad
 |Z_\star|\le3b_\star.                                    \tag{0.50}
\]

Combining (0.50) with \(p_\star\ge3b_\star+1\) proves (0.48); since the
first term in (0.50) is even, \(|Q_\star|\ge2\).

It remains to check that the pair certificate belongs to the literal peel
history.  A Q1 target-defect datum declares both originating loads in its
support.  For either endpoint \(\xi\), take the same datum with \(\xi\) as
the supported load.  It is an exit-(4) witness at the empty peeling set.  At
\(\xi\)'s original `PeelChain` stage, \(\xi\) is fresh by the constructor of
the chain.  The elementary witness-transport step changes only the
``unpeeled'' proof and retains the Q1 datum, so the witness is valid at that
exact stage.  This is the prose content of the existing
`targetDefectAt_of_empty` transport.  The original witness is not replaced;
the Q1 witness is appended.  Thus every matching endpoint retains every
old fact and gains the claimed stage-compatible actual-origin certificate.
\(\square\)

### 0.10 The exact node-[187] residual and quantitative decrease

The negative arm of Theorem 0.7 is empty:

\[
 Q_\star=\varnothing
   \Longrightarrow p_\star=|Z_\star|\le3b_\star,
\]

contrary to (0.31).  On the sole survivor define

\[
 \mu_{186}:=p_\star,qquad
 \mu_{187}:=|Z_\star|.
\]

Then

\[
             \mu_{187}\le3b_\star\le p_\star-1
                         =\mu_{186}-1.                       \tag{0.51}
\]

This is a strict integer decrease on the incoming residual.  No vertex or
entry is deleted from the ledger: the endpoints in \(Q_\star\) are stored in
their disjoint Q1 pairs, with both their old peel witnesses and their new Q1
witnesses, and the unmatched set \(Z_\star\) is the strictly smaller family
whose peel mechanism has not yet been correlated with another actual return.

The literal [187] survivor is therefore much narrower than a generic bounded
Type A graph.  It is the whole state \(\mathcal B_{186}\), together with a
nonempty family of disjoint same-port Q1 target-defect pairs covering at least
\(p_\star-3b_\star\) peeled entries, and at most three unmatched peeled
entries per physical port.  Simultaneously it still has the full boundary
occupancy, the \(J_\star\), receiver, blocker, five-core and seven-core
concentrations of (0.31)--(0.45).  The matching accounts for the actual-return
overlap that [186] had left free; it neither reruns the demand packing nor
performs another peel.

-->

### Corollary 0.6 (simultaneous global concentration on the incoming indices)

On the large node-[185] branch the following are exact integer inequalities:

\[
                         p\ge3b+1,\qquad O\ge9b+1.           \tag{0.30}
\]

Let \(E:=\widetilde\Xi\) be the unchanged unified entry set, let
\(P\subseteq E\) be the set of entries occurring in the recorded peel chain,
and put

\[
\begin{aligned}
 K&:=\{\xi\in\Xi_2\mathbin{\dot\cup}\Xi_{\rm res}:
       \xi\text{ owns at least one open demand unit}\},\\
 J&:=P\cap K.
\end{aligned}                                               \tag{0.31}
\]

Then the same entries, demand units, and supply incidences satisfy

\[
 a+B\le b,\qquad O=3N-a-B\ge3N-b,\qquad
 |K|\ge3b+1,\qquad |J|\ge2b+1.                              \tag{0.32}
\]

Every \(\xi=(X,w,u)\in E\) has, by Theorem 0.3, at least one actual
completion port through which \(u\) is visible. Choose the first such port
and the first scheduled visible return through it; call them \(e(\xi)\) and
\(R_\xi\). The values of \(e\) lie in the actual boundary-incidence supply
\(\mathscr P\), where \(|\mathscr P|=b\). If an open unit \(\upsilon\) is
owned by \(\xi\), put \(e(\upsilon):=e(\xi)\). There are canonically first
incidences \(e_P,e_K,e_J,e_O\in\mathscr P\) for which

\[
\begin{array}{c|c}
\text{fibre}&\text{forced size}\\ \hline
P\cap e^{-1}(e_P)&\ge4\text{ distinct peeled entries},\\
K\cap e^{-1}(e_K)&\ge4\text{ distinct open-owner entries},\\
J\cap e^{-1}(e_J)&\ge3\text{ distinct peeled open-owner entries},\\
\{\upsilon\in\mathcal O:e(\upsilon)=e_O\}
 &\ge10\text{ open units belonging to at least four entries}.
\end{array}                                                  \tag{0.33}
\]

There are also canonically first supply incidences \(c_5,c_7\) such that

\[
\begin{aligned}
 |\{\xi\in J:c_5\in\mathcal C_{\rm ess}(\xi)\}|&\ge5,\\
 |\{\xi\in P:c_7\in\mathcal C_{\rm ess}(\xi)\}|&\ge7.
\end{aligned}                                                \tag{0.34}
\]

All entries in (0.33)--(0.34) retain their receivers, traces, basins,
essential cores, demand classes and units, absorber/open status, blocker
windows, original peel stages and witnesses, and the actual visible returns
chosen above. The selected incidences may coincide or may belong to different
Type A supports; no coincidence is assumed. Each port fibre itself lies at
one receiver of one connected ambient-cubic, \(P_{13}\)-free support of order
at most \(6142\).

#### Proof

The retained stub identity and orbit calculation give

\[
 \frac b r\le\tau^\ast+o(1),\qquad
 \tau^\ast=\frac{45}{4c_{13}-138},\qquad \frac h r=o(1).     \tag{0.35}
\]

Indeed, \(b+2e_\times(W)=15p_{13}+\sigma_W\),
\(\sigma_W\le\sigma(G)=o(r)\),
\(\theta=p_{13}/n\le\theta^\ast+o(1)\), and
\(r=(1-13\theta)n\). The registered constant gives the positive margin

\[
 3-22\tau^\ast
  =\frac{12c_{13}-1404}{4c_{13}-138}>0                     \tag{0.36}
\]

because \(c_{13}=118.108581006\ldots>117\). On the literal large-\(r\)
arm the two incoming error terms are eventually smaller than this fixed
margin, and multiplication by \(r\) gives

\[
                         3r>22b+6h.                          \tag{0.37}
\]

Combining (0.37) with (0.29) gives \(p>3b\), and combining it with
(0.28) gives \(O>9b+3h\ge9b\). Integrality gives (0.30).

The base assignment uses \(a\) distinct supply incidences and the type-(A1)
absorption uses \(B\) further distinct incidences, so \(a+B\le b\).  The
exact demand-unit partition gives
\(O=3N-a-B\), and hence \(O\ge3N-b\).  More is true supportwise.  If
\(O_X>0\) and an incidence of \(\delta_G(X)\) were unused by both the base
assignment and the type-(A1) absorber assignment, assigning it to the first
open unit owned by an entry of \(X\) would preserve the retained
same-support clause (0.16a), injectivity, and disjointness while enlarging the
committed absorption.  Maximality forbids this.  Therefore
\[
 O_X>0\quad\Longrightarrow\quad a_X+B_X=b_X,
 \qquad O_X=3N_X-b_X.                                     \tag{0.32a}
\]
No incidence of another support is used in this argument.

Every entry of \(K\) owns either one or three demand units, and every open
unit has one owner. Hence \(O\le3|K|\), so (0.30) yields
\(|K|\ge3b+1\). A peeled entry outside \(J\) is either in \(\Xi_3\), or is
unpaid and owns no open unit. In the second case all of its demand units are
absorbed; choosing its first demand unit injects such entries into the
\(B\) absorbed units. Consequently

\[
                 p\le |J|+N_3+B.                            \tag{0.38}
\]

Because \(3N_3+B\le a+B=b\), one has \(N_3+B\le b\). Thus
\(|J|\ge p-b\ge2b+1\), proving the remaining part of (0.32).

The maps \(e:E\to\mathscr P\) and
\(e:\mathcal O\to\mathscr P\) use only actual incoming objects. Applying
the pigeonhole principle to (0.30) and (0.32) gives the four fibre sizes in
(0.33). An entry owns at most three open units, so a ten-unit fibre has at
least four distinct owners. A physical completion port has one endpoint in
one receiver of one canonical support, so every listed fibre is automatically
local even though the count producing it was global.

Finally, every entry core has at least two incidences and is contained in the
same global supply of size \(b\). Therefore

\[
 \sum_{\xi\in J}|\mathcal C_{\rm ess}(\xi)|
      \ge2|J|\ge4b+2,
 \qquad
 \sum_{\xi\in P}|\mathcal C_{\rm ess}(\xi)|
      \ge2p\ge6b+2.                                        \tag{0.39}
\]

If every incidence occurred in at most four of the first family of cores,
its incidence count would be at most \(4b\); if every incidence occurred in
at most six of the second, that count would be at most \(6b\). Both
conclusions contradict (0.39), proving (0.34). \(\square\)

### 0.7 The exact node-[186] residual

Corollary 0.6 creates no hypothetical child. It appends to the full [185]
state the canonical fibres and incidences forced by the incoming equalities.
Every diffuse alternative is arithmetically empty:

\[
\begin{array}{rcl}
\max_e|P\cap e^{-1}(e)|\le3&\Longrightarrow&p\le3b,\\
\max_e|K\cap e^{-1}(e)|\le3&\Longrightarrow&|K|\le3b,\\
\max_e|J\cap e^{-1}(e)|\le2&\Longrightarrow&|J|\le2b,\\
\max_e|\{\upsilon\in\mathcal O:e(\upsilon)=e\}|\le9
 &\Longrightarrow&O\le9b,\\
\max_c|\{\xi\in J:c\in\mathcal C_{\rm ess}(\xi)\}|\le4
 &\Longrightarrow&2|J|\le4b,\\
\max_c|\{\xi\in P:c\in\mathcal C_{\rm ess}(\xi)\}|\le6
 &\Longrightarrow&2p\le6b.
\end{array}                                                  \tag{0.40}
\]

Thus the literal residual is not one support with a locally maximal absorber;
that would add a property absent from the incoming ledger. It is the complete
global state together with several forced local fibres of that state. What
has evaded the upstream moves is cross-index reuse: a supply incidence is
spent once by the demand/absorption ledger but may occur in many response
cores, and many entries may choose the same actual port while their
target-defect witnesses use different Q-clauses. Demand, peeling, visibility,
and essentiality counted four projections of this tensor; (0.30)--(0.40) put
them on the same entry indices without asserting that the canonically
selected high fibres coincide.

### 0.8 One state carrying every inherited restriction

The literal state after [186] is

\[
 \mathcal B_{186}:=
 \bigl(\mathcal B_{185};P,K,J,e(\cdot),R_{(\cdot)},
       e_P,e_K,e_J,e_O,c_5,c_7\bigr),                       \tag{0.41}
\]

where \(\mathcal B_{185}\) is the complete immutable `ExactLedger` and all
new coordinates are the canonical objects proved in Corollary 0.6. The
following is a simultaneous account, not a projection.

| Retained block | Restriction on the same state \(\mathcal B_{186}\) | Exact effect |
|---|---|---|
| A, B | Every port fibre is contained in one actual connected ambient-cubic Type A support; all supply incidences form one global set of size \(b\). Base and absorber incidences are globally disjoint and exhaustive. | \(a+B=b\). Cross-support absorber reuse is allowed and already paid; no local occupancy equality is used. |
| C | Each entry has its own selected actual scheduled return through \(e(\xi)\); all Mersenne, target-sum, and illegal-window exits remain absent. | Four entries in one fibre give four actual visible returns at one physical port. |
| D | Entry, support, port, return, fibre, peel stage, demand unit, core, and all witnesses use the fixed orders. | Every supportwise excess and every later leaf/path suppression is selected canonically on the incoming object. |
| E | Exits (5)--(7) are absent and every recorded peel remains a strict earlier descent. | Proposition 0.7 excludes only the literal Q2 clause from an original peel witness; Q1, Q3, Q4 and Q5 records remain attached. |
| F | Each core has size at least two; every unpaid entry has at most two private carriers; all deletion witnesses remain attached. | The five-core and seven-core fibres (0.34) coexist with the port fibres. |
| G, H | Equations (0.17)--(0.29), the orbit cap, peel identity, maximal demand partition, global maximal absorption, and blocker partition all remain live. | Equations (0.30)--(0.40) force peeled, open-owner, peeled-open, open-unit, and repeated-core concentrations simultaneously. |
| I | Every support met by a selected fibre is \(P_{13}\)-free, has diameter at most eleven, and has at most \(6142\) vertices. | Each local fibre is bounded, but no finite enumeration or generic graph statement is introduced. |
| Rest of the ledger | Every other support, all Type B exceptional mass, all window states, and all prior exact tests remain in \(\mathcal B_{185}\). | Nothing outside a selected fibre is discarded or reclassified. |

The remaining unmeasured coordinate is now precise: the global inequalities
do not force their high fibres to belong to one support.  The maximally
adversarial state may put its deficit excess, peeled excess, open-owner
excess, peeled-open excess and open-unit excess on different supports.
Theorem 0.8 therefore localizes each currency separately and then uses the
deficit-heavy support, which independently carries a linear entry excess, as
the one support on which all topological and entry data can be measured
together.

### Proposition 0.7 (the Q2 peel clause is absent)

No original `PeelChain` witness of an entry \(\xi\in P\) is of type Q2.
Hence its retained clause lies in
\(\{\mathrm{Q1},\mathrm{Q3},\mathrm{Q4},\mathrm{Q5}\}\).

#### Proof

Let the peel step for \(\xi=(X,w,u)\) occur at the recorded stage
\(P_{<\xi}\). If its witness were Q2, the `supports` field and the third
conjunct of `SilentUnpeeledExcessAt` would give

\[
 u\in\operatorname{unpeeledExcess}(X,w;P_{<\xi})
 \subseteq
 \operatorname{unpeeledLoads}(X,w;P_{<\xi})
       \setminus\operatorname{visibleLoads}(X,w).            \tag{0.42}
\]

But \(\xi\) is a member of the unchanged unified entry set, so Theorem 0.3
gives \(u\in\operatorname{visibleLoads}(X,w)\). This contradicts (0.42).
The five constructors of `CanonicalMember` are exhaustive, so only Q1, Q3,
Q4, and Q5 remain. This consequence is appended to each existing peel record;
it neither replaces that witness nor creates a child residual. \(\square\)

<!--
RETIRED STAR-KERNEL DRAFT.  The graph-theoretic domination assertion below
may be retained as an overlap certificate, but assigning a leaf to a Q1/Q4
hub does not discharge the leaf's peel, demand, carrier, or blocker
obligations.  Consequently the displayed change from N to |Z| is not a
residual decrease.  This block is excluded from the proof; the exact joint
account begins after the closing comment.

### Theorem 0.8 (actual-origin star-kernel exhaustion)

For each physical port \(e\in\mathscr P\), put

\[
                         E_e:=\{\xi\in E:e(\xi)=e\}.          \tag{0.43}
\]

There are canonical disjoint sets

\[
 E=Z\mathbin{\dot\cup}Q,
 \qquad Z=\mathop{\dot\bigcup}_{e\in\mathscr P}Z_e,
 \qquad Q=E\setminus Z,                                    \tag{0.44}
\]

and a map \(\rho:Q\to Z\) with the following properties.

1. \(Z_e\subseteq E_e\) and \(|Z_e|\le3\) for every port.
2. For every \(\xi\in Q\), the entries \(\xi\) and \(\rho(\xi)\) choose
   the same physical port. Attached to that ordered pair is a canonically
   selected visible-four package made of actual returns and an actual-origin
   exit-(4) record of type Q1 or Q4. In the Q1 case the pair is the two
   response-coordinate origins. In the Q4 case it is the distinguished pair
   of separated rooted germs and its switch support. The compatible context
   certifying target defect remains certificate data and is not treated as a
   path in \(G\).
3. Every entry keeps all of its old data. If \(\xi\in P\cap Q\), the new
   Q1/Q4 datum also gives an empty-stage witness for \(\xi\), which transports
   to its original fresh peel stage; its original non-Q2 witness from
   Proposition 0.7 remains attached as a separate coordinate.

Quantitatively,

\[
 |Z|\le3b<N,\qquad |Q|=N-|Z|\ge N-3b\ge p-3b\ge1,           \tag{0.45}
\]

and

\[
                  |P\cap Q|\ge p-|Z|\ge p-3b\ge1.           \tag{0.46}
\]

#### Proof

On each finite fibre \(E_e\), form a simple graph \(H_e\). Distinct entries
\(\xi,\eta\) are adjacent when there is a four-element set
\(A\subseteq E_e\) and the visible-routing construction applied to the four
already selected actual returns \(\{R_\zeta:\zeta\in A\}\) produces either

- a Q1 record whose two actual response origins are \(\xi,\eta\), or
- a Q4 record whose distinguished actual left/right origins are
  \(\xi,\eta\).

The four inputs have distinct loads because an entry of a fixed support and
receiver is indexed by its load. They are all unpeeled at the empty stage.
The proof of `lem:typeA-unpeeled-visible-routing` uses only these four actual
returns. Exits (1)--(3) contradict the retained return, theta, and window
tests; exits (5)--(6) contradict uncompressibility and support-dependence
exclusion; exit (7) contradicts the retained no-handoff arm. The visible
routing proof produces Q1 in its response-identification subcase and Q4 in
its continuation-switch subcase; Q2, Q3, and Q5 belong to the silent,
trace-local, and carrier-deletion constructions and are not outputs of this
four-return move. In the Q4 subcase its continuation family, including its
distinguished left/right origins, is contained in the chosen four loads.
Consequently every four-element subset of \(E_e\) contains an edge of
\(H_e\), and therefore

\[
                              \alpha(H_e)\le3.               \tag{0.47}
\]

Choose the lexicographically first inclusion-maximal independent set
\(Z_e\) of \(H_e\). Equation (0.47) gives \(|Z_e|\le3\). Maximality gives
the textbook domination conclusion: every vertex of \(E_e\setminus Z_e\)
has a neighbour in \(Z_e\). For each such vertex choose its first neighbour
and then the first edge certificate; these choices define \(\rho\), the
Q1/Q4 colour, the four actual origins, all selected returns, and the relevant
response or switch record. This permits every edge in the adversarial case
to share a hub; no disjoint-pair assertion is made.

Summing \(|Z_e|\le3\) over the \(b\) physical ports proves
\(|Z|\le3b\). Since \(P\subseteq E\) and (0.30) gives \(p>3b\), one has
\(N\ge p>3b\), proving (0.45). Finally

\[
 |P\cap Q|=p-|P\cap Z|\ge p-|Z|\ge p-3b\ge1,
\]

which proves (0.46). For a peeled leaf, the edge record supports that leaf at
the empty stage. `PeelChain.cons` says the entry is fresh at its original
stage, and `targetDefectAt_of_empty` changes only that freshness proof. Thus
the new witness is stage-compatible while all old coordinates are retained.
\(\square\)

### 0.9 The exact node-[187] residual and quantitative decrease

Define the unresolved actual-origin-overlap measure by

\[
                         \mu_{186}:=N,\qquad \mu_{187}:=|Z|.
\]

Then Theorem 0.8 gives the literal strict decrease

\[
                    \mu_{187}\le3b\le N-1=\mu_{186}-1.      \tag{0.48}
\]

No entry is removed. The \(Q\)-entries are stored as leaves of a canonical
Q1/Q4-coloured star forest, with their hub, physical port, four-return
package, actual origins, and every inherited coordinate. Only the kernel
\(Z\)—at most three entries per port—still lacks an assigned actual-origin
parent. This is progress mechanism (1) of structural exhaustion: a strict
natural-valued decrease on the literal incoming residual.

The rest of the simultaneous accounting survives the decrease exactly. Put
\(P_Q=P\cap Q\), \(P_Z=P\cap Z\), and similarly for \(K,J\). Let
\(q_1,q_4\) be the numbers of leaves whose selected edge certificates have
the two colours. Then

\[
\begin{gathered}
 P=P_Q\mathbin{\dot\cup}P_Z,
 \quad K=K_Q\mathbin{\dot\cup}K_Z,
 \quad J=J_Q\mathbin{\dot\cup}J_Z,\\
 |P_Q|\ge p-3b\ge1,
 \qquad |K_Q|\ge |K|-3b\ge1,
 \qquad q_1+q_4=|Q|.                                      \tag{0.49}
\end{gathered}
\]

If \(O_Z\) and \(O_Q\) count open units by whether their owner lies in
\(Z\) or \(Q\), then each kernel entry owns at most three units, whence

\[
 O=O_Q+O_Z,\qquad O_Z\le3|Z|\le9b,\qquad O_Q\ge O-3|Z|\ge1. \tag{0.50}
\]

Thus at least one star leaf is peeled and at least one star leaf owns an open
unit. The method does not assume they are the same entry. Their exact
intersection is exhausted without a nonshrinking split as follows. If
\(J_Q\ne\varnothing\), one leaf simultaneously carries a peel stage, an open
unit, and an actual-origin Q1/Q4 star edge. If \(J_Q=\varnothing\), then
\(J\subseteq Z\). With

\[
 t_3:=|\{e\in\mathscr P:|J\cap Z_e|=3\}|,
\]

the bound \(|J\cap Z_e|\le3\) gives

\[
 |J|=\sum_e|J\cap Z_e|\le2b+t_3,
 \qquad t_3\ge |J|-2b\ge1.                                \tag{0.51}
\]

So the adverse no-intersection case is not left unnamed: it is the exact
kernel-saturation profile in which at least one physical port contains three
peeled open-owner hubs.

The repeated-core facts are retained with the same precision. Let
\(C_5\subseteq J\) and \(C_7\subseteq P\) be the selected five and seven
entries from (0.34). If either set meets \(Q\), the corresponding shared
carrier is now attached to an actual-origin star edge. Otherwise
\(C_5\subseteq Z\) occupies at least two distinct port kernels, and
\(C_7\subseteq Z\) occupies at least three, because every \(Z_e\) has at
most three entries. The receiver fibre, ten-unit fibre, blocker-window map,
base/absorber occupancy, core deletion witnesses, and all other upstream data
remain attached entry by entry regardless of which forced outcome occurs.

This is the maximally adversarial accounting missing at [186]. A matching
would incorrectly require disjoint response pairs. The star-kernel move
allows every Q1/Q4 record at a port to reuse the same one, two, or three hubs,
charges those hubs once to \(Z_e\), and assigns every other entry to an actual
record. The residual has therefore become the bounded hub tensor
\(\mathcal B_{187}=(\mathcal B_{186};Z,Q,\rho,\text{colours and certificates})\)
with the strict bound (0.48), rather than a renamed copy of the incoming
entry family.

-->

### Theorem 0.8 (simultaneous supportwise localization)

Let \(\mathscr A=\widetilde{\mathcal X}\) be the retained family of
negative, zero-surplus, no-handoff Type A supports.  For \(X\in\mathscr A\)
write

\[
\begin{aligned}
 b_X&:=|\delta_G(X)|=\defp(X),
 &D_X&:=|X|-4b_X,\\
 E_X&:=\{\xi\in E:\operatorname{supp}(\xi)=X\},
 &N_X&:=|E_X|,\\
 P_X&:=P\cap E_X,
 &K_X&:=K\cap E_X,\\
 J_X&:=J\cap E_X,
 &O_X&:=|\{\upsilon\in\mathcal O:
               \operatorname{supp}(\operatorname{owner}\upsilon)=X\}|.
\end{aligned}                                               \tag{0.43}
\]

Put \(b_{\mathscr A}=\sum_{X\in\mathscr A}b_X\).  Then

\[
\begin{gathered}
 b_{\mathscr A}\le b,
 \qquad D=\sum_XD_X,\quad N=\sum_XN_X,\quad
 p=\sum_X|P_X|,\\
 |K|=\sum_X|K_X|,\quad |J|=\sum_X|J_X|,\quad
 O=\sum_XO_X.                                               \tag{0.44}
\end{gathered}
\]

The complete node-[186] state canonically selects supports

\[
 X_D,X_P,X_K,X_J,X_O\in\mathscr A                         \tag{0.45}
\]

(not asserted to be distinct or equal) such that

\[
\begin{array}{rclcrcl}
 D_{X_D}&\ge&3b_{X_D}+1,
 &\qquad&N_{X_D}&\ge&3b_{X_D}+1,\\
 |P_{X_P}|&\ge&3b_{X_P}+1,
 &&|K_{X_K}|&\ge&3b_{X_K}+1,\\
 |J_{X_J}|&\ge&2b_{X_J}+1,
 &&O_{X_O}&\ge&9b_{X_O}+1.                                 \tag{0.46}
\end{array}
\]

Moreover, the following local fibres are present simultaneously in the same
global state.

1. In \(X_D\), some physical port is chosen by at least four entries of
   \(E_{X_D}\), and some cut incidence lies in at least seven of their
   essential cores.
2. In \(X_P\), some physical port is chosen by at least four peeled entries,
   and some cut incidence lies in the essential cores of at least seven
   peeled entries.
3. In \(X_K\), some physical port is chosen by at least four open-owner
   entries, and some cut incidence lies in the essential cores of at least
   seven open-owner entries.
4. In \(X_J\), some physical port is chosen by at least three peeled
   open-owner entries, and some cut incidence lies in the essential cores of
   at least five such entries.
5. In \(X_O\), some physical port carries at least ten open units, belonging
   to at least four distinct owners.  The support also has at least
   \(3b_{X_O}+1\) distinct open-owner entries.

Every entry in these fibres keeps its actual visible return, visible-four
package, receiver, trace, basin, demand class and units, absorption/open
status, blocker window, core and deletion witnesses, and, when applicable,
its original peel stage and witness.  This statement makes no intersection
claim between canonically selected high fibres.

#### Proof

The supports in \(\mathscr A\) are distinct components of the retained
remainder decomposition.  Their entry and demand-owner families are
therefore disjoint.  Their cut incidences have distinct inside endpoints, so
their union is contained in the global supply.  This proves (0.44).

The exact `StageAccounting` coordinate gives

\[
                              p\le D.                        \tag{0.47}
\]

Corollary 0.6 gives

\[
 p\ge3b+1,qquad |K|\ge3b+1,qquad
 |J|\ge2b+1,qquad O\ge9b+1.                               \tag{0.48}
\]

Consequently

\[
 D\ge3b_{\mathscr A}+1,\quad
 p\ge3b_{\mathscr A}+1,\quad
 |K|\ge3b_{\mathscr A}+1,\quad
 |J|\ge2b_{\mathscr A}+1,\quad
 O\ge9b_{\mathscr A}+1.                                  \tag{0.49}
\]

If the first inequality in (0.46) failed at every support, summing would give
\(D\le3b_{\mathscr A}\), contradicting (0.49).  The same argument, with
coefficients \(3,3,2,9\), selects \(X_P,X_K,X_J,X_O\).  The supportwise
identity (0.24) says \(N_X=D_X+U_X\) with \(U_X\ge0\), so the selected
\(X_D\) also satisfies the second inequality in the first line of (0.46).
All choices are made first in the fixed support order.

Every member of \(\mathscr A\) is a nonempty proper connected shore of
bridgeless \(G\); hence \(b_X\ge2\).  It has exactly \(b_X\) physical
completion ports.  Assigning each entry to its already selected port gives
the port bounds by the pigeonhole principle.  Every entry has an essential
core of size at least two contained in those same \(b_X\) incidences.  Thus
the core-incidence totals in \(X_D,X_P,X_K,X_J\) are respectively at least

\[
 6b_{X_D}+2,\quad6b_{X_P}+2,\quad
 6b_{X_K}+2,\quad4b_{X_J}+2.                              \tag{0.50}
\]

If all carrier multiplicities were at most \(6,6,6,4\), respectively, these
totals would be at most
\(6b_{X_D},6b_{X_P},6b_{X_K},4b_{X_J}\), a contradiction.  This gives the
four core fibres.  Finally an entry owns at most three open units.  Hence
\(O_{X_O}\ge9b_{X_O}+1\) forces at least \(3b_{X_O}+1\) owners, and ten
units at one of its \(b_{X_O}\) ports force at least four owners.  No
absorber has been localized in this proof; (0.32) remains the exact global
occupancy statement. \(\square\)

### Theorem 0.9 (degree-chain exhaustion on the deficit-heavy support)

Write \(X=X_D\), \(b_0=b_X\), and

\[
 n_i:=|\{v\in X:d_X(v)=i\}|.
\]

The incoming residual forces

\[
 n_0=0,qquad b_0=n_2+2n_1,qquad
 D_X=n_3-3n_2-7n_1,qquad
 n_3\ge6n_2+13n_1+1.                                     \tag{0.51}
\]

In particular

\[
 |X|\ge7b_0+2,qquad b_0\le877,qquad
 \beta(X)=\frac{|X|-b_0}{2}+1\ge3b_0+2.                  \tag{0.52}
\]

There is a canonical exact encoding of this same support by the following
data.

- Repeatedly delete the first internal leaf, retaining the deleted vertex,
  its two old boundary edges and its unique edge toward the survivor.  Let
  \(L\) be the number deleted and let \(Y\) be the terminal connected induced
  shore.
- Suppress every maximal internal-degree-two path of \(Y\), retaining its
  ordered vertex list and its positive edge-length.  The resulting connected
  cubic weighted multigraph is denoted \(\Gamma\); loops and parallel edges
  are permitted only in this encoding.
- Let \(s\) be the number of edges of \(\Gamma\) having weight greater than
  one, and let \(U\) be the actual simple graph on \(V(\Gamma)\) consisting
  of the weight-one edges.  Equivalently,
  \(U=G[V(\Gamma)]\).

These data satisfy the exact identities and inequalities

\[
\begin{gathered}
 |Y|=|X|-L,qquad b(Y)=b_0-L\ge2,\qquad
 \delta(Y)\ge2,                                           \tag{0.53}\\
 |V(\Gamma)|=|Y|-b(Y)=|X|-b_0\ge6b_0+2,                  \tag{0.54}\\
 \beta(\Gamma)=\beta(X)=\frac{|V(\Gamma)|}{2}+1
                                  \ge3b_0+2,              \tag{0.55}\\
 \sum_{e\in E(\Gamma)}(\ell(e)-1)=b(Y),qquad
 1\le s\le b(Y)\le b_0,                                   \tag{0.56}\\
 n_1\le L\le b_0-2,\qquad
 2\le b(Y)\le n_1+n_2,\qquad s\le n_1+n_2,                \tag{0.56a}\\
 c(U)\le s+1,qquad
 \beta(U)\ge\beta(\Gamma)-s\ge2b_0+2,                  \tag{0.57}\\
 |\{v\in V(U):d_U(v)=3\}|\ge|V(\Gamma)|-2s
                                      \ge4b_0+2.          \tag{0.58}
\end{gathered}
\]

Every component of \(U\) contains an endpoint incidence of a weight-greater-
than-one edge.  The graph \(U\) is induced in the original support, is
\(P_{13}\)-free and target-free, and has empty internal \(3\)-core.
The reconstruction fibre \(X\setminus V(\Gamma)\) has exactly \(b_0\)
vertices and contains every receiver and every inside endpoint of an edge in
\(\delta_G(X)\).  Distinct cut edges are not asserted to have distinct
inside endpoints.  More precisely it is the disjoint union of all \(n_2\)
one-port receivers, all \(n_1\) two-port receivers, and exactly \(n_1\)
vertices which had internal degree three in \(X\):

\[
 |X\setminus V(\Gamma)|=n_2+2n_1=b_0,\qquad
 |\{v\in X\setminus V(\Gamma):d_X(v)=3\}|=n_1.             \tag{0.54a}
\]

At least \(2b_0+1\) entries of \(E_X\) have their load vertex in
\(V(\Gamma)\).  Let \(M\) be the canonical set of all such marked entries.
On these same marked vertices:

\[
 |M|\ge2b_0+1,                                             \tag{0.59}
\]

some physical port is chosen by at least three members of \(M\), and some
cut incidence belongs to the essential cores of at least five members of
\(M\).  Finally, two distinct marked entries have canonical shortest paths
in \(U\), each of length at most eleven, to the same oriented endpoint of
the same weight-greater-than-one edge of \(\Gamma\).  Internal vertices of
each path have degree three in \(U\).  The paths are not asserted to be
disjoint.  In addition, two (possibly different) marked entries have actual
canonical trace prefixes in \(U\) which leave the kernel through the same
oriented endpoint incidence, and hence through the same first edge of the
same suppressed path.  The two loads lie in the same component of the
original internal-degree-three subgraph and therefore have the same
canonical receiver.  These trace prefixes are induced and have length at
most eleven; no disjointness or coincidence with the port/core fibres is
asserted.

If \(m_t\) denotes the number of marked canonical traces whose first
kernel-exit is the oriented weighted-edge incidence \(t\), then

\[
 \sum_t\max(m_t-1,0)
    \ge |M|-2s\ge2n_1+1.                                  \tag{0.59a}
\]

#### Proof

The first three identities in (0.51) are the ambient-cubic degree count and
(0.24).  Combining \(D_X\ge3b_0+1\) with
\(b_0=n_2+2n_1\) gives the last inequality.  Hence
\(|X|\ge7b_0+1\).  The ambient degree sum gives
\(b_0\equiv|X|\pmod2\), so the strict difference is even and
\(|X|\ge7b_0+2\).  Since \(|X|\le6142\), this gives \(b_0\le877\).
Finally

\[
 2|E(X)|=3|X|-b_0,qquad
 \beta(X)=|E(X)|-|X|+1=\frac{|X|-b_0}{2}+1,
\]

which proves (0.52).

If \(v\) is an internal leaf of the current shore \(S\), deleting it removes
its two old cut edges and makes its unique internal edge a new cut edge.
Thus

\[
 |S-v|=|S|-1,qquad b(S-v)=b(S)-1,qquad
 (|S-v|-7b(S-v))=(|S|-7b(S))+6.                            \tag{0.60}
\]

The new shore is connected and induced.  It is still a nonempty proper shore
of bridgeless \(G\), so its cut has size at least two.  The finite canonical
deletion therefore terminates at the stated \(Y\), proving (0.53).  Since
all vertices of \(Y\) have ambient degree three and internal degree two or
three, the number of its degree-two vertices is exactly \(b(Y)\).  The
positive quantity \(|Y|-7b(Y)\) excludes the case that \(Y\) is a cycle.
Consequently maximal degree-two suppression produces the connected cubic
weighted multigraph \(\Gamma\).

The deleted leaf set has size \(L\), and the suppressed path interiors have
total size \(b(Y)=b_0-L\).  Exactly \(b_0\) original vertices therefore lie
outside \(V(\Gamma)\), giving (0.54).  Leaf deletion and degree-two
suppression preserve cycle rank, and the cubic handshake identity in
\(\Gamma\) gives (0.55).  Each weighted edge consumes exactly
\(\ell(e)-1\) suppressed vertices.  This proves (0.56).  Every one of the
\(n_1\) original internal leaves is removed by the leaf-stripping process,
so \(L\ge n_1\); and \(b(Y)\ge2\) gives \(L\le b_0-2\).  Using
\(b_0=n_2+2n_1\) now gives
\[
 b(Y)=b_0-L\le n_2+n_1.
\]
Together with \(s\le b(Y)\), this proves (0.56a).

Deleting the \(s\) weighted edges from connected \(\Gamma\) leaves \(U\),
so it creates at most \(s+1\) components and destroys at most \(s\)
independent cycles.  This proves (0.57).  The deletion removes exactly
\(2s\) cubic incidences, counting the two incidences of a loop separately.
Thus at most \(2s\) vertices of \(U\) can have degree below three, proving
(0.58).  If a component of \(U\) met no deleted-edge endpoint, all three
incidences of each of its vertices would remain inside that component.  It
would be a nonempty induced subgraph of minimum degree three, contradicting
the retained empty-internal-\(3\)-core fact.  The remaining inheritance
claims follow because \(U\) is the induced graph on an actual vertex subset
of \(X\).  The weights, rather than the unweighted multigraph, record cycle
lengths; no cycle of \(\Gamma\) is treated as a cycle of \(G\) without
summing its weights.  A kernel vertex has degree three in \(Y\), and hence
degree three already in \(X\); it is neither a receiver nor the inside
endpoint of a cut edge of \(X\).  This proves the assertion about the
\(b_0\)-vertex reconstruction fibre.  All \(n_1+n_2\) deficient vertices
therefore lie in that fibre.  Its remaining cardinality is
\[
 b_0-(n_1+n_2)=(n_2+2n_1)-(n_1+n_2)=n_1,
\]
which proves (0.54a).

Entry loads are distinct internal-degree-three vertices, and
\(N_X\ge3b_0+1\).  Since exactly \(b_0\) vertices of \(X\) lie outside the
kernel vertex set, at least \(N_X-b_0\ge2b_0+1\) entry loads survive there.
This proves (0.59).  Their selected ports take only \(b_0\) values, forcing a
three-entry port fibre.  Their essential cores contain at least
\(2|M|\ge4b_0+2\) incidences counted with multiplicity, so one of the
\(b_0\) cut incidences occurs at least five times.

There are exactly \(2s\le2b_0\) oriented endpoint incidences of weighted
edges.  Every component of \(U\) contains at least one.  Assign each member
of \(M\) to the first closest such incidence in its component and retain the
first shortest path.  Since \(|M|>2s\), two distinct marks receive the same
incidence.  A shortest path of twelve edges would be an induced
\(P_{13}\) in \(G\), so both selected paths have length at most eleven.
Minimality of the endpoint distance makes every internal path vertex
incident with no weighted edge and hence of degree three in \(U\).  All
selected entries and all of their inherited records remain attached.

Every vertex of \(\Gamma\) has degree three already in \(Y\), and therefore
also has internal degree three in the original support \(X\).  A receiver has
internal degree at most two, so the receiver of every entry in \(M\) lies
outside \(V(\Gamma)\).  Follow its already selected canonical trace from its
marked load and take the first edge leaving \(V(\Gamma)\).  No kernel vertex
is adjacent to the deleted leaf forest, since such an edge would lower its
degree in \(Y\).  The first leaving edge is therefore precisely the first
edge at one oriented endpoint of a weight-greater-than-one suppressed path.
Its preceding trace prefix lies in the actual induced graph \(U\).

This assigns the \(2b_0+1\) or more marked entries to the same set of
\(2s\le2b_0\) oriented incidences.  Two distinct entries therefore receive
the same incidence and use the same first leaving edge.  Theorem 0.3 proved
that every selected trace is induced.  Since \(X\) is \(P_{13}\)-free, the
trace, and hence its prefix, has at most eleven edges.  This proves the final
trace assertion without replacing either trace by a profile event.  Both
prefixes lie in one component of \(U\), hence in one component of
\(X[\{v:d_X(v)=3\}]\).  The fixed receiver order assigns the same canonical
receiver to all loads in that component, proving the receiver assertion.
There are at most \(2s\) nonempty fibres of the trace-exit map, and hence
\[
 \sum_t\max(m_t-1,0)
   =|M|-|\{t:m_t>0\}|
   \ge |M|-2s.
\]
Equations (0.59) and (0.56a), together with
\(b_0=n_2+2n_1\), give
\[
 |M|-2s\ge2(n_2+2n_1)+1-2(n_1+n_2)=2n_1+1,
\]
which proves (0.59a).
\(\square\)

### 0.10 Exact residual, exact decrease, and the maximally adversarial shape

The literal post-[186] state is

\[
 \mathcal B_{187}:=
 \bigl(\mathcal B_{186};X_D,X_P,X_K,X_J,X_O;
       Y,\Gamma,\ell,U,M;\text{all selected fibres and reconstruction data}
 \bigr).                                                    \tag{0.61}
\]

Its first coordinate is the complete immutable incoming ledger.  The
leaf lists and suppressed path lists partition exactly the \(b_0\) vertices
outside \(V(\Gamma)\); entries whose loads occur there remain attached to
those lists.  Thus the normalization discards neither a vertex nor an entry.
It nevertheless strictly reduces the active support-internal cycle-skeleton
order:

\[
 \mu_{186}=|X_D|,qquad
 \mu_{187}=|V(\Gamma)|=|X_D|-b_0
                    \le\mu_{186}-2.                         \tag{0.62}
\]

This is the unused A08/E04 textbook move: canonical leaf stripping followed
by safe suppression of maximal degree-two chains, with exact lengths and all
ledger decorations retained.  It is not another demand packing, peel,
visible-four routing, trace-ear argument, or theorem about an arbitrary
graph.

The complete ledger acts on \(\mathcal B_{187}\) as follows.

| Retained block | Simultaneous restriction on the normalized state | Quantitative effect |
|---|---|---|
| A, B | \(X_D\) remains the actual connected ambient-cubic component selected from the incoming support family; its cut and every inside endpoint remain actual. | (0.51)--(0.56a), including the exact \(b_0\)-vertex reconstruction fibre and \(|V(\Gamma)|=|X_D|-b_0\). |
| C | Every edge of \(U\), every trace prefix, and every suppressed path is made of actual edges of \(G\).  Target avoidance is read only after summing the retained path weights. | \(U\) is target-free; the selected actual trace prefixes have length at most eleven and share one first kernel-exit edge. |
| D | Supports, stripping order, maximal paths, weights, marked entries, ports, carriers, endpoint incidences and traces use the inherited fixed orders. | \(\mathcal B_{187}\) is a canonical coordinate of the same labelled counterexample. |
| E | No quotient, replacement graph, or fresh peel is introduced.  Safe suppression stores an inverse reconstruction for every contracted path and leaf. | The strict support-internal cycle-skeleton decrease is exactly \(b_0\), as in (0.62). |
| F | Each marked entry keeps its essential core and all deletion witnesses; the core is still contained in the original cut of \(X_D\). | At least five kernel-marked entries share one actual carrier. |
| G, H | The demand partition is global, while every type-(A1) absorber retains the cut of its owner support; deficit, peel, open-owner, peeled-open and open-unit excesses are localized separately. | (0.46)--(0.50), together with the exact local saturation implication (0.32a). |
| I | \(P_{13}\)-freeness, the order bound \(6142\), and empty internal \(3\)-core are applied to the actual induced graph \(U\). | \(b_0\le877\), every component of \(U\) meets a weighted endpoint, and every selected shortest path has length at most eleven. |
| Other supports and Type B mass | They remain in the first coordinate \(\mathcal B_{186}\), with all exceptional mass, window, entropy, rank and blocker data. | Selecting and normalizing \(X_D\) removes no mass or fact elsewhere. |

The transition audit is exact.

| Test on the incoming active coordinate | Exhaustive outcome | Progress |
|---|---|---|
| Supportwise excess | Some support has the required excess, or all supportwise bounds hold. | The second outcome sums to a contradiction; the first canonically selects (0.45). |
| Current shore has an internal leaf | Delete the first leaf, or the shore has minimum internal degree two. | A deletion changes \((|S|,b(S))\) to \((|S|-1,b(S)-1)\); the terminal arm is \(Y\). |
| Degree-two mass in \(Y\) | It lies on the canonical maximal paths. | Exact suppression removes \(b(Y)\) active skeleton vertices and stores every path and weight. |
| A component of \(U\) misses all weighted endpoints | It exists, or every component meets one. | The first arm is an induced minimum-degree-three subgraph and closes by A-9; the second is the retained arm. |
| First kernel-exit map on \(M\) | It is injective, or two marks share an oriented incidence. | Injectivity gives \(|M|\le2s\), contradicting (0.59); the second yields (0.59a). |

Thus no child repeats the incoming unnormalized support: it either closes or
retains the whole ledger with the strict active-skeleton decrease (0.62).

The earlier star-kernel draft does not provide a second decrease.  Indeed,
even if a port-overlap certificate partitions \(E=Z\mathbin{\dot\cup}Q\) with
\(|Z|\le3b\), equations (0.30) and (0.32) give

\[
 3|Q|=3N-3|Z|=O+b-3|Z|\ge O-8b\ge b+1.                    \tag{0.63}
\]

Thus the leaves \(Q\) are provably nonempty and still carry their peel,
demand, core and blocker obligations.  A hub assignment is a correlation
certificate, not payment, and \(N\mapsto|Z|\) is not a residual measure.

The maximally adversarial survivor has now been quantified without assuming
that unrelated high fibres coincide.  It consists of the whole [186] state,
five possibly different concentration supports, and one distinguished
deficit-heavy support whose exact weighted cubic kernel has at least
\(6b_0+2\) branch vertices and cycle rank at least \(3b_0+2\), while at most
\(b_0\) subdivided kernel edges carry all degree-two structure.  After those
edges are removed, the actual induced graph still has cycle rank at least
\(2b_0+2\) and at least \(4b_0+2\) cubic vertices.  At least \(2b_0+1\)
actual entry loads remain marked on the kernel; five share an essential
carrier, three share an actual port, and two feed the same oriented
subdivision-chain endpoint through induced paths of length at most eleven.
A pair of actual canonical traces (not asserted to be any of those earlier
pairs) also uses the same first kernel-exit edge, and the total excess reuse
of these first-exit incidences is at least \(2n_1+1\).  The selected fibres
may be different and are all retained.

Structurally, this is the one mechanism by which the residual has evaded the
earlier moves: a boundary/reconstruction fibre of only \(b_0\) vertices
controls a cubic kernel with more than \(6b_0\) branch vertices and more than
\(3b_0\) independent cycles.  Demand consumes a boundary incidence once,
but essential cores, visible ports and actual traces may all reuse the same
incidence or subdivision endpoint.  The upstream ledgers measured each of
those projections; they did not measure the multiplicity with which the
large internal kernel funnels through the small reconstruction fibre.
Equations (0.54a), (0.59), and (0.59a) are the first joint quantitative
account of that funnel.

Every alternative in which one of these numerical conclusions fails is
already contradicted by (0.47)--(0.60).  This decorated high-rank,
few-subdivision kernel is therefore the exact structure left for the next
local textbook move.

---

## 1. The path from the root to [181]

Each row: node(s) → arm taken → fact retained on the branch state → technique → register rows evaluated.

| Node(s) | Arm taken | Fact retained | Technique | Rows |
|---|---|---|---|---|
| [1]–[2] | yes | $G$ finite simple, $\delta(G)\ge3$, no cycle of length $2^j$ (`def:counterexample`) | — | A04, C03 |
| [4] | — | $G$ is the lexicographically minimal counterexample: minimum $\lvert V\rvert$, then $\lvert E\rvert$, then lexicographic order | T02 | E01 |
| [5]–[7] | no Mersenne return | $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every oriented edge $e$, $\mathrm{Mers}=\{2^k-1:k\ge2\}$ (`lem:return-equivalence`) | T08 | C02 |
| [8] | — | every proper subgraph $H\subsetneq G$ has $\delta(H)\le2$ (`lem:no-proper-core`) | T02 | E02, A07 |
| [9]–[10] | — | every edge has an endpoint of degree $3$; $V_{\ge4}(G)$ is independent (`lem:deletion-critical`) | T03, T02 | E03, A06 |
| — | — | $G$ is bridgeless (`lem:bridgeless`, by contraction of a bridge) | T03, T02 | B02 |
| [11] | — | boundaried pieces $X\oplus_TY$ with boundary degree profile $\mathbf d_\partial$ (`def:boundaried-gluing`, `lem:degree-profile-fibres`) | T05 | B05, B06 |
| [12] | — | context universality: a target-complete identification agrees against every $T$-context; an identification valid only for the actual outside is target-defective (`lem:context-universality`) | T05 | B07, E06 |
| [13] | — | replacement: no $T$-boundaried $X'\preceq_TX$ with the same $\mathbf d_\partial$, no internal power-of-two cycle, internal degrees $\ge3$, strictly smaller (`lem:replacement`) | T02, T03 | E05 |
| [14] | — | hereditary target-uncompressibility: no proper boundaried piece admits a nontrivial target-complete compression (`cor:uncompressible`) | T02, T05 | E05 |
| retained spine facts | — | contraction criticality and all four gadget-closure clauses remain in the exact ledger: a contractible edge has an actual severed return of length $2^k$ ($k\ge2$); smaller target-free cubic two-terminal pieces have the one-piece, doubled-piece, paired-piece, and complementary Mersenne/power path conclusions stated in §2.C | T02, T03, T08 | E03, C01, C02 |
| [15]–[16] | no | $G$ contains an induced $P_{13}$ (`cor:p13-exists`, via the black box `thm:p13free`: $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle) | T18 | I06, C08 |
| [17] | — | $\mathcal P$: a **maximum-cardinality** family of vertex-disjoint induced $P_{13}$'s, $p_{13}=\lvert\mathcal P\rvert=\theta n$, chosen lexicographically first among maximum ones; $W=\bigcup V(P)$, $R=G-W$ | T06, T16 | C09, C10 |
| [18] | — | $P_{13}$ label algebra: $399$ legal labels (sizes $13,60,122,122,63,17,2$), relations $C_s$, obstruction tensor $\Omega_2$ (`lem:labels`) | T17 | D01, G02 |
| [19]/[20]; [125]–[144] | no non-near-cubic surplus survives | near-cubic spine: $m=\tfrac32n+O(\sqrt n)$, $\sigma(G)=2m-3n=O(\sqrt n)$, $\lvert V_{\ge4}\rvert\le\sigma(G)$ (`def:near-cubic-spine`, `prop:nonnear-cubic-sharp-overload-routing`, `thm:tokenized-surplus-accounting-closure`) | T13, T14, T15 | A02, A05, A14 |
| [21] | — | finite constants: $c_\Omega=2.28922315244$, $c_{13}=118.108581006$; two-step obstruction enumeration $543958,432672,111286$ (`lem:curv-enum`, `lem:p13-window-package`) | T17 | I05, A09, G02 |
| [158] | yes | the joint window package of $\mathcal P$ is realized by the labelled skeleton class: $\ge2^{c_{13}p_{13}\log_2n}$ target-complete states assigned canonically to skeletons in $\mathcal G_{n,m}$ (`def:window-realization-test`) | T12 | G01, G03, G06 |
| [22]/[145]–[157] | the live-hot entropy comparison does not close; the cold machinery returns to [24] on its bounded arm | clause (v) of `def:surviving-cold-branch` scopes `thm:cold-branch-quantitative-closure` to branches that exclude node [181]; its outputs are therefore not [181] facts. What is retained here is only the return at [24] | T12, T13 | G03, H08 |
| [24] | — | the original window-only bound is $\theta\le\theta_{\rm win}+o(1)$, $\theta_{\rm win}=1.5/c_{13}=0.0127002$; the retained relabelling-orbit facts `remainderRelabelingEntropy` (key 501) and `relabelingDensityCap` (key 502), specialized to the realized hot window state, give Theorem 1.5: $\theta\le\theta^\ast+o(1)$ and $\tau\le\tau^\ast+o(1)$ | T12, T16 | G09, G04, I02 |
| [25]–[27] | — | $\lvert R\rvert\ge(1-13\theta)n$; every component of $R$ is $P_{13}$-free, hence of diameter $\le11$ and $\le6142$ vertices, and has empty internal $3$-core: every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ (`lem:remainder-empty-internal-3-core`, black box) | T06, T18, T04 | C10, C08, A07 |
| [28]–[29] | — | $\defp(X)=\sum_v\max(0,3-d_X(v))$; $\defp(R)\le e(R,W)\le15p_{13}+o(n)$; exact split $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; $(\defp(R)-\sigma_R)/\lvert R\rvert\le15\theta/(1-13\theta)+o(1)$, hence the live $\tau_{\rm win}=0.2281749\ldots$ bound | T01, T15 | A10, A11, H01 |
| [30] | — | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$ per component; $W_2(R)\ge\omega_{\rm win}\lvert R\rvert-o(\lvert R\rvert)$, $\omega_{\rm win}=2.54365$ (high entropy $2.57407$) (`lem:wedge-lower`) | T01 | A09, F01 |
| [31]–[47] | no rank drop | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$; every rank-reducing dependence is target-defective, a proper compression (forbidden), a proper-support dependence (forbidden, `lem:proper-smearing`), or a whole-graph dependence that is target-defective, has a smaller closed representative, or is exact on labels (`lem:no-silent-global-smearing`); repair identity $s=p-2+2\beta_Z-\sigma_Z$ (`lem:smearing-support-repair`); separated identical wedges are context-universal or defective (`lem:separated-testers`) | T11, T10, T05 | F01–F07, A12 |
| [48] | — | forced obstruction cost $c_\Omega r_\Omega(R)\ge K_{\rm win}\lvert R\rvert-o(\lvert R\rvert)$, $K_{\rm win}=5.82298$ (high entropy $K=5.89263$) (`cor:forced-curvature-cost`) | T12 | G03, H09 |
| [49]–[50] | high entropy | $\eta(R)=\log_2\lvert\mathcal G(R)\rvert/\lvert R\rvert\ge(1-\tau)\log_2\lvert R\rvert-O(1)>\tfrac1{10}\log_2n$: the low-entropy arms (b),(c) of `prop:two-budget` are empty (Corollary 1.4, relabeling orbits) | T12, T16 | G01, G04, I02 |
| [51]–[53] | remaining non-obstruction budget not $<K\lvert R\rvert$ | large-budget branch: the skeleton budget minus the forced obstruction cost is at least $K\lvert R\rvert$; the entropy cap `prop:entropy-high-theta` ($\theta>\Theta(n)$) does not apply; $\Theta(n)=(1.4-K/\log_2n)/(116.808581006-13K/\log_2n)$ | T12 | H09, G08 |
| [55]–[56]; [173] | — | Residual C: $\Delta_{\rm net}(R)=(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau_{\rm win}+o(1)<\tfrac14$, with the manuscript's stated collision decided exactly at [173] (`lem:exact-collision-test`) | T01, T13 | H01, I03 |
| [57]–[61] | $\No(R)<0$ | net charge $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; $\sum_i\No(X_i)=\defp(R)-\sigma(R)-\tfrac14\lvert R\rvert\le-(\tfrac14-\tau)\lvert R\rvert$; some connected canonical support has $\No(X)<0$ (`def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge`); canonical decomposition of $R$ into components with surplus assigned to the piece containing the high-degree vertex (`def:canonical-decomp`) | T13, T04 | H01–H03, D08 |
| [62]; [64]–[85] | Type B closed | high-degree supports: centers independent, fan neighbours cubic, certificate-marked cap $d_G(h)\le8$, the fan-window ledger, B2 disjointness; every Type B support with $\No<0$ outside the bridge residual has a route-8 profile or a positive-deficit fan residual; the bridge residual mass is $M_B\le16\sigma(G)=o(\lvert R\rvert)$ (`lem:typeB-exclusion`, `prop:typeB-bridge-sublinear`, `thm:branch-kill`(b)) | T07, T13, T14, T15 | D03, D04, H05, H06, H08 |
| [63], [86]–[88] | Type A | the negative supports of linear mass are Type A: $\sigma(X)=0$, so every $v\in V(X)$ has $d_G(v)=3$; $X$ is connected, subcubic, $P_{13}$-free, $\operatorname{diam}X\le11$, $\lvert X\rvert\le6142$, empty internal $3$-core, contextually target-safe, hereditarily uncompressible, every deficient vertex supplied from $W$; $\defp(X)<\lvert X\rvert/4$; receivers $w$ with $d_X(w)\le2$, $q(w)=3-d_X(w)$ ports; canonical traces $T_u$ and loads $L(w)$ (`def:typeA-support`, `def:typeA-receiver-load`) | T04, T05, T07 | A03, A11, B05, C08, D08 |
| [89] | some receiver saturated | $L(w)\ge4q(w)$ for some receiver (else `lem:typeA-unsaturated-discharge`: $\defp(X)\ge\tfrac14\lvert X\rvert$, $n_3\le3n_2+7n_1+11n_0$, closing) | T13 | H04, H05 |
| before [93] | — | the live `portPowerReturn` key retains its witness selected Type A piece; at every completion port of every receiver of **that piece**, absence of a common ambient-cubic neighbour supplies an actual anchored return of length $2^k$, $k\ge2$. It is not silently generalized to every member of $\tilde{\mathcal X}$ | T03, T08 | E03, C01, C02 |
| [93] | tested at every stage | a visible-four port routes to exits (1)–(7); exits (1)–(3), (5), and (6) close, exit (7) hands off to Type B, and exit (4) is recorded and peeled. Thus the node-[181] ledger retains the exit-(4) records but no universal no-visible-four assertion | T07, T08, T19 | C01, C02, E08 |
| [94] | — | visible-first excess: $S^{\rm exc}_{\rm sil}(X)=\sum_w\lvert\mathcal U(w)\rvert\ge n_3-3n_2-7n_1-11n_0=4D_A(X)$, $D_A(X)=\tfrac14\lvert X\rvert-\defp(X)$ (`lem:typeA-silent-excess-count`, `def:typeA-excess-basin`) | T13, T15 | H05, G07 |
| [95]–[108] | exits (1),(2),(3),(5),(6) closed; (7) absent; (4) peels | at every saturated receiver of every $X\in\tilde{\mathcal X}$: no anchored return of Mersenne length through a port; no two internally disjoint receiver-entry returns through one port with lengths summing to a power of two (`lem:typeA-common-port-return-cycle`); no violated label relation $C_s$ on a shared window; no nontrivial target-complete response compression; no delocalizing response equality; no decorated handoff fan (exit (7)) since $X\in\tilde{\mathcal X}$ produces none; continuation routing at a port gives exits (4)–(6) or a surviving first separator of degree $\ge4$ (`lem:typeA-continuation-routing`, `lem:typeA-cubic-switch-absorption`, `lem:typeA-high-degree-handoff`) | T08, T09, T05, T07 | C01–C05, D01, E05, E06, D03 |
| [109]–[113] | — | the unified negative collection $\tilde{\mathcal X}=\{X:\sigma(X)=0,\No(X)<0,\text{no handoff}\}$ with $\tilde D_A=\sum(\tfrac14\lvert X\rvert-\defp(X))\ge(\tfrac14-\tau)\lvert R\rvert-o(\lvert R\rvert)$; entries $\tilde\Xi=\{(X,w,u,B_u):u\in\mathcal U_X(w)\}$, $\tilde N\ge4\tilde D_A$ (`def:typeA-unified-negative`, `lem:typeA-unified-deficit`, `lem:typeA-unified-burden`) | T13, T15 | H03, H08, G07 |
| [114]–[116] | — | every entry passes to its canonical minimal target-complete response-support core $\mathcal C_{\rm ess}(\xi)\subseteq\partial_EX$, $\alpha(\xi)=\lvert\mathcal C_{\rm ess}\rvert\ge2$ (`lem:typeA-unified-carriers`; entries with $\alpha\le1$ realize exits (4)–(7)) | T11, T05 | F02, F04, B08 |
| [117]; [119]–[122] | two-support entry exists | if every entry had $\pi(\xi)\ge3$ private essential incidences then $3\tilde N\le\defp(R)$ against $\tilde N\ge12(\tfrac14-\tau)\lvert R\rvert$, impossible; so some $\xi$ has $\pi(\xi)\le2$ (`prop:typeA-unified-reduction`) | T15, T01 | G07, H06 |
| [118], [124] | route-8 two-support closed | no terminal two-support route-8 obstruction (`thm:typeA-two-carrier-nogo`); Theorem 3.2: every two-support entry realizes exit (4), so route-8 two-support entries do not occur | T05, T11 | E06, F05 |
| [101]–[102], [123] | target-defect two-support: peel | each such entry is peeled: its load leaves the receiver sum, $\Lambda_4=\sum_w\lvert\mathcal L(w)\setminus P_4(w)\rvert$ decreases by one, the deficit by $\tfrac14$, no invariant weakened (`lem:typeA-exit4-discharge`, `lem:typeA-exit4-finite-descent`); iterate while $\tilde D_A^{P_4}\ge(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$ | T19 | E08, H10 |
| [181] | the reduced-rate test fails | the full peeled-demand leaf (§4); maximal-ledger augmentation forces \(|H_{181}|=0\), and the no-witness arm closes at [124] | one-entry packing augmentation | B09, H06 |
| [183] | every unpaid entry has a witness | the complete [181] ledger plus \((|H_{181}|,|N_{181}|)=(0,0)\) | retained-census exhaustion | F04, E08 |
| [184] | silent ownership eliminated | the same unified entries and all inherited ledger facts, with every entry owned by an actual scheduled return and \(|S_{184}|=0\) | shortest-path chord elimination + boundary-support collapse (new local move) | C01, B08, F04 |
| [185] | non-overloaded ownership eliminated | the same unified entries and complete ledger, with an actual canonical visible-four package at every entry receiver and \(|O_{185}|=0\) | visible-first prefix exhaustion on the node-[184] ownership fact | H05, C01, D08 |
| [186] | exact simultaneous balance and silent-terminal exclusion | the whole [185] ledger plus universal saturated-load visibility, zero silent-unpeeled excess for every retained component/receiver/peeling-set triple, (p\le D\le N), (N=D+U), the ambient deficit, demand/open pressure, coupled pressure, failed-rate peel balance, and the exact demand/absorption identities | direct invariant elimination on the incoming peel, deficit, demand, and absorption ledgers | A03, B09, G07, H05, H06, H10 |

Arms not on the path (for completeness): [3] not a counterexample; [16] $P_{13}$-free; [20] non-near-cubic surplus (routed back to the spine); [23] live-hot overflow; [159]–[172] dense-packing residual ($\theta>\theta_{\rm win}$, the no-arm of [158]) and its nodes [163]–[172], [178]–[180], [182]; [60] net-cap contradiction; [90]–[92] unsaturated; [96], [98],[100], [104], [106] closed exits; [108] handoff; [124] closed.

---

## 2. The complete hypothesis ledger, by register category

Every unqualified fact below is on the branch state $\mathcal B_{181}$.
Rows explicitly labelled “candidate” or “exploratory” are included only to
audit the attempted closure and are not incoming live-ledger facts. “Produced
by” names the technique; “Row” the register property it evaluates.

### A — size, degree, sparsity, local incidence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| A-1 | $\delta(G)\ge3$; $n=\lvert V(G)\rvert\to\infty$ along the branch | `def:counterexample` | — | A04, A01 |
| A-2 | $m=\tfrac32n+O(\sqrt n)$; $\sigma(G)=2m-3n=O(\sqrt n)$; $\lvert V_{\ge4}(G)\rvert\le\sigma(G)$ | `def:near-cubic-spine` | T13/T14/T15 (surplus ledger) | A02, A05, A14 |
| A-3 | $m\ge\lceil3n/2\rceil$, $m\le2n-2$; $\beta=m-n+1\ge n/2+1$; $\beta+\lambda=n-2$; $\sigma=2\beta-n-2$ | invariants 9–13 | T01 | A02, A12, A13 |
| A-4 | $V_{\ge4}(G)$ independent; every edge has a degree-3 endpoint | `lem:deletion-critical` | T03/T02 | A06, E03 |
| A-5 | every vertex of every Type A support has $d_G=3$; a vertex of internal degree $3-q$ has $q$ stubs to $W$; $\defp(X)=\sum q$; $\defp(X)<\lvert X\rvert/4$ on $\tilde{\mathcal X}$ | `def:typeA-support` | T05 | A03, A11 |
| A-6 | $\defp(R)\le e(R,W)\le15p_{13}+o(n)$; $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; each window carries at most $15$ stubs (interior vertex one, end two) | `lem:stub-positive` | T01/T15 | A10, A11 |
| A-7 | $(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau^\ast+o(1)$, where $\theta^\ast=\frac{3/4}{c_{13}-39/4-15}$ and $\tau^\ast=\frac{15\theta^\ast}{1-13\theta^\ast}=0.13456\ldots<1/7$ | `prop:p13-density`; `closure_proofs.md`, Theorem 1.5; live orbit keys 501–502 | T12/T16 | A11, H01 |
| A-8 | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$; $W_2(R)\ge2.54365\lvert R\rvert-o(\lvert R\rvert)$ | `lem:wedge-lower` | T01 | A09 |
| A-9 | every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ | `lem:remainder-empty-internal-3-core` | T18 | A07 |
| A-10 | every component of $G-V(X)$ sends $\ge2$ edges to $X$; $\defp(X)\ge2$ | `lem:bridgeless` | T03/T02 | A11, B02 |

### B — connectivity, cuts, boundaries, contexts

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| B-1 | $G$ is bridgeless; every edge lies on a cycle | `lem:bridgeless` | T03/T02 | B02 |
| B-2 | every proper subgraph has $\delta\le2$ | `lem:no-proper-core` | T02 | E02, B01 |
| B-3 | $R=G-W$; its components are the canonical supports; no edges of $R$ between distinct components; surplus units of $V_{\ge4}\cap V(R)$ assigned to their component | `def:canonical-decomp` | T04 | B01, D08 |
| B-4 | boundaried pieces, boundary degree profiles, gluing $X\oplus_TY$; quotients fibrewise over $\mathbf d_\partial$ | `def:boundaried-gluing`, `lem:degree-profile-fibres` | T05 | B05, B06 |
| B-5 | context universality (target-complete identifications agree against every context) | `lem:context-universality` | T05 | B07 |
| B-6 | trace basins $B_u$: lexicographically first inclusion-minimal trace-complete connected subgraph containing $T_u$; trace-response state $\rho_u(B_u)=(\mathbf d_\partial(B_u),\mathcal R_u(B_u),\profile)$ | `def:typeA-trace-basin` | T05/T10 | B08, B06 |
| B-7 | boundary incidences $\partial_EX$, $\lvert\partial_EX\rvert=\defp(X)$; every $u$-supported coordinate leaving $X$ records one | `def:typeA-route8-carriers` | T05 | B05, B09 |
| B-8 | the demand ledger on $\tilde\Xi$: partition $\Xi_3\sqcup\Xi_2\sqcup\Xi_{\rm res}$ with disjoint incidence sets $A(\xi)$ ($3$ or $2$ per entry), lexicographically first maximizing $N_3$ then $N_2$; $\mathsf P_{\rm ext}=N_2+3N_{\rm res}$; $3N_3+2N_2\le\defp(R)$ | `def:typeA-pressure-ledger`, `lem:typeA-pressure-ledger-no-overcount` | T14/T15 | B09, H06 |
| B-9 | absorbers: (A1) single-use unused incidences of the global supply, each lying in the cut of its owner entry's support and disjoint from every base assignment; the committed (A2) dependence set is empty; $\mathsf P_{\rm open}=\lvert\mathcal U_{\rm press}\setminus\mathcal U_{\rm abs}\rvert$ and $3\tilde N\le\defp(R)+\mathsf P_{\rm open}$ | `Route8DemandAbsorptionStatement`, `route8DemandAbsorptionRow`, `lem:typeA-pressure-absorber-no-overcount` | T14/T15 | B09, H06 |
| B-10 | window blockers: each open unit is assigned a packed window through its owner entry, and $\mathsf P_{\rm open}=\sum_P B_{\rm open}(P)$; the live schema stores the window map, not an additional boundary-incidence map | `Route8WindowBlockersStatement`, `lem:typeA-open-window-blocker-count` | T15 | B09, A10 |
| B-11 | $\mathsf P_{\rm open}\ge(3-13\tau)\lvert R\rvert-o(\lvert R\rvert)$ and $\mathsf P^{+}_{\rm zero}\ge\varepsilon_{\rm prim}\lvert R\rvert-o(\lvert R\rvert)$ on the branch (so the offered consumers of [181] are vacuous) | Theorem 3.1 | T01 | B09, H09 |

### C — paths, cycles, lengths

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| C-1 | no cycle of $G$ has length in $\mathrm{Pow}=\{2^j\}$; $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every oriented edge | `lem:return-equivalence` | T08 | C02, C03 |
| C-2 | every completion port has at least one actual anchored return | `lem:typeA-port-return` | T08 | C02 |
| C-3 | receiver-entry returns are actual simple connector–channel paths, and the finite schedule contains every such return | `def:typeA-visible-load`; `VisibleReceiverEntry.lean` | T08/T16 | C01, C02 |
| C-4 | connector/channel arithmetic: for a receiver-entry return $\Gamma\circ Q$ through $(w,h)$ with connector length $g$, $g+\lambda\notin\mathrm{Mers}$ for all $\lambda\in\Lambda_X(r,w)$; interval form with $I_X(r,w)$ | `lem:typeA-spectral-pressure`, `def:typeA-channel-spectrum` | T09 | C01, C04 |
| C-5 | theta closure: all branch-pair sums in a theta avoid $\mathrm{Pow}$; ear closure; symmetric difference of overlapping cycles avoids $\mathrm{Pow}$ | invariants 31–33 | T08/T09 | C05–C07 |
| C-6 | two-path criterion: two internally disjoint returns through one port with lengths summing to $2^k$ give a forbidden cycle | `lem:typeA-common-port-return-cycle`, invariant 30 | T08 | C05 |
| C-7 | every cycle length has an odd prime divisor; no single odd prime divides all cycle lengths; overlap formula $q_p(E)=q_p(C)+q_p(D)-2t$ flat and non-killing | invariants 36–38 | T09/T11 | C04 |
| C-8 | $G$ has an induced $P_{13}$; $R$ has none; every component of $R$ has diameter $\le11$ and $\le6142$ vertices | `cor:p13-exists`, `lem:remainder-empty-internal-3-core` | T18/T06 | C08 |
| C-9 | $p_{13}$ is the **maximum** number of vertex-disjoint induced $P_{13}$'s; the incoming live rate is $\theta=p_{13}/n\le\theta_{\rm win}+o(1)$ | [17], `prop:p13-density` | T06/T12 | C09, G09 |
| C-10 | gadget closure, one-piece and doubled: if $K$ is a smaller target-free cubic two-terminal piece with terminals $a,b$, then closing $a,b$ produces an actual $a$--$b$ path of length $2^e-1$; if $2|K|<|G|$, closing two copies produces two such paths whose lengths sum to $2^e-2$ | live key `gadgetClosure`, clauses 2 and 3 | T02/T03/T08 | C01, C02, E03 |
| C-11 | gadget closure, paired and complementary: two smaller target-free cubic two-terminal pieces whose closed gluing has minimum degree $3$ supply terminal paths whose lengths, plus the two joining edges, sum to a power of two; a complementary closure supplies an outside terminal path of length $2^e-1$ | live key `gadgetClosure`, clauses 1 and 4 | T02/T03/T08 | C01, C02, E03 |

### D — local configurations, motifs, overlap, symmetry

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| D-1 | $399$ legal $P_{13}$ labels; relations $C_s$; the zero-defect quotient through path lengths $1,2,3$ is the identity | `lem:labels` | T17 | D01, G02 |
| D-2 | $0.795414$ of locally safe wedges are obstructing; $c_\Omega=2.2892$ bits per independent obstruction coordinate | `lem:curv-enum` | T17 | D02, G02 |
| D-3 | Type B: fan-safe graphs, certificate labellings, $d_G(h)\le8$ for certificate-marked fans, degree-4 profiles, B2 disjointness, bridge residual sublinear | [64]–[85] | T07/T13/T14 | D03, D04 |
| D-4 | canonical decomposition, canonical traces (lexicographically first receiver-reaching paths in $X_3$), canonical payable set $A(w)$ (visible-first order), lexicographically first ledgers and assignments | `def:canonical-decomp`, `def:typeA-receiver-load`, `def:typeA-excess-basin`, `def:typeA-pressure-ledger` | T16 | D08, I02 |
| D-5 | all auxiliary objects are functions of the labelled adjacency matrix under a fixed tie-break; states are $\mathrm{Sym}(R)$-invariant relative to $W$ | `lem:skeleton-dominates`, Theorem 1.3 | T16/T12 | D09, G06 |

### E — extremality, criticality, replacement, quotients

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| E-1 | lexicographic minimality of $G$ ($\lvert V\rvert$, then $\lvert E\rvert$, then lexicographic) | [4] | T02 | E01 |
| E-2 | no proper subgraph with $\delta\ge3$; deletion criticality | [8]–[9] | T02/T03 | E02, E03 |
| E-3 | replacement lemma and hereditary uncompressibility (I5) | `lem:replacement`, `cor:uncompressible` | T02/T05 | E05 |
| E-4 | a quotient is valid only if target-complete against every context; otherwise target-defective | `lem:context-universality` | T05 | E06 |
| E-5 | exit-(4) peeling is a well-founded descent on $\Lambda_4$ preserving every invariant | `lem:typeA-exit4-finite-descent` | T19 | E08, H10 |
| E-6 | exits (5) and (6) never occur at any saturated receiver of $\tilde{\mathcal X}$ (standing-invariant contradictions); exit (7) is absent | `lem:typeA-exits-discharged`, `lem:typeA-unified-burden` | T02/T05 | E05, E09 |
| E-7 | contraction criticality: for an oriented edge $xy$, if no common neighbour of $x,y$ has ambient degree $3$, then the severed graph contains an **actual** simple $x$--$y$ path of length $2^e$, $e\ge2$ | live key `contractionCritical` | T02/T03 | E03, C01 |

### F — local tests, rank, dependence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| F-1 | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$ | `lem:full-rank` | T11 | F02, F07 |
| F-2 | rank drop routes to target defect, proper compression, or support enlargement; proper enlargements $Z\subsetneq G$ are impossible; whole-graph dependence cannot silently reduce rank | `lem:curvature-dependence-routing`, `lem:proper-smearing`, `lem:no-silent-global-smearing` | T10/T11 | F03–F07 |
| F-3 | separated identical wedges are context-universal or target-defective | `lem:separated-testers` | T05/T11 | F05 |
| F-4 | every entry's trace basin fails target-complete-minimality only through alternative (a) — a trace-local quotient forgetting a coordinate on an internal edge of $B_u$ is distinguished by a compatible context; (b),(c),(d) do not occur | `def:typeA-trace-basin`, Theorem 3.2 | T05/T16 | F04, E06 |
| F-5 | $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$; every $c\in\mathcal C_{\rm ess}$ has a declared deletion witness (internal/mixed) with boundary-incidence support | `lem:typeA-unified-carriers`, `def:typeA-carrier-deletion-witness`, `lem:typeA-deletion-witness-declared` | T05/T11 | F04, F05 |

### G — counting and information

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| G-1 | $\lvert\mathcal G_{n,m}\rvert=\binom{\binom n2}{m}$; skeleton budget $\tfrac32n\log_2n+o(n\log n)$ | `lem:skeleton-dominates`, `lem:near-cubic-budget` | T12 | G01 |
| G-2 | the joint window package is realized: $\ge2^{c_{13}p_{13}\log_2n}$ states | [158] yes | T12 | G03 |
| G-3 | $\log_2\lvert\Phi(\mathcal S)\rvert\le\log_2\lvert\mathcal S\rvert-(\tfrac34\lvert R\rvert-15p_{13})\log_2\lvert R\rvert+O(n)$; the finite orbit inequalities are registered by `remainderRelabelingEntropy` and `relabelingDensityCap` | `closure_proofs.md` Theorem 1.3; live keys 501–502 | T12/T16 | G01, G04 |
| G-4 | $\eta(R)\ge(1-\tau)\log_2\lvert R\rvert-O(1)$ and the specialization of G-3 on the hot arm gives $\theta\le\theta^\ast+o(1)$ | `closure_proofs.md` Corollary 1.4 and Theorem 1.5 | T12/T16 | G04, G09 |
| G-5 | forced cost $c_\Omega r_\Omega\ge K_{\rm win}\lvert R\rvert$; the large-budget arm: remaining budget $\ge K\lvert R\rvert$ | [48], [53] | T12 | G03, H09 |
| G-6 | no double counting: demand incidences pairwise disjoint; absorbers single-use; the exact stage identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ | `lem:typeA-pressure-ledger-no-overcount`, `lem:typeA-peeling-stage-accounting` | T15 | G07 |
| G-7 | the exact collision actually stated at [173] is decided there; it does not exactify a newly introduced coefficient comparison | `lem:exact-collision-test` | T12/T17 | G08 |

### H — charging and discharging

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| H-1 | $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; superadditivity; some connected support has $\No<0$ | `def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge` | T13 | H01–H03 |
| H-2 | Type A: each cubic vertex charges $\tfrac14$ to its receiver; receiver charge $q(w)-\tfrac14-\tfrac14L(w)$; unsaturated receivers ($L\le4q-1$) pay; thresholds $H_0\le4,H_1\le8,H_2\le12$ | `lem:typeA-threshold-algebra`, `lem:typeA-unsaturated-discharge`, `lem:typeA-exit4-peeling-charge` | T13 | H04, H05 |
| H-3 | saturated receivers with silent excess: $S^{\rm exc}_{\rm sil}\ge4D_A(X)$; the unified deficit $\tilde D_A\ge(\tfrac14-\tau)\lvert R\rvert$; $\tilde N\ge4\tilde D_A$ | [94], [111]–[113] | T13/T15 | H05, H08 |
| H-4 | private-support budget: three private incidences per entry would force $3\tilde N\le\defp(R)$, contradiction; hence two-support entries exist | `prop:typeA-unified-reduction` | T15 | H06 |
| H-5 | the demand ledger, absorbers and blockers (B-8–B-11) | — | T14/T15 | H06 |
| H-6 | Type B bridge mass $o(\lvert R\rvert)$ | `prop:typeB-bridge-sublinear` | T13/T15 | H08 |
| H-7 | with the retained cap $\tau^\ast<1/7$, the local inequality $\lvert X\rvert\le7\defp(X)$ on every negative Type A support is sufficient for a global contradiction | `closure_proofs.md` Theorems 1.5 and 3.4 | T13 | H09 |
| H-8 | finite descent $\Lambda_4$ | `lem:typeA-exit4-finite-descent` | T19 | H10 |

### I — finite certification and external inputs

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| I-1 | the black box `thm:p13free` (HSS): $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle; consumed as A-9 and C-8 | [15]–[16] | T18 | I06 |
| I-2 | Bondy--Vince: except for $K_1,K_2$, a graph with at most two vertices of degree below $3$ contains two cycles whose lengths differ by $1$ or $2$.  Only this exact theorem is used below; neither the appendix's quiet-block estimate nor a Gao--Ma consequence is assumed | [Bondy--Vince, *Cycles in a graph whose lengths differ by one or two*](https://people.clas.ufl.edu/avince/files/Cycles.pdf) | T18 | I06 |
| I-3 | finite constants $c_\Omega$, $c_{13}$, label counts; the $91$-barrier computation; the two-strand table | `app:curv-code`, `lem:labels`, [167] | T17 | I05, I01 |
| I-4 | exact small-order collision decided on the object | [173] | T17 | I03, I04 |

---

## 3. Techniques already used upstream, and the structural properties each one consumed

| Technique | Where used | Properties consumed (register rows) | What it left behind |
|---|---|---|---|
| T01 Direct invariant calculation | [28]–[30], [56], [119]–[122], Theorems 3.1, 3.4 | A02, A09–A12, H01, H06, H09 | the inequalities of A-3, A-6–A-8, H-3, H-4, B-11 |
| T05 Boundary-interface analysis | [11]–[14], trace basins, response states, cores, deletion witnesses, contexts | B05–B08, E05, E06, F04, F05 | B-4–B-7, E-3, E-4, F-4, F-5 |
| T08 Path–cycle and cycle-space analysis | [5]–[7], invariants 30–33, `lem:typeA-port-return`, `lem:typeA-common-port-return-cycle` | C02, C03, C05–C07 | C-1, C-3, C-5, C-6 |
| T10 Uncrossing and minimal obstruction | [31]–[47] (dependence localization), trace-basin minimality, continuation routing | F03–F07, B08, D05 (cold branch only) | F-2; on the [181] branch the corridor/overlap consumers of [169]–[172] are **not** available (they live on the dense-packing residual) |
| T11 Linear-algebraic rank | [31]–[47], response-support cores | F01–F07, A12 | F-1, F-2, F-5 |
| T12 Counting and information | [21], [48]–[55], [158], Theorems 1.3–1.5, Corollary 1.4 | G01–G09, H09 | G-1–G-5, A-7, C-9; the low-entropy arms are empty |
| T13 Potential and discharging | [56]–[62], Type A charging, Type B ledger | H01–H05, H08 | H-1–H-3, H-6 |
| T14 Demand–supply and flow | Type B B1/B2, the $2/3$-demand ledger, absorbers, surplus token ledger | B09, H05, H06, D04 | B-8–B-10; the failure of the matching is the leaf |
| T16 Symmetry and canonicalization | lexicographic tie-breaks everywhere, $\mathrm{Sym}(R)$-invariance (Theorem 1.3), canonical traces/ledgers | D08, I02, E07, G04 | D-4, D-5, G-3; the refined-order swap [165]–[166] is used only on the dense residual |
| T18 External structural theorem | [15]–[16] (HSS) | I06, C08 | I-1; Bondy--Vince is not invoked upstream and is consumed locally in Lemma 9.1; no Gao--Ma consequence is used |
| T19 Peeling and finite descent | [101]–[102], [123] | E08, H10 | E-5, H-8, and the leaf's identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ |

The move in Theorem 0.3 is not another application of any closing row in this
table. Upstream path arguments construct returns or forbidden cycles, and
upstream boundary arguments construct response supports. The new move instead
uses the length-first order of the already selected trace to eliminate every
chord, converts exact ambient cubicity into the pointwise boundary identity
(0.6), and then evaluates the literal retained response state on that
boundary-only basin. Its output is the new exact coordinate \(|S_{184}|=0\).

Theorem 0.4 then consumes precisely that new all-visible coordinate. It does
not repeat the node-[93] split: node [93] allowed and recorded exit (4), while
Theorem 0.4 asks whether an entry that is still outside its visible-first
payable prefix can have no overloaded port. The port-cap count makes that
profile impossible and yields the new exact coordinate \(|O_{185}|=0\).

Theorem 0.5 and Corollary 0.6 do not run another demand or peeling procedure.
They put the already retained charge, failed-rate, peel, demand, absorption,
blocker, carrier and density identities into one system, eliminate \(D,N\),
and force the peeled, open-owner, peeled-open, open-unit, and repeated-core
fibres (0.30)--(0.40) on the same incoming indices.  The demand partition is
global, but each absorber retains the cut of its owner support.  Consequently
every support carrying an open unit satisfies the local saturation identity
(0.32a); no cross-support absorption is permitted.

Proposition 0.7 first removes Q2 from the original peel-witness alphabet by
combining the literal Q2 silence clause with the all-visible fact at [184].
Theorem 0.8 then decomposes every live currency and the already owner-local
absorber relation by actual support, and canonically selects the possibly
different supports on which deficit, peel, open-owner, peeled-open-owner, and
open-unit excesses occur.  The deficit-heavy support itself carries at least
\(3b_X+1\) entries, so its topology and its entry fibres can be counted on the
same indices.

Theorem 0.9 consumes the previously unused A08/E04 structure by canonical
leaf stripping and length-preserving suppression of every maximal
degree-two path in that exact support.  The resulting weighted cubic kernel
has \(|X|-b_X\) vertices, while every removed vertex, path length, entry and
witness remains in the reconstruction coordinate.  Its actual unweighted
subgraph retains cycle rank at least \(2b_X+2\), and more than \(2b_X\)
entry loads remain marked on the kernel.  Pigeonhole counting then forces
the simultaneous marked port, carrier, and subdivision-endpoint collisions.
Equation (0.63) separately proves why the retired star assignment could not
serve as a residual measure: its leaves remain quantitatively nonempty and
unpaid.

---

## 4. The leaf: the typed data of [181]

`def:typeA-peeled-demand-residual`, after the procedure of `thm:large-budget-route8-only`:

In the live vocabulary its proposition is definitionally
\[
\begin{gathered}
\texttt{Route8StageRateFailedFact}\;\wedge\;
\texttt{Route8DemandLedgerStatement}\;\wedge\\
\texttt{Route8DemandAbsorptionStatement}\;\wedge\;
\texttt{Route8WindowBlockersStatement}.
\end{gathered}                                      \tag{4.1}
\]
The four conjuncts are retained together with, rather than substituted for,
the incoming `ExactLedger` facts.

- **(R1)** a valid family \(P_4=(P_4(w))_w\) of exit-(4) peeling sets at
  which
  \(\tilde D_A^{P_4}<(\tfrac14-\tau_{\rm win})|R|-o(|R|)\);
- **(R2)** the disjoint partition
  \(\tilde\Xi=\tilde\Xi^{P_4}\mathbin{\dot\cup}\tilde P_4\),
  \(p_4=|\tilde P_4|=\sum_w|P_4^{\rm un}(w)|\), the exact identity
  \(4\tilde D_A=4\tilde D_A^{P_4}+p_4\), and the recorded exit-(4) witness
  for every index actually occurring in the peel chain;
- **(R3)** the maximal \(2/3\)-demand ledger on the full unified entry
  family \(\tilde\Xi\), its maximal absorption ledger, and the unique-window
  blocker partition
  \(\mathsf P_{\rm open}=\sum_P B_{\rm open}(P)\).

The full unified family is not the peeled list and is not a purely silent
family. An index \(\xi=(X,w,u)\in\texttt{route8UnifiedEntries}\) consists of
a retained Type A support \(X\), a saturated receiver \(w\), and an unpaid
load \(u\in E_X(w)\), where \(E_X(w)\) is the visible-first excess basin.
Thus the family contains both unpaid visible-first loads and silent-excess
loads. For every such index the retained unified census supplies the
selected basin \(B_u\), the bound
\(|\mathcal C_{\rm ess}(\xi)|=\alpha(\xi)\ge2\), and exactly the alternative

\[
 \text{target-complete-minimal}\quad\text{or}\quad
 \bigl(\text{trace-local target defect with the other three failures absent
 and a canonical exit-(4) witness for }u\bigr).          \tag{4.2}
\]

Neither silence, the two-private-carrier bound, nor the target-defect arm is
asserted for every unified entry at node [181]. The two-private-carrier
bound for entries unpaid by the selected maximal partition is the new
conclusion of Theorem 0.1; the witness-free part of the first arm in (4.2)
is what routes to [124] in Theorem 0.2.

The assertion \(q(w)\in\{1,2\}\) is a consequence, not an extra hypothesis.
If a connected negative Type A support contained a receiver of internal
degree \(0\), that vertex would be an isolated vertex of \(X\), hence
\(X=\{w\}\). Then \(\defp(X)=3>1/4=|X|/4\), contrary to \(\No(X)<0\).
Thus \(n_0(X)=0\), and every receiver has internal degree \(1\) or \(2\), so
\(q(w)=2\) or \(1\).

For an unpaid index on the target-defect arm, the demand ledger supplies a
`CanonicalDemandRecord`. Its alternative realization, outside context, and
profile event are certificate data, not paths of \(G\). The record must be in
its **profile** disjunct: its actual disjunct would be a target cycle in
\[
 \operatorname{glue}(\operatorname{piece}(B_u),
                     \operatorname{outside}(B_u)).
\]
The owned-decomposition isomorphism
`SupportAtom.decomposition.reconstructionIso` identifies this gluing with
\(G\), and the target predicate is invariant under isomorphism; the actual
disjunct would therefore contradict C-1. A profile event is retained as
certificate data but is never used as an actual path of \(G\).

Derived facts at the leaf: Theorem 3.1 (the offered consumers are vacuous);
Theorem 3.2 (every two-support entry realizes exit (4); no true route-8
two-support entry; at least one peel is performed); Corollary 3.3 ([181] is
the only exit of [123]); Theorem 3.4 (diagnostic rate). The reduction in §0 does
not strengthen this leaf by assumption. The reductions in §0 read the retained
demand maximality and unified census from the same `ExactLedger`, prove
Theorems 0.1--0.4, and append the exact node-[185] interface.  Theorem 0.5 is
now the attached Lean row at [186].  The later structural accounting continues
from that exact implemented interface while retaining the complete ledger.

---

## 5. The newly consumed rows and the retired attempted move

At [186], A08 (degree-two chains) and E04 (safe suppression) are the first
rows in this list that have not already been spent on the same observable.
Theorem 0.9 consumes them together: leaf stripping exposes the exact
degree-two mass and weighted suppression removes it from the active
internal-cycle skeleton while retaining a reconstruction of every
vertex and every attached entry.  A07/C08 prevent a cubic component from
escaping in the unweighted kernel, while G07/H05 keep the entry, core and
port marks on that same support.

B02--B04 beyond bare bridgelessness (cyclic edge cuts, blocks and disjoint
connections), C04/F08, C09, D07 and the unused part of I06 remain on the
monotonically growing ledger.  None is deleted or replaced by a weaker
statement.

The older attempted move below was T10 followed by T18: uncross the **actual canonical
traces** of all silent marks into a trace--ear forest, and apply Bondy--Vince
only to the terminal two-pole shells produced by that forest.  The move is on
the complete state $\mathcal B_{181}$; $X$, a full-vertex component of $X$,
and a shell are active regions on which the move acts, not replacements for
the residual. The intended recursive measure and terminal arms are written in
§8. Section 12 identifies the unhandled multi-boundary cyclic arm, so this
move is not an admitted structural-exhaustion transition. It nevertheless
isolates the exact new accounting that would be needed: no upstream row counted
how many silent marks can survive in the cyclic part of a cubic support.

---

## 6. Retired trace--ear route to the target statement

**Target statement [181].** Let \(G\) be a finite simple graph and suppose that all
facts of §2 (A-1 through I-4), with the arms of §1 as stated, and all leaf data
(R1)–(R3) of §4 hold. Then \(G\) contains a cycle whose length is a power of
two.

Equivalently, the complete declared-support residual routed from [123] after
[124] is empty. Section 0 does not assert that statement: it reduces the
literal branch through [181] and [183] to the all-visible residual [184],
then to the actual-overload residual [185], forces the joint concentration
state [186], and performs the exact degree-chain normalization (0.61). The
older draft below tried instead to act on silent target-defect traces. It did
not account for the shortest-path boundary-support collapse proved in
Theorem 0.3 or the prefix exhaustion proved in Theorem 0.4.

Sections 7–11 give the attempted derivation. Section 7 fixes the actual
objects and the monotone ledger, §8 states the proposed local trace--ear
exhaustion, §9 proves the valid finite shell estimate, §10 records the
arithmetic of the failed draft, and §11 records the intended
implementation interface. Section 12 audits every step and explains why that
derivation does not prove the target statement. The audit is retained only to
preserve its correct local identities; none of its failed children is used in
the implemented [183]→[184]→[185] transitions.

---

## 7. Fixing the object: full vertices, actual traces and boundary half-edges

Throughout §§7–10 the ambient object is still the complete branch state
$\mathcal B_{181}$.  Fix one member $X$ of the unified negative Type A
collection only as the active region of the next move.  Put
\[
 n_i=n_i(X):=|\{x\in X:d_X(x)=i\}|,
 \qquad d:=\defp(X)=n_2+2n_1+3n_0.
\]
By the argument in §4, $n_0=0$, so
\[
 d=n_2+2n_1.                                        \tag{7.1}
\]
Let
\[
 U_X:=\mathop{\dot\bigcup}_{w\in\operatorname{Rec}(X)}\mathcal U_X(w)
\]
be the **original**, visible-first silent excess.  This is the collection
before any exit-(4) peel.  The partition and witnesses (R1)–(R3) remain
attached to its members; passing back from the peeled list to $U_X$ is not a
loss of data.  The exact support-level count at [94] gives
\[
 |U_X|\ge n_3-3n_2-7n_1.                            \tag{7.2}
\]

Let $X_3=X[\{x:d_X(x)=3\}]$, and let $F$ run over the connected components of
$X_3$.  Write $b(F)$ for the number of edges of $X$ with one end in $F$ and
the other end a receiver.  Attach a formal leaf to the $F$-end of each such
edge; these are the boundary half-edges of $F$.  Put
\[
 U(F)=U_X\cap V(F),\qquad b_X=\sum_F b(F).
\]
Then the sets $U(F)$ partition $U_X$.  Moreover,
\[
 b_X\le2n_2+n_1.                                    \tag{7.3}
\]
Indeed a degree-two receiver has at most two neighbours in $X_3$, and a
degree-one receiver at most one; receiver--receiver edges only decrease the
left side.

There is no ambiguity about the routing inside $F$.  From any two vertices of
$F$, exactly the same receivers are reachable by a path whose nonterminal
vertices have internal degree three: they are precisely the receiver
neighbours of $F$.  Since `traceReceiver?` scans the fixed vertex order, it
therefore chooses one and the same receiver $r(F)$ for every full vertex of
$F$.  The selected path `tracePath?` stays in $F$ until its last edge to
$r(F)$.  Thus the marks $U(F)$, their canonical paths and their terminal
receiver are all actual objects of $G$.

Finally, every **completion port** used below has an actual return.  Delete
its port edge.  Since $G$ is bridgeless, its ends remain joined; shortening
the joining walk gives a simple anchored path $P$ from the outside endpoint
$h$ to the receiver $w$. Let $r$ be the first vertex of $X$ on $P$ and let
$\Gamma$ be the prefix from $h$ to $r$. Every vertex of $\Gamma$ before $r$
is outside $X$. Since $X$ is connected, choose a simple path $Q$ inside $X$
from $r$ to $w$. The supports of $\Gamma$ and $Q$ meet only at $r$, so
$\Gamma Q$ is simple. It avoids the deleted port: $\Gamma$ is a prefix of the
anchored path, while $Q$ lies in $X$ and the other endpoint $h$ of the port
does not. Thus $(\Gamma,Q)$ is an actual receiver-entry return. This is the
elementary content needed from C-2. The
$b(F)$ half-edges are only the formal terminals at which such a channel may
enter or leave $F$; they are not silently identified with completion ports.
If an exposure enters a two-pole region whose two outside ends have
coalesced, its two inside terminal incidences are kept distinct and the
lexicographically first simple path between the two inside terminals is used
as an internal exposed route.  Such a path exists by connectedness.  If the
two incidences have the same inside endpoint, that cubic vertex is a branch
vertex and the region is split there first.  The stronger spectral paths of
C-10 and C-11 remain on the ledger but are not needed for this elementary
exposure.  No profile context $Y$, alternative realization $S_1$, or profile
event $E$ is used in the construction.

---

## 8. The new local move: marked cubic trace--ear exhaustion

The point not accounted upstream is that many silent traces cannot occupy the
cyclic part of $F$ independently.  The following lemma records the exact
local statement needed by the count.

### Proposed Lemma 8.1 (marked trace--ear lemma; not proved)

For every component $F$ above there are

- pairwise vertex-disjoint connected induced subgraphs
  $K_1,\ldots,K_p\subseteq F$;
- a set $Z$ of $B$ distinct vertices of
  $F\setminus\bigcup_iV(K_i)$; and
- an injection
  \[
  \iota:U(F)\longrightarrow\{K_1,\ldots,K_p\}\mathbin{\dot\cup}Z
  \]

with the following properties.

1. Every $K_i$ is receiver-free and has exactly two boundary edges in $F$.
   Equivalently, every vertex of $K_i$ has ambient degree three and
   \[
   \sum_{x\in K_i}(3-d_{K_i}(x))=2.                 \tag{8.1}
   \]
2. After contracting each $K_i$ to a marked degree-two vertex, adjoining the
   $b(F)$ boundary leaves and suppressing every other degree-two vertex, the
   resulting connected multigraph $Q_F$ has $B$ cubic branch vertices and
   cycle rank $\beta_F\le p$.

Consequently
\[
 |U(F)|\le p+B,qquad |F|\ge8p+B,qquad B\le b(F)+2p.       \tag{8.2}
\]

### Attempted proof

The following is the attempted exhaustion. The audit in §12 shows that the
multi-boundary cyclic case is not exhausted and that the asserted injection
of rank tokens into terminal shells does not follow.

**The exposure state.**  Adjoin the $b(F)$ formal boundary leaves to $F$.
An exposed route is the $F$-part of an actual receiver-entry return from §7,
or a tagged lexicographically first internal terminal path when the two
exterior ends have coalesced.
At any stage let $D$ be the union of the routes already exposed.  The active
regions are the induced connected shores cut off by the first and last
contacts of a canonical trace with $D$; their interiors are chosen
inclusion-minimally.  Each active region carries precisely the still
unassigned members of $U(F)$ in its interior and all of their original
branch-state data.  We order active states by
\[
 \mu=(\#\hbox{ unassigned marks},
      \sum_A|V(A)|,
      \#\hbox{ unsuppressed active edges})           \tag{8.3}
\]
lexicographically.  When a region is replaced by several regions, the sums
in (8.3) are over their disjoint interiors.

**One exposure.**  Take the first unassigned mark $u$ in the fixed order and
read its canonical trace from $r(F)$ towards $u$.  Up to the last point at
which it follows $D$ there is nothing to decide.  At the next edge exactly
one of the following happens.

1. The trace never leaves $D$.  If the containing route is tagged as an
   actual receiver-entry channel, it is a terminal segment of that channel,
   so $u$ is visible.  This is excluded by the definition of $U(F)$ (and, at
   an overloaded port, is one of the already closed exits (1)–(3)).  If the
   containing route is an internal terminal route, its two ordered terminal
   incidences delimit a two-pole active region; the mark is passed to that
   region, where the two-mark argument below either splits it or leaves the
   unique terminal shell.  Thus the internal-route case does not pretend to
   prove visibility.
2. The new segment first returns to $D$ at a vertex different from its first
   contact.  Its first and last contacts bound an ear.  Add the ear to $D$
   and replace its shore by the inclusion-minimal induced shore with those
   two contact incidences.  If the shore has a third boundary incidence, use
   the first one in the fixed edge order: the first vertex at which the three
   routes separate is put in $Z$, a mark there (if any) is assigned to that
   vertex, and the remaining marks pass to the strict components after that
   vertex is deleted.  If there is no third incidence, the shore is a
   two-pole active region.
3. The new segment has no second contact with $D$.  Continue from its loose
   end through unused edges.  Finiteness gives either a first return to $D$
   (case 2), a boundary half-edge, or a repeated vertex.  A repeated vertex
   is shortened to its first repetition and again gives an ear.  At a
   boundary half-edge, let $C$ be the component of $G-X$ incident with that
   half-edge.  If $C$ is the component of the outside connector already in
   $D$, a path in $C$ closes the new segment to an actual receiver-entry
   return whose channel contains $T_u$, contrary to silence.  If it is a
   different component, that half-edge is retained as a new terminal of the
   active route diagram.  A region with only one retained boundary edge
   would make that edge a bridge of $G$, contrary to B-1.  Hence this case
   again gives either a branch vertex or a two-pole region.

This list is exhaustive because every vertex of $F$ has three incidences when
the formal boundary half-edges are counted.  Notice also that it handles the
apparently exceptional lobe whose two boundary edges meet the same outside
vertex: delete that outside vertex and regard the two incidences as distinct
ordered poles.  Connectedness supplies the terminal-to-terminal route used as $D$.
If that route and the current trace do not have distinct first and last
contacts, their first repeated contact is a cubic branch vertex; if they do,
they give case 2.  Thus a one-vertex attachment is not discarded as a new
residual.

**Why a two-pole region with two marks splits.**  Let $A$ be such a region and
let $u\ne v$ be its first two marks.  Compare the two canonical traces from
the receiver side.  If their first divergence has two different later
contacts, those contacts give the ear of case 2.  Otherwise one trace is a
terminal segment of the other until the first unused incidence.  Start at
the other pole and seek a path to that unused incidence avoiding the common
terminal segment.  If it exists, concatenating it with the common segment
has two readings, according to the tag of the parent route.  For an actual
receiver-entry route, adjoining the exposed outside connector makes a simple
actual channel containing one of $T_u,T_v$, so that mark is visible.  For an
internal terminal route, the new path and the tagged route have distinct
first and last contacts and hence give the strict ear of case 2; if their
contacts coincide, the common contact has three continuations and is the
branch case.  If the avoiding path does not exist, the elementary vertex form
of Menger's theorem gives a separating vertex on the common segment.  Its
three incident directions are the parent route and the two marked sides; it
is again the branch vertex of case 2, and deletion of it puts the two marks in
strict active regions.  This proves that a terminal two-pole region contains
exactly one unassigned mark.

This paragraph also covers overlap of more than two basins: take the first
pair in the canonical order.  It is precisely the D05 overlap consumer.
No target-defect event is substituted for either trace.  The only paths in
the Menger argument are subpaths of $F$ and of the actual exposed connector.

**Uncrossing.**  If two two-pole shores cross, edge-cut submodularity gives
\[
 |\delta(A\cap A')|+|\delta(A\cup A')|
 \le |\delta(A)|+|\delta(A')|=4.                    \tag{8.4}
\]
Neither nonempty shore has cut size zero, and cut size one is forbidden by
bridgelessness.  Hence both new shores have cut size two.  Replacing the
crossing pair by its intersection and union preserves every mark in the
union and makes the ordered pair laminar; marks outside the intersection stay
active in the corresponding difference region of the union.  Repeating this
finite uncrossing leaves pairwise disjoint terminal shores.  These are the
$K_i$.  A terminal shore receives its unique mark; a mark met at a cubic
separation vertex receives that vertex.  The preceding paragraph shows that
no two marks receive the same object, proving the injection.

**Termination and cycle rank.**  Assigning a mark decreases the first
coordinate of (8.3).  Replacing a shore by strict shores moves at least one
contact path into $D$, and therefore decreases the second coordinate or,
when the vertex sets agree, the third.  Thus every arm closes or strictly
decreases $\mu$, so the construction terminates.

Contract the terminal shores and suppress the unmarked degree-two chains.
Orient every exposed ear by its exposure time.  A tree extension does not
increase rank.  An ear whose two ends already lie in the same exposed
component increases rank by one and places one rank token on its
inclusion-minimal two-pole shore.  Tokens are followed down the laminar
family.  If two tokens were to reach the same active shore, compare the two
corresponding ears after their last common segment.  Their first distinct
contacts either give two disjoint strict shores, one for each token, or give
three continuations at their first common contact, in which case that contact
is retained as a branch vertex and deletion again puts the two ear interiors
in different strict regions.  This is the same first-divergence argument as
for two marks, now with the two ear interiors in place of $T_u,T_v$.
Consequently no terminal shore receives two rank tokens.  The number of rank
tokens is exactly the cycle rank left after contraction and suppression, so
$\beta_F\le p$.
All remaining nonleaf, nonshell vertices have degree three, and they are
exactly the vertices counted by $B$.  The handshake identity in the connected
multigraph $Q_F$ is
\[
 B=b(F)-2+2\beta_F\le b(F)+2p.                      \tag{8.5}
\]
The assertion that the shells are disjoint and avoid the branch vertices
depends on the missing rank-token injection. That injection is not produced,
so the argument proves neither $|F|\ge8p+B$ nor (8.2); see §12.

---

## 9. The terminal shell estimate

### Lemma 9.1 (a target-free cubic two-pole shell has at least eight vertices)

Let $K$ be a connected simple graph all of whose vertices have ambient degree
three and with exactly two edges leaving $K$.  If $K$ contains no cycle of
power-of-two length, then $|K|\ge8$.

### Proof

The degree sum is
\[
 2|E(K)|=3|K|-2,                                    \tag{9.1}
\]
so $|K|$ is even.  The case $|K|=2$ would require two parallel internal
edges and is impossible in a simple graph.  If $|K|=4$, then $|E(K)|=5$, so
$K=K_4-e$ and contains a $4$-cycle.

It remains to exclude $|K|=6$.  Equation (9.1) gives $|E(K)|=8$, and the
total internal deficiency is two; hence at most two vertices have degree
below three.  Bondy--Vince (I-2) supplies two cycles whose lengths differ by
one or two.  Since a $4$-cycle is already a target, in a target-free graph on
six vertices the possible cycle lengths are $3,5,6$, and every pair among
these differing by one or two contains a $5$-cycle.  Let $C$ be such a
$5$-cycle and let $x$ be the sixth vertex.  Besides the five edges of $C$
there are exactly three edges.  If $d_K(x)\le2$, at least one of them is a
chord of $C$; that chord together with the three-edge arc of $C$ is a
$4$-cycle.  If $d_K(x)=3$, the three neighbours of $x$ on $C$ include two at
cyclic distance two; their two edges to $x$ and the two-edge arc between them
again form a $4$-cycle.  Both cases contradict C-1.  Thus the next possible
even order is eight.  $\square$

This is the sole use of I-2.  In particular the proof does not assume the
appendix's quiet-block estimate and does not enumerate bounded graphs.

---

## 10. Arithmetic of the failed trace--ear draft (not a transition)

### 10.1 The exact component inequality

The draft substituted the unproved displays (8.2) and (8.5) into the following
calculation. Because (8.2) has no producer, the calculation records no fact of
the node-[181] residual. Its algebra is retained for audit:
\[
\begin{aligned}
 10|U(F)|
 &\le10(p+B)\\
 &=3(8p+B)+7(B-2p)\\
 &\le3|F|+7b(F).
\end{aligned}                                       \tag{10.1}
\]
Summing over the full-vertex components and using (7.3) gives
\[
 10|U_X|\le3n_3+7b_X
             \le3n_3+14n_2+7n_1.                  \tag{10.2}
\]
Combine this with the retained visible-first lower bound (7.2):
\[
 10(n_3-3n_2-7n_1)
 \le3n_3+14n_2+7n_1,
\]
and hence
\[
 7n_3\le44n_2+77n_1.                               \tag{10.3}
\]
Using (7.1),
\[
\begin{aligned}
 7|X|
 &=7(n_3+n_2+n_1)\\
 &\le51n_2+84n_1\\
 &\le51(n_2+2n_1)=51\defp(X).
\end{aligned}                                       \tag{10.4}
\]
Thus every negative, zero-surplus, no-handoff Type A component in the full
unified collection satisfies the exact estimate
\[
 |X|\le\frac{51}{7}\defp(X).                       \tag{10.5}
\]
The argument used the full $U_X$, including every member later recorded as a
peel.  Therefore (10.5) closes the original [123] continuation and, a
fortiori, its complete [181] descendant; it does not prove a surrogate about
the reduced list.

### 10.2 Summing without dropping a component

Use the canonical decomposition B-3.  A component with $\No(X)\ge0$ satisfies
$|X|\le4(\defp(X)-\sigma(X))\le4\defp(X)$ and hence (10.5).  A negative
zero-surplus no-handoff component satisfies (10.5) by §10.1.  A negative
handoff or positive-surplus component is already in the Type B ledger; all
of it is closed except the bridge residual of total mass
$M_B\le16\sigma(G)$.  Consequently the exact pre-asymptotic statement is
\[
 7|R|\le51\defp(R)+7M_B.                            \tag{10.6}
\]
This summation includes nonnegative components, the unified collection,
handoff pieces and the bridge residual exactly once.  No piece and no surplus
unit disappears.

Since $|R|=(1-13\theta)n=\Omega(n)$, A-2 gives
$M_B=o(|R|)$ and $\sigma_R\le\sigma(G)=o(|R|)$.  A-7 bounds
$\defp(R)-\sigma_R$; adding the preceding estimate for $\sigma_R$ gives
\[
 \defp(R)\le\tau^*|R|+o(|R|),
 \qquad
 \tau^*=\frac{15\theta^*}{1-13\theta^*}.            \tag{10.7}
\]
The margin is strict.  Indeed
\[
 \theta^*=\frac{3/4}{118.108581006-39/4-15}
           =0.008033\ldots <\frac7{856},
\]
and direct cross-multiplication shows
\[
 \frac{15\theta^*}{1-13\theta^*}<\frac7{51}
 \quad\Longleftrightarrow\quad 856\theta^*<7.       \tag{10.8}
\]
Substitution of (10.7) into (10.6) now gives
\[
 |R|\le\frac{51}{7}\tau^*|R|+o(|R|),               \tag{10.9}
\]
where $(51/7)\tau^*=0.9803\ldots<1$.  Dividing by
$|R|$ contradicts (10.9) on the branch.

The earlier draft tried to read G-7 and I-4 as an exactification of the
$o(|R|)$ terms and to reuse [173] for (10.8).  That reuse is not justified:
[173] decides a different integer collision.  The repaired simultaneous
account in §0 does not make that inference.  It derives the sharpened cap from
the retained orbit keys and uses the literal large-$r$ arm to obtain the exact
eventual inequality (0.36).  Hence the numerical producer is now present.

The trace--ear calculation nevertheless does not close node [181], because
its first local input (8.2) is still not produced: the multi-boundary cyclic
arm does not yield the asserted forest or decrease its measure.  Arithmetic
cannot repair that earlier structural failure.

---

## 11. Candidate exhaustion ledger (not an admitted proof DAG)

The following table records what the attempted proof intended to establish.
It is not a list of descendants that may be added to the proof graph.  A row
is admissible only when its status says that it is a certificate or a closed
arm; every failed row must remain outside the proof DAG.

| Move | Fact or claimed output | Required progress | Audited status |
|---|---|---|---|
| actual/profile record | every canonical demand record at [181] is profile-only | the actual disjunct contradicts reconstruction of $G$; append the profile-only consequence without creating a child | **valid certificate** |
| degree-zero receiver | $n_0(X)=0$ and $q(w)\in\{1,2\}$ | the $q=3$ case contradicts connectedness and negative charge | **valid certificate** |
| trace follows one exposed channel | the oriented trace is a terminal segment of one actual channel | visibility contradicts membership in $U(F)$ | **closed** |
| first divergence and rejoining | an actual ear and an induced shore | prove the shore proper and transport every mark before claiming fewer vertices or edges | **failed: neither properness nor transport is proved** |
| three continuations | a distinct cubic articulation vertex | delete it and pass marks to strict components | **failed: a multi-terminal region need not have an articulation** |
| dangling continuation | a same-component outside path, or a different-component terminal | the first must give a simple visible return; the second must have a consumer or shrink the shore | **closed on the first arm; failed on the second** |
| crossing two-pole shores | laminar intersection/union shores | preserve every mark and decrease a declared measure while obtaining disjoint terminal shores | **failed** |
| terminal two-pole shore | one mark assigned to one shell | decrease the unassigned-mark count | **failed: neither the shore nor uniqueness is produced** |
| shell orders $2,4,6$ | impossible by simplicity, a $C_4$, or Bondy--Vince plus a $C_4$ | surviving shell has at least eight vertices | **valid certificate** |
| component/global sum | (10.5), then (10.6) | pay every component exactly once | **algebra only: the forest input is absent, so no branch fact is produced** |
| final rate | coefficient strictly below one | use the retained orbit cap and the literal large-$r$ arm | **valid by (0.34)--(0.36), but unusable here because the forest row fails first** |

The recursive measure (8.3) would certify termination only after every arm is
shown to decrease it. The union-of-routes arm, the multi-boundary cyclic arm,
the different-outside-component arm, the separator-of-order-at-least-two arm,
and the crossing-shore replacement do not have such a proof, so none may be
installed as a descendant and the displayed measure does not certify a
recursion.
The ledger is monotone: R1–R3, the profile tokens, essential cores and deletion
witnesses, demand/absorption/blocker assignments, window data, entropy and rank
facts, gadget and contraction facts, and every exit exclusion remain attached
throughout.  Some are not needed in the final numerical line, but none is
projected away.

The failed draft suggested the following interface names. They are not Lean
implementation obligations because the required producer is absent:

1. `canonicalDemandRecord_profile_only`, proved from the owned-decomposition
   reconstruction isomorphism and target invariance;
2. `negative_typeA_no_degree_zero`;
3. `markedTraceEarExhaustion`, which is **not yet available**: it would have to
   return $p,B,b$, the injection, disjoint two-pole shells and $\beta\le p$
   while taking the complete [181] ledger as its input;
4. `targetFreeTwoPole_eight_le`, the proof of §9;
5. `negativeTypeA_card_le_51_sevenths_defect` and the exact aggregate form
   (10.6).

At the entrance to this retired attempt, the live [181] proposition is
exactly
`Route8StageRateFailedFact ∧ Route8DemandLedgerStatement ∧
Route8DemandAbsorptionStatement ∧ Route8WindowBlockersStatement`. The five
suggested trace--ear interfaces above do not exist, because the attempt does
not prove them. The current implementation instead retains that conjunction
on its full inherited `ExactLedger`, derives the maximal-ledger residual at
[183], and then appends (0.4) through
`route8UnifiedVisibleResidualRow` and then appends the overload package and
zero non-overload count through `route8UnifiedVisibleOverloadRow`. It does not
return `False`; its exact frontier is node [185].

---

## 12. Airtightness audit of the attempted closure

The full node-local red-team report is
[`audits/erdos-64-red-team/reports/node-181.md`](audits/erdos-64-red-team/reports/node-181.md).
Its verdict for the trace--ear proposal is **NONEXHAUSTIVE**. The audit
preserves all incoming facts and separates the valid textbook consequences
from the unsupported trace--ear producer. It is independent of the implemented
shortest-trace boundary-support reduction in §0.

### 12.1 What is valid

1. The live proposition (4.1) and the append-only `ExactLedger` reading are
   exact.
2. The arguments $n_0(X)=0$, (7.1), the silent-excess lower bound (7.2), and
   the boundary count (7.3) are valid on the stated Type A support.
3. Full vertices in one component $F$ have the same set of traceable receivers
   and hence the same receiver selected by the fixed order.
4. Lemma 9.1 is valid. Total internal deficiency two leaves at most two
   vertices of degree below three, exactly the hypothesis of Bondy--Vince
   Theorem 1; the orders $2,4,6$ are then excluded by the written elementary
   argument.
5. The substitutions in (10.1)–(10.5) are arithmetically correct, but their
   input (8.2) is unproved and therefore none is a branch fact.

The port-return sentence in §7 has been repaired as follows. From an anchored
return, take the prefix ending at its first entry into $X$; every
earlier prefix vertex is outside $X$. Join that first-entry receiver to the
terminal receiver by a simple path inside connected $X$. The two paths meet
only at the first entry, their concatenation is simple, and it avoids the
deleted port. This produces a genuine receiver-entry return. The earlier
first/last-visit split did not ensure that the connector stayed outside $X$.

### 12.2 First unhandled residual

The first nonlocal inference is case 2 of “One exposure.” If an induced ear
shore has a third boundary incidence, the proof chooses that incidence and
asserts a “first vertex at which the three routes separate.” A two-connected
three-terminal cyclic region need not have a single vertex whose deletion
separates the three routes. Cubicity limits local degree; it does not create
an articulation vertex. No fact in (4.1), no retained exit exclusion, and no
ancestor of [181] supplies that articulation. The cold-branch overlap
consumers [169]–[172] are not on this branch.

This arm neither closes nor replaces the active region by strict active
regions. It can return the same cyclic region with the same unassigned marks,
so it does not decrease any coordinate of $\mu$ in (8.3). It is therefore a
literal violation of the residual-shrink rule, not a presentational omission.

### 12.3 Further failed inferences

- If a trace is contained in the **union** $D$ of exposed routes, it may switch
  between intersecting routes. Containment in the union does not make it a
  suffix of one actual receiver-entry channel, so case 1 does not establish
  visibility.
- In the two-mark paragraph, failure of a path avoiding an entire common
  segment says that the segment contains a separator. Vertex Menger does not
  imply that a separator of order one exists; a minimum separator can have two
  or more vertices.
- Cut submodularity can make crossing cut-two shores laminar under additional
  nonempty/proper checks. Intersection and union are nested, however, not
  pairwise disjoint, and the proof does not preserve and reassign all marks in
  the difference regions. Moreover, the number of crossings is not a
  coordinate of $\mu$; an uncrossing can leave all three coordinates in (8.3)
  unchanged.
- In the dangling-continuation case, retaining a terminal in a different
  outside component adds information to the route diagram but does not by
  itself replace the active shore by a strict shore or route it to a closed
  consumer.
- The rank-token paragraph assumes the missing conclusion. Independent ears
  can end in one multi-boundary cyclic core; first divergence does not give a
  distinct cut-two terminal shore for each ear. Thus $\beta_F\le p$ has no
  proof.

A minimal abstract stress test is a triangle with one formal boundary leaf at
each vertex. The reduced diagram has $b=3$, three cubic branch vertices,
cycle rank one, and no induced cut-two shore. Hence $p=0$ and the asserted
$\beta_F\le p$ would read $1\le0$. This is not claimed to be a realization of
the full node-[181] counterexample ledger; it isolates the exact topological
inference that the local argument lacks.

### 12.4 A standalone forest-count identity (not a transition)

The following is a complete identity about an already given forest
configuration; it does not assert that node [181] produces such a
configuration. Fix pairwise disjoint two-pole shells $K_1,\ldots,K_p$, a set
$Z$ outside them, and an injection
\[
 U(F)\longrightarrow\{K_1,\ldots,K_p\}\mathbin{\dot\cup}Z,
\]
and an embedded forest whose leaves are among the $b(F)$ boundary leaves and
the two formal poles of each shell, with every member of $Z$ of forest degree
at least three. The forest leaf identity gives
\[
 |Z|\le b(F)+2p.
\]
Lemma 9.1 and disjointness give $|F|\ge8p+|Z|$, while injectivity gives
$|U(F)|\le p+|Z|$. Therefore
\[
 10|U(F)|
 \le10(p+|Z|)
 =3(8p+|Z|)+7(|Z|-2p)
 \le3|F|+7b(F).
\]
This proof is complete, local, and uses only textbook moves. What is not
proved is that the full node-[181] residual produces this forest certificate.
Splitting on its existence would not repair the proof: the negative arm can be
the same multi-boundary cyclic core and hence would not shrink the residual.

### 12.5 Global ledger check

The global-rate part of this old audit is superseded by the simultaneous
account in §0.  The sharper $\theta^*,\tau^*$ estimate is derived there from
the retained realized-window and relabelling-orbit keys, and (0.35)--(0.36)
turn its positive constant margin into an exact inequality on the literal
large branch.  Node [173] is not reused.  This repair does not validate the
trace--ear transition: that proposal still fails earlier, at the missing
forest certificate identified in §§12.2--12.4.

### 12.6 Transition-by-transition progress audit

For this audit a *child residual* means the complete state carried after a
case distinction, not merely the active shore drawn in the local picture.  A
deterministic construction may append a proved certificate without creating
a child.  Every genuine child must either be closed or carry the whole
incoming ledger together with a strict decrease of
\[
 \mu=(M,V,E),
 \qquad
 M=\#\text{unassigned marks},\quad
 V=\sum_A|V(A)|,\quad
 E=\#\text{unsuppressed active edges}.
\]
The following table checks every transition used in the attempted proof.

| Transition | Exact incoming predicate | Textbook move | Output on each arm | Progress verdict |
|---|---|---|---|---|
| Construct one port return | a completion-port edge of a connected support in bridgeless $G$ | delete the edge, shorten a return walk, take the prefix to the first entry into $X$, then join inside connected $X$ | an actual simple receiver-entry return, appended as a certificate; no child residual | **valid certificate step** |
| Trace already exposed | $T_u$ is an oriented terminal segment of one tagged actual channel | take the corresponding connector--channel subpath | $u$ is visible, contradicting $u\in U(F)$ | **closed** |
| Trace contained only in the union | $T_u\subseteq D$, but it is not an oriented terminal segment of one tagged actual channel | none | the same active region and the same mark $u$ | **invalid: $\mu$ unchanged** |
| Proper two-contact ear | the new trace segment has two distinct contacts and its chosen induced shore is proper with exactly two boundary incidences | first/last-contact ear extraction | a strict two-pole active shore, carrying every inherited fact whose objects lie in it and retaining the ambient ledger | **invalid transition: the move does not prove properness or transport, so no child is created** |
| Third incidence with a cut vertex | three relevant route sectors meet a vertex $z$ whose deletion separates their marked interiors | articulation decomposition | assign at most the mark at $z$ to $z$ and pass all other marks to strict components of $A-z$ | **valid: $M$ decreases, or $V$ decreases by deletion of $z$** |
| Third incidence without such a cut vertex | the ear shore is a two- or three-connected multi-terminal cyclic region | cubicity alone gives no separator | the same cyclic region with the same marks and edges | **invalid: $\mu$ unchanged** |
| Loose end returns to $D$ or repeats | the continuation first meets $D$, or first repeats a vertex | shorten at the first contact/repetition | the preceding two-contact-ear case | **inherits that case's invalid verdict** |
| Loose end reaches the same outside component | the outside connector and the new boundary incidence lie in one component and can be joined without meeting the channel internally | path shortening and concatenation | an actual channel containing $T_u$, hence visibility | **closed** |
| Loose end reaches a different outside component | the new boundary incidence belongs to another component of $G-X$ | retain the incidence as a terminal | the same active shore with one more terminal tag | **invalid: no coordinate of $\mu$ decreases** |
| One-edge shore | the retained incidence is the only edge from an actual nonempty proper shore to its complement | bridge criterion | contradiction to B-1 | **closed**, but only for an actual cut of $G$, not for a formal route-diagram boundary |
| Two marks, avoiding path exists | the required path avoids the whole common trace segment, and its concatenation is simple | path concatenation / first--last contact | visibility on an actual-route tag, or a strict ear on an internal tag | **actual-route arm closed; internal-tag arm invalid because no proper transported child is produced** |
| Two marks, separator of order one | the avoiding path fails and a one-vertex separator $z$ is independently proved | vertex separation | strict components of $A-z$ | **valid: $V$decreases** |
| Two marks, separator of order at least two | the avoiding path fails but the minimum separator has size at least two | vertex Menger gives only the separator set | the same two-connected cyclic core | **invalid: the claimed one-vertex child does not exist** |
| Uncross two cut-two shores | both intersection and union are nonempty proper shores and all four cut lower bounds are established | cut submodularity | a laminar pair $A\cap A'\subseteq A\cup A'$ | **invalid: the shores are nested, not disjoint; marks in the differences are unassigned; $\mu$ has no crossing coordinate** |
| Create a rank token | a new ear raises cycle rank | ear-decomposition rank identity | a token is asserted to lie on a new terminal cut-two shore | **invalid in a multi-boundary cyclic core: no such shore follows** |
| Terminal shell | a receiver-free induced shore with exactly two leaving edges has been produced | degree sum and Lemma 9.1 | at least eight vertices paid to that shell | **closed certificate** |
| Forest count | the disjoint shells, injection, and embedded forest of §12.4 have all been produced | the forest leaf identity | $10|U(F)|\le3|F|+7b(F)$ | **standalone arithmetic only: the preceding moves do not produce this input** |

Thus the first failed child is not a later numerical edge: it is the
multi-terminal cyclic child in the third-incidence arm.  The same failure
reappears in the union-of-routes, different-outside-component,
higher-separator, uncrossing, and rank-token arms.  Adding any of those arms
as a descendant of [181] would violate monotonicity because its complete
state has the same $M,V,E$ as its parent. The implemented reduction never
creates any of these children: Theorem 0.3 proves that their required silent
mark set is empty before a trace--ear state is formed, while retaining the
broad unified entry family.

### 12.7 No retained fact removes the nonshrinking child

The Lean producer makes the retention check literal.  Its output index is
\[
 [\texttt{peeledResidual},\texttt{windowBlockers},
   \texttt{demandAbsorption},\texttt{demandLedger},
   \texttt{stageRateFailed},\texttt{peelingDescent}]
 \mathbin{+\!+}\texttt{known}.
\]
In particular the required keys `route8UnifiedNegative`, `typeAExclusion`,
`typeBBridgeReduction`, `route8PiecesClassified`, `typeBBridgeSublinear`,
`route8ExtractedEntryCensus`, `typeBSublinearLedger`,
`route8UnifiedDeficit`, `route8QuotientFree`, `typeAReceiverRouting`,
`route8UnifiedEntryCensus`, and `selection` remain in `known`.  The proposed
local proof is therefore not permitted to forget any of them.  Checking them
by mathematical content, rather than by name, gives:

| Retained ledger block | What it actually supplies on the cyclic child | Why it does not close or shrink that child |
|---|---|---|
| A, B | subcubic/full-degree incidence, connectedness, bridgelessness, boundary profiles, and absence of a proper internal $3$-core | bridgelessness excludes cut size one but permits two- and three-connected multi-terminal cyclic regions; none of these facts creates an articulation or cut-two shore |
| C | target avoidance, actual returns, length exclusions, and the gadget/contraction conclusions under their exact terminal hypotheses | visibility is available only after one actual simple channel containing the whole canonical trace is constructed; a union of routes or a profile context is not such a channel, and a multi-terminal core is not a two-terminal gadget |
| D | canonical choices, label data, and symmetry | a tie-break chooses among existing objects; it neither creates a separator nor turns a laminar family into disjoint marked shores |
| E | minimality, replacement exclusion, quotient rules, and the completed peel descent | minimality can be invoked only after constructing an admissible smaller target-complete representative; no such representative is produced from the cyclic child, while another peel only re-encodes the already recorded mass |
| F | essential response supports, declared deletion witnesses, quotient-freeness, and the trace-local target-defect alternative | these are statements about response coordinates and boundary-compatible realizations. The surviving `CanonicalDemandRecord` is in its profile disjunct, whose outside context is explicitly non-actual; it supplies no path or separator in $G$ |
| G, H | the exact deficit, disjoint incidence ledger, failed stage rate, maximal absorption, and blocker partition | these facts prove how many unpaid units remain and prevent double counting; they do not inject those units into vertices or two-pole shells of the cyclic core |
| I | the $P_{13}$-free theorem, finite constants, exact previously registered collision, and Bondy--Vince | HSS applies to a graph of minimum degree at least three, not to the present multi-boundary piece; Bondy--Vince yields the proved eight-vertex bound only after a cut-two shell has been produced; [173] decides a different comparison |

This table also rules out the tempting misuse of the demand token.  In the
live definition `TraceLocalTargetDefect` is a context-distinguishability
statement about a retained reading.  `CanonicalDemandRecord` is a disjunction
of an actual-exterior record and a record in a context unequal to the actual
exterior.  Target avoidance eliminates the first disjunct on this branch, so
only the second remains.  Treating its certificate, event, or corridor as a
path in $G$ would drop the inequality of contexts and hence drop an upstream
fact.

### 12.8 Final audit verdict for the trace--ear attempt

Accordingly, the honest present conclusion is: Lemma 9.1 and the displayed
coefficient arithmetic are sound, but Proposed Lemma 8.1 is nonexhaustive,
its supposed recursive residuals do not all shrink, and node [181] is not
closed by §§7–11.

---

## 13. Retired block--cut shore draft (not part of the proof)

**Audit status.** The material in §§13–20 is retained only to preserve any
independently useful shore identities. Its proposed transition is invalid for
the actual node-[181] input because Lemma 15.1 assumes every unpaid owner is
silent. The live unified family also contains visible-first excess entries.
Consequently Proposition 16.3 is unavailable, the block--cut recursion is not
exhaustive, and none of §§13–20 may be cited as closing [181] or [183]. The
implemented proof chain is Theorems 0.1–0.4 above, ending at [185].

**Reading convention for §§13–20.** Identities about an already given
ambient-cubic shore remain ordinary proved identities. Any statement using a
newly rebuilt shore ledger, the assertion that every unpaid or open owner is
silent, or recursive application of Proposition 16.3 is false as a
node-[181] transition and is labeled as such below. No extra hypothesis is
introduced to rescue it. The remaining calculations are retained only to
show what is independently correct and exactly where the implication breaks.

The conclusion of §12.8 concerns only the trace--ear proposal of §§7--11.
The retired draft below does not use Proposed Lemma 8.1 or a trace ear. It
attempted to enrich the node-[181] state at every stage to

\[
   \mathcal B_{181}[S,\mathscr L_S]
   :=(\mathcal B_{181};S,\delta_G(S),\mathscr L_S),       \tag{13.1}
\]

where the first coordinate would be the complete immutable ledger of §§1--4,
\(S\) is the current connected induced shore inside one member of
\(\widetilde{\mathcal X}\), and \(\mathscr L_S\) is the canonical local
restriction of the already established receiver, trace, response-support and
demand interfaces.  In particular, (R1)--(R3), every peel witness, every
closed exit, the relabelling cap, and the original support remain in the
state. This notation records the intended monotone bookkeeping; it does not
prove that \(\mathscr L_S\) exists with the claimed inherited properties.

For a nonempty vertex set \(S\subseteq V(G)\), write

\[
 b(S):=|\delta_G(S)|.
\]

Every vertex of every shore considered below has ambient degree three.
Consequently

\[
 b(S)=\sum_{v\in S}(3-d_S(v))=3|S|-2|E(G[S])|.          \tag{13.2}
\]

The draft proposed the following textbook move.

> **Retired block--cut transition.** Take the first open demand unit in the canonical
> shore ledger and its silent owner \((S,w,u,B_u)\).  Visibility forces
> \(d_S(w)=2\) and forces \(S-w\) to have exactly two components.  Replace
> the active shore \(S\) by those two components, retaining the whole parent
> ledger.

If a silent open owner on a transported shore ledger had been available, the
resulting split would use B03 and would have the exact progress measure

\[
        M(\mathscr F):=\sum_{S\in\mathscr F}|S|.          \tag{13.3}
\]

Such a block--cut move replaces \(S\) by \(K,H\) with
\(|K|+|H|=|S|-1\).  Hence it changes \(M\) to \(M-1\), not merely to a
lexicographically selected subproblem.  The removed separator vertex is not
discarded: it appears as the \(+1\) in the order identity and as the exact
\(+1\) in the boundary identity proved in §16.

The remainder of the retired draft attempted to establish the three facts
needed to iterate this move:

1. the local burden and pressure interfaces transport to every derived
   shore (§§14--15);
2. every open unit supplies the stated strict block--cut decomposition
   (§16);
3. a shore on which no unit is open either satisfies the required
   \(7b-8\) estimate or already contains a forbidden \(4\)- or \(8\)-cycle
   (§17).

The first item is not established on the incoming residual: rebuilding the
ledger on \(S\) neither preserves the original indexed family nor eliminates
its unpaid visible-first entries. Consequently the second and third items do
not form an exhaustive recursion. Sections 18–19 retain only the arithmetic
and bookkeeping identities of that failed draft, not a transition.

---

## 14. Elementary shore identities and the claimed interface transport

### Definition 14.1 (derived shore)

Fix \(X\in\widetilde{\mathcal X}\).  A *derived shore of \(X\)* is obtained
recursively as follows.

- The root shore is \(V(X)\).
- If \(S\) is a derived shore and the block--cut move selects \(w\in S\),
  the two connected components of \(G[S]-w\) are its children.

The choice is canonical: use the first open unit in the retained demand-unit
order, then the first owner in the retained entry order.  Thus this is one
well-founded recursion, not an uncontrolled family of choices.

### Lemma 14.2 (elementary shore identities)

Every derived shore \(S\) has the following properties.

\[
\begin{array}{ll}
\text{(a)}&\varnothing\ne S\subseteq V(X),\quad G[S]\text{ is connected and induced};\\
\text{(b)}&d_G(v)=3\text{ for every }v\in S;\\
\text{(c)}&b(S)=3|S|-2|E(G[S])|\text{ and }b(S)\equiv |S|\pmod2;\\
\text{(d)}&b(S)\ge2;\\
\text{(e)}&G[S]\text{ is }P_{13}\text{-free and every nonempty induced}\
&\qquad\text{subgraph of }G[S]\text{ has a vertex of degree at most }2;\\
\text{(f)}&G[S]\text{ contains no power-of-two cycle.}
\end{array}                                                   \tag{14.1}
\]

#### Proof

The root has (a) and (b) by the definition of a Type A support.  A child is a
connected component after deleting one vertex from an induced graph, hence is
again a nonempty connected induced vertex set; ambient degrees do not change.
This proves (a) and (b) inductively.  Summing ambient degree three over \(S\)
gives

\[
 3|S|=2|E(G[S])|+|\delta_G(S)|,
\]

which proves the equality and parity assertion in (c).

The packing is nonempty because the counterexample contains an induced
\(P_{13}\), so \(S\subseteq R\subsetneq V(G)\).  Since \(G\) is connected,
\(b(S)>0\).  If \(b(S)=1\), the unique edge of \(\delta_G(S)\) disconnects
\(S\) from its complement and is a bridge of \(G\), contrary to B-1.  Hence
\(b(S)\ge2\), proving (d).

An induced subgraph of the \(P_{13}\)-free graph \(G[X]\) is
\(P_{13}\)-free.  By A-9, every nonempty \(P_{13}\)-free induced subgraph
of \(G\) has a vertex of internal degree at most two.  This proves (e),
including the empty internal \(3\)-core condition.  Finally any cycle of
\(G[S]\) is a cycle of \(G\), so C-1 proves (f). \(\square\)

### Failed Claim 14.3 (boundary-interface transport)

Let \(S\) be a derived shore. The draft claimed that every boundary and
response statement used by the Type A local ledger remains valid with \(S\)
in place of \(X\):

1. every edge of \(\delta_G(S)\) is an actual oriented completion incidence;
2. the outside context is the actual induced complement together with the
   boundary vertices, so gluing reconstructs \(G\);
3. a target-complete quotient on a proper subpiece of \(S\) is forbidden by
   hereditary target-uncompressibility;
4. a target-defective event meeting an internal edge of \(S\) and an edge
   outside \(S\) uses at least two distinct incidences of \(\delta_G(S)\);
5. the node-[124] two-carrier terminal accepts a target-complete-minimal shore
   entry with at most two private essential incidences;
6. a decorated handoff produced inside \(S\) is the same actual Type B
   handoff when the omitted vertices \(X-S\) are glued back.

#### Audit of the argument

Items 1–2 are elementary descriptions of the actual cut, and the cycle-cut
parity used in item 4 is independently valid. What is not supplied by the
incoming ledger is a new entry census on \(S\), target-complete-minimality for
those new entries, or transport of the closed alternatives and absorber
ownership to that census. Thus items 3–6 do not jointly establish the claimed
ledger transport. The following argument is retained to identify its valid
cut identities and invalid transport inferences; it is not a lemma.

Items 1 and 2 are definitions: no formal half-edge is introduced.  The
vertex partition

\[
  \partial S\ \dot\cup\ (S-\partial S)\ \dot\cup\ (V(G)-S)
\]

and the ownership of each internal or external edge give a canonical graph
isomorphism from the glued actual piece and actual outside to \(G\).

For item 3, a proper boundaried subpiece of \(S\) is also a proper
boundaried piece of \(G\).  The boundary degree profile is the actual one,
so `cor:uncompressible` applies without changing its fibre.  The same gluing
observation transports proper- and whole-support dependence to the already
closed rows E-3, F-2.

For item 4, add the root edge when the event is edge-rooted.  The result is a
simple cycle meeting both \(S\) and its complement.  A cycle crosses every
edge cut an even number of times.  It crosses this cut positively, and a
simple cycle cannot traverse one cut edge twice, so it uses at least two
distinct cut incidences.  This is precisely the proof of
`lem:typeA-pressure-token-two-carriers`; it does not require the cut edges to
end in \(W\).

For item 5, inspect the terminal contract of [124].  It asks for ambient
cubicity, contextual target-safety, a target-complete-minimal trace basin, an
essential core of size at least two, at most two private essential
incidences, and the declared deletion witnesses.  Ambient cubicity and
actual target-safety are Lemma 14.2(b),(f), while contextual target-safety is
the inherited boundaried-piece fact in \(\mathcal B_{181}\); the response-state
construction and its deletion witnesses use the actual boundary just
established; and the one-carrier case is excluded by the cut-parity argument
of item 4.  The terminal's smaller two-terminal-piece clauses are supplied by
the retained `gadgetClosure` fact (key 500), whose statement is uniform in the
chosen proper piece.  Thus all clauses of the [124] input interface, and no
stronger clause, hold.

For item 6, the handoff certificate consists of actual connector tails, their
first high-degree separator, and the decorated core.  Gluing \(X-S\) back
does not change any of those ambient vertices, edges, degrees, or return
tests.  Hence it is a handoff for the original branch state.  Members of
\(\widetilde{\mathcal X}\) have already taken the no-handoff arm, so it
cannot occur on a surviving derived shore. \(\square\)

The important point is that an edge of \(\delta_G(S)\) may end in
\(X-S\), rather than in a packed window.  None of items 1--6 uses a window
blocker.  The closing proof retains the blocker partition from (R3) but does
not spend it again.

---

## 15. Retired hereditary-shore ledger construction

The draft next reruns the receiver, trace, visible-first, demand, and
absorption constructions on \(G[S]\). This is not transport of the incoming
node-[181] ledger. That ledger is indexed by the original full unified family,
whose excess basins contain unpaid visible-first as well as silent loads; no
upstream statement identifies it with a newly constructed silent-only family
on every derived shore. The construction therefore stops here. The notation
below is retained as notation from the failed draft and creates no fact or
child residual.

Write

\[
 n_i(S):=|\{v\in S:d_S(v)=i\}|,
 \qquad N(S):=\text{number of indexed silent-excess entries on }S. \tag{15.1}
\]

The retired draft let \(o(S)\) be the number of open demand units after the
lexicographically
first maximal \(2/3\)-ledger and maximal same-shore type-(A1) absorption have
been formed on these entries and all type-(A2) conclusions have routed to
their already closed compression/support-dependence rows.  This is a derived
quantity. It is not supplied by the incoming residual.

### Failed Claim 15.1 (local burden)

The retired draft asserted

\[
 N(S)\ge n_3(S)-3n_2(S)-7n_1(S)-11n_0(S)
      =|S|-4b(S).                                      \tag{15.2}
\]

#### Audit

For a receiver \(w\), put \(q_S(w)=3-d_S(w)\) and
\(c_S(w)=4q_S(w)-1\).  The visible-first normalization first routes a
four-visible configuration through the exhaustive exits and repeats after
an exit-(4) record; finite peeling terminates because its integer load measure
decreases. The unavailable step is the next one: the draft transports all
closed exits and then concludes that every unpayable load in the rebuilt
family is silent. The live node-[181] family disproves that identification at
the level of available data, since it also contains unpaid visible-first
loads. The implication to the next display is therefore invalid on the
incoming ledger. The draft wrote

\[
 |\mathcal U_S(w)|\ge L_S(w)-c_S(w),                   \tag{15.3}
\]

where the right side may be negative.  The exact peeling identity retains a
recorded load on the entry side when it is removed from a receiver sum, so
(15.3) is unchanged by each normalization step; this is the local form of
\(4D=4D^{P_4}+p_4\).

Every internal-degree-three vertex is routed exactly once, hence
\(\sum_wL_S(w)=n_3(S)\).  Receivers of degrees \(2,1,0\) have capacities
\(3,7,11\).  Summing (15.3) gives the first inequality.  Finally,

\[
 b(S)=3n_0(S)+2n_1(S)+n_2(S),
 \qquad |S|=n_0(S)+n_1(S)+n_2(S)+n_3(S),
\]

and direct subtraction gives

\[
 |S|-4b(S)=n_3(S)-3n_2(S)-7n_1(S)-11n_0(S).
\]

The last degree identity is correct, but the false silence step means that
the lower bound for \(N(S)\), and hence (15.2), has not been proved on the
incoming residual. \(\square\)

### Failed Claim 15.2 (local three-unit pressure)

The retired draft asserted

\[
             3N(S)-o(S)\le b(S).                      \tag{15.4}
\]

Moreover every open unit has a silent owner
\(\xi=(S,w,u,B_u)\) in the ledger of (15.1).

#### Proof

For each entry, the four trace-basin failure alternatives are exhaustive.
The compression and support-dependence alternatives are already closed, and
the handoff alternative is excluded by Lemma 14.3(6).  Thus an entry is
either target-complete-minimal or target-defective.

If it is target-complete-minimal and has at most two private essential
incidences, Lemma 14.3(5) routes it to [124].  Therefore every surviving
target-complete-minimal entry has three private incidences; these incidences
are pairwise disjoint by privacy.  If it is target-defective, Lemma 14.3(4)
gives a canonical token with at least two actual boundary incidences.  The
lexicographically first maximal ledger therefore partitions the \(N(S)\)
entries as

\[
  \Xi_3(S)\ \dot\cup\ \Xi_2(S)\ \dot\cup\ \Xi_{\rm res}(S),
\]

uses

\[
 a(S)=3N_3(S)+2N_2(S)                                 \tag{15.5}
\]

distinct incidences, and creates

\[
 d(S)=N_2(S)+3N_{\rm res}(S)                          \tag{15.6}
\]

demand units.  Equations (15.5)--(15.6) give the exact identity

\[
                 3N(S)=a(S)+d(S).                     \tag{15.7}
\]

Let \(A_1(S)\) be the number of these units absorbed by unused incidences of
the same shore.  These incidences are disjoint from the base assignment and
from one another.  Type-(A2) certificates have left through their closed
rows, so maximal absorption gives

\[
 o(S)=d(S)-A_1(S),
 \qquad a(S)+A_1(S)\le|\delta_G(S)|=b(S).              \tag{15.8}
\]

Substituting (15.8) into (15.7) proves (15.4).  Demand units exist only for
entries in \(\Xi_2(S)\cup\Xi_{\rm res}(S)\), all of which are members of the
silent-excess family used to define \(N(S)\).  Hence every open unit has the
stated silent owner. \(\square\)

### Invalid draft consequence 15.3 (no-open shore estimate)

If \(o(S)=0\), then

\[
                    |S|\le\frac{13}{3}b(S).           \tag{15.9}
\]

#### Proof

By Lemmas 15.1--15.2,

\[
 3(|S|-4b(S))\le3N(S)\le b(S).
\]

Rearranging gives \(3|S|\le13b(S)\). \(\square\)

The identities (15.5)--(15.8) are correct algebra for the newly defined draft
ledger, and the displayed boundary incidences are counted once. That ledger
is not the incoming one, while (15.2) is unproved. Therefore (15.9) is not a
node-[181] consequence and this section supplies no child.

---

## 16. Valid cut facts and the failed open-owner split

### Lemma 16.1 (an ambient cubic vertex is not a cut vertex of \(G\))

If \(d_G(v)=3\), then \(G-v\) is connected.

#### Proof

The minimal counterexample is connected: otherwise one connected component
would be a smaller graph of minimum degree at least three with no
power-of-two cycle.  Suppose \(G-v\) has \(k\ge2\) components.  Each such
component sends at least two edges to \(v\), because a component sending one
edge would make that edge a bridge.  Hence
\(d_G(v)\ge2k\ge4\), contrary to \(d_G(v)=3\). \(\square\)

### Lemma 16.2 (nonseparating receivers make every load visible)

Let \(S\) be a derived shore, \(w\) a receiver, and \(u\) a routed load whose
canonical trace ends with the edge \(tw\).  Fix a completion port \(wh\).
If \(t\) lies in a component of \(S-w\) that is reached by an actual
\(h\)-to-\(S\) connector avoiding \(w\), then \(u\) is visible through
\(wh\).  In particular this holds through every port if

\[
 d_S(w)=1,
 \quad\text{or}\quad
 d_S(w)=2\text{ and }S-w\text{ is connected}.          \tag{16.1}
\]

#### Proof

By Lemma 16.1, \(G-w\) is connected.  Choose a simple path in \(G-w\) from
\(h\) into the component of \(S-w\) containing \(t\), and stop it at its
first vertex \(r\) in \(S\).  Such a path is exactly the connector assumed
in the first sentence; in the two cases of (16.1), any \(h\)-to-\(t\) path
in \(G-w\) has its first entry in that unique component.  Its prefix
\(\Gamma:h\leadsto r\) has all internal vertices outside \(S\).  The entering
edge shows \(d_S(r)\le2\), so \(r\) is a receiver.  By the hypothesis, choose
an internal path \(Q_0:r\leadsto t\) in the relevant component of \(S-w\)
and append \(tw\).  The connector and this channel meet only at \(r\), so
\(\Gamma\circ Q_0\circ tw\) is a simple receiver-entry return avoiding
\(wh\).  Replacing \(Q_0\circ tw\) by the first scheduled channel with the
same terminal trace edge preserves these properties and satisfies the second
clause of `VisibleFor`.  Thus \(u\) is visible.

If \(d_S(w)=1\), deleting the leaf \(w\) leaves \(S-w\) connected.  The
second case of (16.1) states the same connectivity explicitly. \(\square\)

### Failed Claim 16.3 (open-owner split)

This claim is not available on node [181]. Its first inference invokes Failed
Claim 15.2 to turn an arbitrary open owner into a silent-excess owner. The
incoming ledger does not do that. The boundary identities below are retained
because they are correct for an actual split; they do not produce the split.

Let an open unit of \(\mathscr L_S\) have owner
\(\xi=(S,w,u,B_u)\).  Then

\[
 d_S(w)=2,
 \qquad S-w=K\mathbin{\dot\cup}H                         \tag{16.2}
\]

for exactly two nonempty connected components \(K,H\).  Both are proper
derived shores and

\[
 \begin{aligned}
 |S|&=|K|+|H|+1,\\
 b(K)+b(H)&=b(S)+1,\\
 b(K)&\ge2,\qquad b(H)\ge2.                             \tag{16.3}
 \end{aligned}
\]

#### Audit of the failed proof

The first sentence of the draft, “by Lemma 15.2 the owner is a silent excess
load,” is unsupported. The argument after that sentence studies a silent
owner and correctly derives the following local consequences, but it does not
apply to every open owner of the incoming unified family.
The case \(d_S(w)=0\) is impossible: connectivity would give
\(S=\{w\}\), which has no internal-degree-three vertex and hence no routed
load.  If \(d_S(w)=1\), Lemma 16.2 makes every routed load visible through
both ports; saturation gives at least eight loads, so a port carries four.
If \(d_S(w)=2\) and \(S-w\) is connected, the same lemma makes every load
visible through the unique port; saturation gives at least four.  Either
conclusion contradicts that \(u\) is in the silent-excess family.

Therefore \(d_S(w)=2\) and \(S-w\) is disconnected.  Since \(S\) is
connected and \(w\) has exactly two neighbours in \(S\), deletion of \(w\)
has exactly two components, one containing each neighbour.  This proves
(16.2) and the order identity.

Let \(b_K^0\) and \(b_H^0\) count the original edges of \(\delta_G(S)\)
whose endpoint in \(S\) lies in \(K\) and \(H\), respectively.  The third
edge at \(w\) is the unique edge of \(\delta_G(S)\) incident with \(w\), so

\[
        b(S)=1+b_K^0+b_H^0.                            \tag{16.4}
\]

There is no edge between \(K\) and \(H\), and each has exactly one edge to
\(w\).  Hence

\[
        b(K)=1+b_K^0,\qquad b(H)=1+b_H^0.              \tag{16.5}
\]

Adding (16.5) and using (16.4) gives
\(b(K)+b(H)=b(S)+1\).  Finally a cut of size one in connected \(G\) is a
bridge, so Lemma 14.2(d) gives \(b(K),b(H)\ge2\). This verifies the displayed
boundary identities for the split described in (16.2); it does not prove
that node [181] supplies such a split. \(\square\)

### Exact accounting after an actual split

Replacing \(S\) by \(K,H\) changes the active vertex measure by

\[
 M_{\rm after}-M_{\rm before}
   =|K|+|H|-|S|=-1.                                   \tag{16.6}
\]

Equations (16.2)--(16.5) make every child a proper subset of \(S\). The
separator \(w\) is accounted
once by the \(+1\) in the first line of (16.3), and the new interface cost is
accounted once by the \(+1\) in its second line. Thus (16.6) is the correct
decrease certificate for an actual split. Failed Claim 16.3 produces no such
split from the incoming residual, so (16.6) cannot be registered as progress
below [181].

---

## 17. The independent boundary-two lemma and its invalid draft use

The numerical comparison

\[
 \frac{13}{3}b(S)\le7b(S)-8
 \quad\Longleftrightarrow\quad b(S)\ge3.               \tag{17.1}
\]

is correct. The input (15.9), however, is Invalid Draft Consequence 15.3 and
is not available on node [181]. The following elementary lemma is independent
of that failure and is retained; no finite search is used.

### Lemma 17.1 (small two-boundary shore contains \(C_4\) or \(C_8\))

Let \(S\) be a connected induced ambient-cubic shore in a bridgeless simple
graph.  If \(b(S)=2\) and \(|S|\le8\), then \(G[S]\) contains a cycle of
length four or eight.

#### Proof

Because

\[
 2=b(S)=\sum_{v\in S}(3-d_S(v)),                       \tag{17.2}
\]

the degree deficit is either two degree-two vertices or one degree-one
vertex.  The latter is impossible.  Indeed both boundary edges would then be
incident with the degree-one vertex \(x\); its unique internal edge would be
the only edge joining \(S-\{x\}\) to \(x\) and the outside, hence a bridge
of \(G\).  Thus \(G[S]\) has exactly two vertices of degree two and every
other vertex has degree three.  The degree sum is \(3|S|-2\), so \(|S|\) is
even.  The case \(|S|=2\) is incompatible with (17.2).  It remains to treat
orders four, six and eight.

If \(|S|=4\), the graph has five edges and is \(K_4\) with one edge deleted;
it contains a \(4\)-cycle.

Let \(|S|=6\).  If the graph is triangle-free, take a cubic vertex \(v\).
Its three neighbours are independent.  Each needs a further neighbour among
the remaining two vertices, and two of them therefore share such a neighbour;
together with \(v\) they form a \(4\)-cycle.  Now suppose \(abc\) is a
triangle, and let \(k\) of its vertices be the two degree-two terminals.  A
cubic triangle vertex has one spoke to the remaining three vertices.  In the
absence of a \(4\)-cycle, spoke endpoints of distinct triangle vertices are
distinct and nonadjacent.  The graph has eight edges, so the graph induced by
the three outside vertices has \(2+k\) edges.  If \(k=0\), the three spoke
endpoints would have to support two edges, contrary to their required
nonadjacency.  If \(k=1\), the outside graph has three edges and is a triangle,
again joining the two spoke endpoints.  If \(k=2\), it would have four edges
on three vertices.  All cases are impossible without a \(4\)-cycle.

Let \(|S|=8\).  First suppose the graph is triangle-free.  For a cubic
vertex \(v\), let \(A\) be its three independent neighbours and let \(B\)
be the other four vertices.  A vertex of \(B\) has at most one neighbour in
\(A\), otherwise it and \(v\) give a \(4\)-cycle.  If \(t\) terminals lie
in \(A\), the vertices of \(A\) require \(6-t\) edges to \(B\).  Hence
\(6-t\le4\), so \(t=2\) and equality holds.  Every vertex of \(B\) then has
one neighbour in \(A\); all terminals have already been used, so every vertex
of \(B\) has two neighbours in \(B\).  The induced graph on four vertices is
therefore a \(4\)-cycle.

It remains that \(abc\) is a triangle.  Let \(F=S-\{a,b,c\}\) and let
\(k\) terminals lie on the triangle.  There are \(3-k\) spokes and, since
the whole graph has eleven edges,

\[
                  |E(F)|=5+k.                         \tag{17.3}
\]

In the absence of a \(4\)-cycle, distinct spoke endpoints are distinct and
nonadjacent.

- If \(k=2\), the degree sequence in \(F\) is
  \((3,3,3,3,2)\).  Its complement has degree sequence
  \((2,1,1,1,1)\), hence is a three-vertex path plus a disjoint edge.  If
  its edges are \(xa,xb,cd\), then \(a-c-b-d-a\) is a \(4\)-cycle in
  \(F\).
- If \(k=1\) and the outside terminal is a spoke endpoint, \(F\) has degree
  sequence \((3,3,3,2,1)\).  Deleting its degree-one vertex leaves five
  edges on four vertices, a \(K_4\) minus one edge, and hence a
  \(4\)-cycle.  If the outside terminal is not a spoke endpoint, the degree
  sequence is \((3,3,2,2,2)\).  Call the degree-three vertices \(p,q\).
  If they are nonadjacent they share the three remaining vertices and give a
  \(4\)-cycle.  If they are adjacent, each has two neighbours among the
  remaining three.  Their two neighbour sets meet in exactly one vertex;
  the two noncommon vertices must be adjacent to complete their degree two,
  and these four vertices with \(pq\) give a \(4\)-cycle.
- If \(k=0\), let \(d,e,f\) be the three independent spoke endpoints and
  let \(g,h\) be the other vertices of \(F\).  If \(gh\notin E(F)\), all
  five edges of \(F\) lie in \(K_{3,2}\); two of \(d,e,f\) then meet both
  \(g,h\), giving a \(4\)-cycle.  Hence \(gh\in E(F)\).  The other four
  edges have degree pattern \((2,1,1)\) on \(d,e,f\): each spoke endpoint
  needs at least one edge in \(F\).  They have pattern \((2,2)\) on
  \(g,h\), since each already uses \(gh\), has degree at most three, and
  the four cross edges must all be counted.  Relabel so the cross edges are
  \(dg,dh,eg,fh\), and relabel the triangle so its spokes are
  \(ad,be,cf\).  Then
  \[
       a-b-e-g-d-h-f-c-a
  \]
  is an \(8\)-cycle.

Thus every case contains \(C_4\) or \(C_8\). \(\square\)

### Invalid draft consequence 17.2 (the \(b=2\) no-open arm)

If \(o(S)=0\) and \(b(S)=2\), Corollary 15.3 gives
\(|S|\le26/3\), hence \(|S|\le8\).  Lemma 17.1 gives a cycle of length four
or eight, contradicting C-1. The finite implication is correct, but its
premise \(|S|\le26/3\) comes only from Invalid Draft Consequence 15.3.
Therefore it closes no arm of the incoming node-[181] residual.

Notice also that an open-owner split cannot start at \(b(S)=2\): (16.3)
would give \(b(K)+b(H)=3\) while each summand is at least two.  This is an
independent exact check on the terminal.

---

## 18. Failed seven-deficit claim and retained tree arithmetic

### Failed Claim 18.1 (sharp shore estimate)

The retired draft asserted that every surviving derived shore satisfies

\[
                       |S|\le7b(S)-8.                  \tag{18.1}
\]

In particular, every original support
\(X\in\widetilde{\mathcal X}\) satisfies

\[
                       |X|\le7\defp(X)-8.              \tag{18.2}
\]

#### Audit of the failed induction

This is not an induction on the node-[181] residual: its zero-open case uses
Invalid Draft Consequence 15.3 and its positive-open case uses Failed Claim
16.3. The algebra the draft wrote was as follows.

If \(o(S)=0\), Corollary 15.3 gives
\(|S|\le13b(S)/3\).  When \(b(S)\ge3\), (17.1) gives (18.1).  When
\(b(S)=2\), Corollary 17.2 closes the branch; hence no target-free
counterexample shore remains in this case.

On its \(o(S)>0\) line, the draft invoked Failed Claim 16.3 to obtain two
proper children \(K,H\), then invoked Failed Claims 14.3--15.2 to apply the
induction statement to each. Its arithmetic using (16.3) was

\[
\begin{aligned}
 |S|
   &=|K|+|H|+1\\
   &\le (7b(K)-8)+(7b(H)-8)+1\\
   &=7(b(S)+1)-15\\
   &=7b(S)-8.
\end{aligned}                                         \tag{18.3}
\]

The calculation (18.3) correctly propagates a \(7b-8\) estimate across an
actual split satisfying (16.3). The incoming residual supplies neither the
leaf estimate nor the split, so it proves neither (18.1) nor (18.2).
\(\square\)

### 18.2 Exact arithmetic of an already produced decomposition tree

This subsection is a standalone bookkeeping identity, not a construction.
For any already constructed full binary shore-exhaustion tree, let \(\ell\)
be its number of leaves and \(t\) its number of split vertices.
It is a full binary tree, so \(t=\ell-1\).  Repeated use of (16.3) gives the
literal identities

\[
 |S|=\sum_{L\text{ leaf}}|L|+t,
 \qquad
 \sum_{L\text{ leaf}}b(L)=b(S)+t.                    \tag{18.4}
\]

Every surviving leaf has \(b(L)\ge3\) and satisfies
\(|L|\le7b(L)-8\).  Therefore

\[
\begin{aligned}
 |S|
 &\le\sum_L(7b(L)-8)+t\\
 &=7(b(S)+t)-8\ell+t\\
 &=7b(S)+8(\ell-1)-8\ell\\
 &=7b(S)-8.
\end{aligned}                                         \tag{18.5}
\]

Thus each separator is paid exactly once; the \(+1\) boundary increment is
neither lost nor charged twice.  At the transition level, (16.6) says the
active residual loses exactly one vertex per split.  At the completed-tree
level, (18.4)--(18.5) account for every original vertex and every newly
exposed boundary incidence. No such tree is produced from node [181], so
these identities do not reduce its residual.

---

## 19. Retired global summation; no node-[181] contradiction

The global account below is retained because its summation and numerical
comparison are useful checks. It is not a proof chain: equation (19.4) invokes
Failed Claim 18.1, so the first unsupported line is visible before the global
sum is formed.

Put

\[
                  Q(Y):=\defp(Y)-\sigma(Y).            \tag{19.1}
\]

Let \(\mathcal E_B\) be the Type B bridge/envelope residual family.  The
incoming Type B ledger gives

\[
 M_B:=\sum_{Y\in\mathcal E_B}|Y|=o(|R|),
 \qquad \sigma(G)=o(|R|).                              \tag{19.2}
\]

Every canonical support outside \(\mathcal E_B\) is accounted as follows.

- If \(\No(Y)\ge0\), then
  \[
       |Y|\le4Q(Y)\le7Q(Y).                            \tag{19.3}
  \]
- The draft claimed that if \(\No(Y)<0\) and it is Type A with no handoff,
  then \(\sigma(Y)=0\) and Failed Claim 18.1 gives
  \[
       |Y|\le7\defp(Y)-8<7Q(Y).                        \tag{19.4}
  \]
- Every other negative support has already routed through the Type B
  handoff/bridge ledger; its only surviving mass is included in
  \(\mathcal E_B\).

The canonical supports partition \(R\), and their deficits and assigned
surpluses add.  Moreover

\[
 \left|\sum_{Y\in\mathcal E_B}Q(Y)\right|
 \le3M_B+\sigma(G)=o(|R|),                             \tag{19.5}
\]

because positive deficiency is at most three per vertex and all assigned
surplus is bounded by the global surplus.  Summing (19.3)--(19.4), using
(19.2)--(19.5), gives

\[
\begin{aligned}
 |R|-M_B
   &\le7\sum_{Y\notin\mathcal E_B}Q(Y)\\
   &=7Q(R)-7\sum_{Y\in\mathcal E_B}Q(Y),
\end{aligned}
\]

The draft therefore wrote

\[
             |R|\le7(\defp(R)-\sigma(R))+o(|R|).       \tag{19.6}
\]

It remains to compare (19.6) with the retained cap.  Theorem 1.5 gives

\[
 \frac{\defp(R)-\sigma(R)}{|R|}\le\tau^\ast+o(1),
 \qquad
 \theta^\ast=\frac{3}{4c_{13}-99},
 \qquad
 \tau^\ast=\frac{45}{4c_{13}-138}.                    \tag{19.7}
\]

The registered finite constant satisfies
\(c_{13}=118.108581006\ldots>453/4\).  Therefore

\[
 7\tau^\ast<1,
 \qquad
 1-7\tau^\ast
   =\frac{4c_{13}-453}{4c_{13}-138}
   =0.0581\ldots>0.                                   \tag{19.8}
\]

Divide (19.6) by \(|R|\) and use (19.7):

\[
                    1\le7\tau^\ast+o(1).              \tag{19.9}
\]

The numerical margin in (19.8) is strict. But (19.6) is not a branch fact,
because its Type A summand uses the unproved estimate (19.4). Therefore
(19.9) is not obtained and §§13–20 do not close node [181].

For completeness, the cap used here is itself an accumulated upstream fact,
not a new assumption.  On the hot arm, the realized window state supplies
\((c_{13}-o(1))p_{13}\log_2n\) bits.  The relabelling-orbit inequality of
keys 501--502 and the \(\tfrac32n\log_2n+O(n)\) skeleton budget give

\[
 c_{13}\theta+\frac34(1-13\theta)-15\theta
 \le\frac32+o(1),
\]

so \((c_{13}-99/4)\theta\le3/4+o(1)\), which is the first
formula in (19.7). The stub identity then gives the second. This confirms
that the numerical cap is retained upstream; it does not supply the missing
local estimate (19.4).

---

## 20. Audit of the retired block--cut draft

### 20.1 Transition audit against the incoming residual

| Draft step | Claimed output | Exact audit verdict | Residual decrease |
|---|---|---|---|
| Shore-interface transport, §§14–15 | a new silent-only ledger on every shore | **invalid:** it is not the original unified census and drops unpaid visible-first entries | none |
| Open-unit test | \(o(S)=0\) or \(o(S)>0\) on that new ledger | **invalid:** \(o(S)\) is not an incoming-ledger quantity | none |
| Block--cut move | two components of \(S-w\) | **invalid as a transition:** the silent-owner premise is not produced; (16.3) is only the exact arithmetic of a split already in hand | none |
| Boundary-two terminal | a \(C_4\) or \(C_8\) | Lemma 17.1 is valid, but the draft never produces the required no-open \(b=2,\ |S|\le8\) state | none |
| Shore induction | \(|S|\le7b(S)-8\) | **invalid:** both base and recursive producers are absent | none |
| Global sum | (19.6) | **invalid:** the negative Type A summand (19.4) cites Failed Claim 18.1 | none |
| Density collision | numerical contradiction | the retained cap and arithmetic margin are valid, but their local premise (19.6) is absent | none |

No block--cut operation is admitted below [181]. Equation (16.6) verifies the
size change of a split but does not produce one, so it cannot serve as the
progress certificate of a descendant. The complete upstream ledger remains
unchanged. The implemented chain is the maximal-ledger augmentation at [181]
followed by the shortest-trace boundary-support reduction at [183] and the
visible-first prefix exhaustion at [184]; it ends at the exact actual-overload
residual [185], not at a claimed contradiction.

### 20.2 What remains correct

- The elementary shore identities in Lemma 14.2, the cubic cut-vertex lemma
  16.1, the local visibility implication 16.2, the boundary arithmetic
  (16.3)--(16.6), and the finite boundary-two Lemma 17.1 remain available as
  independently stated mathematics.
- The draft did not construct a descendant state, a transported absorber
  ledger, or a decomposition tree. Claims that these objects retained every
  parent fact are removed from the proof record.
- Type B exceptional mass is retained explicitly as \(M_B\), and both its
  vertex mass and its possible \(Q\)-contribution are absorbed only into the
  displayed \(o(|R|)\) term in (19.2), (19.5).
- The sharpened cap is derived from the registered orbit inequalities; it is
  an incoming fact, not a new assumption. It has no valid local \(7b-8\)
  estimate to consume in this draft.

### 20.3 Rejected Lean implementation sketch

The retired draft proposed the following interface names. None is a legal row
below `route8PeeledDemandResidual`, and none is implemented:

1. `route8ShoreLedgerTransport` is rejected because (15.2) and (15.4) are not
   transported facts of the incoming unified census.
2. `route8OpenOwnerBlockCut` is rejected because an open owner is not proved
   silent.
3. `route8BoundaryTwoTerminal` is rejected because the required no-open
   boundary-two child is not produced.
4. `route8SevenDeficit` is rejected because its base and recursive steps are
   Failed Claims 15.3 and 16.3.
5. `route8Node181Closure` is rejected because (19.6) has no producer.

Adding any of these names would re-encode the same residual without reducing
it. They are audit history, not pending implementation obligations.

The original LaTeX paper records Theorems 0.1–0.2 as
`thm:typeA-unpaid-exit4-reduction`; its [183] continuation records
Theorem 0.3 as `lem:typeA-unified-visible-ownership`, and its [184]
continuation records Theorem 0.4 as
`lem:typeA-unified-visible-overload`. Theorem 0.5 is recorded as
`lem:typeA-unified-joint-balance`; its `route8JointBalanceRow` appends key 506
and moves the unchanged ledger from [185] to [186].
