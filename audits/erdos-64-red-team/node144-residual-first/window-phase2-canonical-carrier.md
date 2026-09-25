# [144a] window history: canonical carrier shared by the source pattern

Fix one witness of `typeBHandoff` on `G = selected.object`, including its
capacity presentation, certified ledger, token `t`, role `r`, and selected
matching or star `P`.  This is the handoff's own witness; the separate
`windowClassOverload` witness is not identified with it.  Every `pair ∈ P`
lies in that ledger's `roleFibre t r`.  In this concrete presentation the
ledger's canonical label is `capacityCharge`, so every such pair has charge
`some t` and canonical blocker kind `r.blocker`.  The role's token coordinate
is the subtype of `t` on charged pairs.

The charge gives a physical observable on **every original pair of P**, not
only on the two same-label edges chosen by [144]'s routing proof.  In the
first three cases below this is a selected part of the canonical blocker
*support*, not the blocker's primitive carrier:

* If `t = boundaryWindow e`, both endpoints of the fixed window–remainder
  incidence `e` lie in that pair's canonical blocker support.
* If `t = crossWindow e`, both endpoints of the fixed cross-window incidence
  `e` lie in that support, and the earlier window-choice case failed.
* If `t = remainder (v,j)`, the same vertex `v` lies in every such support;
  both window incidence choices failed.  The unit `j` additionally records a
  residue class of the pair's rank in the cohort at `v`.
* If `t = primitive item`, all three geometric choices failed and `item` is
  the primitive carrier of each pair's actual canonical blocker.  For the
  subtype `primitiveVertex v` with canonical kind `sharedDeclaredSupport`,
  the blocker is `sharedDeclaredSupport (.vertex v)`, so `v` lies in both
  demands' declared supports `T(p)∪Γ(p)`. This does not place `v` in their
  smaller port supports `T(p)`.

There is an important **empty role case**. A blocker of kind
`sharedLocalBuffer` at a vertex `v` places `v` in both demands' local
buffers. Each local buffer lies in its declared support. Thus the earlier
`sharedDeclaredSupport (.vertex v)` blocker is applicable to the same pair.
The canonical blocker enumerates every applicable shared-declared-support
object before any shared-local-buffer object, so its kind cannot be
`sharedLocalBuffer`. Any role fibre with that canonical kind is empty. This
eliminates the tempting primitive-vertex/local-buffer incidence argument;
it supplies no live [144a] case to count.

These are separate conditional cases on the *handoff token*.  The tagged
window-incidence ancestry alone does not select the first case.  The fixed
edge or vertex belongs to canonical blocker supports; the definition does not
place every source route through it or assign the source pairs to the
decorated envelope.  No bound on the size of `P`, token load, or envelope
multiplicity is claimed here.

The unresolved interaction is whether the fixed support or primitive
carrier, combined with the **remaining possible** blocker kinds, limits the
number of distinct source demands or forces a forbidden graph configuration.
The now-empty local-buffer role is a classification fact, not a homogeneous
cap or a payoff for the surviving roles. This differs from the earlier
route-terminal count: it reads the canonical blocker attached to each
original source pair, before any route or envelope is selected.

Sources: `CapacityTokenAssignment.lean:264–352,504–536,658–673`;
`CapacityTokenLedger.lean:123–141`; `ObjectCapacityLedger.lean:623–682`;
`SurplusBlockers.lean:390–430`; `SparseEntropySandwich.lean:146–213,247–256`;
`SparsePortActivation.lean:50–69`; `SpineVocabulary.lean:3961–3979`.
