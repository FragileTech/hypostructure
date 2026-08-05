import Hypostructure.Graph.Strategy.InterfaceReplacement
import Hypostructure.Graph.MinimumDegreeCycleTarget
import Hypostructure.Graph.FinitePathSelection

/-!
# The cold return corridor: cut-states and the same-interface table

Two manuscript objects live here, and nothing else.

`def:cold-corridor-first-failure` fixes, for an initial segment `J` of a cold
return corridor, the two active boundary interfaces `T(J)` and the **cold
corridor state** of `J`: the finite two-boundary cut-state obtained from the
exact response profile `ρ^ex_{T(J)}(J)` by retaining exactly

* the boundary-degree profile,
* the two active boundary half-edges,
* the cold-window offsets met at the two interfaces, and
* the declared local coordinates of `def:declared-coordinate-signature` whose
  support is contained in the bounded active interface.

Finiteness of that retained data is the constant `Q_cold`, and `M_cold`,
`B_cold`, `D_cold` are read off it.

`def:cold-same-interface-table` fixes the finite table whose rows are
equal-length cold bounded germs and the short self-return exceptions of
`lem:cold-short-self-return-filter`, and `lem:cold-same-interface-table` closes
every row of it.

Nothing here is specialized to one manuscript.  The declared signature is a
registered parameter -- its clauses (D1)--(D7) are supplied by whoever owns
their data, and its closure clause (D8) is the framework's own -- and the
retained cut-state, the constants, the germ, the table and its closure are
stated against that parameter.  No numeral of a manuscript appears below.
-/

namespace Hypostructure.Graph.ColdCorridor

open Hypostructure

universe u v uProfile

/-! ## `def:declared-coordinate-signature`

A declared coordinate is a tuple `(k, ι, supp_X(r), val_X(r))`: a kind, a
label, a finite support, and the value read in the embedded support.  Clauses
(D1)--(D7) *generate*; clause (D8) *closes* the generated family under finite
products, labelled copies, restrictions, and quotient images, "with support
equal to the union of the supports of the entries used".

The registration below is that split, verbatim.  `Clause` is the kind index and
`Generator c` the coordinates of one kind, so the manuscript's (D1)--(D7) are
values of `Clause` supplied by whoever owns the corresponding data; the
framework never enumerates them.  `Label` is the label alphabet used by the two
labelling operations of (D8).  All four are finite, which is the manuscript's
"the fixed declared signature", and is the only reason `Q_cold` below is a
constant rather than a function of the graph. -/
structure DeclaredSignature where
  /-- The generating clauses (D1)--(D7): the *kinds* of declared coordinate. -/
  Clause : Type
  clauseEnum : FinEnum Clause
  /-- The declared coordinates of one kind. -/
  Generator : Clause → Type
  generatorEnum : ∀ clause, FinEnum (Generator clause)
  /-- The value alphabet `val_X(r)` reads into. -/
  Value : Type
  valueEnum : FinEnum Value
  /-- The label alphabet of (D8)'s labelled copies and quotient images. -/
  Label : Type
  labelEnum : FinEnum Label
  /-- The bound on a retained boundary datum imposed by the local target
  algebra.  `def:cold-bounded-germ`'s "bounded by the fixed finite cut-state
  constant used by the local target algebra" is this number. -/
  degreeBound : Nat
  /-- The order of the cold window whose offsets the two interfaces meet. -/
  windowOrder : Nat
  windowOrder_pos : 0 < windowOrder

namespace DeclaredSignature

variable (S : DeclaredSignature)

instance : FinEnum S.Clause := S.clauseEnum
instance (clause : S.Clause) : FinEnum (S.Generator clause) :=
  S.generatorEnum clause
instance : FinEnum S.Value := S.valueEnum
instance : FinEnum S.Label := S.labelEnum

end DeclaredSignature

/-! ### The generating clauses (D1)--(D7)

`def:declared-coordinate-signature` fixes the signature "once and for all" and
lists what generates it.  Every named kind of the manuscript's clauses
(D1)--(D7) is a constructor below, in the manuscript's own order, and nothing
else is.  Clause (D8) is not here: it is `Generated`, the framework's closure of
this list under finite products, labelled copies, restrictions, and quotient
images.

"No other local response coordinate is available to a quotient." -/

/-- **The kinds of declared coordinate, clauses (D1)--(D7).** -/
inductive SignatureClause where
  /-- (D1) boundary-degree entries at labelled boundary vertices. -/
  | boundaryDegree
  /-- (D2) edge-rooted return data. -/
  | rootedReturn
  /-- (D2) completion-port data. -/
  | completionPort
  /-- (D2) first-entry receivers. -/
  | firstEntryReceiver
  /-- (D2) connector lengths. -/
  | connectorLength
  /-- (D2) receiver-entry channels. -/
  | receiverEntryChannel
  /-- (D2) the corresponding Mersenne return tests. -/
  | mersenneTest
  /-- (D3) induced-window labels. -/
  | windowLabel
  /-- (D3) legal-label relations. -/
  | legalLabelRelation
  /-- (D3) packed-window incidences. -/
  | packedWindowIncidence
  /-- (D3) cross-window incidence data. -/
  | crossWindowIncidence
  /-- (D4) raw curvature coordinates indexed by internal length-two wedges. -/
  | rawCurvature
  /-- (D5) Type A canonical traces. -/
  | canonicalTrace
  /-- (D5) trace-incidence coordinates. -/
  | traceIncidence
  /-- (D5) connector-band constraints. -/
  | connectorBand
  /-- (D5) cross-port theta constraints. -/
  | crossPortTheta
  /-- (D5) silent-basin response coordinates. -/
  | silentBasinResponse
  /-- (D5) carrier restrictions. -/
  | carrierRestriction
  /-- (D6) Type B fan centers. -/
  | fanCenter
  /-- (D6) fan-safe pairs. -/
  | fanSafePair
  /-- (D6) certificate labels. -/
  | certificateLabel
  /-- (D6) closed fan-window pairs. -/
  | closedFanWindowPair
  /-- (D6) hybrid incidence entries. -/
  | hybridIncidence
  /-- (D6) candidate ledger entries. -/
  | candidateLedgerEntry
  /-- (D6) overlap demands. -/
  | overlapDemand
  /-- (D6) decorated handoff fan response coordinates. -/
  | handoffFanResponse
  /-- (D6) decorated handoff-arm coordinates. -/
  | handoffArm
  /-- (D7) selected surplus ports. -/
  | surplusPort
  /-- (D7) canonical port returns. -/
  | canonicalPortReturn
  /-- (D7) open-port suppression paths. -/
  | openPortSuppressionPath
  /-- (D7) triangular-port response triangles. -/
  | triangularPortResponse
  /-- (D7) sparse surplus-pair response coordinates. -/
  | sparseSurplusPairResponse
  deriving DecidableEq

namespace SignatureClause

/-- The clause a kind belongs to, as the manuscript numbers them.  It is a
diagnostic: the signature never routes on it. -/
def clauseNumber : SignatureClause → Nat
  | .boundaryDegree => 1
  | .rootedReturn | .completionPort | .firstEntryReceiver | .connectorLength
  | .receiverEntryChannel | .mersenneTest => 2
  | .windowLabel | .legalLabelRelation | .packedWindowIncidence
  | .crossWindowIncidence => 3
  | .rawCurvature => 4
  | .canonicalTrace | .traceIncidence | .connectorBand | .crossPortTheta
  | .silentBasinResponse | .carrierRestriction => 5
  | .fanCenter | .fanSafePair | .certificateLabel | .closedFanWindowPair
  | .hybridIncidence | .candidateLedgerEntry | .overlapDemand
  | .handoffFanResponse | .handoffArm => 6
  | .surplusPort | .canonicalPortReturn | .openPortSuppressionPath
  | .triangularPortResponse | .sparseSurplusPairResponse => 7

/-- The thirty-two generating kinds, in the manuscript's order. -/
def all : List SignatureClause :=
  [.boundaryDegree,
    .rootedReturn, .completionPort, .firstEntryReceiver, .connectorLength,
      .receiverEntryChannel, .mersenneTest,
    .windowLabel, .legalLabelRelation, .packedWindowIncidence,
      .crossWindowIncidence,
    .rawCurvature,
    .canonicalTrace, .traceIncidence, .connectorBand, .crossPortTheta,
      .silentBasinResponse, .carrierRestriction,
    .fanCenter, .fanSafePair, .certificateLabel, .closedFanWindowPair,
      .hybridIncidence, .candidateLedgerEntry, .overlapDemand,
      .handoffFanResponse, .handoffArm,
    .surplusPort, .canonicalPortReturn, .openPortSuppressionPath,
      .triangularPortResponse, .sparseSurplusPairResponse]

theorem mem_all (clause : SignatureClause) : clause ∈ all := by
  cases clause <;> decide

theorem all_nodup : all.Nodup := by decide

instance : FinEnum SignatureClause := FinEnum.ofNodupList all mem_all all_nodup

/-- Every generating kind belongs to one of the seven clauses. -/
theorem clauseNumber_mem (clause : SignatureClause) :
    clause.clauseNumber ∈ [1, 2, 3, 4, 5, 6, 7] := by
  cases clause <;> decide

end SignatureClause

/-- **One declared coordinate of a generating kind**, at a bounded active
interface.

`def:declared-coordinate-signature` says a declared coordinate is a tuple
`(k, ι, supp_X(r), val_X(r))`: a kind, a label, a finite support, and its value.
The kind is the `SignatureClause` this is indexed by; `support` is
`supp_X(r)`, a finite set of positions of the bounded active interface -- the
manuscript's "finite set of vertices, edges, boundary incidences, paths, or
windows of `X`", read inside the interface; and `label` is `ι`, which is what
keeps two coordinates of the same kind and the same support distinct.  The value
is not here: it is what a `Presentation` reads.

Everything is bounded by the *interface*, never by the graph.  That is exactly
what `def:cold-corridor-first-failure` relies on when it concludes that the set
of cold corridor states is bounded by a constant of the signature. -/
structure Coordinate (interfaceBound : Nat) where
  /-- `supp_X(r)`, inside the bounded active interface. -/
  support : Finset (Fin interfaceBound)
  /-- `ι`, the coordinate's label. -/
  label : Fin interfaceBound
  deriving DecidableEq

namespace Coordinate

/-- The tuple, as an ordinary product; it carries finiteness onto
`Coordinate`. -/
@[simps] def equivProduct (interfaceBound : Nat) :
    Coordinate interfaceBound ≃
      Finset (Fin interfaceBound) × Fin interfaceBound where
  toFun coordinate := (coordinate.support, coordinate.label)
  invFun pair := { support := pair.1, label := pair.2 }
  left_inv := by intro coordinate; cases coordinate; rfl
  right_inv := by intro pair; rfl

instance (interfaceBound : Nat) : FinEnum (Coordinate interfaceBound) :=
  FinEnum.ofEquiv _ (equivProduct interfaceBound)

end Coordinate

/-- **The bounded active interface of `def:cold-corridor-first-failure`.**

"The additive `30` only covers the two `P₁₃`-window interfaces and the two
boundary stubs", so an interface of a corridor at a window of the given order
carries `2·order + 2·2` positions.  Nothing else in this file supplies a size,
and no caller may choose one. -/
def interfaceWidth (order : Nat) : Nat := 2 * order + 2 * 2

/-- **`def:declared-coordinate-signature`, complete.**

The signature "fixed once and for all": its generating kinds are the
thirty-two of clauses (D1)--(D7), its coordinates are the tuples
`(k, ι, supp_X(r))` bounded by the active interface of a window of the given
order, and its closure clause (D8) is `Generated`.  A reading is a bounded
value together with the outcome of the test the coordinate carries -- a degree,
a return length, a connector length, or a window label on the one hand; a
Mersenne, legality, incidence, curvature, or response test on the other.

No number is supplied by a caller: the interface width is the manuscript's own
`2·order + 2·2`, and every other bound is that width. -/
def declaredSignature (order : Nat) (order_pos : 0 < order) : DeclaredSignature where
  Clause := SignatureClause
  clauseEnum := inferInstance
  Generator := fun _clause => Coordinate (interfaceWidth order)
  generatorEnum := fun _clause => inferInstance
  Value := Fin (interfaceWidth order + 1) × Fin 2
  valueEnum := inferInstance
  Label := Fin (interfaceWidth order)
  labelEnum := inferInstance
  degreeBound := interfaceWidth order
  windowOrder := order
  windowOrder_pos := order_pos

@[simp] theorem declaredSignature_windowOrder (order : Nat) (order_pos : 0 < order) :
    (declaredSignature order order_pos).windowOrder = order := rfl

/-- **Clause (D8) of `def:declared-coordinate-signature`.**

The declared coordinates are the closure of the generating clauses under finite
products, labelled copies, restrictions, and quotient images.  A `gen` is a
coordinate of one of the clauses (D1)--(D7); the other four constructors are
(D8) itself, listed in the manuscript's own order.

`restriction base region` is `base` restricted to the support of `region`; the
manuscript takes the support of every (D8) entry to be the union of the
supports of the entries used, so a restriction names the coordinate whose
support delimits it rather than an ambient vertex set. -/
inductive Generated (S : DeclaredSignature) : Type where
  /-- A coordinate of one of the generating clauses (D1)--(D7). -/
  | gen (clause : S.Clause) (generator : S.Generator clause)
  /-- (D8), finite products. -/
  | product (left right : Generated S)
  /-- (D8), labelled copies. -/
  | copy (label : S.Label) (base : Generated S)
  /-- (D8), restrictions. -/
  | restriction (base region : Generated S)
  /-- (D8), quotient images. -/
  | image (label : S.Label) (base : Generated S)

/-- The value a declared coordinate reads.  A generating coordinate reads its
own value; an (D8) coordinate reads exactly the values of the entries it was
generated from, which is the whole content of "with support equal to the union
of the supports of the entries used": a derived coordinate reads nothing of the
support that its entries did not already read. -/
inductive Reading (S : DeclaredSignature) : Type where
  | base (value : S.Value)
  | product (left right : Reading S)
  | copy (label : S.Label) (base : Reading S)
  | restriction (base region : Reading S)
  | image (label : S.Label) (base : Reading S)

/-! ## The retained cut-state

`def:cold-corridor-first-failure` retains exactly four items.  The structure
below has exactly four fields, one per retained item, and the accompanying
`Equiv` is what makes it finite. -/

/-- **The cold corridor state of `def:cold-corridor-first-failure`.**

The finite two-boundary cut-state obtained from `ρ^ex_{T(J)}(J)` by retaining
exactly the boundary-degree profile, the two active boundary half-edges, the
cold-window offsets met at the two interfaces, and the declared local
coordinates whose support is contained in the bounded active interface.

The last field is that retention, literally: a generating coordinate supported
inside the active interface contributes `some` of its value, and one whose
support leaves the interface contributes `none`.  It "is not the full labelled
prefix": every (D8) coordinate is absent from the state, and
`reading_eq_of_state_eq` below is the theorem that it did not need to be
present. -/
structure CutState (S : DeclaredSignature) where
  /-- `d_∂`: the boundary-degree profile of the two active interfaces. -/
  boundaryDegrees : Fin 2 → Fin (S.degreeBound + 1)
  /-- The two active boundary half-edges. -/
  halfEdges : Fin 2 → Fin (S.degreeBound + 1)
  /-- The cold-window offsets met at the two interfaces. -/
  offsets : Fin 2 → Fin S.windowOrder
  /-- The declared local coordinates whose support is contained in the bounded
  active interface, with their values. -/
  declared : (clause : S.Clause) → S.Generator clause → Option S.Value

namespace CutState

variable {S : DeclaredSignature}

/-- The retained tuple, as an ordinary product.  It exists to carry finiteness
and decidable equality onto `CutState`; no declaration reads a component
through it. -/
@[simps] def equivProduct :
    CutState S ≃
      ((Fin 2 → Fin (S.degreeBound + 1)) × (Fin 2 → Fin (S.degreeBound + 1))) ×
        (Fin 2 → Fin S.windowOrder) ×
        ((clause : S.Clause) → S.Generator clause → Option S.Value) where
  toFun state :=
    ((state.boundaryDegrees, state.halfEdges), state.offsets, state.declared)
  invFun tuple :=
    { boundaryDegrees := tuple.1.1
      halfEdges := tuple.1.2
      offsets := tuple.2.1
      declared := tuple.2.2 }
  left_inv := by intro state; cases state; rfl
  right_inv := by intro tuple; rfl

noncomputable instance : Fintype (CutState S) := by
  letI : FinEnum S.Clause := S.clauseEnum
  letI : ∀ clause : S.Clause, FinEnum (S.Generator clause) := S.generatorEnum
  letI : FinEnum S.Value := S.valueEnum
  exact Fintype.ofEquiv _ equivProduct.symm

noncomputable instance : DecidableEq (CutState S) := by
  letI : FinEnum S.Clause := S.clauseEnum
  letI : ∀ clause : S.Clause, FinEnum (S.Generator clause) := S.generatorEnum
  letI : FinEnum S.Value := S.valueEnum
  exact fun left right =>
    decidable_of_iff (equivProduct left = equivProduct right)
      equivProduct.injective.eq_iff

end CutState

/-! ## The registered constants

`Q_cold` is the number of possible cold corridor states, which the manuscript
says depends only on the fixed declared signature.  Here it is exactly that:
`Fintype.card` of a type built from the signature's own finite alphabets, with
no graph in sight.

The three derived constants are the manuscript's, with its additive `30` and
its factor `15` read off the registered order and baseline rather than written:

* `30` "only covers the two `P₁₃`-window interfaces and the two boundary
  stubs", so it is `2·order + 2·2`;
* `15` is `b(P)`'s own numerator `δ·order − 2(order−1)`, the external-stub count
  of `lem:cold-window-stub-excess`, which at the registered presentation is
  `3·13 − 24 = 15`;
* the inner `3` of `1 + 3(2^{M+2} − 1)` is the registered baseline `δ`.
-/

/-- **`Q_cold`.**  The number of possible cold corridor states. -/
noncomputable def stateBound (S : DeclaredSignature) : Nat :=
  Fintype.card (CutState S)

/-- The manuscript's additive `30`: the two window interfaces and the two
boundary stubs, at the registered window order. -/
def interfaceBudget (S : DeclaredSignature) : Nat :=
  2 * S.windowOrder + 2 * 2

/-- **`M_cold := Q_cold + 30`.**  A uniform upper bound for the number of
vertices in a first-failure cold exchange. -/
noncomputable def exchangeBound (S : DeclaredSignature) : Nat :=
  stateBound S + interfaceBudget S

/-- The external-stub excess `b(P)`'s numerator `δ·order − 2(order−1)` of
`lem:cold-window-stub-excess`: the manuscript's `15`. -/
def stubExcess (threshold : Nat) (S : DeclaredSignature) : Nat :=
  threshold * S.windowOrder - 2 * (S.windowOrder - 1)

/-- **`B_cold := 15(1 + 3(2^{M_cold+2} − 1))`.**  A uniform upper bound for the
number of selected cold half-edges whose first-failure support can contain a
fixed subcubic vertex. -/
noncomputable def overlapBound (threshold : Nat) (S : DeclaredSignature) : Nat :=
  stubExcess threshold S * (1 + threshold * (2 ^ (exchangeBound S + 2) - 1))

/-- **`D_cold := M_cold·B_cold + 1`.** -/
noncomputable def extractionDenominator (threshold : Nat)
    (S : DeclaredSignature) : Nat :=
  exchangeBound S * overlapBound threshold S + 1

/-! ## Reading a corridor prefix

A presentation says how the corridor prefixes of one object supply the four
retained items and the declared values.  It is the interface between the
registered signature and a concrete corridor; the theorems below hold at every
presentation, so no corridor construction travels with a fact. -/

/-- **How the corridor prefixes of one object present their declared data.** -/
structure Presentation (S : DeclaredSignature) (object : FiniteObject.{u}) where
  /-- The initial segments `J` of the cold return corridors. -/
  Segment : Type u
  /-- `T(J)`: the bounded active interface of a segment. -/
  activeInterface : Segment → Finset object.Vertex
  /-- `supp_X(r)` for a generating coordinate. -/
  generatorSupport : (clause : S.Clause) → S.Generator clause →
    Finset object.Vertex
  /-- `val_X(r)` for a generating coordinate, read at a segment. -/
  generatorValue : Segment → (clause : S.Clause) → S.Generator clause → S.Value
  /-- The retained boundary-degree profile of the two active interfaces. -/
  boundaryDegrees : Segment → Fin 2 → Fin (S.degreeBound + 1)
  /-- The two active boundary half-edges. -/
  halfEdges : Segment → Fin 2 → Fin (S.degreeBound + 1)
  /-- The cold-window offsets met at the two interfaces. -/
  offsets : Segment → Fin 2 → Fin S.windowOrder

namespace Presentation

variable {S : DeclaredSignature} {object : FiniteObject.{u}}

/-- `supp_X(r)` for every declared coordinate, generating or derived.  Clause
(D8)'s support is the union of the supports of the entries used. -/
def support (presentation : Presentation.{u} S object) :
    Generated S → Set object.Vertex
  | .gen clause generator =>
      ↑(presentation.generatorSupport clause generator)
  | .product left right =>
      presentation.support left ∪ presentation.support right
  | .copy _label base => presentation.support base
  | .restriction base region =>
      presentation.support base ∪ presentation.support region
  | .image _label base => presentation.support base

/-- `val_X(r)` for every declared coordinate.  A derived coordinate is
evaluated from the entries it was generated from and reads nothing else. -/
def reading (presentation : Presentation.{u} S object)
    (segment : presentation.Segment) : Generated S → Reading S
  | .gen clause generator =>
      .base (presentation.generatorValue segment clause generator)
  | .product left right =>
      .product (presentation.reading segment left)
        (presentation.reading segment right)
  | .copy label base => .copy label (presentation.reading segment base)
  | .restriction base region =>
      .restriction (presentation.reading segment base)
        (presentation.reading segment region)
  | .image label base => .image label (presentation.reading segment base)

variable (presentation : Presentation.{u} S object)

/-- **The cold corridor state of a segment**, retaining exactly the four items
`def:cold-corridor-first-failure` names. -/
noncomputable def state (segment : presentation.Segment) : CutState S := by
  classical
  exact
    { boundaryDegrees := presentation.boundaryDegrees segment
      halfEdges := presentation.halfEdges segment
      offsets := presentation.offsets segment
      declared := fun clause generator =>
        if presentation.generatorSupport clause generator ⊆
            presentation.activeInterface segment then
          some (presentation.generatorValue segment clause generator)
        else
          none }

/-- **The state retains every generating coordinate supported in the active
interface.**

This is the first half of the manuscript's "equality of cold corridor states is
equality for every target-response coordinate used by the local replacement":
two segments with the same state agree at every generating coordinate whose
support one of them keeps -- and, as the second conclusion records, the other
keeps it too. -/
theorem generatorValue_eq_of_state_eq
    {left right : presentation.Segment}
    (same : presentation.state left = presentation.state right)
    (clause : S.Clause) (generator : S.Generator clause)
    (inside : presentation.generatorSupport clause generator ⊆
      presentation.activeInterface left) :
    presentation.generatorSupport clause generator ⊆
        presentation.activeInterface right ∧
      presentation.generatorValue left clause generator =
        presentation.generatorValue right clause generator := by
  classical
  have entries := congrArg (fun s => CutState.declared s clause generator) same
  simp only [state, inside, if_true] at entries
  by_cases outside : presentation.generatorSupport clause generator ⊆
      presentation.activeInterface right
  · simp only [outside, if_true] at entries
    exact ⟨outside, Option.some.inj entries⟩
  · simp only [outside, if_false] at entries
    exact absurd entries (Option.some_ne_none _)

/-- **Equality of cold corridor states is equality for every declared
coordinate supported in the active interface**, generating or derived.

This is the manuscript's sentence in full.  The state retains no (D8)
coordinate, and it does not have to: an (D8) coordinate reads only the entries
it was generated from, so once the generating readings agree the derived
reading agrees by induction on the generation.  That is exactly why the state
"is not the full labelled prefix" and is still complete for the local
replacement. -/
theorem reading_eq_of_state_eq
    {left right : presentation.Segment}
    (same : presentation.state left = presentation.state right) :
    ∀ coordinate : Generated S,
      presentation.support coordinate ⊆
          ↑(presentation.activeInterface left) →
        presentation.reading left coordinate =
          presentation.reading right coordinate := by
  intro coordinate
  induction coordinate with
  | gen clause generator =>
      intro inside
      exact congrArg Reading.base
        ((presentation.generatorValue_eq_of_state_eq same clause generator
          (by exact_mod_cast inside)).2)
  | product left' right' leftIH rightIH =>
      intro inside
      rw [support] at inside
      exact congrArg₂ Reading.product
        (leftIH (Set.Subset.trans Set.subset_union_left inside))
        (rightIH (Set.Subset.trans Set.subset_union_right inside))
  | copy label base baseIH =>
      intro inside
      exact congrArg (Reading.copy label) (baseIH inside)
  | restriction base region baseIH regionIH =>
      intro inside
      rw [support] at inside
      exact congrArg₂ Reading.restriction
        (baseIH (Set.Subset.trans Set.subset_union_left inside))
        (regionIH (Set.Subset.trans Set.subset_union_right inside))
  | image label base baseIH =>
      intro inside
      exact congrArg (Reading.image label) (baseIH inside)

/-! ### Excluding (F2)

`def:cold-corridor-first-failure` continues: "If two prefixes have the same
finite cut-state but differ in exact target response against some compatible
context, that discrepancy is recorded as a first failure of type (F2) below.
Thus, after excluding (F2), equality of cold corridor states is equality for
every target-response coordinate used by the local replacement."

The discrepancy is named and the conclusion is drawn.  A prefix's response is
read at whatever boundary piece carries it -- the carrier is a parameter, so
the statement holds for every reading of the corridor, not for one chosen
one. -/

/-- **(F2) at two segments**: they have the same finite cut-state but differ in
exact target response against some compatible context. -/
def FirstFailureResponse {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} → Prop)
    (carrier : presentation.Segment → BoundaryPiece boundary)
    (left right : presentation.Segment) : Prop :=
  presentation.state left = presentation.state right ∧
    Response.TargetDefect Target (carrier left) (carrier right)

/-- **"After excluding (F2), equality of cold corridor states is equality for
every target-response coordinate used by the local replacement."**

With the discrepancy excluded, two segments carrying the same cut-state have
the same target response against *every* compatible context -- which is
precisely what the local replacement of `lem:cold-same-interface-table` needs
in order to identify them. -/
theorem contextEquivalent_of_state_eq {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} → Prop}
    {carrier : presentation.Segment → BoundaryPiece boundary}
    {left right : presentation.Segment}
    (excluded : ¬ presentation.FirstFailureResponse Target carrier left right)
    (same : presentation.state left = presentation.state right) :
    Response.ContextEquivalent Target (carrier left) (carrier right) := by
  classical
  intro outside
  by_contra distinguishes
  exact excluded ⟨same, ⟨outside, distinguishes⟩⟩

/-- The converse reading: a genuine response discrepancy between two segments
with the same cut-state *is* a first failure of type (F2).  Together with the
theorem above this is the manuscript's dichotomy at a repeated state -- either
the responses agree, or (F2) has occurred. -/
theorem firstFailureResponse_of_not_contextEquivalent {boundary : Boundary.{u}}
    {Target : FiniteObject.{u} → Prop}
    {carrier : presentation.Segment → BoundaryPiece boundary}
    {left right : presentation.Segment}
    (same : presentation.state left = presentation.state right)
    (separated :
      ¬ Response.ContextEquivalent Target (carrier left) (carrier right)) :
    presentation.FirstFailureResponse Target carrier left right :=
  ⟨same, Response.targetDefect_of_not_contextEquivalent separated⟩

/-- **The cold corridor states of one object number at most `Q_cold`.**

Read `Q_cold` states of a corridor and two of them are equal: that is the
pigeonhole `lem:cold-corridor-first-failure` uses to produce the repeat subcase
of (F5). -/
theorem exists_state_eq_of_stateBound_lt
    (segments : Fin (stateBound S + 1) → presentation.Segment) :
    ∃ left right, left ≠ right ∧
      presentation.state (segments left) = presentation.state (segments right) := by
  classical
  have card :
      Fintype.card (CutState S) < Fintype.card (Fin (stateBound S + 1)) := by
    rw [Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨left, right, distinct, same⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun index => presentation.state (segments index)) card
  exact ⟨left, right, distinct, same⟩

end Presentation

/-! ## The cold return corridor

`def:cold-corridor-first-failure` opens by building the corridor before it
states the cut-state:

> Let `X_cold` be the union of the ambient-cubic cold windows, with their
> internal path edges retained.  Delete the interiors of these windows and look
> at a connected component `K` of the remaining outside graph.  The *boundary
> stubs* of `K` are the edges from `K` to ambient-cubic cold windows.  By
> `lem:bridgeless`, no such component has only one boundary stub, since that
> unique boundary edge would be a bridge of `G`.
>
> Order the boundary stubs of `K` lexicographically as `h₁,…,h_m` (`m ≥ 2`) and
> give them the cyclic successor relation `hᵢ ↦ hᵢ₊₁`, with `h_{m+1} = h₁`.  If
> `hᵢ = ε` is a selected branch-excess half-edge, choose inside `K` the
> lexicographically first simple path joining the outside endpoint of `hᵢ` to
> the outside endpoint of `hᵢ₊₁`.  Together with the two boundary stubs
> `hᵢ, hᵢ₊₁`, this path is the *cold return corridor* of `ε`.
>
> Thus each selected branch-excess half-edge has exactly one corridor, and each
> boundary stub is the successor of at most one selected half-edge.

All of that is below, and it is what makes the cut-state theorems apply to a
graph rather than to an abstract interface: `Corridor.presentation` produces a
`Presentation` from a real corridor, so `stateBound`,
`reading_eq_of_state_eq` and `exists_state_eq_of_stateBound_lt` speak about
real prefixes of a real corridor.

`lem:bridgeless` itself is a separate lemma about the selected object, not part
of this definition; it enters as the named field `twoStubs`. -/

/-- **A boundary stub of `K`**: an edge from the component to the ambient-cubic
cold windows, recorded by its outside endpoint and its window endpoint. -/
def IsBoundaryStub (object : FiniteObject.{u})
    (windows component : Finset object.Vertex)
    (stub : object.Vertex × object.Vertex) : Prop :=
  stub.1 ∈ component ∧ stub.2 ∈ windows ∧ object.graph.Adj stub.1 stub.2

instance (object : FiniteObject.{u}) (windows component : Finset object.Vertex)
    (stub : object.Vertex × object.Vertex) :
    Decidable (IsBoundaryStub object windows component stub) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  unfold IsBoundaryStub
  infer_instance

/-- **The boundary stubs of `K`, "ordered lexicographically as `h₁,…,h_m`".**

The order is the object's own enumeration of vertex pairs, which is the only
order available on a finitely enumerated carrier and is what "lexicographically"
names.  Nothing chooses it. -/
noncomputable def boundaryStubs (object : FiniteObject.{u})
    (windows component : Finset object.Vertex) :
    List (object.Vertex × object.Vertex) := by
  letI : FinEnum object.Vertex := object.vertices
  exact (FinEnum.toList (object.Vertex × object.Vertex)).filter
    fun stub => decide (IsBoundaryStub object windows component stub)

theorem mem_boundaryStubs_iff (object : FiniteObject.{u})
    (windows component : Finset object.Vertex)
    (stub : object.Vertex × object.Vertex) :
    stub ∈ boundaryStubs object windows component ↔
      IsBoundaryStub object windows component stub := by
  letI : FinEnum object.Vertex := object.vertices
  simp only [boundaryStubs, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun member => member.2, fun isStub => ⟨FinEnum.mem_toList _, isStub⟩⟩

theorem boundaryStubs_nodup (object : FiniteObject.{u})
    (windows component : Finset object.Vertex) :
    (boundaryStubs object windows component).Nodup := by
  letI : FinEnum object.Vertex := object.vertices
  exact List.Nodup.filter _ FinEnum.nodup_toList

/-- **The cyclic successor `hᵢ ↦ hᵢ₊₁`, with `h_{m+1} = h₁`.** -/
def successorIndex {count : Nat} (positive : 0 < count) (index : Fin count) :
    Fin count :=
  ⟨(index.1 + 1) % count, Nat.mod_lt _ positive⟩

/-- **"Each boundary stub is the successor of at most one selected
half-edge."**  The cyclic successor is injective, so two distinct selected
half-edges never share a successor stub. -/
theorem successorIndex_injective {count : Nat} (positive : 0 < count) :
    Function.Injective (successorIndex positive) := by
  intro left right same
  have equal : (left.1 + 1) % count = (right.1 + 1) % count :=
    congrArg Fin.val same
  refine Fin.ext ?_
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt left.2) with leftEq | leftSmall
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt right.2) with rightEq | rightSmall
    · omega
    · have leftZero : (left.1 + 1) % count = 0 :=
        (congrArg (· % count) leftEq).trans (Nat.mod_self count)
      rw [leftZero, Nat.mod_eq_of_lt rightSmall] at equal
      omega
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt right.2) with rightEq | rightSmall
    · have rightZero : (right.1 + 1) % count = 0 :=
        (congrArg (· % count) rightEq).trans (Nat.mod_self count)
      rw [rightZero, Nat.mod_eq_of_lt leftSmall] at equal
      omega
    · rw [Nat.mod_eq_of_lt leftSmall, Nat.mod_eq_of_lt rightSmall] at equal
      omega

/-- The outside endpoint of a boundary stub, as a vertex of `K`. -/
noncomputable def stubFoot (object : FiniteObject.{u})
    (windows component : Finset object.Vertex)
    (index : Fin (boundaryStubs object windows component).length) :
    (object.induce component).Vertex :=
  ⟨((boundaryStubs object windows component).get index).1,
    ((mem_boundaryStubs_iff object windows component _).1
      (List.get_mem _ _)).1⟩

/-- **The cold return corridor of a selected branch-excess half-edge.**

`entry` is the index of the selected half-edge `ε = hᵢ` among the ordered
boundary stubs of `K`; its corridor runs to the cyclic successor `hᵢ₊₁`.

`twoStubs` is `lem:bridgeless` at this component -- "no such component has only
one boundary stub, since that unique boundary edge would be a bridge of `G`".
It is a field because it is a theorem about the selected object, proved
elsewhere, and not part of this definition.

`connected` is what lets the manuscript "choose inside `K` the lexicographically
first simple path": the two outside feet are joined inside the component. -/
structure Corridor (object : FiniteObject.{u})
    (windows component : Finset object.Vertex) where
  /-- `lem:bridgeless`: the component has at least two boundary stubs. -/
  twoStubs : 2 ≤ (boundaryStubs object windows component).length
  /-- The index of the selected branch-excess half-edge `ε = hᵢ`. -/
  entry : Fin (boundaryStubs object windows component).length
  /-- The two outside endpoints are joined inside `K`. -/
  connected :
    (object.induce component).graph.Reachable
      (stubFoot object windows component entry)
      (stubFoot object windows component
        (successorIndex (Nat.lt_of_lt_of_le Nat.zero_lt_two twoStubs) entry))

namespace Corridor

/-- The component has at least one boundary stub. -/
theorem positive {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) :
    0 < (boundaryStubs object windows component).length :=
  Nat.lt_of_lt_of_le Nat.zero_lt_two corridor.twoStubs

/-- `ε = hᵢ`, the selected branch-excess half-edge. -/
noncomputable def entryStub {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) :
    object.Vertex × object.Vertex :=
  (boundaryStubs object windows component).get corridor.entry

/-- `hᵢ₊₁`, its cyclic successor stub. -/
noncomputable def successorStub {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) :
    object.Vertex × object.Vertex :=
  (boundaryStubs object windows component).get
    (successorIndex corridor.positive corridor.entry)

/-- **The path inside `K`**: the lexicographically first simple path joining the
two outside endpoints, selected by the framework's own canonical schedule --
which is exactly the manuscript's "lexicographically first". -/
noncomputable def inside {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) :
    (object.induce component).graph.Path
      (stubFoot object windows component corridor.entry)
      (stubFoot object windows component
        (successorIndex corridor.positive corridor.entry)) := by
  letI : FinEnum (object.induce component).Vertex :=
    (object.induce component).vertices
  letI : Fintype (object.induce component).Vertex := inferInstance
  letI : DecidableEq (object.induce component).Vertex :=
    (object.induce component).vertices.decEq
  letI : DecidableRel (object.induce component).graph.Adj :=
    (object.induce component).decideAdj
  exact (Hypostructure.Graph.FinitePathSelection.selectOfReachable
    (object.induce component).graph corridor.connected).path

/-- **The initial segments `J` of the corridor**, indexed by how far along the
inside path they reach.  Segment `0` is the entry stub alone and the last is the
whole corridor. -/
abbrev Segment {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) : Type :=
  Fin (corridor.inside.1.length + 1)

/-- The head of an initial segment: the vertex of `K` the prefix has reached. -/
noncomputable def head {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component)
    (segment : corridor.Segment) : object.Vertex :=
  (corridor.inside.1.getVert segment.1).1

/-- **`T(J)`, the two active boundary interfaces of an initial segment.**

The entry stub's two endpoints -- its window interface and its outside foot --
together with the vertex the prefix has reached.  Both interfaces are active:
the corridor is anchored at `ε` and advances at its head, and the manuscript's
"bounded active interface" is exactly this. -/
noncomputable def activeInterface {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component)
    (segment : corridor.Segment) : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact {corridor.entryStub.2, corridor.entryStub.1, corridor.head segment}

/-- **The active interface is bounded, uniformly in the segment.**  It never
carries more than the two boundary endpoints and the prefix head, which is why
the retained cut-state is bounded by a constant of the signature and not by the
graph. -/
theorem activeInterface_card_le {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component)
    (segment : corridor.Segment) :
    (corridor.activeInterface segment).card ≤ 3 := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
  exact le_trans (Finset.card_insert_le _ _)
    (Nat.succ_le_succ (le_of_eq (Finset.card_singleton _)))

/-- **The corridor's presentation of the declared data.**

Everything the cut-state retains is computed here from the corridor itself: the
segments are its initial segments, the active interface is `T(J)`, the
boundary-degree profile is the object's own degree at the two interfaces, the
half-edges are the two boundary stubs, and the offsets are the cold-window
offsets the two interfaces meet, read by the packing's own offset map.

`supp_X(r)` and `val_X(r)` are supplied by the owner of the clause a coordinate
belongs to -- a degree, a return length, a Mersenne test, a trace, a fan, a
surplus port.  That is what a clause *is* in
`def:declared-coordinate-signature`: the signature fixes which coordinates exist
and the cut-state fixes what is retained of them, and neither invents what one
reads. -/
noncomputable def presentation {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) (S : DeclaredSignature)
    (offsetOf : object.Vertex → Fin S.windowOrder)
    (support : (clause : S.Clause) → S.Generator clause →
      Finset object.Vertex)
    (value : corridor.Segment → (clause : S.Clause) → S.Generator clause →
      S.Value) :
    Presentation.{u} S object where
  Segment := ULift corridor.Segment
  activeInterface := fun segment => corridor.activeInterface segment.down
  generatorSupport := support
  generatorValue := fun segment => value segment.down
  boundaryDegrees := fun segment index =>
    ⟨min (object.degree (if index = 0 then corridor.entryStub.1
        else corridor.head segment.down)) S.degreeBound,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  halfEdges := fun _segment index =>
    ⟨min (if index = 0 then corridor.entry.1
        else (successorIndex corridor.positive corridor.entry).1) S.degreeBound,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  offsets := fun _segment index =>
    offsetOf (if index = 0 then corridor.entryStub.2
      else corridor.successorStub.2)

@[simp] theorem presentation_activeInterface {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (corridor : Corridor object windows component) (S : DeclaredSignature)
    (offsetOf : object.Vertex → Fin S.windowOrder)
    (support : (clause : S.Clause) → S.Generator clause →
      Finset object.Vertex)
    (value : corridor.Segment → (clause : S.Clause) → S.Generator clause →
      S.Value) (segment : corridor.Segment) :
    (corridor.presentation S offsetOf support value).activeInterface
        (ULift.up segment) =
      corridor.activeInterface segment := rfl

/-- **"Each selected branch-excess half-edge has exactly one corridor."**

A corridor of a component is determined by its selected half-edge: the other two
fields are proofs, so two corridors with the same `entry` run between the same
two stubs and select the same path. -/
theorem eq_of_entry_eq {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (left right : Corridor object windows component)
    (same : left.entry = right.entry) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- **"Each boundary stub is the successor of at most one selected
half-edge."**  Two corridors of one component whose successor stubs coincide
have the same selected half-edge -- the stub list has no repeats and the cyclic
successor is injective -- and therefore are the same corridor. -/
theorem eq_of_successorStub_eq {object : FiniteObject.{u}}
    {windows component : Finset object.Vertex}
    (left right : Corridor object windows component)
    (same : left.successorStub = right.successorStub) : left = right := by
  refine eq_of_entry_eq left right (successorIndex_injective left.positive ?_)
  have indices :
      (boundaryStubs object windows component).get
          (successorIndex left.positive left.entry) =
        (boundaryStubs object windows component).get
          (successorIndex left.positive right.entry) := by
    simpa [Corridor.successorStub, successorIndex] using same
  exact (List.Nodup.get_inj_iff
    (boundaryStubs_nodup object windows component)).1 indices

/-! ### The cut-state theorems, at a real corridor

`Presentation` is where the cut-state theorems are stated, and
`Corridor.presentation` inhabits it from a corridor of an actual graph.  The two
corollaries below are those theorems read there, so nothing about `Q_cold` or
the retention is vacuous: they speak about the initial segments of the
lexicographically first simple path inside `K`. -/

section CorridorState

variable {object : FiniteObject.{u}} {windows component : Finset object.Vertex}
variable (corridor : Corridor object windows component) (S : DeclaredSignature)
variable (offsetOf : object.Vertex → Fin S.windowOrder)
variable (support : (clause : S.Clause) → S.Generator clause →
  Finset object.Vertex)
variable (value : corridor.Segment → (clause : S.Clause) → S.Generator clause →
  S.Value)

/-- **`lem:cold-corridor-first-failure`, the pigeonhole of (F5).**

*"Otherwise, before the successor is reached, `Q_cold + 1` states are read; two
states are equal by the definition of `Q_cold`, and the first such equality
gives the repeat subcase of (F5)."*

Read `Q_cold + 1` initial segments of a real corridor and two of them carry the
same cold corridor state.  This is the step that makes a first failure always
exist. -/
theorem exists_repeated_state
    (segments : Fin (stateBound S + 1) → corridor.Segment) :
    ∃ left right, left ≠ right ∧
      (corridor.presentation S offsetOf support value).state
          (ULift.up (segments left)) =
        (corridor.presentation S offsetOf support value).state
          (ULift.up (segments right)) :=
  (corridor.presentation S offsetOf support value).exists_state_eq_of_stateBound_lt
    (fun index => ULift.up (segments index))

/-- **The retention is complete on a real corridor.**  Two initial segments with
the same cold corridor state agree at every declared coordinate supported in the
active interface, derived (D8) coordinates included. -/
theorem reading_eq_of_state_eq {left right : corridor.Segment}
    (same : (corridor.presentation S offsetOf support value).state
        (ULift.up left) =
      (corridor.presentation S offsetOf support value).state (ULift.up right))
    (coordinate : Generated S)
    (inside : (corridor.presentation S offsetOf support value).support coordinate
      ⊆ ↑(corridor.activeInterface left)) :
    (corridor.presentation S offsetOf support value).reading (ULift.up left)
        coordinate =
      (corridor.presentation S offsetOf support value).reading (ULift.up right)
        coordinate :=
  (corridor.presentation S offsetOf support value).reading_eq_of_state_eq same
    coordinate inside

end CorridorState

end Corridor

/-! ## `lem:cold-short-self-return-filter`

A cold-window outside self-return of outside length `ℓ` is smeared over the
window offsets, which tests the whole interval `[ℓ, ℓ+smear]` with
`smear = order − 1`.  The return *survives* the filter when that interval
avoids every accepted length; all other short self-returns realize an accepted
cycle, because the corresponding offset closes one through the window.

Nothing here writes the manuscript's `{17,18,19,33,…,39}`: that list is the
value of `survivingLengths` at the registered accepted-length predicate, the
registered window order, and the registered stub excess, and
`Fixtures.ColdCorridorShortSelfReturn` computes it. -/

/-- **The surviving-length condition of `lem:cold-short-self-return-filter`.**
The smear interval `[length, length+smear]` avoids every accepted length. -/
def SurvivesSmear (LengthOK : Nat → Prop) (smear length : Nat) : Prop :=
  ∀ tested, length ≤ tested → tested ≤ length + smear → ¬ LengthOK tested

/-- **"All other short self-returns realize a dyadic cycle."**  A length that
does not survive the smear supplies the offset that closes an accepted
cycle. -/
theorem exists_accepted_of_not_survivesSmear {LengthOK : Nat → Prop}
    {smear length : Nat} (failed : ¬ SurvivesSmear LengthOK smear length) :
    ∃ tested, length ≤ tested ∧ tested ≤ length + smear ∧ LengthOK tested := by
  classical
  by_contra missing
  exact failed fun tested lower upper accepted =>
    missing ⟨tested, lower, upper, accepted⟩

/-- The surviving lengths of `[1, bound]`, computed from the accepted-length
predicate.  `lem:cold-short-self-return-filter` is the statement that this list
is what it is at the registered data; the list itself is not written down. -/
def survivingLengths (LengthOK : Nat → Prop) [DecidablePred LengthOK]
    (smear bound : Nat) : List Nat :=
  (List.range' 1 bound).filter fun length =>
    ((List.range' length (smear + 1)).all fun tested => !decide (LengthOK tested))

/-- The computed list is exactly the surviving lengths of the range. -/
theorem mem_survivingLengths_iff {LengthOK : Nat → Prop}
    [DecidablePred LengthOK] {smear bound length : Nat} :
    length ∈ survivingLengths LengthOK smear bound ↔
      (1 ≤ length ∧ length < 1 + bound) ∧ SurvivesSmear LengthOK smear length := by
  classical
  simp only [survivingLengths, List.mem_filter, List.mem_range', List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, SurvivesSmear]
  constructor
  · rintro ⟨⟨index, small, rfl⟩, avoids⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro tested lower upper
    exact avoids tested ⟨tested - (1 + 1 * index), by omega, by omega⟩
  · rintro ⟨⟨lower, upper⟩, avoids⟩
    refine ⟨⟨length - 1, by omega, by omega⟩, ?_⟩
    rintro tested ⟨index, small, rfl⟩
    exact avoids _ (by omega) (by omega)

/-! ## `def:cold-same-interface-table`

The table's rows are equal-length cold bounded germs and the short self-return
exceptions above.  A row records (T1) the two boundary vertices and their
boundary-degree profile, (T2) the two terminal cold-window stubs and their
offsets, (T3) the exact response profile generated by the declared signature,
and (T4) the target truth value of every compatible completion represented by
that exact profile.

`Record` is that recording, one field per clause, and `Fintype (Record S)` is
the manuscript's "the table is finite because the support size, boundary size,
window labels, and declared coordinate labels are bounded". -/

/-- **What `def:cold-same-interface-table` records of a row.** -/
structure Record (S : DeclaredSignature) where
  /-- (T1) the two boundary vertices and their boundary-degree profile. -/
  boundaryDegrees : Fin 2 → Fin (S.degreeBound + 1)
  /-- (T2) the two terminal cold-window stubs. -/
  stubs : Fin 2 → Fin (S.degreeBound + 1)
  /-- (T2) and their offsets in the cold window. -/
  offsets : Fin 2 → Fin S.windowOrder
  /-- (T3) the exact response profile generated by the declared signature,
  which is the row's own cold corridor state. -/
  state : CutState S
  /-- (T4) the target truth value of every compatible completion represented by
  that exact profile. -/
  truth : Bool

namespace Record

variable {S : DeclaredSignature}

/-- The recorded tuple, as an ordinary product.  It carries finiteness onto
`Record`; no declaration reads a clause through it. -/
@[simps] def equivProduct :
    Record S ≃
      ((Fin 2 → Fin (S.degreeBound + 1)) × (Fin 2 → Fin (S.degreeBound + 1))) ×
        (Fin 2 → Fin S.windowOrder) × CutState S × Bool where
  toFun row := ((row.boundaryDegrees, row.stubs), row.offsets, row.state, row.truth)
  invFun tuple :=
    { boundaryDegrees := tuple.1.1
      stubs := tuple.1.2
      offsets := tuple.2.1
      state := tuple.2.2.1
      truth := tuple.2.2.2 }
  left_inv := by intro row; cases row; rfl
  right_inv := by intro tuple; rfl

noncomputable instance : Fintype (Record S) :=
  Fintype.ofEquiv _ equivProduct.symm

end Record

/-- **The same-interface cold table is finite**, with at most this many
distinct rows.  Every bound is the registered signature's: the boundary size is
two, the retained boundary data is capped by the local target algebra's own
cut-state constant, the offsets range over the registered window order, and the
declared coordinate labels are the signature's finite alphabets. -/
noncomputable def tableBound (S : DeclaredSignature) : Nat :=
  Fintype.card (Record S)

/-! ## A row of the table

A row sits at a proper connected support of the object: `Q[x,y]` is the
support's own boundary piece, `E` is the canonical same-interface
representative determined by the repeated cold corridor state, and the two
share an interface, a boundary-degree profile, and -- this being the
equal-length half of the table -- an internal size.

`Handoff` is the already-closed ledger the manuscript hands a row's charge to:
"the corridor first enters a declared Type B handoff envelope or the route-8
carrier support **already recorded in the branch state**".  It is a parameter
supplied by whoever owns that ledger, never a field the row may choose. -/

variable {object : FiniteObject.{u}}

/-- The proper atom a row's support determines. -/
@[reducible] noncomputable def rowAtom (object : FiniteObject.{u})
    (support : Finset object.Vertex)
    (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) :
    OwnedDecomposition object :=
  (Strategy.InterfaceReplacement.SupportAtom.properAtom object support connected
    proper).decomposition

/-- **`def:cold-bounded-germ`**, at a proper support of one object.

*"A cold bounded germ is a finite boundaried support with two boundary
interfaces `x, y` and two same-interface `x`-`y` representatives `Q[x,y]` and
`E`. … The germ also carries the inherited boundary degree profile,
`P₁₃`-window labels, and target-response profile."*

The first three fields are the support, whose own boundary piece is `Q[x,y]`;
`canonical` is the second representative `E`; `sameProfile` is the inherited
boundary-degree profile; `record` and `record_truth` are the window labels and
the target-response profile, recorded exactly as `def:cold-same-interface-table`
records them, because that definition's (T1)--(T4) *is* the germ's carried
data.  The increment `δ := |E| − |Q[x,y]|` is derived below rather than stored,
so no germ may declare a length change it does not have.

The germ says nothing about `δ`: `def:cold-bounded-germ` is the common
definition of the equal-length rows of the table and the length-changing germs
of `lem:cold-bounded-germ-trichotomy`, and `TableRow` below is exactly this
structure with the equal-length clause added. -/
structure BoundedGerm (S : DeclaredSignature)
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u}) where
  /-- The bounded support the germ occupies. -/
  support : Finset object.Vertex
  connected : Graph.SupportComponents.Connected.ConnectedOn object support
  proper : ∃ vertex, vertex ∉ support
  /-- `E`: the second same-interface representative. -/
  canonical : BoundaryPiece (rowAtom object support connected proper).interface
  /-- The inherited boundary-degree profile is shared. -/
  sameProfile :
    canonical.boundaryDegreeProfile =
      (rowAtom object support connected proper).piece.boundaryDegreeProfile
  /-- The replacement meets the standing baseline. -/
  baseline :
    Baseline (glue canonical (rowAtom object support connected proper).outside)
  /-- The carried window labels and target-response profile. -/
  record : Record S
  /-- The recorded truth value, at this germ's own completions. -/
  record_truth : ∀ outside, record.truth = true ↔ Target (glue canonical outside)

namespace BoundedGerm

variable {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
variable (germ : BoundedGerm S Baseline Target object)

/-- The proper atom the germ's support determines. -/
@[reducible] noncomputable def atom : OwnedDecomposition object :=
  rowAtom object germ.support germ.connected germ.proper

/-- `Q[x,y]`: the support's own boundary piece, the first representative. -/
@[reducible] noncomputable def piece :
    BoundaryPiece germ.atom.interface :=
  germ.atom.piece

/-- **G1, hit-realized**: the germ's own compatible completion realizes the
target.  `lem:cold-bounded-germ-trichotomy`'s first case is that "some
compatible live completion and window offset close a dyadic cycle", and the
corridor representative's own completion *is* `G`, up to the decomposition's
reconstruction. -/
def Realizing : Prop :=
  Target (glue germ.piece germ.atom.outside)

/-- **G2, hit-distinguished**: some compatible outside context distinguishes
the two representatives by target truth value. -/
def Distinguishing : Prop :=
  Response.TargetDefect Target germ.piece germ.canonical

/-- **G3, silent**: neither realizing nor distinguishing. -/
def Neutral : Prop := ¬ germ.Realizing ∧ ¬ germ.Distinguishing

/-- **`def:cold-bounded-germ`'s increment `δ := |E| − |Q[x,y]|`.**

`Q[x,y]` is the corridor representative -- "the actual corridor segment" -- and
`E` is the canonical one "determined by the repeated cold corridor state".  The
increment is their difference in internal size, taken in `Int` so that the
manuscript's sign is available and no truncation hides a length change. -/
noncomputable def increment : Int :=
  (germ.canonical.internalVertexCount : Int) -
    (germ.piece.internalVertexCount : Int)

/-- **Length-changing**, `δ ≠ 0`; its negation is the equal-length case. -/
def LengthChanging : Prop := germ.increment ≠ 0

/-- `δ = 0` is exactly the equal-length clause of `def:cold-bounded-germ`. -/
theorem increment_eq_zero_iff :
    germ.increment = 0 ↔
      germ.canonical.internalVertexCount = germ.piece.internalVertexCount := by
  unfold increment
  omega

/-- **`def:cold-bounded-germ`'s dichotomy.**  *"It is length-changing if
`δ ≠ 0`, and equal-length if `δ = 0`."*  A germ fails to be length-changing
exactly when its two representatives have the same internal size, which is
`TableRow`'s `equalLength` clause -- so the germs that are *not* length-changing
are exactly the rows of `def:cold-same-interface-table`.  This is
`lem:cold-increment-arithmetic`'s case (d): "the equal-length switch belongs to
the finite same-interface cold table". -/
theorem not_lengthChanging_iff :
    ¬ germ.LengthChanging ↔
      germ.canonical.internalVertexCount = germ.piece.internalVertexCount := by
  rw [LengthChanging, not_not]
  exact germ.increment_eq_zero_iff

/-- **The three cases are exhaustive.**  `lem:cold-bounded-germ-trichotomy`'s
own reading: the split is "by whether a compatible completion realizes a dyadic
hit, distinguishes dyadic truth without realization in `G`, or never
distinguishes the two representatives", so G3 is the negation of the first two
and nothing falls outside.  This is also what
`lem:cold-increment-arithmetic` (c) appeals to when it routes a periodic
carrier to G2 when target-visible and to G3 when not. -/
theorem trichotomy : germ.Realizing ∨ germ.Distinguishing ∨ germ.Neutral := by
  classical
  by_cases realizing : germ.Realizing
  · exact Or.inl realizing
  · by_cases distinguishing : germ.Distinguishing
    · exact Or.inr (Or.inl distinguishing)
    · exact Or.inr (Or.inr ⟨realizing, distinguishing⟩)

/-- **G1: a realizing germ would give the ambient object the target.**  The
corridor representative glued to its own outside context is the object, up to
the decomposition's reconstruction isomorphism.  "This contradicts the
counterexample condition." -/
theorem target_of_realizing
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (realizing : germ.Realizing) : Target object :=
  (targetInvariant.iff_of_iso ⟨germ.atom.reconstructionIso⟩).mp realizing

/-- **G2, through `lem:context-universality`: a distinguishing germ's
identification is not target-complete.**

*"The two local responses agree in the actual quotient but disagree in a
compatible context.  By `lem:context-universality`, such an identification is
not target-complete; equivalently it is a target-defective quotient."*

The conclusion holds in *every* immutable profile fibre, which is what makes it
a statement about the quotient rather than about one chosen profile: the
distinguishing context already denies the all-context clause of
`def:target-complete-quotient`, so no fibre can repair it. -/
theorem not_targetComplete_of_distinguishing
    {Profile : Type uProfile}
    (profile : BoundaryPiece germ.atom.interface → Profile)
    (distinguishing : germ.Distinguishing) :
    ¬ Response.TargetComplete profile Target germ.piece germ.canonical := by
  rintro complete
  obtain ⟨outside, distinguishes⟩ := distinguishing
  exact distinguishes (complete.contextEquivalent outside)

/-- The shorter representative, glued back into the germ's own outside context,
is strictly smaller than the ambient object.

Only the vertex count is needed: gluing adds the boundary and the context's
internal vertices to the piece's own, so a representative with strictly fewer
internal vertices gives a strictly smaller graph, and the germ's own completion
is the object up to the decomposition's reconstruction isomorphism. -/
theorem lexicographicallySmaller_of_increment_neg
    (shorter : germ.increment < 0) :
    (glue germ.canonical germ.atom.outside).LexicographicallySmaller object := by
  have internal :
      germ.canonical.internalVertexCount < germ.atom.piece.internalVertexCount := by
    unfold increment at shorter
    change (germ.canonical.internalVertexCount : Int) -
      (germ.atom.piece.internalVertexCount : Int) < 0 at shorter
    omega
  refine (FiniteObject.lexicographicallySmaller_congr_right
    ⟨germ.atom.reconstructionIso⟩).mp ?_
  apply FiniteObject.lexicographicallySmaller_of_vertexCount_lt
  simp only [atom, glue_vertexCount] at internal ⊢
  omega

/-- **G3: a silent length-changing germ is a target-complete compression of its
own proper support.**

*"Then replacing the longer representative by the shorter one preserves the
boundary degree profile and the target response against every context, creates
no dyadic cycle, and strictly decreases the support.  This is a nontrivial
target-complete compression of a proper support."*

Every clause of `CompressibleSupport` is present: the shared boundary-degree
profile and the baseline are fields of the germ, the strict decrease is the
increment's own sign, and the target response against every context is exactly
the failure of `Distinguishing`.  Unlike the equal-length rows of
`def:cold-same-interface-table`, no appeal to `def:admissible-rank-quotient` is
made or needed here -- the manuscript descends on the length change itself. -/
theorem compressibleSupport_of_not_distinguishing
    (shorter : germ.increment < 0)
    (notDistinguishing : ¬ germ.Distinguishing) :
    Strategy.InterfaceReplacement.CompressibleSupport Baseline Target object
      germ.support := by
  classical
  have equivalent :
      Response.ContextEquivalent Target germ.piece germ.canonical := by
    intro outside
    by_contra distinguishes
    exact notDistinguishing ⟨outside, distinguishes⟩
  exact ⟨germ.connected, germ.proper, germ.canonical, germ.sameProfile,
    germ.baseline, germ.lexicographicallySmaller_of_increment_neg shorter,
    fun outside => (equivalent outside).symm⟩

end BoundedGerm

/-- **A row of the same-interface cold table**, at a proper support of one
object.

A row is a cold bounded germ with two clauses added.  `equalLength` is
`def:cold-bounded-germ`'s `δ = 0`, which is what makes a germ a *row*:
`def:cold-same-interface-table`'s rows are the equal-length germs, and the
length-changing ones are `lem:cold-bounded-germ-trichotomy`'s business, not the
table's.

`admissible` is `def:admissible-rank-quotient`, spent exactly where
`lem:cold-same-interface-table` spends it: a row that is not handed off and
whose two representatives *are* target-completely identified is admissible only
when the identification has a strictly smaller proper representative in the
sense of `def:proper-quotient-representative`.  Without that clause the
equal-length switch has nothing to descend on, which is why the manuscript
cites the definition at exactly this point -- and why the length-changing germs,
which descend on their own increment, do not need it. -/
structure TableRow (S : DeclaredSignature)
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (Handoff : Finset object.Vertex → Prop)
    extends BoundedGerm S Baseline Target object where
  /-- `def:cold-bounded-germ`, the equal-length case `δ = 0`. -/
  equalLength :
    canonical.internalVertexCount =
      (rowAtom object support connected proper).piece.internalVertexCount
  /-- `def:admissible-rank-quotient` at a row that was not handed off. -/
  admissible : ¬ Handoff support →
    Response.ContextEquivalent Target
      (rowAtom object support connected proper).piece canonical →
    (glue canonical (rowAtom object support connected proper).outside).LexicographicallySmaller
      object

namespace TableRow

variable {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
variable {Handoff : Finset object.Vertex → Prop}
variable (row : TableRow S Baseline Target object Handoff)

/-- **Every row of the table is equal-length**, `δ = 0`. -/
theorem increment_eq_zero : row.increment = 0 :=
  row.toBoundedGerm.increment_eq_zero_iff.mpr row.equalLength

/-- A row that is neither handed off nor distinguishing is a target-complete
compression of its own proper support.  Every clause of
`CompressibleSupport` is a field of the row: the shared boundary-degree
profile, the baseline of the replacement, the strictly smaller representative
`def:admissible-rank-quotient` supplies, and the context-universality that
failure of `Distinguishing` is.

This is the equal-length descent.  The germ's own
`BoundedGerm.compressibleSupport_of_not_distinguishing` is the length-changing
one, and it descends on the increment instead. -/
theorem compressibleSupport_of_not_distinguishing
    (notHandoff : ¬ Handoff row.support)
    (notDistinguishing : ¬ row.Distinguishing) :
    Strategy.InterfaceReplacement.CompressibleSupport Baseline Target object
      row.support := by
  classical
  have equivalent :
      Response.ContextEquivalent Target
        (rowAtom object row.support row.connected row.proper).piece
        row.canonical := by
    intro outside
    by_contra distinguishes
    exact notDistinguishing ⟨outside, distinguishes⟩
  exact ⟨row.connected, row.proper, row.canonical, row.sameProfile, row.baseline,
    row.admissible notHandoff equivalent, fun outside => (equivalent outside).symm⟩

end TableRow

/-! ### The short self-return exceptions, as rows

`def:cold-same-interface-table`'s rows are "equal-length cold bounded germs
**and the short self-return exceptions** of
`lem:cold-short-self-return-filter`".  The germs are `TableRow` itself.  This
section supplies the second family and proves that it *is* a family of
exceptions: a cold-window outside self-return whose smear interval meets an
accepted length realizes it, so on a target-avoiding object only the surviving
lengths reach the table.

The datum is the smear itself.  "Smearing over the window offsets
`{0,…,order−1}` tests the whole interval `[ℓ, ℓ+order−1]`" is the statement
that each tested length is realized as a completion through the corresponding
offset; a `SelfReturn` carries exactly that family, and nothing else about the
corridor is needed to run the filter. -/

/-- **A cold-window outside self-return, with its smear.**

`outsideLength` is the manuscript's `ℓ`.  `smear` is the offset family: every
length the interval `[ℓ, ℓ+order−1]` tests is realized by the completion
through the corresponding cold-window offset, so an *accepted* tested length is
a target of the ambient object.  `row` is the entry this self-return
contributes to the same-interface table. -/
structure SelfReturn (S : DeclaredSignature) (LengthOK : Nat → Prop)
    (Baseline Target : FiniteObject.{u} → Prop) (object : FiniteObject.{u})
    (Handoff : Finset object.Vertex → Prop) where
  /-- The exceptional row this self-return contributes to the table. -/
  row : TableRow S Baseline Target object Handoff
  /-- `ℓ`, the outside length of the self-return. -/
  outsideLength : Nat
  /-- Smearing over the window offsets tests the whole interval
  `[ℓ, ℓ+order−1]`: an accepted length in it is realized in the object. -/
  smear : ∀ tested, outsideLength ≤ tested →
    tested ≤ outsideLength + (S.windowOrder - 1) → LengthOK tested → Target object

namespace SelfReturn

variable {S : DeclaredSignature} {LengthOK : Nat → Prop}
variable {Baseline Target : FiniteObject.{u} → Prop}
variable {Handoff : Finset object.Vertex → Prop}
variable (self : SelfReturn S LengthOK Baseline Target object Handoff)

/-- **"All other short self-returns realize a dyadic cycle."**

On an object that avoids the target, a self-return's length must survive the
smear: a tested length that is accepted would be realized through its offset,
and the object does not realize it.  So exactly the surviving lengths of
`lem:cold-short-self-return-filter` reach the table, and they reach it as rows
`lem:cold-same-interface-table` closes. -/
theorem surviving (avoids : ¬ Target object) :
    SurvivesSmear LengthOK (S.windowOrder - 1) self.outsideLength :=
  fun tested lower upper accepted =>
    avoids (self.smear tested lower upper accepted)

/-- A self-return whose length does *not* survive realizes the target, and is
therefore excluded before it can be a row.  This is the contrapositive of the
previous theorem and the manuscript's own routing of the non-exceptional
lengths. -/
theorem target_of_not_surviving
    (failed : ¬ SurvivesSmear LengthOK (S.windowOrder - 1) self.outsideLength) :
    Target object := by
  obtain ⟨tested, lower, upper, accepted⟩ :=
    exists_accepted_of_not_survivesSmear failed
  exact self.smear tested lower upper accepted

end SelfReturn

/-- **`lem:cold-same-interface-table`.**

*"Every row of the same-interface cold table is routed to one of the already
closed outcomes: a dyadic cycle, a target-defective quotient, an existing Type
B or route-8 handoff, or a target-complete proper-support compression.  In
particular, an equal-length cold bounded germ and a short exceptional
self-return cannot be a terminal cold residual."*

The two hypotheses are the two facts the selected minimal counterexample
already carries and nothing else: it avoids the target, and no proper support
of it admits a target-complete compression.  A realizing row would hand the
object the target it avoids; a row that is neither handed off nor
distinguishing is a compression of its own support.  What is left is exactly
the manuscript's routing, so no row is terminal. -/
theorem row_closed {S : DeclaredSignature} {Baseline Target : FiniteObject.{u} → Prop}
    {Handoff : Finset object.Vertex → Prop}
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (avoids : ¬ Target object)
    (uncompressible : ∀ support : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport Baseline Target object
        support)
    (row : TableRow S Baseline Target object Handoff) :
    ¬ row.Realizing ∧ (Handoff row.support ∨ row.Distinguishing) := by
  classical
  refine ⟨fun realizing => avoids (row.target_of_realizing targetInvariant realizing),
    ?_⟩
  by_contra unrouted
  push Not at unrouted
  exact uncompressible row.support
    (row.compressibleSupport_of_not_distinguishing unrouted.1 unrouted.2)

/-- **`lem:cold-same-interface-table`, at a short exceptional self-return.**

"In particular, an equal-length cold bounded germ **and a short exceptional
self-return** cannot be a terminal cold residual."

The self-return half is the second conjunct of `def:cold-same-interface-table`'s
row family, and it is closed the same way, with one extra step in front: on a
target-avoiding object the self-return's length *is* one of
`lem:cold-short-self-return-filter`'s surviving exceptions, because any accepted
length in its smear interval would be realized through the corresponding
cold-window offset.  Its row is then closed by `row_closed`. -/
theorem selfReturn_closed {S : DeclaredSignature} {LengthOK : Nat → Prop}
    {Baseline Target : FiniteObject.{u} → Prop}
    {Handoff : Finset object.Vertex → Prop}
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (avoids : ¬ Target object)
    (uncompressible : ∀ support : Finset object.Vertex,
      ¬ Strategy.InterfaceReplacement.CompressibleSupport Baseline Target object
        support)
    (self : SelfReturn S LengthOK Baseline Target object Handoff) :
    SurvivesSmear LengthOK (S.windowOrder - 1) self.outsideLength ∧
      ¬ self.row.Realizing ∧
        (Handoff self.row.support ∨ self.row.Distinguishing) :=
  ⟨self.surviving avoids,
    row_closed targetInvariant avoids uncompressible self.row⟩

end Hypostructure.Graph.ColdCorridor
