import Hypostructure.Graph.Statements.Spine

/-!
# Canonical objects of the selected counterexample: Type A

Every Type A fact is about the one selected counterexample `G` and about the
objects the ledger has already fixed on `G`: the canonical maximal packing
`P₀ = canonicalWindowPacking data G`, the negative support `X₀` of node `[61]`,
the saturated receiver of node `[89]`, the entry receiver and overloaded port
of nodes `[93]`/`[94]`, the witnessed exit-`(4)` peeling set of nodes
`[101]`/`[102]`, and the surviving first separator of exit `(7)` (node `[107]`).
Ledger values are data-free (`FactSystem.value_subsingleton`), so a witness
can never travel inside a fact.  This module therefore names each such object
as a *function of `G`*, exactly as `canonicalWindowPacking` already does.

## Design

* Each object `X` whose existence is asserted by an upstream key is the
  `Classical.choose` of **that key's existential body at `G`**, written here as
  a predicate `XSpec data G x`:

    `canonicalX data G := if h : ∃ x, XSpec data G x then some (choose h) else none`

  (`canonicalChoice` below).  The spec is the literal `∃`-body of the upstream
  statement, so a downstream fact about `canonicalX` is about exactly the object
  the upstream fact asserted, and never re-chooses it.
* Each object comes with `_spec` (existence ⇒ `∃ x, canonicalX = some x ∧
  XSpec x`), `_spec_of_eq_some`, and `_eq_none_iff`.
* **No statement becomes vacuous.**  Downstream keys pin an object with the
  positive form `∃ x, canonicalX data G = some x ∧ Q x`.  This is *false*, not
  vacuously true, when the object does not exist; and on the arm where the
  upstream key holds, the `_spec` lemma makes `x` the upstream witness.  The
  two arms of a decision about the object are then `∃ x, canonicalX = some x ∧
  Q x` and `∃ x, canonicalX = some x ∧ ¬ Q x`, exact complements under the
  upstream fact.  Objects whose existence is unconditional (the overloaded port
  order, the peeling sequence) are total definitions.
* Objects that depend on a support are stated at an arbitrary piece (`…At`) and
  instantiated at `X₀` by `Option.bind`, so every Type A object is a function
  of `G` and of the upstream canonical objects only.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-! ## The generic guarded choice -/

/-- The canonical guarded choice: the `Classical.choose` of `∃ x, spec x` when it
holds, and `none` otherwise. -/
noncomputable def canonicalChoice {α : Type*} (spec : α → Prop) : Option α := by
  classical
  exact if h : ∃ x, spec x then some (Classical.choose h) else none

theorem canonicalChoice_spec {α : Type*} {spec : α → Prop} (h : ∃ x, spec x) :
    ∃ x, canonicalChoice spec = some x ∧ spec x := by
  classical
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp [canonicalChoice, h]

theorem canonicalChoice_spec_of_eq_some {α : Type*} {spec : α → Prop} {x : α}
    (h : canonicalChoice spec = some x) : spec x := by
  classical
  by_cases exists_ : ∃ x, spec x
  · simp only [canonicalChoice, exists_, dite_true, Option.some.injEq] at h
    exact h ▸ Classical.choose_spec exists_
  · simp [canonicalChoice, exists_] at h

theorem canonicalChoice_eq_none_iff {α : Type*} {spec : α → Prop} :
    canonicalChoice spec = none ↔ ¬ ∃ x, spec x := by
  classical
  by_cases exists_ : ∃ x, spec x
  · simp [canonicalChoice, exists_]
  · simp [canonicalChoice, exists_]

/-! ## `X₀`: the negative support of node `[61]` -/

/-- The remainder `R(P₀)` of the canonical packing. -/
noncomputable abbrev canonicalRemainder (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Finset object.Vertex :=
  object.remainderSupport (canonicalWindowPacking data object)

/-- The `∃ component`-body of node `[61]` (`NegativeSupportStatement`,
`prop:negative-net-charge`, tex 10278): a canonical piece of `R(P₀)` with
negative net charge. -/
def NegativeComponentSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (component : Graph.SupportComponents.Connected.Component object
      (canonicalRemainder data object)) : Prop :=
  component ∈ object.canonicalPieces (canonicalRemainder data object) ∧
    object.NegativeNetCharge
      (object.pieceSupport (canonicalRemainder data object) component)
      data.threshold data.dischargeScale

/-- **`X₀`**, the negative canonical component fixed at node `[61]`
(`K .negativeSupport`); every Type A/B split of node `[62]` is at this
component (d2ded0e: `TypeSplitDichotomy` destructured `K .negativeSupport`). -/
noncomputable def canonicalNegativeComponent (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Option (Graph.SupportComponents.Connected.Component object
      (canonicalRemainder data object)) :=
  canonicalChoice (NegativeComponentSpec data object)

theorem canonicalNegativeComponent_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    (h : ∃ component, NegativeComponentSpec data object component) :
    ∃ component, canonicalNegativeComponent data object = some component ∧
      NegativeComponentSpec data object component :=
  canonicalChoice_spec h

theorem canonicalNegativeComponent_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {component}
    (h : canonicalNegativeComponent data object = some component) :
    NegativeComponentSpec data object component :=
  canonicalChoice_spec_of_eq_some h

theorem canonicalNegativeComponent_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} :
    canonicalNegativeComponent data object = none ↔
      ¬ ∃ component, NegativeComponentSpec data object component :=
  canonicalChoice_eq_none_iff

/-- The support `V(X₀)` of the selected negative component. -/
noncomputable def canonicalNegativePiece (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (Finset object.Vertex) :=
  (canonicalNegativeComponent data object).map
    (object.pieceSupport (canonicalRemainder data object))

theorem canonicalNegativePiece_eq_some_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex} :
    canonicalNegativePiece data object = some piece ↔
      ∃ component, canonicalNegativeComponent data object = some component ∧
        object.pieceSupport (canonicalRemainder data object) component = piece := by
  simp [canonicalNegativePiece]

/-- `NegativeSupportStatement`'s `∃ component` is exactly the existence
premise of `canonicalNegativeComponent`. -/
theorem negativeSupportStatement_iff (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    NegativeSupportStatement data object ↔
      (object.IsWindowPacking data.windowOrder (canonicalWindowPacking data object) ∧
        (∀ window : Finset object.Vertex,
          object.InducesWindow data.windowOrder window →
          ∃ member ∈ canonicalWindowPacking data object, ¬ Disjoint window member)) ∧
      ∃ component, NegativeComponentSpec data object component := by
  constructor
  · rintro ⟨packing, rfl, valid, maximal, component, member, negative⟩
    exact ⟨⟨valid, maximal⟩, component, member, negative⟩
  · rintro ⟨⟨valid, maximal⟩, component, member, negative⟩
    exact ⟨_, rfl, valid, maximal, component, member, negative⟩

/-! ## `w₀`: the saturated receiver of node `[89]` -/

/-- The `∃ receiver`-body of node `[89]` (`TypeASaturatedReceiverStatement`,
`lem:typeA-saturated-handoff`, tex 10402) at a piece. -/
def SaturatedReceiverSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex) : Prop :=
  object.IsReceiver piece data.threshold receiver ∧
    object.Saturated piece data.threshold data.dischargeScale receiver

/-- The saturated receiver chosen at a piece. -/
noncomputable def canonicalSaturatedReceiverAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    Option object.Vertex :=
  canonicalChoice (SaturatedReceiverSpec data object piece)

theorem canonicalSaturatedReceiverAt_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    (h : ∃ receiver, SaturatedReceiverSpec data object piece receiver) :
    ∃ receiver, canonicalSaturatedReceiverAt data object piece = some receiver ∧
      SaturatedReceiverSpec data object piece receiver :=
  canonicalChoice_spec h

theorem canonicalSaturatedReceiverAt_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex}
    (h : canonicalSaturatedReceiverAt data object piece = some receiver) :
    SaturatedReceiverSpec data object piece receiver :=
  canonicalChoice_spec_of_eq_some h

theorem canonicalSaturatedReceiverAt_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex} :
    canonicalSaturatedReceiverAt data object piece = none ↔
      ¬ ∃ receiver, SaturatedReceiverSpec data object piece receiver :=
  canonicalChoice_eq_none_iff

/-- **`w₀`**: the saturated receiver of `X₀` fixed at node `[89]`
(`K .typeASaturatedReceiver`; d2ded0e `TypeASaturationDichotomy` split on
`∃ receiver, IsReceiver ∧ Saturated` at the `K .typeALowSurplus` piece). -/
noncomputable def canonicalSaturatedReceiver (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option object.Vertex :=
  (canonicalNegativePiece data object).bind
    (canonicalSaturatedReceiverAt data object)

/-! ## The exit-chain receiver and overloaded port of nodes `[93]`/`[94]` -/

/-- The `∃ receiver`-body of node `[93]`, yes arm (`TypeAVisibleEntryStatement`,
`lem:typeA-visible-entry`, tex 11208): a saturated receiver some completion
port of which carries the registered number of visible receiver-entry
returns. -/
def VisibleReceiverSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex) : Prop :=
  object.IsReceiver piece data.threshold receiver ∧
    object.Saturated piece data.threshold data.dischargeScale receiver ∧
    Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver ∅)

/-- The visible entry receiver at a piece (node `[93]` yes). -/
noncomputable def canonicalVisibleReceiverAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    Option object.Vertex :=
  canonicalChoice (VisibleReceiverSpec data object piece)

theorem canonicalVisibleReceiverAt_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    (h : ∃ receiver, VisibleReceiverSpec data object piece receiver) :
    ∃ receiver, canonicalVisibleReceiverAt data object piece = some receiver ∧
      VisibleReceiverSpec data object piece receiver :=
  canonicalChoice_spec h

theorem canonicalVisibleReceiverAt_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex}
    (h : canonicalVisibleReceiverAt data object piece = some receiver) :
    VisibleReceiverSpec data object piece receiver :=
  canonicalChoice_spec_of_eq_some h

theorem canonicalVisibleReceiverAt_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex} :
    canonicalVisibleReceiverAt data object piece = none ↔
      ¬ ∃ receiver, VisibleReceiverSpec data object piece receiver :=
  canonicalChoice_eq_none_iff

/-- **The exit-chain receiver** at a piece: the node-`[93]` visible receiver on
the visible arm, and otherwise the node-`[89]` saturated receiver.  This is
the receiver the shared exit entry `K .typeASaturatedExitEntry` carries: at
d2ded0e the visible entry read the receiver of `K .typeAVisibleEntry`, and the
silent lane (`TypeASilentExitEntry`, node `[94]`) continued at the saturated
receiver of `K .typeASaturatedReceiver`.  On the `[93]`-no arm the visible
choice is `none` by `_eq_none_iff`, so the `[89]` receiver is taken. -/
noncomputable def canonicalExitReceiverAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    Option object.Vertex :=
  (canonicalVisibleReceiverAt data object piece).orElse
    fun _ => canonicalSaturatedReceiverAt data object piece

/-- The exit-chain receiver is a saturated receiver of the piece. -/
theorem canonicalExitReceiverAt_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex}
    (h : canonicalExitReceiverAt data object piece = some receiver) :
    object.IsReceiver piece data.threshold receiver ∧
      object.Saturated piece data.threshold data.dischargeScale receiver := by
  unfold canonicalExitReceiverAt at h
  cases visible : canonicalVisibleReceiverAt data object piece with
  | some chosen =>
      rw [visible] at h
      cases h
      have spec := canonicalVisibleReceiverAt_spec_of_eq_some visible
      exact ⟨spec.1, spec.2.1⟩
  | none =>
      rw [visible] at h
      exact canonicalSaturatedReceiverAt_spec_of_eq_some h

/-- The exit-chain receiver of `X₀`. -/
noncomputable def canonicalExitReceiver (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option object.Vertex :=
  (canonicalNegativePiece data object).bind (canonicalExitReceiverAt data object)

/-- **The overloaded port** of a receiver at a peeling set: the head of the
canonical overloaded-port order (`def:typeA-visible-load`).  Every
`VisibleFourUnpeeledPackage` selects exactly this port
(`VisibleFourUnpeeledPackage.selectedPort`), so no choice is made here. -/
noncomputable def canonicalOverloadedPortAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Option object.Vertex :=
  (Graph.ExitFour.overloadedPortOrder piece data.threshold data.dischargeScale
    receiver peeled).head?

theorem VisibleFourUnpeeledPackage.outside_eq_canonicalOverloadedPortAt
    {data : Parameters} {object : Graph.FiniteObject.{u}}
    {piece : Finset object.Vertex} {receiver : object.Vertex}
    {peeled : Finset object.Vertex}
    (package : Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled) :
    canonicalOverloadedPortAt data object piece receiver peeled =
      some package.outside := by
  simp [canonicalOverloadedPortAt, package.selectedPort]

/-- **The canonical visible-four package** at a state: the four selected visible
unpeeled loads at the overloaded port and their first scheduled returns
(node `[93]`, `lem:typeA-visible-entry`; d2ded0e `TypeAVisibleEntryDichotomy`
published `visibleFourUnpeeledPackage … overloaded` at the entry receiver). -/
noncomputable def canonicalVisiblePackageAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Option (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled) := by
  classical
  exact if h : Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece
      data.threshold data.dischargeScale receiver peeled) then
    some (Classical.choice h) else none

theorem canonicalVisiblePackageAt_isSome_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex} {peeled : Finset object.Vertex} :
    (canonicalVisiblePackageAt data object piece receiver peeled).isSome ↔
      Nonempty (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
        data.dischargeScale receiver peeled) := by
  classical
  unfold canonicalVisiblePackageAt
  split
  · next h => simp [h]
  · next h => simp [h]

/-! ## The witnessed exit-`(4)` peeling sequence of nodes `[101]`/`[102]` -/

/-- The `∃ witness`-body of exit `(4)` (`ExitFourAt`,
`lem:typeA-exit4-residual-routing`, tex 11606) at one state: a canonical
target-defective quotient whose load is a selected visible unpeeled load of the
overloaded port, or a load of the silent residual excess. -/
def ExitFourWitnessSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver : object.Vertex)
    (peeled : Finset object.Vertex)
    (witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver peeled) : Prop :=
  (∃ package : Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
      data.dischargeScale receiver peeled,
    ∃ load ∈ Graph.ExitFour.selectedVisibleUnpeeledLoads piece
        data.threshold data.dischargeScale receiver package.outside peeled,
      witness.load = load) ∨
  (Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
      data.dischargeScale receiver peeled ∧
    witness.load ∈ Graph.ExitFour.unpeeledExcess piece data.threshold
      data.dischargeScale receiver peeled)

/-- **The exit-`(4)` witness** at a state: the witness the node-`[101]` yes arm
asserts (`K .typeASaturatedHandoffExitFour`), which node `[102]` peels
(d2ded0e `TypeAExitFourPeelingStep` peeled exactly this `∃ witness`). -/
noncomputable def canonicalExitFourWitnessAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Option (Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver peeled) :=
  canonicalChoice (ExitFourWitnessSpec data object piece receiver peeled)

theorem canonicalExitFourWitnessAt_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex} {peeled : Finset object.Vertex}
    (h : ∃ witness, ExitFourWitnessSpec data object piece receiver peeled witness) :
    ∃ witness, canonicalExitFourWitnessAt data object piece receiver peeled =
        some witness ∧ ExitFourWitnessSpec data object piece receiver peeled witness :=
  canonicalChoice_spec h

theorem canonicalExitFourWitnessAt_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex} {peeled : Finset object.Vertex} {witness}
    (h : canonicalExitFourWitnessAt data object piece receiver peeled = some witness) :
    ExitFourWitnessSpec data object piece receiver peeled witness :=
  canonicalChoice_spec_of_eq_some h

theorem canonicalExitFourWitnessAt_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver : object.Vertex} {peeled : Finset object.Vertex} :
    canonicalExitFourWitnessAt data object piece receiver peeled = none ↔
      ¬ ∃ witness, ExitFourWitnessSpec data object piece receiver peeled witness :=
  canonicalChoice_eq_none_iff

/-- One step of the `[101]`/`[102]` loop (`def:typeA-exit4-peeling`,
`lem:typeA-exit4-finite-descent`): while the receiver is still saturated at the
current peeling set and exit `(4)` has a witness there, adjoin that witness's
load (`Witness.nextPeeled`); otherwise stay. -/
noncomputable def canonicalPeelStep (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    Finset object.Vertex := by
  classical
  exact if Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
      receiver peeled then
    match canonicalExitFourWitnessAt data object piece receiver peeled with
    | some witness => witness.nextPeeled
    | none => peeled
  else peeled

/-- **The canonical witnessed peeling sequence** `P₄⁽ᵏ⁾(w)`, from the entry
peeling set `∅` of `K .typeASaturatedExitEntry`. -/
noncomputable def canonicalPeel (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (step : Nat) : Finset object.Vertex :=
  (canonicalPeelStep data object piece receiver)^[step] ∅

/-- **The terminal peeled set `P₄(w)`**: the sequence after `|ℒ(w)|` steps,
which is a fixed point of the step (`canonicalTerminalPeeled_step`). -/
noncomputable def canonicalTerminalPeeled (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) : Finset object.Vertex :=
  canonicalPeel data object piece receiver
    (object.routedLoads piece data.threshold receiver).card

theorem canonicalPeelStep_cases (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (peeled : Finset object.Vertex) :
    canonicalPeelStep data object piece receiver peeled = peeled ∨
      ∃ witness : Graph.ExitFour.Witness (Graph.HasCycleWithLength data.LengthOK)
          piece data.threshold data.dischargeScale receiver peeled,
        canonicalExitFourWitnessAt data object piece receiver peeled = some witness ∧
          canonicalPeelStep data object piece receiver peeled =
            witness.nextPeeled := by
  classical
  unfold canonicalPeelStep
  split
  · cases h : canonicalExitFourWitnessAt data object piece receiver peeled with
    | none => exact Or.inl rfl
    | some witness => exact Or.inr ⟨witness, rfl, rfl⟩
  · exact Or.inl rfl

theorem canonicalPeel_zero (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) :
    canonicalPeel data object piece receiver 0 = ∅ := rfl

theorem canonicalPeel_succ (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (step : Nat) :
    canonicalPeel data object piece receiver (step + 1) =
      canonicalPeelStep data object piece receiver
        (canonicalPeel data object piece receiver step) :=
  Function.iterate_succ_apply' _ _ _

/-- Every canonical peeling set consists of routed loads. -/
theorem canonicalPeel_subset_routedLoads (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (step : Nat) :
    canonicalPeel data object piece receiver step ⊆
      object.routedLoads piece data.threshold receiver := by
  induction step with
  | zero => simp [canonicalPeel_zero]
  | succ step ih =>
      rw [canonicalPeel_succ]
      rcases canonicalPeelStep_cases data object piece receiver
          (canonicalPeel data object piece receiver step) with same | ⟨witness, _, next⟩
      · rw [same]
        exact ih
      · rw [next]
        exact witness.nextPeeled_subset_routedLoads ih

/-- **Witnessed by construction**: every canonical peeling set is a union of
exit-`(4)` witness loads (`def:typeA-exit4-peeling`, tex 11435). -/
theorem canonicalPeel_peeledByWitnesses (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (step : Nat) :
    Graph.ExitFour.PeeledByWitnesses (Graph.HasCycleWithLength data.LengthOK)
      piece data.threshold data.dischargeScale receiver
      (canonicalPeel data object piece receiver step) := by
  induction step with
  | zero =>
      rw [canonicalPeel_zero]
      exact Graph.ExitFour.peeledByWitnesses_empty
        (Graph.HasCycleWithLength data.LengthOK) piece data.threshold
        data.dischargeScale receiver
  | succ step ih =>
      rw [canonicalPeel_succ]
      rcases canonicalPeelStep_cases data object piece receiver
          (canonicalPeel data object piece receiver step) with same | ⟨witness, _, next⟩
      · rw [same]
        exact ih
      · rw [next]
        exact Graph.ExitFour.peeledByWitnesses_nextPeeled ih witness

/-- Until it stops, the sequence gains one load per step. -/
theorem canonicalPeel_fixed_or_card (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) (step : Nat) :
    (∃ earlier ≤ step,
      canonicalPeelStep data object piece receiver
          (canonicalPeel data object piece receiver earlier) =
        canonicalPeel data object piece receiver earlier) ∨
      step ≤ (canonicalPeel data object piece receiver step).card := by
  induction step with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ step ih =>
      rcases ih with ⟨earlier, le, fixed⟩ | large
      · exact Or.inl ⟨earlier, Nat.le_succ_of_le le, fixed⟩
      · rcases canonicalPeelStep_cases data object piece receiver
            (canonicalPeel data object piece receiver step) with same | ⟨witness, _, next⟩
        · exact Or.inl ⟨step, Nat.le_succ step, same⟩
        · refine Or.inr ?_
          rw [canonicalPeel_succ, next]
          simp only [Graph.ExitFour.Witness.nextPeeled, Finset.card_cons]
          omega

/-- Once the step fixes a set, the sequence stays there. -/
theorem canonicalPeel_stable (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) {earlier : Nat}
    (fixed : canonicalPeelStep data object piece receiver
        (canonicalPeel data object piece receiver earlier) =
      canonicalPeel data object piece receiver earlier) :
    ∀ later, earlier ≤ later →
      canonicalPeel data object piece receiver later =
        canonicalPeel data object piece receiver earlier := by
  intro later le
  induction later with
  | zero =>
      have : earlier = 0 := Nat.le_zero.mp le
      subst this; rfl
  | succ later ih =>
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · have prior := ih (Nat.le_of_lt_succ lt)
        rw [canonicalPeel_succ, prior, fixed]
      · rw [eq]

/-- **The terminal peeled set is a fixed point of the loop**: either the
receiver is unsaturated there, or exit `(4)` has no witness there. -/
theorem canonicalTerminalPeeled_step (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver : object.Vertex) :
    canonicalPeelStep data object piece receiver
        (canonicalTerminalPeeled data object piece receiver) =
      canonicalTerminalPeeled data object piece receiver := by
  classical
  set bound := (object.routedLoads piece data.threshold receiver).card
  rcases canonicalPeel_fixed_or_card data object piece receiver bound with
    ⟨earlier, le, fixed⟩ | large
  · have stable := canonicalPeel_stable data object piece receiver fixed bound le
    unfold canonicalTerminalPeeled
    rw [stable, fixed]
  · -- All routed loads are peeled, so no witness load is unpeeled.
    have subset := canonicalPeel_subset_routedLoads data object piece receiver bound
    have equal : canonicalPeel data object piece receiver bound =
        object.routedLoads piece data.threshold receiver :=
      Finset.eq_of_subset_of_card_le subset large
    unfold canonicalTerminalPeeled
    rcases canonicalPeelStep_cases data object piece receiver
        (canonicalPeel data object piece receiver bound) with same | ⟨witness, _, _⟩
    · exact same
    · exfalso
      have unpeeled := (Graph.ExitFour.mem_unpeeledLoads (object := object) piece
        data.threshold receiver).mp witness.unpeeled
      rw [← equal] at unpeeled
      exact unpeeled.2 unpeeled.1

/-- The terminal peeled set of `X₀` at its exit-chain receiver. -/
noncomputable def canonicalTypeATerminalPeeled (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option (Finset object.Vertex) :=
  (canonicalNegativePiece data object).bind fun piece =>
    (canonicalExitReceiverAt data object piece).map
      (canonicalTerminalPeeled data object piece)

/-! ## Exit `(7)`: the canonical surviving first separator -/

/-- The data of `Route8.TraceBasin.TraceSurvivingSeparator` at one saturated
receiver and load, as one structure: a continuation family through one
completion port, two distinct routed loads of it, their first separation, and
its surviving switch reading (`def:typeA-continuation-classes`, tex 10611;
`lem:typeA-high-degree-handoff`, tex 11110). -/
structure ExitSevenSeparation (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (receiver load : object.Vertex) where
  family : Graph.ExitFour.ContinuationFamily object piece data.threshold receiver
  loadMem : load ∈ family.loads
  leftLoad : object.Vertex
  rightLoad : object.Vertex
  leftMem : leftLoad ∈ family.loads
  rightMem : rightLoad ∈ family.loads
  distinct : leftLoad ≠ rightLoad
  separation : Graph.DecoratedHandoff.Separation object piece receiver family.outside
  leftPath : separation.left.path = (family.germ leftLoad leftMem).path
  rightPath : separation.right.path = (family.germ rightLoad rightMem).path
  reading : Graph.DecoratedHandoff.SwitchReading separation
  surviving : Graph.DecoratedHandoff.Surviving
    (Graph.HasCycleWithLength data.LengthOK) reading
    (∃ representative : Graph.FiniteObject.{u},
      representative.LexicographicallySmaller object ∧
        Graph.MinimumDegreeAtLeast data.threshold representative ∧
        (Graph.HasCycleWithLength data.LengthOK representative →
          Graph.HasCycleWithLength data.LengthOK object))

theorem traceSurvivingSeparator_iff_nonempty (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (receiver load : object.Vertex) :
    Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece data.threshold
        data.LengthOK receiver load piece ↔
      Nonempty (ExitSevenSeparation data object piece receiver load) := by
  constructor
  · rintro ⟨family, loadMem, leftLoad, rightLoad, leftMem, rightMem, distinct,
      separation, leftPath, rightPath, reading, surviving⟩
    exact ⟨⟨family, loadMem, leftLoad, rightLoad, leftMem, rightMem, distinct,
      separation, leftPath, rightPath, reading, surviving⟩⟩
  · rintro ⟨s⟩
    exact ⟨s.family, s.loadMem, s.leftLoad, s.rightLoad, s.leftMem, s.rightMem,
      s.distinct, s.separation, s.leftPath, s.rightPath, s.reading, s.surviving⟩

/-- The `∃`-body of `SeparatorHandoffAt data G X` (Statements/Spine.lean; exit `(7)` of `def:typeA-saturated-exits`, tex 10811,
`lem:typeA-visible-entry` tex 11240-11250, `def:typeA-unified-negative`
tex 15236): a receiver of `X` and a routed load whose continuation
family has a surviving first separator
(`separatorHandoffAt_iff_exists_spec`). -/
def SeparatorHandoffSpec (data : Parameters) (object : Graph.FiniteObject.{u})
    (piece : Finset object.Vertex) (pair : object.Vertex × object.Vertex) : Prop :=
  pair.1 ∈ object.receivers piece data.threshold ∧
    Graph.Route8.TraceBasin.TraceSurvivingSeparator object piece data.threshold
      data.LengthOK pair.1 pair.2 piece

theorem separatorHandoffAt_iff_exists_spec (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    SeparatorHandoffAt data object piece ↔
      ∃ pair, SeparatorHandoffSpec data object piece pair := by
  constructor
  · rintro ⟨receiver, member, load, separated⟩
    exact ⟨(receiver, load), member, separated⟩
  · rintro ⟨⟨receiver, load⟩, member, separated⟩
    exact ⟨receiver, member, load, separated⟩

/-- **The canonical exit-`(7)` separation of a piece**: the `Classical.choose` of
the `SeparatorHandoffAt` existential (its receiver and load) together with the
chosen surviving separation data at them.  Node `[107]` yes / `[108]`
(`K .typeAExitSevenHandoff`) asserts exactly this existential; d2ded0e
`TypeAExitSevenDichotomy` split on exit (7) at the `K .typeAExitSixFree`
piece. -/
noncomputable def canonicalHandoffSeparationAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    Option (Σ pair : object.Vertex × object.Vertex,
      ExitSevenSeparation data object piece pair.1 pair.2) := by
  classical
  exact if h : ∃ pair, SeparatorHandoffSpec data object piece pair then
    some ⟨Classical.choose h, Classical.choice
      ((traceSurvivingSeparator_iff_nonempty data object piece _ _).mp
        (Classical.choose_spec h).2)⟩
  else none

theorem canonicalHandoffSeparationAt_spec {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    (h : ∃ pair, SeparatorHandoffSpec data object piece pair) :
    ∃ separated, canonicalHandoffSeparationAt data object piece = some separated ∧
      SeparatorHandoffSpec data object piece separated.1 := by
  classical
  refine ⟨⟨Classical.choose h, Classical.choice
      ((traceSurvivingSeparator_iff_nonempty data object piece _ _).mp
        (Classical.choose_spec h).2)⟩, ?_, Classical.choose_spec h⟩
  simp [canonicalHandoffSeparationAt, h]

theorem canonicalHandoffSeparationAt_spec_of_eq_some {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex} {separated}
    (h : canonicalHandoffSeparationAt data object piece = some separated) :
    SeparatorHandoffSpec data object piece separated.1 := by
  classical
  unfold canonicalHandoffSeparationAt at h
  split at h
  · next exists_ =>
      cases h
      exact Classical.choose_spec exists_
  · cases h

theorem canonicalHandoffSeparationAt_eq_none_iff {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex} :
    canonicalHandoffSeparationAt data object piece = none ↔
      ¬ ∃ pair, SeparatorHandoffSpec data object piece pair := by
  classical
  unfold canonicalHandoffSeparationAt
  split
  · next h => simp [h]
  · next h => simp [h]

/-- The surviving first separator `z` of the canonical exit-`(7)` separation. -/
noncomputable def canonicalHandoffSeparatorAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex) :
    Option object.Vertex :=
  (canonicalHandoffSeparationAt data object piece).map
    fun separated => separated.2.separation.separator

/-- `lem:typeA-high-degree-handoff` (tex 11110) at one surviving separation:
the separator with its two separated connector tails, as the decorated handoff
fan envelope `envelopeOfSeparation` with core the support.  The construction is
the one of `Route8.TraceBasin.exists_envelope_of_traceSurvivingSeparator`, kept
as a term so the envelope can be named. -/
noncomputable def ExitSevenSeparation.envelope {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver load : object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (separated : ExitSevenSeparation data object piece receiver load)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex, ¬ Absorbing centre first second) :
    Graph.DecoratedHandoff.Envelope object data.LengthOK HighDegree Absorbing :=
  let separation := separated.separation
  have leftChain :
      (separation.nextLeft :: separation.tailLeft).IsChain object.graph.Adj := by
    have chain := separation.left.chain
    rw [separation.leftEq] at chain
    exact (List.isChain_cons.mp (List.isChain_append.mp chain).2.1).2
  have rightChain :
      (separation.nextRight :: separation.tailRight).IsChain object.graph.Adj := by
    have chain := separation.right.chain
    rw [separation.rightEq] at chain
    exact (List.isChain_cons.mp (List.isChain_append.mp chain).2.1).2
  have leftNodup : (separation.nextLeft :: separation.tailLeft).Nodup := by
    have nodup := separation.left.nodup
    rw [separation.leftEq] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).2
  have rightNodup : (separation.nextRight :: separation.tailRight).Nodup := by
    have nodup := separation.right.nodup
    rw [separation.rightEq] at nodup
    exact (List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).2
  have leftLast :
      (separation.nextLeft :: separation.tailLeft).getLast? =
        some separation.left.terminal := by
    have last := separation.left.terminal_last
    rw [separation.leftEq] at last
    simpa using last
  have rightLast :
      (separation.nextRight :: separation.tailRight).getLast? =
        some separation.right.terminal := by
    have last := separation.right.terminal_last
    rw [separation.rightEq] at last
    simpa using last
  have leftInterior : ∀ vertex ∈ separation.nextLeft :: separation.tailLeft,
      vertex ∈ piece ∨ vertex = separation.separator →
        (separation.nextLeft :: separation.tailLeft).getLast? = some vertex := by
    intro vertex member alternatives
    rcases alternatives with inside | rfl
    · have memberTail : vertex ∈ separation.left.path.tail := by
        rw [separation.leftEq]
        simp only [List.tail_append_of_ne_nil separation.common_ne_nil]
        exact List.mem_append_right _ (by simp [member])
      exact leftLast.trans (congrArg some
        (separation.left.interior vertex memberTail inside).symm)
    · have nodup := separation.left.nodup
      rw [separation.leftEq] at nodup
      exact False.elim
        ((List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 member)
  have rightInterior : ∀ vertex ∈ separation.nextRight :: separation.tailRight,
      vertex ∈ piece ∨ vertex = separation.separator →
        (separation.nextRight :: separation.tailRight).getLast? = some vertex := by
    intro vertex member alternatives
    rcases alternatives with inside | rfl
    · have memberTail : vertex ∈ separation.right.path.tail := by
        rw [separation.rightEq]
        simp only [List.tail_append_of_ne_nil separation.common_ne_nil]
        exact List.mem_append_right _ (by simp [member])
      exact rightLast.trans (congrArg some
        (separation.right.interior vertex memberTail inside).symm)
    · have nodup := separation.right.nodup
      rw [separation.rightEq] at nodup
      exact False.elim
        ((List.nodup_cons.mp (List.nodup_append.mp nodup).2.1).1 member)
  Graph.DecoratedHandoff.envelopeOfSeparation separation
    (separation.nextLeft :: separation.tailLeft)
    (separation.nextRight :: separation.tailRight) (by simp) (by simp)
    leftChain rightChain leftNodup rightNodup
    ⟨separation.left.terminal, leftLast, separation.left.terminal_inside⟩
    ⟨separation.right.terminal, rightLast, separation.right.terminal_inside⟩
    leftInterior rightInterior
    (high separation.separator
      (Graph.DecoratedHandoff.four_le_degree_of_surviving separated.surviving))
    avoids (denied _ _ _) (denied _ _ _)

theorem ExitSevenSeparation.envelope_core {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver load : object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (separated : ExitSevenSeparation data object piece receiver load)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex, ¬ Absorbing centre first second) :
    (separated.envelope (HighDegree := HighDegree) avoids high denied).core = piece :=
  rfl

theorem ExitSevenSeparation.envelope_decorations {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {receiver load : object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (separated : ExitSevenSeparation data object piece receiver load)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex, ¬ Absorbing centre first second) :
    (separated.envelope (HighDegree := HighDegree) avoids high denied).decorations =
      {separated.separation.separator} := by
  simp [ExitSevenSeparation.envelope, Graph.DecoratedHandoff.envelopeOfSeparation]

/-- **The canonical exit-`(7)` envelope of a piece** (node `[108]`,
`def:decorated-fan-envelope`): the envelope of the canonical surviving
separation.  It exists exactly when the separation exists and the envelope's
three standing hypotheses hold on `G` (target avoidance from `K .selection`,
the high-degree registration, the denied absorbing clause of exit `(3)`). -/
noncomputable def canonicalHandoffEnvelopeAt (data : Parameters)
    (object : Graph.FiniteObject.{u}) (piece : Finset object.Vertex)
    (HighDegree : object.Vertex → Prop)
    (Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop) :
    Option (Graph.DecoratedHandoff.Envelope object data.LengthOK HighDegree Absorbing) := by
  classical
  exact if standing : ¬ Graph.HasCycleWithLength data.LengthOK object ∧
      (∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex) ∧
      (∀ centre first second : object.Vertex, ¬ Absorbing centre first second) then
    (canonicalHandoffSeparationAt data object piece).map fun separated =>
      separated.2.envelope standing.1 standing.2.1 standing.2.2
  else none

theorem canonicalHandoffEnvelopeAt_core {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    {envelope : Graph.DecoratedHandoff.Envelope object data.LengthOK HighDegree Absorbing}
    (h : canonicalHandoffEnvelopeAt data object piece HighDegree Absorbing = some envelope) :
    envelope.core = piece := by
  classical
  unfold canonicalHandoffEnvelopeAt at h
  split at h
  · obtain ⟨separated, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  · cases h

theorem canonicalHandoffEnvelopeAt_isSome {data : Parameters}
    {object : Graph.FiniteObject.{u}} {piece : Finset object.Vertex}
    {HighDegree : object.Vertex → Prop}
    {Absorbing : object.Vertex → object.Vertex → object.Vertex → Prop}
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (high : ∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex)
    (denied : ∀ centre first second : object.Vertex, ¬ Absorbing centre first second)
    (handoff : ∃ pair, SeparatorHandoffSpec data object piece pair) :
    (canonicalHandoffEnvelopeAt data object piece HighDegree Absorbing).isSome := by
  classical
  obtain ⟨separated, eq, _⟩ := canonicalHandoffSeparationAt_spec handoff
  have standing : ¬ Graph.HasCycleWithLength data.LengthOK object ∧
      (∀ vertex : object.Vertex, 3 < object.degree vertex → HighDegree vertex) ∧
      (∀ centre first second : object.Vertex, ¬ Absorbing centre first second) :=
    ⟨avoids, high, denied⟩
  unfold canonicalHandoffEnvelopeAt
  rw [dif_pos standing, eq]
  rfl

/-- The canonical exit-`(7)` separation of `X₀`. -/
noncomputable def canonicalTypeAHandoffSeparator (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Option object.Vertex :=
  (canonicalNegativePiece data object).bind (canonicalHandoffSeparatorAt data object)

end Hypostructure.Graph.Strategy.Spine
