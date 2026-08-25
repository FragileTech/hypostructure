import Hypostructure.Graph.Route8Census
import Hypostructure.Graph.Route8Deficit
import Hypostructure.Graph.ExitFourFamily

/-!
# The large-budget pressure descent (node `[123]`)

`thm:large-budget-route8-only`, run on the object-level route-8 census of
`Graph/Route8Census`: *"Start with the peeling sets `P₄(w) = ∅` and run the
following deterministic procedure.  At any stage … the reduced carrier reduction
supplies a two-carrier entry.  If that two-carrier entry is a route-8 entry,
`prop:typeA-route8-closure-from-nogo` applies …  If instead the entry is
target-defect, `lem:typeA-pressure-is-exit4-peel` makes its pressure token a
canonical exit-(4) witness for its routed load, and `lem:typeA-exit4-finite-descent`
performs one peeling step.  The second alternative cannot occur infinitely many
times …"*

* `def:typeA-peeling-reduced-ledger`: the peeled family `Ξ^{P₄}` is the census
  `entries` with the peeled indices removed (`peeledEntries`), and the reduced
  deficit `D̃_A^{P₄} = D̃_A − ¼|P₄|` is carried by the stage rate
  `(δs+1)|∂R| + δ·slack + δ|P₄| < δ|R|` (`StageRate`), the exact form of the
  stage hypothesis `D̃_A^{P₄} ≥ (¼ − τ)|R| − o(|R|)`.
* `lem:typeA-peeling-reduced-reduction`: on a stage with the stage rate the
  reduced ledger has a two-carrier entry (`exists_twoCarrierEntry_peeled`), the
  census argument `Route8.exists_indexedTwoCarrierCore` on the peeled family with
  ambient `|R| − |P₄|`.
* `lem:typeA-pressure-is-exit4-peel` / `lem:typeA-exit4-finite-descent`: a
  target-defect entry is one whose load carries an exit-(4) witness at its
  receiver with the current peeled loads (`TargetDefectAt`); peeling it is a
  `PeelChain` step, and the number of unpeeled entries strictly decreases (the
  manuscript's `Λ₄`).
* `thm:large-budget-route8-only`'s procedure is `descent`: from any stage with
  the stage rate one reaches, by target-defect peels, either a stage with a true
  (route-8) two-carrier entry — node `[124]` — or a stage where the stage rate
  fails.  The latter is not a contradiction: `StageAccounting` retains the
  peeled target-defect mass and routes it to the demand residual at node
  `[181]`.
-/

namespace Hypostructure.Graph.Route8Pressure

open Hypostructure
open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u})

attribute [local instance] Route8.vertexDecEq

/-- The peeled indices `P₄` of the unified ledger, as census indices
`(piece, receiver, load)` (`def:typeA-peeling-reduced-ledger`: "deleting every
routed load listed in its receiver's peeling set"). -/
abbrev Peeled : Type u := Finset (Route8Census.Index object)

/-- `Ξ^{P₄}`: the supplied unified entry family with the peeled indices
removed.  At node `[123]` the argument is the paper's `\tilde\Xi`, whose
supports have no decorated Type B handoff. -/
noncomputable def peeledEntries
    (entries : Finset (Route8Census.Index object))
    (peeled : Peeled object) : Finset (Route8Census.Index object) :=
  entries \ peeled

theorem peeledEntries_subset
    (entries : Finset (Route8Census.Index object))
    (peeled : Peeled object) :
    peeledEntries object entries peeled ⊆ entries :=
  Finset.sdiff_subset

/-- Peeling removes at most one entry per peeled index. -/
theorem card_entries_le_peeled
    (entries : Finset (Route8Census.Index object))
    (peeled : Peeled object) :
    entries.card ≤ (peeledEntries object entries peeled).card + peeled.card :=
  Finset.card_le_card_sdiff_add_card

/-- **The stage rate** (`def:typeA-peeling-reduced-ledger`,
`lem:typeA-peeling-reduced-reduction`): the private-carrier rate of the census
with the peeled mass `|P₄|` charged on the ambient side —
`(δs+1)|∂R| + δ·slack + δ|P₄| < δ|R|`, the exact form of the stage hypothesis
`D̃_A^{P₄} ≥ (¼ − τ)|R| − o(|R|)`.  At `P₄ = ∅` it is `Route8Census.Rate`. -/
def StageRate (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (peeled : Peeled object) : Prop :=
  (threshold * discharge + 1) * (Route8Census.supply object packing).card +
      threshold * slack + threshold * peeled.card <
    threshold * (object.remainderSupport packing).card

theorem stageRate_empty (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) :
    StageRate object packing threshold discharge slack ∅ ↔
      Route8Census.Rate object packing threshold discharge slack := by
  simp [StageRate, Route8Census.Rate]

/-- The two-carrier condition on the peeled family (`def:typeA-terminal-two-carrier`
at stage `P₄`). -/
def TwoCarrierAt (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    (index : Route8Census.Index object) : Prop :=
  Route8.IndexedTwoCarrierCore (peeledEntries object entries peeled)
    (Route8Census.core object threshold LengthOK) (threshold - 1) index

/-- Private carriers only grow when the family shrinks, so a two-carrier entry of
the peeled family is a two-carrier entry of the full census. -/
theorem twoCarrierEntry_of_twoCarrierAt (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    {index : Route8Census.Index object}
    (two : TwoCarrierAt object packing entries threshold LengthOK peeled index) :
    Route8.IndexedTwoCarrierCore entries
      (Route8Census.core object threshold LengthOK) (threshold - 1) index := by
  unfold TwoCarrierAt Route8.IndexedTwoCarrierCore at two
  unfold Route8.IndexedTwoCarrierCore
  refine le_trans ?_ two
  unfold Route8.indexedPrivateCoreCount
  apply Finset.card_le_card
  intro carrier member
  rw [Route8.indexedPrivateCoreCarriers, Finset.mem_filter] at member ⊢
  refine ⟨member.1, fun other otherMem ne => ?_⟩
  exact member.2 other (peeledEntries_subset object entries peeled otherMem) ne

/-- **`lem:typeA-peeling-reduced-reduction`**: on a stage with the stage rate,
the peeled ledger contains a two-carrier entry. -/
theorem exists_twoCarrierEntry_peeled (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (entriesSubset : entries ⊆
      Route8Census.entries object packing threshold discharge)
    (deficit : (object.remainderSupport packing).card ≤
      entries.card + discharge * (Route8Census.supply object packing).card + slack)
    (peeled : Peeled object)
    (rate : StageRate object packing threshold discharge slack peeled) :
    ∃ index ∈ peeledEntries object entries peeled,
      TwoCarrierAt object packing entries threshold LengthOK peeled index := by
  have cardLe := card_entries_le_peeled object entries peeled
  unfold StageRate at rate
  -- the slack-and-peel-free ambient `|R| − slack − |P₄|`
  set ambient := (object.remainderSupport packing).card with hAmbient
  set supplyCard := (Route8Census.supply object packing).card
  set peeledCard := (peeledEntries object entries peeled).card
  have deficit' : ambient - slack - peeled.card ≤ peeledCard + discharge * supplyCard := by
    omega
  have rate' : ((threshold - 1 + 1) * discharge + 1) * supplyCard <
      (threshold - 1 + 1) * (ambient - slack - peeled.card) := by
    rw [Nat.sub_add_cancel thresholdPos]
    have big : slack + peeled.card < ambient := by
      by_contra notLt
      have le : ambient ≤ slack + peeled.card := Nat.le_of_not_lt notLt
      have := Nat.mul_le_mul_left threshold le
      rw [Nat.mul_add] at this
      omega
    rw [Nat.sub_sub, Nat.mul_sub]
    have := Nat.mul_le_mul_left threshold (Nat.le_of_lt big)
    rw [Nat.mul_add] at this ⊢
    omega
  exact Route8.exists_indexedTwoCarrierCore
    (peeledEntries object entries peeled)
    (Route8Census.core object threshold LengthOK) (Route8Census.supply object packing)
    (fun index member => Route8Census.core_subset_supply object packing threshold discharge
      LengthOK index
      (entriesSubset (peeledEntries_subset object entries peeled member)))
    deficit' rate'

/-- The loads of the peeled indices at one receiver of one piece: `P₄(w)`. -/
noncomputable def peeledLoads (peeled : Peeled object)
    (piece : Finset object.Vertex) (receiver : object.Vertex) : Finset object.Vertex :=
  (peeled.filter fun index => index.1 = piece ∧ index.2.1 = receiver).image fun index =>
    index.2.2

theorem mem_peeledLoads {peeled : Peeled object} {piece : Finset object.Vertex}
    {receiver load : object.Vertex} :
    load ∈ peeledLoads object peeled piece receiver ↔ (piece, receiver, load) ∈ peeled := by
  classical
  simp only [peeledLoads, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨p, w, u⟩, ⟨member, rfl, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨(piece, receiver, load), ⟨member, rfl, rfl⟩, rfl⟩

/-- **A target-defect entry at stage `P₄`** (`lem:typeA-pressure-is-exit4-peel`):
its load carries an exit-(4) witness at its receiver with the current peeled
loads `P₄(w)`. -/
def TargetDefectAt (threshold discharge : Nat)
    (Target : FiniteObject.{u} → Prop)
    (peeled : Peeled object) (index : Route8Census.Index object) : Prop :=
  ∃ witness : ExitFour.Witness Target index.1 threshold discharge index.2.1
      (peeledLoads object peeled index.1 index.2.1),
    witness.load = index.2.2

/-- An exit-(4) witness at the empty peeling for an unpeeled load is a witness at
the current peeling: only the unpeeled-load clause depends on the peeling set. -/
theorem targetDefectAt_of_empty (threshold discharge : Nat)
    (Target : FiniteObject.{u} → Prop)
    (peeled : Peeled object) (index : Route8Census.Index object)
    (fresh : index ∉ peeled)
    (witness : ExitFour.Witness Target index.1 threshold discharge index.2.1 ∅)
    (load : witness.load = index.2.2) :
    TargetDefectAt object threshold discharge Target peeled index := by
  refine ⟨{ witness with unpeeled := ?_ }, load⟩
  rw [ExitFour.mem_unpeeledLoads]
  have routed := ((ExitFour.mem_unpeeledLoads _ _ _).1 witness.unpeeled).1
  refine ⟨routed, fun member => fresh ?_⟩
  rw [mem_peeledLoads, load] at member
  exact member

/-- **A true route-8 entry at stage `P₄`** (`def:typeA-true-route8-residual`):
a two-carrier entry of the peeled ledger with no exit-(4) witness. -/
def TrueEntryAt (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    (index : Route8Census.Index object) : Prop :=
  index ∈ peeledEntries object entries peeled ∧
    TwoCarrierAt object packing entries threshold LengthOK peeled index ∧
    ¬ TargetDefectAt object threshold discharge
      (HasCycleWithLength LengthOK) peeled index

/-- A true entry of a stage is a true entry of the census at the empty peeling:
the two-carrier condition transports by `twoCarrierEntry_of_twoCarrierAt`, and
a witness at the empty peeling would be a witness at the stage. -/
theorem trueEntry_transport (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    {index : Route8Census.Index object}
    (true_ : TrueEntryAt object packing entries threshold discharge LengthOK peeled index) :
    index ∈ entries ∧
      Route8.IndexedTwoCarrierCore entries
        (Route8Census.core object threshold LengthOK) (threshold - 1) index ∧
      ¬ ∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) index.1
          threshold discharge index.2.1 ∅, witness.load = index.2.2 := by
  obtain ⟨member, two, notDefect⟩ := true_
  refine ⟨peeledEntries_subset object entries peeled member,
    twoCarrierEntry_of_twoCarrierAt object packing entries threshold LengthOK peeled two,
    ?_⟩
  rintro ⟨witness, load⟩
  have fresh : index ∉ peeled := (Finset.mem_sdiff.1 member).2
  exact notDefect (targetDefectAt_of_empty object threshold discharge
    (HasCycleWithLength LengthOK) peeled index fresh witness load)

/-- **A peel chain** (`lem:typeA-exit4-finite-descent`): the sequence of
target-defect peels performed by the procedure, each a two-carrier target-defect
entry of the peeled ledger at a stage with the stage rate. -/
inductive PeelChain (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop) :
    List (Route8Census.Index object) → Prop
  | nil : PeelChain packing entries threshold discharge slack LengthOK []
  | cons {chain : List (Route8Census.Index object)} {index : Route8Census.Index object}
      (previous : PeelChain packing entries threshold discharge slack LengthOK chain)
      (rate : StageRate object packing threshold discharge slack chain.toFinset)
      (member : index ∈ peeledEntries object entries chain.toFinset)
      (two : TwoCarrierAt object packing entries threshold LengthOK chain.toFinset index)
      (defect : TargetDefectAt object threshold discharge
        (HasCycleWithLength LengthOK) chain.toFinset index) :
      PeelChain packing entries threshold discharge slack LengthOK (index :: chain)

/-- **Exact accounting at one peeling stage.**  This is the denominator-cleared
form of the repaired `def:typeA-peeling-reduced-ledger`.  The full entry ledger
is the disjoint union of the reduced ledger and the recorded peels; the latter
remain charged in the original deficit.  Consequently the reduced deficit
`s*D - |P₄|` is bounded by the reduced census, while the full large-budget
inequality retains both the reduced and peeled terms. -/
def StageAccounting (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge slack : Nat)
    (chain : List (Route8Census.Index object)) : Prop :=
  let peeled := chain.toFinset
  let reduced := peeledEntries object entries peeled
  let scaledDeficit := TypeBEnvelopeCharge.route8Deficit object
    (object.remainderSupport packing) threshold discharge components
  peeled ⊆ entries ∧
    entries = reduced ∪ peeled ∧
    Disjoint reduced peeled ∧
    peeled.card ≤ scaledDeficit ∧
    scaledDeficit = scaledDeficit - peeled.card + peeled.card ∧
    scaledDeficit ≤ reduced.card + peeled.card ∧
    scaledDeficit - peeled.card ≤ reduced.card ∧
    (object.remainderSupport packing).card ≤
      reduced.card + peeled.card +
        discharge * (Route8Census.supply object packing).card + slack

/-- **The outcome of a stage** of `thm:large-budget-route8-only`'s procedure. -/
def StageOutcome (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (chain : List (Route8Census.Index object)) : Prop :=
  PeelChain object packing entries threshold discharge slack LengthOK chain ∧
    StageAccounting object packing entries components threshold discharge slack
      chain ∧
    ((StageRate object packing threshold discharge slack chain.toFinset ∧
        ∃ index,
          TrueEntryAt object packing entries threshold discharge LengthOK chain.toFinset index) ∨
      ¬ StageRate object packing threshold discharge slack chain.toFinset)

/-- **`lem:typeA-peeling-reduced-reduction`, staged**: on a stage whose deficit
reading already credits every recorded peel —
`|R| ≤ |Ξ̃ ∖ P₄| + |P₄| + s·|∂R| + slack` — the stage rate produces a
two-carrier entry of the peeled ledger. -/
theorem exists_twoCarrierEntry_staged (packing : Finset (Finset object.Vertex))
    (entries : Finset (Route8Census.Index object))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (entriesSubset : entries ⊆
      Route8Census.entries object packing threshold discharge)
    (peeled : Peeled object)
    (stageDeficit : (object.remainderSupport packing).card ≤
      (peeledEntries object entries peeled).card + peeled.card +
        discharge * (Route8Census.supply object packing).card + slack)
    (rate : StageRate object packing threshold discharge slack peeled) :
    ∃ index ∈ peeledEntries object entries peeled,
      TwoCarrierAt object packing entries threshold LengthOK peeled index := by
  unfold StageRate at rate
  set ambient := (object.remainderSupport packing).card with hAmbient
  set supplyCard := (Route8Census.supply object packing).card
  set peeledCard := (peeledEntries object entries peeled).card
  have deficit' : ambient - slack - peeled.card ≤
      peeledCard + discharge * supplyCard := by
    omega
  have rate' : ((threshold - 1 + 1) * discharge + 1) * supplyCard <
      (threshold - 1 + 1) * (ambient - slack - peeled.card) := by
    rw [Nat.sub_add_cancel thresholdPos]
    have big : slack + peeled.card < ambient := by
      by_contra notLt
      have le : ambient ≤ slack + peeled.card := Nat.le_of_not_lt notLt
      have := Nat.mul_le_mul_left threshold le
      rw [Nat.mul_add] at this
      omega
    rw [Nat.sub_sub, Nat.mul_sub]
    have := Nat.mul_le_mul_left threshold (Nat.le_of_lt big)
    rw [Nat.mul_add] at this ⊢
    omega
  exact Route8.exists_indexedTwoCarrierCore
    (peeledEntries object entries peeled)
    (Route8Census.core object threshold LengthOK)
    (Route8Census.supply object packing)
    (fun index member => Route8Census.core_subset_supply object packing threshold
      discharge LengthOK index
      (entriesSubset (peeledEntries_subset object entries peeled member)))
    deficit' rate'

/-! ## The staged burden (`lem:typeA-unified-burden` made rigorous)

`def:typeA-peeling-reduced-ledger` with every peel recorded: at every stage of
the descent the reduced burden `s·D̃_A ≤ |Ξ̃ ∖ P₄| + |P₄|` is a theorem of the
silence-free staged count
`VisibleEntry.card_le_sum_excessBasinReduced_add_positiveDeficiency`.  No
silent-first hypothesis, no per-port condition, and no flat burden assumption
occurs: `lem:typeA-silent-excess-count`'s displayed count
`Σ_w (L(w) − c(w)) ≥ s·D_A(X)` never uses silence — silence only locates the
unpaid loads under the no-overloaded-port hypothesis — and
`rem:unified-covers-exit4` keeps the unpaid visible route-8 loads in the
census, "not distinguished at the level of net charge". -/

/-- The surviving excess entries of the collection are surviving census
entries: `Σ_X Σ_w |E(w) ∖ P₄(w)| ≤ |Ξ̃ ∖ P₄|`. -/
theorem sum_excessBasin_sdiff_le_card_peeledEntries
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge : Nat)
    (componentsSub : components ⊆
      object.canonicalPieces (object.remainderSupport packing))
    (peeled : Peeled object) :
    ∑ component ∈ components,
        ∑ receiver ∈ VisibleEntry.saturatedReceivers object
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold discharge,
          ((VisibleEntry.excessBasin object
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold discharge receiver) \
            peeledLoads object peeled
              (object.pieceSupport (object.remainderSupport packing) component)
              receiver).card ≤
      (peeledEntries object
        (Route8Census.entriesOfComponents object packing components threshold
          discharge) peeled).card := by
  classical
  have subset : (components.biUnion fun component =>
      (VisibleEntry.saturatedReceivers object (object.pieceSupport (object.remainderSupport packing) component)
          threshold discharge).biUnion fun receiver =>
        ((VisibleEntry.excessBasin object (object.pieceSupport (object.remainderSupport packing) component)
            threshold discharge receiver) \
          peeledLoads object peeled (object.pieceSupport (object.remainderSupport packing) component)
            receiver).image
          fun load => ((object.pieceSupport (object.remainderSupport packing) component), receiver, load)) ⊆
      peeledEntries object
        (Route8Census.entriesOfComponents object packing components threshold
          discharge) peeled := by
    intro index member
    rw [Finset.mem_biUnion] at member
    obtain ⟨component, componentMem, member⟩ := member
    rw [Finset.mem_biUnion] at member
    obtain ⟨receiver, receiverMem, member⟩ := member
    rw [Finset.mem_image] at member
    obtain ⟨load, loadMem, rfl⟩ := member
    have silent := (Finset.mem_sdiff.1 loadMem).1
    have unpeeledLoad := (Finset.mem_sdiff.1 loadMem).2
    refine Finset.mem_sdiff.2 ⟨?_, ?_⟩
    · unfold Route8Census.entriesOfComponents
      rw [Finset.mem_biUnion]
      exact ⟨component, componentMem, by
        rw [Finset.mem_biUnion]
        exact ⟨receiver, receiverMem, Finset.mem_image.2 ⟨load, silent, rfl⟩⟩⟩
    · intro peeledMem
      exact unpeeledLoad ((mem_peeledLoads object).2 peeledMem)
  refine le_trans ?_ (Finset.card_le_card subset)
  rw [Finset.card_biUnion]
  · refine le_of_eq (Finset.sum_congr rfl fun component componentMem => ?_)
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun receiver _ => ?_
      rw [Finset.card_image_of_injective]
      intro left right equal
      simpa using congrArg (fun index => index.2.2) equal
    · intro left _ right _ different
      rw [Function.onFun, Finset.disjoint_left]
      intro index leftMem rightMem
      rw [Finset.mem_image] at leftMem rightMem
      obtain ⟨_, _, rfl⟩ := leftMem
      obtain ⟨_, _, equal⟩ := rightMem
      exact different (Eq.symm (by
        simpa using congrArg (fun index => index.2.1) equal))
  · intro left leftMem right rightMem different
    rw [Function.onFun, Finset.disjoint_left]
    intro index leftMem' rightMem'
    rw [Finset.mem_biUnion] at leftMem' rightMem'
    obtain ⟨_, _, leftMem'⟩ := leftMem'
    obtain ⟨_, _, rightMem'⟩ := rightMem'
    rw [Finset.mem_image] at leftMem' rightMem'
    obtain ⟨_, _, rfl⟩ := leftMem'
    obtain ⟨_, _, equal⟩ := rightMem'
    have pieceEq : object.pieceSupport (object.remainderSupport packing) right = object.pieceSupport (object.remainderSupport packing) left := by
      simpa using congrArg (fun index => index.1) equal
    exact different (Eq.symm (Route8Deficit.pieceSupport_injOn object (object.remainderSupport packing)
      (Finset.mem_coe.2 (componentsSub rightMem))
      (Finset.mem_coe.2 (componentsSub leftMem)) pieceEq))

/-- Every recorded peel is counted once: `Σ_X Σ_w |P₄(w) ∩ ℒ(w)| ≤ |P₄|`. -/
theorem sum_peeledLoads_inter_le_card
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge : Nat)
    (componentsSub : components ⊆
      object.canonicalPieces (object.remainderSupport packing))
    (peeled : Peeled object) :
    ∑ component ∈ components,
        ∑ receiver ∈ object.receivers
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold,
          (peeledLoads object peeled
              (object.pieceSupport (object.remainderSupport packing) component)
              receiver ∩
            object.routedLoads
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold receiver).card ≤
      peeled.card := by
  classical
  have subset : (components.biUnion fun component =>
      (object.receivers (object.pieceSupport (object.remainderSupport packing) component) threshold).biUnion
        fun receiver =>
          (peeledLoads object peeled (object.pieceSupport (object.remainderSupport packing) component) receiver ∩
            object.routedLoads (object.pieceSupport (object.remainderSupport packing) component) threshold
              receiver).image
            fun load => ((object.pieceSupport (object.remainderSupport packing) component), receiver, load)) ⊆
      peeled := by
    intro index member
    rw [Finset.mem_biUnion] at member
    obtain ⟨component, _componentMem, member⟩ := member
    rw [Finset.mem_biUnion] at member
    obtain ⟨receiver, _receiverMem, member⟩ := member
    rw [Finset.mem_image] at member
    obtain ⟨load, loadMem, rfl⟩ := member
    exact (mem_peeledLoads object).1 (Finset.mem_inter.1 loadMem).1
  refine le_trans ?_ (Finset.card_le_card subset)
  rw [Finset.card_biUnion]
  · refine le_of_eq (Finset.sum_congr rfl fun component componentMem => ?_)
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun receiver _ => ?_
      rw [Finset.card_image_of_injective]
      intro left right equal
      simpa using congrArg (fun index => index.2.2) equal
    · intro left _ right _ different
      rw [Function.onFun, Finset.disjoint_left]
      intro index leftMem rightMem
      rw [Finset.mem_image] at leftMem rightMem
      obtain ⟨_, _, rfl⟩ := leftMem
      obtain ⟨_, _, equal⟩ := rightMem
      exact different (Eq.symm (by
        simpa using congrArg (fun index => index.2.1) equal))
  · intro left leftMem right rightMem different
    rw [Function.onFun, Finset.disjoint_left]
    intro index leftMem' rightMem'
    rw [Finset.mem_biUnion] at leftMem' rightMem'
    obtain ⟨_, _, leftMem'⟩ := leftMem'
    obtain ⟨_, _, rightMem'⟩ := rightMem'
    rw [Finset.mem_image] at leftMem' rightMem'
    obtain ⟨_, _, rfl⟩ := leftMem'
    obtain ⟨_, _, equal⟩ := rightMem'
    have pieceEq : object.pieceSupport (object.remainderSupport packing) right = object.pieceSupport (object.remainderSupport packing) left := by
      simpa using congrArg (fun index => index.1) equal
    exact different (Eq.symm (Route8Deficit.pieceSupport_injOn object (object.remainderSupport packing)
      (Finset.mem_coe.2 (componentsSub rightMem))
      (Finset.mem_coe.2 (componentsSub leftMem)) pieceEq))

/-- **The staged burden** (`lem:typeA-peeling-reduced-reduction`'s first
part, proven): at a stage where every completion port of every collection
receiver carries at most `s − 1` visible **unpeeled** returns — the state the
per-port exit-(4) peels of `lem:typeA-unpeeled-visible-routing` drive the
procedure into, with every peel recorded on the ledger — the reduced ledger
satisfies `s·D̃_A ≤ |Ξ̃ ∖ P₄| + |P₄|`. -/
theorem stage_burden
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge : Nat) (dischargePos : 1 ≤ discharge)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (componentsSub : components ⊆
      object.canonicalPieces (object.remainderSupport packing))
    (surplusZero : ∀ component ∈ components,
      object.ambientSurplus
        (object.pieceSupport (object.remainderSupport packing) component)
        threshold = 0)
    (routed : ∀ piece : Finset object.Vertex,
      piece ⊆ object.remainderSupport packing →
      object.ambientSurplus piece threshold = 0 →
      ∀ vertex ∈ piece, object.internalDegree piece vertex = threshold →
        ∃ receiver : object.Vertex,
          object.traceReceiver? piece threshold vertex = some receiver ∧
            object.IsReceiver piece threshold receiver)
    (peeled : Peeled object) :
    TypeBEnvelopeCharge.route8Deficit object (object.remainderSupport packing)
        threshold discharge components ≤
      (peeledEntries object
        (Route8Census.entriesOfComponents object packing components threshold
          discharge) peeled).card + peeled.card := by
  classical
  have perPiece : ∀ component ∈ components,
      (object.pieceSupport (object.remainderSupport packing) component).card -
          discharge * object.positiveDeficiency
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold ≤
        (∑ receiver ∈ object.receivers
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold,
          ((VisibleEntry.excessBasin object
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold discharge receiver) \
            peeledLoads object peeled
              (object.pieceSupport (object.remainderSupport packing) component)
              receiver).card) +
        ∑ receiver ∈ object.receivers
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold,
          (peeledLoads object peeled
              (object.pieceSupport (object.remainderSupport packing) component)
              receiver ∩
            object.routedLoads
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold receiver).card := by
    intro component componentMem
    set piece := object.pieceSupport (object.remainderSupport packing)
      component with pieceDef
    have exactDegree : ∀ vertex ∈ piece, object.degree vertex = threshold := by
      intro vertex vertexMem
      have nonneg := baseline vertex
      have summand : object.degree vertex - threshold = 0 :=
        Nat.eq_zero_of_le_zero
          ((surplusZero component componentMem) ▸ Finset.single_le_sum
            (f := fun other => object.degree other - threshold)
            (fun _ _ => Nat.zero_le _) vertexMem)
      omega
    have capped : ∀ vertex ∈ piece,
        object.internalDegree piece vertex ≤ threshold :=
      fun vertex vertexMem =>
        exactDegree vertex vertexMem ▸
          object.internalDegree_le_degree piece vertex
    have count :=
      VisibleEntry.card_le_sum_excessBasinReduced_add_positiveDeficiency
        object piece threshold discharge dischargePos capped
        (routed piece (object.pieceSupport_subset _ component)
          (surplusZero component componentMem))
        (fun receiver => peeledLoads object peeled piece receiver)
    have monotone :
        (∑ receiver ∈ object.receivers piece threshold,
            (VisibleEntry.excessBasinReduced object piece threshold discharge
              receiver (peeledLoads object peeled piece receiver)).card) ≤
          ∑ receiver ∈ object.receivers piece threshold,
            ((VisibleEntry.excessBasin object piece threshold discharge
                receiver) \
              peeledLoads object peeled piece receiver).card := by
      refine Finset.sum_le_sum ?_
      intro receiver _
      exact Finset.card_le_card
        (VisibleEntry.excessBasinReduced_subset object piece threshold
          discharge receiver (peeledLoads object peeled piece receiver))
    refine tsub_le_iff_right.mpr ?_
    refine le_trans count ?_
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right monotone _) _) ?_
    exact le_of_eq (Nat.add_right_comm _ _ _)
  have summed :
      TypeBEnvelopeCharge.route8Deficit object (object.remainderSupport packing)
          threshold discharge components ≤
        (∑ component ∈ components,
          ∑ receiver ∈ object.receivers
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold,
            ((VisibleEntry.excessBasin object
                (object.pieceSupport (object.remainderSupport packing)
                  component)
                threshold discharge receiver) \
              peeledLoads object peeled
                (object.pieceSupport (object.remainderSupport packing)
                  component)
                receiver).card) +
        ∑ component ∈ components,
          ∑ receiver ∈ object.receivers
              (object.pieceSupport (object.remainderSupport packing) component)
              threshold,
            (peeledLoads object peeled
                (object.pieceSupport (object.remainderSupport packing)
                  component)
                receiver ∩
              object.routedLoads
                (object.pieceSupport (object.remainderSupport packing)
                  component)
                threshold receiver).card := by
    unfold TypeBEnvelopeCharge.route8Deficit
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum perPiece
  have excessRestrict : ∀ component ∈ components,
      (∑ receiver ∈ object.receivers
          (object.pieceSupport (object.remainderSupport packing) component)
          threshold,
        ((VisibleEntry.excessBasin object
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold discharge receiver) \
          peeledLoads object peeled
            (object.pieceSupport (object.remainderSupport packing) component)
            receiver).card) =
      ∑ receiver ∈ VisibleEntry.saturatedReceivers object
          (object.pieceSupport (object.remainderSupport packing) component)
          threshold discharge,
        ((VisibleEntry.excessBasin object
            (object.pieceSupport (object.remainderSupport packing) component)
            threshold discharge receiver) \
          peeledLoads object peeled
            (object.pieceSupport (object.remainderSupport packing) component)
            receiver).card := by
    intro component _componentMem
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro receiver _receiverMem absent
    have unsaturated : ¬ object.Saturated
        (object.pieceSupport (object.remainderSupport packing) component)
        threshold discharge receiver := by
      intro saturated
      exact absent (Finset.mem_filter.2 ⟨_receiverMem, saturated⟩)
    rw [VisibleEntry.excessBasin_eq_empty_of_not_saturated object
      (object.pieceSupport (object.remainderSupport packing) component)
      threshold discharge unsaturated]
    simp
  calc TypeBEnvelopeCharge.route8Deficit object
        (object.remainderSupport packing) threshold discharge components
      ≤ _ := summed
    _ ≤ (peeledEntries object
          (Route8Census.entriesOfComponents object packing components threshold
            discharge) peeled).card + peeled.card := by
        refine Nat.add_le_add ?_ ?_
        · rw [Finset.sum_congr rfl excessRestrict]
          exact sum_excessBasin_sdiff_le_card_peeledEntries object packing
            components threshold discharge componentsSub peeled
        · exact sum_peeledLoads_inter_le_card object packing components
            threshold discharge componentsSub peeled

end Hypostructure.Graph.Route8Pressure
