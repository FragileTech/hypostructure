import Hypostructure.Graph.Route8Census
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
  fails (the manuscript's "the stage closes by the large-budget net-deficiency
  cap and `thm:branch-kill`").
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

/-- `Ξ^{P₄}`: the census entries with the peeled indices removed. -/
noncomputable def peeledEntries (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (peeled : Peeled object) :
    Finset (Route8Census.Index object) :=
  Route8Census.entries object packing threshold discharge \ peeled

theorem peeledEntries_subset (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (peeled : Peeled object) :
    peeledEntries object packing threshold discharge peeled ⊆
      Route8Census.entries object packing threshold discharge :=
  Finset.sdiff_subset

/-- Peeling removes at most one entry per peeled index. -/
theorem card_entries_le_peeled (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (peeled : Peeled object) :
    (Route8Census.entries object packing threshold discharge).card ≤
      (peeledEntries object packing threshold discharge peeled).card + peeled.card :=
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
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    (index : Route8Census.Index object) : Prop :=
  Route8.IndexedTwoCarrierCore (peeledEntries object packing threshold discharge peeled)
    (Route8Census.core object threshold LengthOK) (threshold - 1) index

/-- Private carriers only grow when the family shrinks, so a two-carrier entry of
the peeled family is a two-carrier entry of the full census. -/
theorem twoCarrierEntry_of_twoCarrierAt (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    {index : Route8Census.Index object}
    (two : TwoCarrierAt object packing threshold discharge LengthOK peeled index) :
    Route8Census.TwoCarrierEntry object packing threshold discharge LengthOK index := by
  unfold TwoCarrierAt Route8.IndexedTwoCarrierCore at two
  unfold Route8Census.TwoCarrierEntry Route8.IndexedTwoCarrierCore
  refine le_trans ?_ two
  unfold Route8.indexedPrivateCoreCount
  apply Finset.card_le_card
  intro carrier member
  rw [Route8.indexedPrivateCoreCarriers, Finset.mem_filter] at member ⊢
  refine ⟨member.1, fun other otherMem ne => ?_⟩
  exact member.2 other (peeledEntries_subset object packing threshold discharge peeled otherMem) ne

/-- **`lem:typeA-peeling-reduced-reduction`**: on a stage with the stage rate,
the peeled ledger contains a two-carrier entry. -/
theorem exists_twoCarrierEntry_peeled (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (deficit : Route8Census.Deficit object packing threshold discharge slack)
    (peeled : Peeled object)
    (rate : StageRate object packing threshold discharge slack peeled) :
    ∃ index ∈ peeledEntries object packing threshold discharge peeled,
      TwoCarrierAt object packing threshold discharge LengthOK peeled index := by
  have cardLe := card_entries_le_peeled object packing threshold discharge peeled
  unfold Route8Census.Deficit at deficit
  unfold StageRate at rate
  -- the slack-and-peel-free ambient `|R| − slack − |P₄|`
  set ambient := (object.remainderSupport packing).card with hAmbient
  set supplyCard := (Route8Census.supply object packing).card
  set peeledCard := (peeledEntries object packing threshold discharge peeled).card
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
    (peeledEntries object packing threshold discharge peeled)
    (Route8Census.core object threshold LengthOK) (Route8Census.supply object packing)
    (fun index member => Route8Census.core_subset_supply object packing threshold discharge
      LengthOK index (peeledEntries_subset object packing threshold discharge peeled member))
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
def TargetDefectAt (threshold : Nat) (Target : FiniteObject.{u} → Prop)
    (peeled : Peeled object) (index : Route8Census.Index object) : Prop :=
  ∃ witness : ExitFour.Witness Target index.1 threshold index.2.1
      (peeledLoads object peeled index.1 index.2.1),
    witness.load = index.2.2

/-- An exit-(4) witness at the empty peeling for an unpeeled load is a witness at
the current peeling: only the unpeeled-load clause depends on the peeling set. -/
theorem targetDefectAt_of_empty (threshold : Nat) (Target : FiniteObject.{u} → Prop)
    (peeled : Peeled object) (index : Route8Census.Index object)
    (fresh : index ∉ peeled)
    (witness : ExitFour.Witness Target index.1 threshold index.2.1 ∅)
    (load : witness.load = index.2.2) :
    TargetDefectAt object threshold Target peeled index := by
  refine ⟨{ witness with unpeeled := ?_ }, load⟩
  rw [ExitFour.mem_unpeeledLoads]
  have routed := ((ExitFour.mem_unpeeledLoads _ _ _).1 witness.unpeeled).1
  refine ⟨routed, fun member => fresh ?_⟩
  rw [mem_peeledLoads, load] at member
  exact member

/-- **A true route-8 entry at stage `P₄`** (`def:typeA-true-route8-residual`):
a two-carrier entry of the peeled ledger with no exit-(4) witness. -/
def TrueEntryAt (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    (index : Route8Census.Index object) : Prop :=
  index ∈ peeledEntries object packing threshold discharge peeled ∧
    TwoCarrierAt object packing threshold discharge LengthOK peeled index ∧
    ¬ TargetDefectAt object threshold (HasCycleWithLength LengthOK) peeled index

/-- A true entry of a stage is a true entry of the census at the empty peeling:
the two-carrier condition transports by `twoCarrierEntry_of_twoCarrierAt`, and
a witness at the empty peeling would be a witness at the stage. -/
theorem trueEntry_transport (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (peeled : Peeled object)
    {index : Route8Census.Index object}
    (true_ : TrueEntryAt object packing threshold discharge LengthOK peeled index) :
    index ∈ Route8Census.entries object packing threshold discharge ∧
      Route8Census.TwoCarrierEntry object packing threshold discharge LengthOK index ∧
      ¬ ∃ witness : ExitFour.Witness (HasCycleWithLength LengthOK) index.1 threshold
          index.2.1 ∅, witness.load = index.2.2 := by
  obtain ⟨member, two, notDefect⟩ := true_
  refine ⟨peeledEntries_subset object packing threshold discharge peeled member,
    twoCarrierEntry_of_twoCarrierAt object packing threshold discharge LengthOK peeled two,
    ?_⟩
  rintro ⟨witness, load⟩
  have fresh : index ∉ peeled := (Finset.mem_sdiff.1 member).2
  exact notDefect (targetDefectAt_of_empty object threshold (HasCycleWithLength LengthOK)
    peeled index fresh witness load)

/-- **A peel chain** (`lem:typeA-exit4-finite-descent`): the sequence of
target-defect peels performed by the procedure, each a two-carrier target-defect
entry of the peeled ledger at a stage with the stage rate. -/
inductive PeelChain (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop) :
    List (Route8Census.Index object) → Prop
  | nil : PeelChain packing threshold discharge slack LengthOK []
  | cons {chain : List (Route8Census.Index object)} {index : Route8Census.Index object}
      (previous : PeelChain packing threshold discharge slack LengthOK chain)
      (rate : StageRate object packing threshold discharge slack chain.toFinset)
      (member : index ∈ peeledEntries object packing threshold discharge chain.toFinset)
      (two : TwoCarrierAt object packing threshold discharge LengthOK chain.toFinset index)
      (defect : TargetDefectAt object threshold (HasCycleWithLength LengthOK)
        chain.toFinset index) :
      PeelChain packing threshold discharge slack LengthOK (index :: chain)

/-- Every peeled index of a chain is a census entry. -/
theorem PeelChain.toFinset_subset {packing : Finset (Finset object.Vertex)}
    {threshold discharge slack : Nat} {LengthOK : Nat → Prop}
    {chain : List (Route8Census.Index object)}
    (valid : PeelChain object packing threshold discharge slack LengthOK chain) :
    chain.toFinset ⊆ Route8Census.entries object packing threshold discharge := by
  induction valid with
  | nil => simp
  | cons _ _ member _ _ ih =>
      intro index memberIndex
      rw [List.toFinset_cons, Finset.mem_insert] at memberIndex
      rcases memberIndex with rfl | tail
      · exact peeledEntries_subset object _ _ _ _ member
      · exact ih tail

/-- **The outcome of a stage** of `thm:large-budget-route8-only`'s procedure. -/
def StageOutcome (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (chain : List (Route8Census.Index object)) : Prop :=
  PeelChain object packing threshold discharge slack LengthOK chain ∧
    ((StageRate object packing threshold discharge slack chain.toFinset ∧
        ∃ index, TrueEntryAt object packing threshold discharge LengthOK chain.toFinset index) ∨
      ¬ StageRate object packing threshold discharge slack chain.toFinset)

/-- **`thm:large-budget-route8-only`'s procedure**: from the census, the
target-defect peels reach a stage with a true (route-8) two-carrier entry —
node `[124]` — or a stage where the stage rate fails.  Termination is
`lem:typeA-exit4-finite-descent`: each target-defect peel removes one unpeeled
entry (`Λ₄` strictly decreases). -/
theorem descent (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (deficit : Route8Census.Deficit object packing threshold discharge slack) :
    ∀ chain : List (Route8Census.Index object),
      PeelChain object packing threshold discharge slack LengthOK chain →
      ∃ final : List (Route8Census.Index object),
        StageOutcome object packing threshold discharge slack LengthOK final := by
  classical
  intro chain valid
  -- strong induction on the number of unpeeled entries
  suffices key : ∀ n : Nat, ∀ chain : List (Route8Census.Index object),
      PeelChain object packing threshold discharge slack LengthOK chain →
      (peeledEntries object packing threshold discharge chain.toFinset).card = n →
      ∃ final, StageOutcome object packing threshold discharge slack LengthOK final from
    key _ chain valid rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro chain valid cardEq
    by_cases rate : StageRate object packing threshold discharge slack chain.toFinset
    · obtain ⟨index, member, two⟩ :=
        exists_twoCarrierEntry_peeled object packing threshold discharge slack LengthOK
          thresholdPos deficit chain.toFinset rate
      by_cases defect :
          TargetDefectAt object threshold (HasCycleWithLength LengthOK) chain.toFinset index
      · -- peel: one more index, strictly fewer unpeeled entries
        have valid' := PeelChain.cons (object := object) valid rate member two defect
        have fresh : index ∉ chain.toFinset := (Finset.mem_sdiff.1 member).2
        have smaller :
            (peeledEntries object packing threshold discharge (index :: chain).toFinset).card
              < n := by
          rw [← cardEq]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨index, member, ?_⟩
            simp [peeledEntries]
          · intro other otherMem
            simp only [peeledEntries, List.toFinset_cons, Finset.mem_sdiff,
              Finset.mem_insert, not_or] at otherMem ⊢
            exact ⟨otherMem.1, otherMem.2.2⟩
        exact ih _ smaller (index :: chain) valid' rfl
      · exact ⟨chain, valid, Or.inl ⟨rate, index, member, two, defect⟩⟩
    · exact ⟨chain, valid, Or.inr rate⟩

/-- The procedure started at the empty peeling with the census: the paper's
`thm:large-budget-route8-only` outcome. -/
theorem descent_of_census (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (deficit : Route8Census.Deficit object packing threshold discharge slack) :
    ∃ final : List (Route8Census.Index object),
      StageOutcome object packing threshold discharge slack LengthOK final :=
  descent object packing threshold discharge slack LengthOK thresholdPos deficit []
    PeelChain.nil

end Hypostructure.Graph.Route8Pressure
