import Hypostructure.Graph.Strategy.SpineVocabulary

/-! Independently compiled spine row declarations. -/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy

universe u v

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}
variable {data : Data.{u}}

variable [FactSystem (Input BranchState Presentation presentation data)]

/-! ## Node `[32]`: the finite circuit form of the rank split

The paragraph immediately after `lem:target-rank-circuit` states the exact
finite implication `r_Ω(R) < W₂(R) ⇒` a raw curvature coordinate is
target-dependent.  The complementary finite arm is `r_Ω(R) = W₂(R)`;
`lem:full-rank` later records its weaker asymptotic consequence
`r_Ω(R) ≥ W₂(R) - o(W₂(R))`.  This decision publishes precisely those
two finite branch facts on the concrete remainder. -/
omit [FactSystem (Input BranchState Presentation presentation data)] in
noncomputable def curvatureRankDichotomy
    {current : Input BranchState Presentation presentation data}
    {known : @FactKeys (Input BranchState Presentation presentation data)
      _ (factSystem BranchState Presentation presentation data)}
    (previous :
      @ExactLedger (Input BranchState Presentation presentation data)
        _ (factSystem BranchState Presentation presentation data) current known)
    [@Core.Residual.FactKeys.Has
      (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data)
      (K .targetRankCircuit) known]
    (dropFresh : K .curvatureRankDrop ∉ known)
    (fullFresh : K .curvatureFullRank ∉ known) :
    @Decision (Input BranchState Presentation presentation data) _
      (factSystem BranchState Presentation presentation data) current known
      (K .curvatureRankDrop) (K .curvatureFullRank) previous :=
  @Decision.run (Input BranchState Presentation presentation data) _
    (factSystem BranchState Presentation presentation data) current known
    previous (K .curvatureRankDrop) (K .curvatureFullRank)
    `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy
    (by
      classical
      -- `lem:target-rank-circuit` at the manuscript's fixed maximal packing.
      let circuit := (@ExactLedger.get
        (Input BranchState Presentation presentation data) _
        (factSystem BranchState Presentation presentation data)
        current known previous (K .targetRankCircuit)).down
      let packing := canonicalWindowPacking data current.object
      have packingSpec := Classical.choose_spec
        (current.object.exists_windowPacking_card_eq data.windowOrder)
      have valid : current.object.IsWindowPacking data.windowOrder packing := packingSpec.1
      have packingCard : packing.card = current.object.windowPackingNumber data.windowOrder :=
        packingSpec.2
      have extract := (circuit packing valid packingCard).1
      have attained := Graph.FiniteObject.exists_attaining_curvatureTargetRank
        (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) current.object
        (current.object.remainderSupport packing)
      let independent := Classical.choose attained
      have independentSpec := Classical.choose_spec attained
      have independentSubset : independent ⊆ _ := independentSpec.1
      have survives : Graph.FiniteObject.SurvivesCurvatureSystem
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) current.object
          (current.object.remainderSupport packing) independent := independentSpec.2.1
      have rank : independent.card = _ := independentSpec.2.2
      clear_value independent
      by_cases below :
          remainderCurvatureTargetRank data current.object packing <
            remainderWedgeSupply current.object packing
      · refine .inl ⟨⟨packing, valid, packingCard, below, ?_⟩⟩
        have outside : ∃ test ∈
            current.object.internalWedgeFamily
              (current.object.remainderSupport packing),
            test ∉ independent := by
          by_contra noOutside
          push Not at noOutside
          have familySubset :
              current.object.internalWedgeFamily
                  (current.object.remainderSupport packing) ⊆ independent :=
            noOutside
          have equal : independent =
              current.object.internalWedgeFamily
                (current.object.remainderSupport packing) :=
            Finset.Subset.antisymm independentSubset familySubset
          rw [equal, Graph.FiniteObject.internalWedgeFamily_card] at rank
          exact (Nat.ne_of_lt below) rank.symm
        obtain ⟨test, testMember, testOutside⟩ := outside
        obtain ⟨determiners, determinersSubset, finite, proper, declared,
          functional, reducing, determines⟩ :=
          extract independent independentSubset survives rank test testMember testOutside
        exact ⟨test, testMember, determiners,
          determinersSubset.trans independentSubset, finite, proper,
          declared, functional, reducing, determines⟩
      · refine .inr ⟨⟨packing, valid, packingCard, ?_⟩⟩
        apply Nat.le_antisymm
        · change
            current.object.curvatureTargetRank
                (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK)
                (current.object.remainderSupport packing) ≤
              current.object.internalWedgeCount
                (current.object.remainderSupport packing)
          rw [← rank]
          calc
            independent.card ≤
                (current.object.internalWedgeFamily
                  (current.object.remainderSupport packing)).card :=
              Finset.card_le_card independentSubset
            _ = current.object.internalWedgeCount
                  (current.object.remainderSupport packing) :=
              Graph.FiniteObject.internalWedgeFamily_card
                (object := current.object)
                (support := current.object.remainderSupport packing)
        exact Nat.le_of_not_gt below)
    dropFresh fullFresh

end Hypostructure.Graph.Strategy.Spine
