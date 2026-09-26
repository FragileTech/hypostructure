import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.SparsePortActivation
import Hypostructure.Graph.PrimitiveCarrier
import Hypostructure.Graph.SparsePairLedger
import Hypostructure.Graph.SameTokenBlockerRoles
import Hypostructure.Graph.SparseEntropySandwich
import Hypostructure.Graph.CapacityTokenAssignment
import Hypostructure.Graph.SparseUpperEnvelope
import Hypostructure.Graph.ObjectCapacityLedger
import Hypostructure.Graph.Induced

/-!
# Contract lemmas: the sparse-surplus setup `[126]`--`[129]`

`lem:sparse-slack-surplus`, `lem:sparse-excess-port-extraction`,
`lem:sparse-port-activation`, `lem:surviving-active-family` and
`def:baseline-spine-demand`, each stated over a finite object at the
registered baseline with the paper's assumptions as explicit hypotheses.
-/

namespace Hypostructure.Graph.Contracts.SurplusPair

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- Node `[126]`, `lem:sparse-slack-surplus`, cleared of division:
`2m = δn + σ(G)` at the baseline. -/
theorem sparseSlackSurplus_of_baseline
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object) :
    SparseSlackSurplusStatement data object := by
  have handshake : data.threshold * object.vertexCount ≤ 2 * object.edgeCount :=
    Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount object
      data.threshold fun vertex =>
        le_trans atBaseline (object.minDegree_le_degree vertex)
  unfold SparseSlackSurplusStatement Graph.FiniteObject.degreeSurplus
  omega

/-- Node `[127]`, `lem:sparse-excess-port-extraction` with the family half of
`lem:surviving-active-family`: at the baseline with slack vertices pairwise
nonadjacent (node `[10]`), the excess selector has `σ(G)` members and each port
has a centre above the baseline, an endpoint at it, and `δ − 1` shoulders. -/
theorem activeSurplusFamily_of_slackIndependent
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (independent : SlackIndependentStatement data object) :
    ActiveSurplusFamilyStatement data object := by
  have baseline : ∀ vertex : object.Vertex, data.threshold ≤ object.degree vertex :=
    fun vertex => le_trans atBaseline (object.minDegree_le_degree vertex)
  exact ⟨object.card_excessPorts baseline, fun _pair member =>
    ⟨Graph.FiniteObject.centre_high_of_mem_excessPorts member,
      (object.surplusPortOfMem member).endpoint_degree_eq baseline independent,
      (object.surplusPortOfMem member).card_shoulders baseline independent⟩⟩

/-- Node `[128]`, `lem:sparse-port-activation` (a)--(d): at the selected
minimal counterexample, every port with a shoulder pair carries its return
path `R_p`, an open port carries the single-port suppression witness `Q_p`, and
a triangular port carries its triangle. -/
theorem sparsePortActivation_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selection : SelectionStatement BranchState Presentation presentation data
      object)
    (suppressionWitness : SingleOpenPortSuppressionWitnessStatement data object) :
    SparsePortActivationStatement data object :=
  fun _pair member left right shoulders distinct =>
    ⟨(object.surplusPortOfMem member).portReturn_of_minimal
        shoulders atBaseline selection.1 selection.2,
      fun openPort => suppressionWitness
        ((object.surplusPortOfMem member).configuration
          shoulders distinct openPort)
        (object.surplusPortOfMem member).centre_high,
      fun adjacent =>
        (object.surplusPortOfMem member).triangle_of_shoulders_adj
          (shoulders left |>.2 (Or.inl rfl))
          (shoulders right |>.2 (Or.inr rfl)) adjacent⟩

/-- Node `[125]`, `def:active-surplus-demands` with
`lem:surviving-active-family`: at the cubic baseline, a survivor of the sparse
exits with the extracted and activated excess ports has its active family. -/
theorem activeSurplusDemands_of_activation
    (cubic : data.threshold = 3)
    (survivor : SparseSurplusSurvivorStatement data object)
    (family : ActiveSurplusFamilyStatement data object)
    (activation : SparsePortActivationStatement data object) :
    ActiveSurplusDemandsStatement data object :=
  Graph.surviving_active_family survivor family.1
    (by
      classical
      intro pair member
      have cardAt := family.2 pair member |>.2.2
      have cardTwo : (object.surplusPortOfMem member).shoulders.card = 2 := by
        simpa [cubic] using cardAt
      obtain ⟨left, right, distinct, description⟩ := Finset.card_eq_two.mp cardTwo
      refine ⟨left, right, ?_, distinct⟩
      intro vertex
      rw [description]
      simp)
    activation

/-- Node `[129]`, `def:baseline-spine-demand`: on a survivor of the sparse
exits at the baseline with a strict surplus, no proper baseline subgraph and a
tight endpoint on every edge, the clause-(D8) family of labelled Boolean
quotient images of the full-support return-data profile is declared,
independently target-testable, realized in the current fixed-edge stratum, and
its cubic-baseline deficit is at most `C_E n`. -/
theorem baselineSpineDemand_of_survivor
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (activeFact : ActiveSurplusDemandsStatement data object)
    (survivorFact : SparseSurplusSurvivorStatement data object)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (noProperBaseline : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (threeLe : 3 ≤ data.threshold)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤
      data.surplusScale) :
    BaselineSpineDemandStatement data object := by
  classical
  let active := activeFact
  let survivor := survivorFact
  have surplusPositive :
      0 < object.degreeSurplus data.threshold :=
    lt_of_le_of_lt (Nat.zero_le _)
      above
  let bits := Graph.realizableBaselineExponent object.vertexCount
    data.threshold
  let Label := Option (ULift.{u} (Fin bits))
  let Coordinate := Graph.DeclaredSignature.Coordinate object.Vertex Label
  let source : Coordinate :=
    Graph.DeclaredSignature.Coordinate.base
      .returnData none object.vertexFinset
  let family : Finset Coordinate :=
    Finset.univ.image fun bit =>
      Graph.DeclaredSignature.Coordinate.copy (some bit)
        (.quotientImage source)
  let coordinateSupport : Coordinate → Finset object.Vertex :=
    Graph.DeclaredSignature.Coordinate.support
  have familyCard : family.card = bits := by
    rw [Finset.card_image_iff.mpr]
    · simp [Fintype.card_ulift]
    · intro left _ right _ equality
      have labelEquality : (some left : Label) = some right :=
        congrArg
        (fun coordinate => match coordinate with
          | .copy label _source => label
          | _ => none)
        equality
      exact Option.some.inj labelEquality
  have aboveBaseline :
      Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
        object.edgeCount := by
    have handshake : data.threshold * object.vertexCount ≤
        2 * object.edgeCount :=
      Graph.baselineDegree_mul_vertexCount_le_two_mul_edgeCount
        object data.threshold fun vertex =>
          le_trans atBaseline
            (object.minDegree_le_degree vertex)
    exact Graph.cubicBaselineEdgeCount_le_edgeCount_of_handshake
      object data.threshold handshake
  have edgePositive : 0 < object.edgeCount :=
    object.edgeCount_pos_of_degreeSurplus_pos surplusPositive
  have envelope : object.edgeCount + 2 ≤
      (data.threshold - 1) * object.vertexCount :=
    object.edgeCount_add_two_le threeLe
      noProperBaseline.1
      tight edgePositive
  have baselineCount : 2 ^ family.card ≤
      Graph.skeletonBudget object := by
    rw [familyCard]
    exact
      Graph.two_pow_realizableBaselineExponent_le_skeletonBudget
        object data.threshold aboveBaseline envelope
  let Assignment := {coordinate // coordinate ∈ family} → Bool
  let Skeleton := Graph.PackedWindowRealization.Skeleton
    object.vertexCount object.edgeCount
  letI : Fintype Assignment := Fintype.ofFinite Assignment
  letI : Fintype Skeleton := Fintype.ofFinite Skeleton
  have cardLe : Fintype.card Assignment ≤ Fintype.card Skeleton := by
    have codeCard : Nat.card Assignment = 2 ^ family.card := by
      dsimp [Assignment]
      rw [Nat.card_fun]
      simp
    have skeletonCard : Nat.card Skeleton =
        Graph.skeletonBudget object := by
      dsimp [Skeleton]
      simpa [Graph.skeletonBudget, Graph.edgeStratumCount] using
        Graph.PackedWindowRealization.card_skeleton
          object.vertexCount object.edgeCount
    simpa [← Nat.card_eq_fintype_card, codeCard, skeletonCard] using
      baselineCount
  let encode : Assignment → Skeleton := fun assignment =>
    (Fintype.equivFin Skeleton).symm
      (Fin.castLE cardLe ((Fintype.equivFin Assignment) assignment))
  have encodeInjective : Function.Injective encode := by
    intro left right equality
    apply (Fintype.equivFin Assignment).injective
    apply Fin.castLE_injective cardLe
    apply (Fintype.equivFin Skeleton).symm.injective
    exact equality
  let ReturnProfile := Fin object.vertexCount →
    Fin object.vertexCount → Option (Finset Nat)
  let returnProfile : Graph.LabelledOn object.vertexCount →
      ReturnProfile :=
    fun member left right =>
      if adjacent : member.graph.Adj left right then
        some (Graph.EdgeRootedReturn.returnLengthFinset
          member.toFiniteObject ⟨(left, right), adjacent⟩)
      else
        none
  have returnProfileInjective : Function.Injective returnProfile := by
    intro left right same
    apply Graph.LabelledOn.ext
    ext first second
    constructor
    · intro leftAdjacent
      by_contra rightAdjacent
      have profileEquality := congrFun (congrFun same first) second
      simp [returnProfile, leftAdjacent, rightAdjacent] at profileEquality
    · intro rightAdjacent
      by_contra leftAdjacent
      have profileEquality := congrFun (congrFun same first) second
      simp [returnProfile, leftAdjacent, rightAdjacent] at profileEquality
  letI : Nonempty (Graph.LabelledOn object.vertexCount) :=
    ⟨⟨⊥⟩⟩
  let quotientMap : {coordinate // coordinate ∈ family} →
      ReturnProfile → Bool :=
    fun coordinate profile =>
      let member := Function.invFun returnProfile profile
      if edgeCount : Nat.card member.graph.edgeSet = object.edgeCount then
        Function.invFun encode ⟨member, edgeCount⟩ coordinate
      else false
  have realization : Graph.BaselineCodeRealization object family :=
    { Label := Label
      asDeclared := id
      source := source
      source_is_returnProfile := ⟨none, rfl⟩
      quotientImage := by
        rintro ⟨coordinate, membership⟩
        obtain ⟨bit, _bitMem, equality⟩ := Finset.mem_image.mp membership
        exact ⟨some bit, equality.symm⟩
      returnProfile := returnProfile
      returnProfile_edge := by
        intro member left right adjacent
        simp [returnProfile, adjacent]
      returnProfile_nonedge := by
        intro member left right adjacent
        simp [returnProfile, adjacent]
      quotientMap := quotientMap
      realized := by
        intro assignment
        refine ⟨encode assignment, ?_⟩
        funext coordinate
        dsimp [quotientMap]
        rw [Function.leftInverse_invFun returnProfileInjective
          (encode assignment).1]
        split
        · exact congrFun
            (Function.leftInverse_invFun encodeInjective assignment)
            coordinate
        · rename_i edgeCount
          exact (edgeCount (encode assignment).2).elim }
  refine ⟨active, Coordinate, family, coordinateSupport, ?_,
    ⟨realization⟩, ?_, ?_⟩
  · intro declared _functional
    by_contra reducing
    rcases declared.localize reducing with replacement |
      ⟨representative, smaller, baseline, transfer⟩
    · exact survivor
        (.compression declared.support replacement)
    · exact survivor
        (.delocalization representative smaller baseline transfer)
  · rw [familyCard]
    exact
      Graph.cubicBaselineBudget_le_two_pow_add_spineDeficit
        object.vertexCount
        (le_trans (by omega) threeLe) bits
  · rw [familyCard]
    exact (Graph.spineDeficit_realizableBaselineExponent_le
      object.vertexCount data.threshold).trans
        (Nat.mul_le_mul_right object.vertexCount
          deficitSafety)

end Hypostructure.Graph.Contracts.SurplusPair
