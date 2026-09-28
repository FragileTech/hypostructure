import Hypostructure.Graph.Statements.SparseExitResidual
import Hypostructure.Graph.SparseOrderArithmetic
import Hypostructure.Graph.DeclaredQuotientRank
import Hypostructure.Graph.WindowInternalMass
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.Contracts.SurplusPair.Estimate
import Hypostructure.Graph.Contracts.SurplusPair.OverloadClass
import Hypostructure.Graph.Contracts.SurplusPair.Activation
import Hypostructure.Graph.Contracts.TypeB.OpenPort
import Hypostructure.Graph.Contracts.SurplusPair.Entropy
import Hypostructure.Graph.Contracts.SurplusPair.PairOverlap
import Hypostructure.Graph.Contracts.SurplusPair.PairCode
import Hypostructure.Graph.Contracts.SurplusPair.Routing

/-!
# Contracts: the strict-surplus named sparse exit `[20a]`, made explicit

Proof-agnostic contract lemmas for `Statements/SparseExitResidual.lean`.  Each
is stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every hypothesis explicit; the hypotheses are exactly the facts
the `[20a]` ledger carries (selection, the presentation laws, the baseline,
noProperBaseline, tightEndpoint, the replacement exclusion, target-complete
context universality, the maximal packing, surplusAbove, and `[125]`'s pinned
target-defect witness).  One contract per statement: `<statement>_holds`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SparseExitResidual

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.GluedReadings

universe u v

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## The canonical witness: basic consequences of its clauses -/

section WitnessLevel

variable {w : SparseTargetDefectWitness data object}

/-- The separation clause of the witness, in glue form. -/
theorem separated_of_spec (spec : w.Spec) :
    ¬ (Graph.HasCycleWithLength data.LengthOK (glue (w.reading w.first) w.outside) ↔
      Graph.HasCycleWithLength data.LengthOK (glue (w.reading w.second) w.outside)) :=
  spec.2.2.2.2.2.2

theorem geometryAt_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) :
    Hypostructure.Graph.BoundTargetDefectGeometryAt object w.support data.LengthOK
      (w.reading w.first) (w.reading w.second) w.outside :=
  boundTargetDefectGeometryAt_of_separated (separated_of_spec spec) avoid

theorem two_le_cutBoundary_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) : 2 ≤ (SupportAtom.cutBoundary object w.support).card :=
  two_le_cutBoundary_of_geometryAt avoid (geometryAt_of_spec avoid spec)

theorem proper_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) : ∃ v, v ∉ w.support :=
  proper_of_boundary (by have := two_le_cutBoundary_of_spec avoid spec; omega)

theorem support_card_lt_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) : w.support.card + 1 ≤ object.vertexCount := by
  obtain ⟨out, hout⟩ := proper_of_spec avoid spec
  have : w.support.card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => hout (h (object.mem_vertexFinset out))⟩
  omega

theorem support_connected (spec : w.Spec) :
    SupportComponents.Connected.ConnectedOn object w.support :=
  (CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates spec.2.2.2.1)).2

theorem first_subset_support (spec : w.Spec) :
    sparseDeclaredSupport data object w.first ⊆ w.support := by
  classical
  intro v hv
  exact (CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates spec.2.2.2.1)).1
    (Finset.mem_union.2 (Or.inl hv))

theorem second_subset_support (spec : w.Spec) :
    sparseDeclaredSupport data object w.second ⊆ w.support := by
  classical
  intro v hv
  exact (CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates spec.2.2.2.1)).1
    (Finset.mem_union.2 (Or.inr hv))

theorem swap_spec (spec : w.Spec) : w.swap.Spec := by
  classical
  obtain ⟨a, b, c, d, e, f, g⟩ := spec
  refine ⟨b, a, Ne.symm c, ?_, e.symm, f.symm, fun h => g h.symm⟩
  change CanonicalSupport.select? object
      (sparseDeclaredSupport data object w.second ∪
        sparseDeclaredSupport data object w.first) = some w.support
  convert d using 2
  exact Finset.union_comm _ _

end WitnessLevel

/-! ## Witness-level G facts -/

section WitnessFacts

theorem witnessReadingsNotTargetComplete_holds
    (universality : TargetCompleteContextUniversalityStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessReadingsNotTargetCompleteStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (universality.2 w.support _ _ spec.2.2.2.2.2.1
    (fun ce => separated_of_spec spec (ce w.outside))).2⟩

theorem witnessActualOutsideNegative_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessActualOutsideNegativeStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, retainedGlue_avoids avoid _ _, retainedGlue_avoids avoid _ _⟩

theorem witnessReadingsCycleFree_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessReadingsCycleFreeStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, retainedPiece_avoids avoid _ _, retainedPiece_avoids avoid _ _⟩

theorem witnessSupportOrderBound_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessSupportOrderBoundStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, support_card_lt_of_spec avoid spec⟩

theorem witnessReadingGluesNotSmallerBaseline_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessReadingGluesNotSmallerBaselineStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  refine ⟨w, canon, fun X _ ⟨baseline, smaller⟩ => ?_⟩
  exact retainedGlue_avoids avoid w.support X (minimal _ smaller baseline)

theorem noSuppressionChordViolation_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    NoSuppressionChordViolationStatement data object := by
  intro tvs certificate violates
  let expanded := tvs.expandCycle certificate
  have accepted : data.LengthOK expanded.walk.length := by
    rw [expanded.length_eq]
    exact violates
  exact avoid ⟨⟨tvs.sourceVertex certificate.vertex, expanded.walk,
    expanded.isCycle, accepted⟩⟩

end WitnessFacts

/-! ## The single budget -/

section Budget

/-- The numeric core at the cubic baseline, from the ledger's baseline, tight
endpoint, no-proper-baseline and strict-surplus facts. -/
theorem budget_core (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    data.spineScale * Core.ceilSqrt object.vertexCount + 1 ≤
        object.degreeSurplus data.threshold ∧
      object.edgeCount + 2 ≤ 2 * object.vertexCount ∧
      2 * object.edgeCount = 3 * object.vertexCount + object.degreeSurplus data.threshold ∧
      object.degreeSurplus data.threshold + 4 ≤ object.vertexCount ∧
      object.vertexCount ≤ Core.ceilSqrt object.vertexCount ^ 2 := by
  have base3 : Graph.MinimumDegreeAtLeast 3 object := three ▸ baseline
  have tight3 : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := three ▸ tight
  obtain ⟨-, -, hm⟩ := SparseOrderArithmetic.surplus_dart_identity object base3 tight3
  have above' : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := above
  have h3 : object.degreeSurplus data.threshold = object.degreeSurplus 3 := by rw [three]
  rw [h3] at above' ⊢
  have mpos : 0 < object.edgeCount := by
    unfold Graph.FiniteObject.degreeSurplus at above'
    omega
  have env := object.edgeCount_add_two_le (threshold := data.threshold) (by omega)
    noProper.1 tight mpos
  rw [three] at env
  have sq := Core.le_ceilSqrt_sq object.vertexCount
  refine ⟨above', by simpa using env, hm, by omega, sq⟩

theorem edgeSurplusIdentity_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    EdgeSurplusIdentityStatement data object := by
  obtain ⟨-, -, hm, -⟩ := budget_core three baseline tight noProper above
  unfold EdgeSurplusIdentityStatement
  rw [three] at hm ⊢; exact hm

theorem surplusDartIdentity_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object) :
    SurplusDartIdentityStatement data object := by
  have base3 : Graph.MinimumDegreeAtLeast 3 object := three ▸ baseline
  have tight3 : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := three ▸ tight
  obtain ⟨ident, -, -⟩ := SparseOrderArithmetic.surplus_dart_identity object base3 tight3
  unfold SurplusDartIdentityStatement sparseHighDegreeCount sparseLowDartCount
  rw [three]
  omega

theorem highDegreeCountBound_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object) :
    HighDegreeCountBoundStatement data object := by
  have base3 : Graph.MinimumDegreeAtLeast 3 object := three ▸ baseline
  have tight3 : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := three ▸ tight
  obtain ⟨-, hle, -⟩ := SparseOrderArithmetic.surplus_dart_identity object base3 tight3
  unfold HighDegreeCountBoundStatement sparseHighDegreeCount
  rw [three]
  exact hle

theorem packingOrderBound_holds : PackingOrderBoundStatement data object := by
  classical
  unfold PackingOrderBoundStatement
  obtain ⟨valid, _, _⟩ := canonicalWindowPacking_spec data object
  have hcard := Finset.card_biUnion (s := canonicalWindowPacking data object) (t := id)
    (fun x hx y hy ne => valid.2 x hx y hy ne)
  have hsum : ∑ u ∈ canonicalWindowPacking data object, (id u).card =
      (canonicalWindowPacking data object).card * data.windowOrder := by
    calc ∑ u ∈ canonicalWindowPacking data object, (id u).card
        = ∑ _u ∈ canonicalWindowPacking data object, data.windowOrder :=
          Finset.sum_congr rfl (fun x hx => (valid.1 x hx).2)
      _ = (canonicalWindowPacking data object).card * data.windowOrder := by simp
  have sub : (canonicalWindowPacking data object).biUnion id ⊆ object.vertexFinset :=
    fun v _ => object.mem_vertexFinset v
  have := Finset.card_le_card sub
  rw [Graph.FiniteObject.card_vertexFinset, hcard, hsum] at this
  linarith [this]

theorem ceilSqrtAboveScale_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    CeilSqrtAboveScaleStatement data object := by
  obtain ⟨h1, -, -, h4, sq⟩ := budget_core three baseline tight noProper above
  exact (SparseOrderArithmetic.sqrt_chain _ _ _ _ h1 h4 sq).1

end Budget

/-! ## The order of G (K4) -/

section Order

variable (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
  Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)

include minimal

end Order

/-! ## The envelope (K5) -/

section Envelope

/-- `m + 3 ≤ 2n` and `m + 4 ≤ 2n` at G, with the order bounds they need. -/
theorem envelope_core (three : data.threshold = 3) (four : data.LengthOK 4)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    object.edgeCount + 3 ≤ 2 * object.vertexCount ∧
      object.edgeCount + 4 ≤ 2 * object.vertexCount := by
  obtain ⟨h1, h2, hm, h4, -⟩ := budget_core three baseline tight noProper above
  have np : ∀ subgraph : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 subgraph.value :=
    three ▸ noProper.1
  have mpos : 0 < object.edgeCount := by omega
  obtain ⟨dart⟩ := object.exists_dart_of_edgeCount_pos mpos
  have t3 : object.degree dart.fst = 3 ∨ object.degree dart.snd = 3 := three ▸ tight dart
  have five : 5 ≤ object.vertexCount := by omega
  have sharp : object.edgeCount + 3 ≤ 2 * object.vertexCount := by
    rcases t3 with t | t
    · exact object.edgeCount_add_three_le_of_noC4 four avoid np t five
    · exact object.edgeCount_add_three_le_of_noC4 four avoid np t five
  have seven : 7 ≤ object.vertexCount := by omega
  have sharper : object.edgeCount + 4 ≤ 2 * object.vertexCount := by
    rcases t3 with t | t
    · exact object.edgeCount_add_four_le_of_noC4 four avoid np t seven
    · exact object.edgeCount_add_four_le_of_noC4 four avoid np t seven
  exact ⟨sharp, sharper⟩

theorem orderAboveScaleSquare_holds (three : data.threshold = 3) (four : data.LengthOK 4)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    OrderAboveScaleSquareStatement data object := by
  obtain ⟨h1, -, hm, -, sq⟩ := budget_core three baseline tight noProper above
  have env := (envelope_core three four avoid baseline tight noProper above).2
  have h8 : object.degreeSurplus data.threshold + 8 ≤ object.vertexCount := by omega
  have hc := (SparseOrderArithmetic.sqrt_chain _ _ _ _ h1 (by omega) sq).1
  have : data.spineScale * (data.spineScale + 1) ≤
      data.spineScale * Core.ceilSqrt object.vertexCount := Nat.mul_le_mul_left _ hc
  unfold OrderAboveScaleSquareStatement
  omega

theorem sixVertexExtremalEnvelope_holds (three : data.threshold = 3) (four : data.LengthOK 4)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    SixVertexExtremalEnvelopeStatement object :=
  (envelope_core three four avoid baseline tight noProper above).2

end Envelope

/-! ## The window packing -/

section Packing

theorem remainderDeficiencyBelowCut_holds (baseline : MinDegreeBaselineStatement data object) :
    RemainderDeficiencyBelowCutStatement data object :=
  object.positiveDeficiency_le_boundaryIncidence _ data.threshold
    (fun v => baseline.trans (object.minDegree_le_degree v))

theorem windowCutCapacity_holds (baseline : MinDegreeBaselineStatement data object) :
    WindowCutCapacityStatement data object :=
  object.boundaryIncidence_add_internal_mass_le (canonicalWindowPacking_spec data object).1
    (fun v => baseline.trans (object.minDegree_le_degree v))

end Packing

/-! ## The capacity presentations of G (K6) -/

section Capacity

open Hypostructure.Graph.SameTokenBlockerRoles

section AnyLedger

variable (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
  (safety : TokenLoad.quadraticSafetyScale ≤ data.spineScale)
  {capacity : SurplusCapacity data object}
  (certified : SurplusCertified data object capacity)

include above safety

end AnyLedger

open Hypostructure.Graph.Contracts.SurplusPair in
theorem baselineSpineDemand_of_noCD
    (atBaseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (noCompression : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object support)
    (noDelocalization : ∀ representative : Graph.FiniteObject.{u},
      representative.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold representative →
      (Graph.HasCycleWithLength data.LengthOK representative →
        Graph.HasCycleWithLength data.LengthOK object) → False)
    (above : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold)
    (noProperBaseline : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (threeLe : 3 ≤ data.threshold)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤
      data.surplusScale) :
    BaselineSpineDemandStatement data object := by
  classical
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
  have spec : BaselineSpineFamilySpec data object Coordinate family
      coordinateSupport := by
    refine ⟨?_, ⟨realization⟩, ?_, ?_⟩
    · intro declared _functional
      by_contra reducing
      rcases declared.localize reducing with replacement |
        ⟨representative, smaller, baseline, transfer⟩
      · exact noCompression declared.support replacement
      · exact noDelocalization representative smaller baseline transfer
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
  -- The node publishes the canonical choice of its own `∃`-body: the family
  -- constructed above witnesses that the canonical spine family of G exists.
  exact canonicalBaselineSpineFamily_spec data object
    ⟨Coordinate, family, coordinateSupport, spec⟩


/-- **`[129]`'s baseline spine demand on the `[20a]` path**: its survivor
premise is used only against exits (c) and (d), which G's replacement
exclusion and selection refute. -/
theorem baselineSpineDemand_of_selection (three : data.threshold = 3)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (exclusion : ReplacementExclusionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object) :
    BaselineSpineDemandStatement data object :=
  baselineSpineDemand_of_noCD baseline exclusion
    (fun representative smaller b transfer =>
      avoid (transfer (minimal representative smaller b)))
    above noProper tight (by omega) deficitSafety

end Capacity

/-! ## Contexts realized in G, sub-contexts, the path spectrum (K1) -/

section Realized

theorem witnessOutsideNotRealized_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WitnessOutsideNotRealizedStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, ⟨fun r => ?_⟩⟩
  apply separated_of_spec spec
  exact ⟨fun h => (realized_context_negative avoid r _ h).elim,
    fun h => (realized_context_negative avoid r _ h).elim⟩

theorem realizedContextsNegative_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    RealizedContextsNegativeStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, fun O' ⟨r⟩ =>
    ⟨realized_context_negative avoid r _, realized_context_negative avoid r _⟩⟩

/-- The positive/negative ordering of the two readings at `O`. -/
theorem positive_negative_of_spec {w : SparseTargetDefectWitness data object} (spec : w.Spec) :
    ∃ P ∈ w.pairSupports, ∃ N ∈ w.pairSupports,
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support P) w.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support N) w.outside) := by
  have sep := separated_of_spec spec
  by_cases h1 : Graph.HasCycleWithLength data.LengthOK (glue (w.reading w.first) w.outside)
  · have h2 : ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (w.reading w.second) w.outside) := fun h2 => sep ⟨fun _ => h2, fun _ => h1⟩
    exact ⟨_, Or.inl rfl, _, Or.inr rfl, h1, h2⟩
  · have h2 : Graph.HasCycleWithLength data.LengthOK (glue (w.reading w.second) w.outside) := by
      by_contra h2
      exact sep ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    exact ⟨_, Or.inr rfl, _, Or.inl rfl, h2, h1⟩

theorem negativeSubGluingNotSmallerBaseline_holds
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    NegativeSubGluingNotSmallerBaselineStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  obtain ⟨-, -, N, hN, -, neg⟩ := positive_negative_of_spec spec
  exact ⟨w, canon, N, hN, neg, fun g le =>
    negative_subContext_not_smaller_baseline minimal _ _ neg g le⟩

theorem cycleSubContextSeparates_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    CycleSubContextSeparatesStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  have proper := proper_of_spec avoid spec
  obtain ⟨P, hP, N, hN, pos, neg⟩ := positive_negative_of_spec spec
  obtain ⟨c⟩ := pos
  refine ⟨w, canon, P, hP, N, hN, _, cycleContext_le _ _ c, cycleContext_positive _ _ c,
    subContext_negative _ _ neg _ (cycleContext_le _ _ c),
    cycleContext_degree_le_two _ _ c, fun baseline => ?_⟩
  have empty := cycleContext_baseline_chordOnly _ _ _ c (by omega) baseline
  exact negative_subContext_not_smaller_baseline minimal _ _ neg _ (cycleContext_le _ _ c)
    ⟨baseline, chordOnly_retainedGlue_smaller _ empty proper⟩

theorem pathSpectrumSplit_holds
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    PathSpectrumSplitStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  obtain ⟨P, hP, N, hN, pos, neg⟩ := positive_negative_of_spec spec
  refine ⟨w, canon, P, hP, N, hN, pos, neg, ?_⟩
  rcases spectrum_split pos neg (retainedPiece_avoids avoid w.support P) with
    ⟨a, b, hab, π, hπ, σ, hσ, lab, ok, three, rest⟩ | many
  · left
    refine ⟨a, b, hab, π, hπ, σ, hσ, lab,
      (Core.DyadicLength.powerOfTwoLength_iff _).mp ((lengthLaw _).mp ok),
      fun π' hπ' => ⟨(rest π' hπ').1, fun j hj eq => ?_⟩⟩
    by_cases hn : 1 < π'.length ∨ 1 < σ.length
    · exact (rest π' hπ').2 hn
        ((lengthLaw _).mpr ((Core.DyadicLength.powerOfTwoLength_iff _).mpr ⟨j, hj, eq⟩))
    · push Not at hn
      have : 4 ≤ 2 ^ j := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
  · exact Or.inr many

end Realized

/-! ## Admissible quotients of G (K7) -/

section Quotients

variable {w : SparseTargetDefectWitness data object}

/-- Every admissible quotient of G is label-injective: its representative
clauses are refuted by the replacement exclusion and by selection. -/
theorem declared_labelInjective_at
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (exclusion : ReplacementExclusionStatement data object)
    {Coordinate : Type u} {family : Finset Coordinate}
    {cs : Coordinate → Finset object.Vertex}
    (quotient : DeclaredQuotient (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object family cs) :
    Set.InjOn quotient.label ↑family :=
  DeclaredQuotientRank.declared_labelInjective_generic exclusion minimal avoid quotient

theorem admissibleQuotientsLabelInjective_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (exclusion : ReplacementExclusionStatement data object) :
    AdmissibleQuotientsLabelInjectiveStatement data object :=
  fun _ _ q => declared_labelInjective_at avoid minimal exclusion q

end Quotients

/-! ## The boundary of the canonical support (K2) -/

section Boundary

open Classical

theorem baseline_three (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object) :
    Graph.MinimumDegreeAtLeast 3 object := three ▸ baseline

theorem noProper_three (three : data.threshold = 3)
    (noProper : NoProperBaselineStatement data object) :
    ∀ sub : Graph.ProperSubgraph object, ¬ Graph.MinimumDegreeAtLeast 3 sub.value :=
  three ▸ noProper.1

theorem minimal_three (three : data.threshold = 3)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H) :
    ∀ candidate : Graph.FiniteObject.{u},
      candidate.LexicographicallySmaller object → 3 ≤ candidate.minDegree →
        Graph.HasCycleWithLength data.LengthOK candidate :=
  fun candidate smaller baseline => minimal candidate smaller (by
    unfold Graph.MinimumDegreeAtLeast; omega)

theorem singleBoundaryShape_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object) :
    SingleBoundaryShapeStatement object := by
  intro S b single z hz zb proper
  have := single_boundary_shape object (baseline_three three baseline)
    (noProper_three three noProper) bridgeless S b single hz zb proper
  convert this

/-- The declared support of the reading positive at `O` meets `∂Z` in two
vertices. -/
theorem positive_support_two_boundary (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec) :
    2 ≤ (SupportAtom.cutBoundary object w.support ∩
          sparseDeclaredSupport data object w.first).card ∨
      2 ≤ (SupportAtom.cutBoundary object w.support ∩
          sparseDeclaredSupport data object w.second).card := by
  have geo := geometryAt_of_spec avoid spec
  have go : ∀ (Xp Xn : Finset object.Vertex),
      DefectGeometry.PositiveStructure object w.support data.LengthOK
        (SupportAtom.retainedPiece object w.support Xp)
        (SupportAtom.retainedPiece object w.support Xn) w.outside →
      2 ≤ (SupportAtom.cutBoundary object w.support ∩ Xp).card := by
    intro Xp Xn ps
    obtain ⟨c⟩ := ps.positive
    have ho : DefectGeometry.ContextExclusive c := by
      rcases ps.external c with loc | ⟨mixed, _⟩
      · exact (retainedPiece_avoids avoid w.support Xp
          (DefectGeometry.local_target c loc)).elim
      · exact mixed
    obtain ⟨l₁, l₂, ne, h₁, h₂⟩ := two_retained_labels c (ps.indispensable c) ho
    have sub : ({l₁.1, l₂.1} : Finset object.Vertex) ⊆
        SupportAtom.cutBoundary object w.support ∩ Xp := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.2 ⟨l₁.2, h₁⟩
      · exact Finset.mem_inter.2 ⟨l₂.2, h₂⟩
    have c2 : ({l₁.1, l₂.1} : Finset object.Vertex).card = 2 :=
      Finset.card_pair (fun h => ne (Subtype.ext h))
    exact c2 ▸ Finset.card_le_card sub
  rcases geo.2 with ps | ps
  · exact Or.inl (go _ _ ps)
  · exact Or.inr (go _ _ ps)

theorem positiveSupportBoundaryTwo_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    PositiveSupportBoundaryTwoStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, ?_⟩
  convert positive_support_two_boundary avoid spec

theorem supportCutEdgesTwo_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SupportCutEdgesTwoStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, ?_⟩
  have := le_trans (two_le_cutBoundary_of_spec avoid spec)
    (card_cutBoundary_le_cutEdges object w.support)
  unfold supportCutEdgeCount
  convert this

theorem support_nonempty_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec) : w.support.Nonempty := by
  rw [← Finset.card_pos]
  have sub : SupportAtom.cutBoundary object w.support ⊆ w.support := fun v hv =>
    ((SupportAtom.mem_cutBoundary_iff _ _ v).1 hv).1
  have := Finset.card_le_card sub
  have := two_le_cutBoundary_of_spec avoid spec
  omega

theorem boundaryLowInsideVertex_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    BoundaryLowInsideVertexStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  obtain ⟨b, hb, low⟩ := exists_boundary_low_inside object 3 (baseline_three three baseline)
    (noProper_three three noProper) w.support (support_nonempty_of_spec avoid spec)
    (proper_of_spec avoid spec)
  exact ⟨w, canon, b, hb, by omega⟩

theorem outsideLowVertex_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    OutsideLowVertexStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  obtain ⟨x, hx, xlow, xadj⟩ := exists_outside_low object 3 (baseline_three three baseline)
    (noProper_three three noProper) w.support (support_nonempty_of_spec avoid spec)
    (proper_of_spec avoid spec)
  refine ⟨w, canon, x, hx, ?_, xadj⟩
  convert Nat.le_of_lt_succ xlow using 2

theorem twoBoundaryLowOutsideSide_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundaryLowOutsideSideStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  refine ⟨w, canon, fun a b hab interior => ?_⟩
  obtain ⟨i, hi, hib⟩ := interior
  have iNot : i ∉ outsideSide object w.support a b := by
    rw [hab] at hib
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hib
    simp [outsideSide, hi, hib.1, hib.2]
  have lt : (outsideSide object w.support a b).card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => iNot (h (object.mem_vertexFinset i))⟩
  obtain ⟨v, hv, low⟩ := exists_low_internalDegree object 3
    (noProper_three three noProper) _ ⟨a, by simp [outsideSide]⟩ lt
  by_cases va : v = a
  · subst va; exact Or.inl (by omega)
  by_cases vb : v = b
  · subst vb; exact Or.inr (by omega)
  exfalso
  rw [internalDegree_eq_degree_of_closed object _ v
    (outsideSide_closed object w.support hab v hv va vb)] at low
  have := le_trans (baseline_three three baseline) (object.minDegree_le_degree v)
  omega

theorem twoBoundarySupportClosure_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundarySupportClosureStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, fun a b ab hab notAdj da db => ?_⟩
  obtain ⟨x, hx⟩ := proper_of_spec avoid spec
  have mem : ∀ v, v ∈ SupportAtom.cutBoundary object w.support → v ∈ w.support :=
    fun v hv => ((SupportAtom.mem_cutBoundary_iff _ _ v).1 hv).1
  have lt : w.support.card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => hx (h (object.mem_vertexFinset x))⟩
  exact side_closure_path object (baseline_three three baseline) avoid
    (minimal_three three minimal) w.support (mem a (by rw [hab]; simp))
    (mem b (by rw [hab]; simp)) ab notAdj lt
    (closedZ_of_two object w.support hab) da db

theorem twoBoundaryOutsideClosure_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundaryOutsideClosureStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  refine ⟨w, canon, fun a b ab hab interior notAdj da db => ?_⟩
  obtain ⟨i, hi, hib⟩ := interior
  have iNot : i ∉ outsideSide object w.support a b := by
    rw [hab] at hib
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hib
    simp [outsideSide, hi, hib.1, hib.2]
  have lt : (outsideSide object w.support a b).card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => iNot (h (object.mem_vertexFinset i))⟩
  exact side_closure_path object (baseline_three three baseline) avoid
    (minimal_three three minimal) _ (by simp [outsideSide]) (by simp [outsideSide]) ab notAdj
    lt (outsideSide_closed object w.support hab) da db

theorem twoBoundaryNoTargetSum_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundaryNoTargetSumStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  refine ⟨w, canon, fun a b hab p hp pZ q hq qT long => ?_⟩
  refine no_target_two_sides object avoid w.support
    (outsideSide object w.support a b) ?_ p hp pZ q hq qT long
  intro v vZ vT
  simp only [outsideSide, Finset.mem_filter] at vT
  rcases vT.2 with h | h | h
  · exact (h vZ).elim
  · exact Or.inl h
  · exact Or.inr h

theorem outsideOrBoundaryLarge_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    OutsideOrBoundaryLargeStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, ?_⟩
  obtain ⟨x, hx⟩ := proper_of_spec avoid spec
  have xW : x ∈ supportOutside object w.support := by simp [supportOutside, hx]
  by_cases one : (supportOutside object w.support).card = 1
  · right
    obtain ⟨x', hx'⟩ := Finset.card_eq_one.mp one
    have only : ∀ y, y ∉ w.support → y = x := by
      intro y hy
      have yW : y ∈ supportOutside object w.support := by simp [supportOutside, hy]
      rw [hx'] at yW xW
      rw [Finset.mem_singleton] at yW xW
      rw [yW, xW]
    rw [single_outside_boundary_card object w.support hx only]
    exact le_trans (baseline_three three baseline) (object.minDegree_le_degree x)
  · left
    have := Finset.card_pos.2 ⟨x, xW⟩
    omega

end Boundary

/-! ## The compression route at G's own pieces (K3) -/

section Compression

/-! ### G-level facts from the residual's objects -/

/-- Reading comparability: `B ⊆ A ⇒` the `A`-reading is positive at the
separating `O` and the `B`-reading negative. -/
theorem larger_reading_positive {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (BA : sparseDeclaredSupport data object w.second ⊆
      sparseDeclaredSupport data object w.first) :
    HasCycleWithLength data.LengthOK (glue (w.reading w.first) w.outside) ∧
      ¬ HasCycleWithLength data.LengthOK (glue (w.reading w.second) w.outside) := by
  have sep := spec.2.2.2.2.2.2
  unfold Graph.canonicalCoordinateResponse at sep
  change ¬ (HasCycleWithLength _ (glue (w.reading w.first) w.outside) ↔
    HasCycleWithLength _ (glue (w.reading w.second) w.outside)) at sep
  have mono := fun c => glue_retained_mono (L := data.LengthOK) BA w.outside c
  by_cases pA : HasCycleWithLength data.LengthOK (glue (w.reading w.first) w.outside)
  · exact ⟨pA, fun pB => sep ⟨fun _ => pB, fun _ => pA⟩⟩
  · exact (sep ⟨fun h => (pA h).elim, fun h => (pA (mono h)).elim⟩).elim

/-- **At most one reading is whole**: `Z ⊆ A` and `Z ⊆ B` are incompatible
with the separation at `O`. -/
theorem not_both_whole {w : SparseTargetDefectWitness data object} (spec : w.Spec) :
    ¬ (w.support ⊆ sparseDeclaredSupport data object w.first ∧
        w.support ⊆ sparseDeclaredSupport data object w.second) := by
  rintro ⟨hA, hB⟩
  have sep := spec.2.2.2.2.2.2
  unfold Graph.canonicalCoordinateResponse at sep
  change ¬ (HasCycleWithLength _ (glue (w.reading w.first) w.outside) ↔
    HasCycleWithLength _ (glue (w.reading w.second) w.outside)) at sep
  exact sep ⟨fun h => glue_retained_mono (fun v hv => hB (first_subset_support spec hv))
      w.outside h,
    fun h => glue_retained_mono (fun v hv => hA (second_subset_support spec hv)) w.outside h⟩

/-- The canonical support has at least two vertices (it contains `|∂Z| ≥ 2`). -/
theorem support_two {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (avoid : ¬ HasCycleWithLength data.LengthOK object) : 1 < w.support.card := by
  have sep := spec.2.2.2.2.2.2
  unfold Graph.canonicalCoordinateResponse at sep
  change ¬ (HasCycleWithLength _ (glue (w.reading w.first) w.outside) ↔
    HasCycleWithLength _ (glue (w.reading w.second) w.outside)) at sep
  have two := two_le_cutBoundary_of_geometryAt avoid (boundTargetDefectGeometryAt_of_separated sep avoid)
  have sub : SupportAtom.cutBoundary object w.support ⊆ w.support := fun v hv =>
    ((SupportAtom.mem_cutBoundary_iff object w.support v).1 hv).1
  have := Finset.card_le_card sub
  omega

/-- **Tight-endpoint deficit of a dropped edge.**  In `glue(ret_X, G − Z)`
(a spanning copy of a subgraph of G), if two vertices `a, b` are adjacent in G
but not in the gluing, then one of them has degree `< threshold` (deficit ≥ 1),
namely one whose G-degree is exactly the threshold. -/
theorem dropped_edge_tight_deficit
    (tight : TightEndpointStatement data object) (Z X : Finset object.Vertex)
    (a b : (glue (SupportAtom.retainedPiece object Z X) (SupportAtom.outside object Z)).Vertex)
    (inG : object.graph.Adj (retainedGlueHom Z X a) (retainedGlueHom Z X b))
    (notIn : ¬ (glue (SupportAtom.retainedPiece object Z X)
        (SupportAtom.outside object Z)).graph.Adj a b) :
    (glue (SupportAtom.retainedPiece object Z X) (SupportAtom.outside object Z)).degree a
        < data.threshold ∨
      (glue (SupportAtom.retainedPiece object Z X) (SupportAtom.outside object Z)).degree b
        < data.threshold := by
  have inj := retainedGlueHom_injective (object := object) Z X
  rcases tight ⟨(_, _), inG⟩ with ha | hb
  · left
    have := degree_lt_of_injHom_missing (retainedGlueHom Z X) inj a _ inG
      (fun z hz hzb => notIn (by rw [← inj hzb]; exact hz))
    simp only at ha
    omega
  · right
    have := degree_lt_of_injHom_missing (retainedGlueHom Z X) inj b _ inG.symm
      (fun z hz hza => notIn (by rw [← inj hza]; exact hz.symm))
    simp only at hb
    omega

/-- **Whole case, boundary side.**  If `Z ⊆ A`, then every Z-neighbour of a
boundary vertex lies in `B`, and so does the boundary vertex: the equal
boundary profile forces `ret_B` to own every piece edge at `∂Z`. -/
theorem whole_case_boundary_nbrs_in_B {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (whole : w.support ⊆ sparseDeclaredSupport data object w.first)
    {b v : object.Vertex} (hb : b ∈ SupportAtom.cutBoundary object w.support)
    (hv : v ∈ w.support) (adj : object.graph.Adj b v) :
    b ∈ sparseDeclaredSupport data object w.second ∧
      v ∈ sparseDeclaredSupport data object w.second := by
  classical
  have hbZ : b ∈ w.support := ((SupportAtom.mem_cutBoundary_iff object w.support b).1 hb).1
  have BA : sparseDeclaredSupport data object w.second ⊆
      sparseDeclaredSupport data object w.first :=
    fun x hx => whole (second_subset_support spec hx)
  have prof := congrFun spec.2.2.2.2.1 ⟨b, hb⟩
  unfold BoundaryPiece.boundaryDegreeProfile BoundaryPiece.boundaryDegree at prof
  rw [FiniteObject.degree_eq_ncard_neighborSet, FiniteObject.degree_eq_ncard_neighborSet] at prof
  let e := pieceEncode object w.support v hv
  have adjA : (w.reading w.first).graph.Adj (.inl ⟨b, hb⟩) e := by
    refine ⟨?_, ?_⟩
    · change object.graph.Adj b (SupportAtom.pieceDecode object w.support e)
      rw [pieceDecode_encode]; exact adj
    · simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      change b ≠ SupportAtom.pieceDecode object w.support e ∧ _
      rw [pieceDecode_encode]
      exact ⟨adj.ne, Or.inl ⟨whole hbZ, whole hv⟩⟩
  by_contra hcon
  have notB : ¬ (w.reading w.second).graph.Adj (.inl ⟨b, hb⟩) e := by
    rintro ⟨-, h2⟩
    simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at h2
    change b ≠ SupportAtom.pieceDecode object w.support e ∧ _ at h2
    rw [pieceDecode_encode] at h2
    rcases h2 with ⟨-, hh | hh⟩
    · exact hcon ⟨hh.1, hh.2⟩
    · exact hcon ⟨hh.2, hh.1⟩
  have fin : ((w.reading w.first).pack.graph.neighborSet (.inl ⟨b, hb⟩)).Finite := by
    letI : FinEnum (w.reading w.first).pack.Vertex := (w.reading w.first).pack.vertices
    exact Set.toFinite _
  have lt : ((w.reading w.second).pack.graph.neighborSet (.inl ⟨b, hb⟩)).ncard <
      ((w.reading w.first).pack.graph.neighborSet (.inl ⟨b, hb⟩)).ncard := by
    refine Set.ncard_lt_ncard ⟨fun x hx => retainedPiece_le BA hx, fun sub => ?_⟩
      fin
    exact notB (sub adjA)
  rw [prof] at lt
  exact lt_irrefl _ lt

/-- **Whole case, the deficit set `S = Z ∖ B`.**  If `Z ⊆ A`:
`S` is nonempty; every `s ∈ S` is internal, has no neighbour on `∂Z`, and is
isolated (degree `0`) in `glue(ret_B, O')` for every context `O'`. -/
theorem whole_case_deficit_set
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (whole : w.support ⊆ sparseDeclaredSupport data object w.first) :
    (∃ s ∈ w.support, s ∉ sparseDeclaredSupport data object w.second) ∧
    ∀ s ∈ w.support, s ∉ sparseDeclaredSupport data object w.second →
      s ∉ SupportAtom.cutBoundary object w.support ∧
      (∀ b ∈ SupportAtom.cutBoundary object w.support, ¬ object.graph.Adj s b) ∧
      ∃ i : SupportAtom.PieceInternal object w.support, i.1 = s ∧
        ∀ O' : OutsideContext (SupportAtom.boundary object w.support),
          (glue (w.reading w.second) O').degree (.inr (.inl i)) = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    exact not_both_whole spec ⟨whole, fun v hv => hcon v hv⟩
  · intro s hsZ hsB
    have notBd : s ∉ SupportAtom.cutBoundary object w.support := by
      intro hsbd
      obtain ⟨t, ht, hst⟩ := Finset.exists_mem_ne (support_two spec avoid) s
      obtain ⟨v, hsv, hv⟩ := exists_adj_in_of_connectedOn object (support_connected spec)
        hsZ ht (Ne.symm hst)
      exact hsB (whole_case_boundary_nbrs_in_B spec whole hsbd hv hsv).1
    refine ⟨notBd, fun b hb adj => hsB
      (whole_case_boundary_nbrs_in_B spec whole hb hsZ adj.symm).2,
      ⟨s, hsZ, notBd⟩, rfl, fun O' => internal_isolated _ hsB O'⟩

open Classical in
/-- **Budget form.**  In the whole case, for every context `O'`, the gluing
`glue(ret_B, O')` has at least `|Z ∖ B| ≥ 1` isolated vertices, and its total
degree deficit `Σ_v (k − deg v)` is at least `k · |Z ∖ B|` (for every `k`;
at G `k = 3`). -/
theorem whole_case_deficit_budget
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (whole : w.support ⊆ sparseDeclaredSupport data object w.first)
    (O' : OutsideContext (SupportAtom.boundary object w.support)) (k : Nat) :
    letI : FinEnum (glue (w.reading w.second) O').Vertex :=
      (glue (w.reading w.second) O').vertices
    1 ≤ (w.support \ sparseDeclaredSupport data object w.second).card ∧
    (w.support \ sparseDeclaredSupport data object w.second).card ≤
      (Finset.univ.filter fun v => (glue (w.reading w.second) O').degree v = 0).card ∧
    k * (w.support \ sparseDeclaredSupport data object w.second).card ≤
      Finset.univ.sum fun v => k - (glue (w.reading w.second) O').degree v := by
  classical
  letI : FinEnum (glue (w.reading w.second) O').Vertex :=
    (glue (w.reading w.second) O').vertices
  obtain ⟨⟨s0, hs0Z, hs0B⟩, each⟩ := whole_case_deficit_set avoid spec whole
  set S := w.support \ sparseDeclaredSupport data object w.second
  have memS : ∀ s, s ∈ S ↔ s ∈ w.support ∧ s ∉ sparseDeclaredSupport data object w.second :=
    fun s => Finset.mem_sdiff
  let f : {s // s ∈ S} → (glue (w.reading w.second) O').Vertex := fun s =>
    .inr (.inl ⟨s.1, ((memS s.1).1 s.2).1,
      (each s.1 ((memS s.1).1 s.2).1 ((memS s.1).1 s.2).2).1⟩)
  have finj : Function.Injective f := by
    intro x y h
    have h' := congrArg (fun g : (glue (w.reading w.second) O').Vertex => match g with
      | .inr (.inl i) => some i.1 | _ => none) h
    simp only [f, Option.some.injEq] at h'
    exact Subtype.ext h'
  have fdeg : ∀ s, (glue (w.reading w.second) O').degree (f s) = 0 := by
    intro s
    exact internal_isolated _ ((memS s.1).1 s.2).2 O'
  let T := S.attach.map ⟨f, finj⟩
  have Tcard : T.card = S.card := by simp [T]
  have Tsub : T ⊆ Finset.univ.filter fun v => (glue (w.reading w.second) O').degree v = 0 := by
    intro v hv
    simp only [T, Finset.mem_map, Finset.mem_attach, true_and, Function.Embedding.coeFn_mk] at hv
    obtain ⟨s, rfl⟩ := hv
    simp [fdeg s]
  refine ⟨Finset.card_pos.2 ⟨s0, (memS s0).2 ⟨hs0Z, hs0B⟩⟩, Tcard ▸ Finset.card_le_card Tsub, ?_⟩
  calc k * S.card = T.sum fun v => k - (glue (w.reading w.second) O').degree v := by
        simp [T, fdeg, Finset.sum_const, mul_comm]
    _ ≤ Finset.univ.sum fun v => k - (glue (w.reading w.second) O').degree v :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem droppedEdgeTightDeficit_holds (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DroppedEdgeTightDeficitStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, fun X _ a b inG notIn =>
    dropped_edge_tight_deficit tight w.support X a b inG notIn⟩

theorem notBothReadingsWhole_holds (residual : SparseTargetDefectResidualStatement data object) :
    NotBothReadingsWholeStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, not_both_whole spec⟩

/-- The whole-case facts, for the witness and for its swap. -/
theorem whole_case_facts (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec) :
    WholeOrientation w w.first w.second ∧ WholeDeficitNonempty w w.first w.second ∧
      WholeDeficitStructure w w.first w.second ∧ WholeNoBaseline w w.first w.second ∧
      WholeIsolatedCount w w.first w.second ∧ WholeDeficitSum w w.first w.second := by
  refine ⟨fun hA => larger_reading_positive spec
      (fun x hx => hA (second_subset_support spec hx)),
    fun hA => ?_, fun hA => (whole_case_deficit_set avoid spec hA).2,
    fun hA O' => ?_, fun hA O' => ?_, fun hA O' => ?_⟩
  · convert (whole_case_deficit_budget avoid spec hA (w.outside) data.threshold).1
  · obtain ⟨⟨s, hsZ, hsB⟩, each⟩ := whole_case_deficit_set avoid spec hA
    obtain ⟨-, -, i, -, zero⟩ := each s hsZ hsB
    exact not_minDegree_of_degree_zero (by omega) _ (zero O')
  · convert (whole_case_deficit_budget avoid spec hA O' data.threshold).2.1
  · convert (whole_case_deficit_budget avoid spec hA O' data.threshold).2.2

theorem firstWholeOrientation_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    FirstWholeOrientationStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid spec).1⟩

theorem firstWholeDeficitNonempty_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    FirstWholeDeficitNonemptyStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid spec).2.1⟩

theorem firstWholeDeficitStructure_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    FirstWholeDeficitStructureStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid spec).2.2.1⟩

theorem firstWholeDeficitSum_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    FirstWholeDeficitSumStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid spec).2.2.2.2.2⟩

theorem secondWholeOrientation_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SecondWholeOrientationStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid (swap_spec spec)).1⟩

theorem secondWholeDeficitNonempty_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SecondWholeDeficitNonemptyStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid (swap_spec spec)).2.1⟩

theorem secondWholeDeficitStructure_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SecondWholeDeficitStructureStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid (swap_spec spec)).2.2.1⟩

theorem secondWholeDeficitSum_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SecondWholeDeficitSumStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, (whole_case_facts three avoid (swap_spec spec)).2.2.2.2.2⟩

end Compression

/-! ## Deleting the deficit set; the keeps-all split (K3, continued) -/

section Deleted

open SupportAtom

/-- **The sub-case `KeepsAll Z A ∧ Z ⊄ A`, exactly.**  Every `z ∈ Z ∖ A`:
lies on `∂Z`; has a `Z`-neighbour, and all its `Z`-neighbours lie on `∂Z`;
has boundary degree `0` in BOTH readings (profile equality) while the whole
piece has boundary degree `> 0` there; and no `Z`-edge at `z` lies inside `B`. -/
theorem keepsAll_notWhole_first
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (keep : KeepsAll w.support (sparseDeclaredSupport data object w.first))
    {z : object.Vertex} (hzZ : z ∈ w.support)
    (hzA : z ∉ sparseDeclaredSupport data object w.first) :
    ∃ hz : z ∈ cutBoundary object w.support,
      (∃ v ∈ w.support, object.graph.Adj z v) ∧
      (∀ v ∈ w.support, object.graph.Adj z v → v ∈ cutBoundary object w.support) ∧
      (w.reading w.first).boundaryDegreeProfile ⟨z, hz⟩ = 0 ∧
      (w.reading w.second).boundaryDegreeProfile ⟨z, hz⟩ = 0 ∧
      0 < (piece object w.support).boundaryDegreeProfile ⟨z, hz⟩ ∧
      (∀ v ∈ w.support, object.graph.Adj z v →
        ¬ (z ∈ sparseDeclaredSupport data object w.second ∧
          v ∈ sparseDeclaredSupport data object w.second)) := by
  have D := (keepsAll_iff _ _).1 keep
  obtain ⟨t, ht, hzt⟩ := Finset.exists_mem_ne (support_two spec avoid) z
  obtain ⟨v0, hzv0, hv0⟩ := exists_adj_in_of_connectedOn object (support_connected spec)
    hzZ ht (Ne.symm hzt)
  have hz : z ∈ cutBoundary object w.support :=
    (D z v0 hzZ hv0 hzv0 (fun h => hzA h.1)).1
  have zeroA : (w.reading w.first).boundaryDegreeProfile ⟨z, hz⟩ = 0 := by
    change (w.reading w.first).pack.degree (.inl ⟨z, hz⟩) = 0
    apply degree_zero_of_no_adj
    intro y hy
    exact hzA (mem_of_retained_adj hy).1
  have zeroB : (w.reading w.second).boundaryDegreeProfile ⟨z, hz⟩ = 0 := by
    have e := congrFun spec.2.2.2.2.1 ⟨z, hz⟩
    rw [← e]; exact zeroA
  have posP : 0 < (piece object w.support).boundaryDegreeProfile ⟨z, hz⟩ := by
    change 0 < (piece object w.support).pack.degree (.inl ⟨z, hz⟩)
    refine degree_pos_of_adj _ (y := pieceEncode object w.support v0 hv0) ?_
    change object.graph.Adj z (pieceDecode object w.support _)
    rw [pieceDecode_encode]; exact hzv0
  have noB : ∀ v ∈ w.support, object.graph.Adj z v →
      ¬ (z ∈ sparseDeclaredSupport data object w.second ∧
        v ∈ sparseDeclaredSupport data object w.second) := by
    rintro v hv adj ⟨hzB, hvB⟩
    have : 0 < (w.reading w.second).pack.degree (.inl ⟨z, hz⟩) := by
      refine degree_pos_of_adj _ (y := pieceEncode object w.support v hv) ?_
      exact retained_adj_of (by rw [pieceDecode_encode]; exact adj) hzB
        (by rw [pieceDecode_encode]; exact hvB)
    have z2 : (w.reading w.second).pack.degree (.inl ⟨z, hz⟩) = 0 := zeroB
    omega
  exact ⟨hz, ⟨v0, hv0, hzv0⟩, fun v hv adj => (D z v hzZ hv adj (fun h => hzA h.1)).2,
    zeroA, zeroB, posP, noB⟩

/-- In that sub-case, neither reading is whole, and the first reading's
profile differs from the whole piece's (so `lem:replacement`'s signature
condition fails for it). -/
theorem keepsAll_notWhole_first_global
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (keep : KeepsAll w.support (sparseDeclaredSupport data object w.first))
    (notWhole : ¬ w.support ⊆ sparseDeclaredSupport data object w.first) :
    ¬ w.support ⊆ sparseDeclaredSupport data object w.second ∧
    (w.reading w.first).boundaryDegreeProfile ≠
      (piece object w.support).boundaryDegreeProfile ∧
    (w.reading w.second).boundaryDegreeProfile ≠
      (piece object w.support).boundaryDegreeProfile := by
  obtain ⟨z, hzZ, hzA⟩ := Finset.not_subset.1 notWhole
  obtain ⟨hz, ⟨v, hv, adj⟩, -, zA, zB, pos, noB⟩ :=
    keepsAll_notWhole_first avoid spec keep hzZ hzA
  refine ⟨fun sub => noB v hv adj ⟨sub hzZ, sub hv⟩, fun h => ?_, fun h => ?_⟩
  · have := congrFun h ⟨z, hz⟩; omega
  · have := congrFun h ⟨z, hz⟩; omega


/-- The whole-case deletion facts, at one witness with its clauses. -/
theorem deleted_core (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (whole : w.support ⊆ sparseDeclaredSupport data object w.first) :
    ((object.induce (wholeKeptSet w)).LexicographicallySmaller object ∧
      ¬ HasCycleWithLength data.LengthOK (object.induce (wholeKeptSet w)) ∧
      ¬ MinimumDegreeAtLeast 3 (object.induce (wholeKeptSet w))) ∧
    (∀ v (hv : v ∈ wholeKeptSet w), (object.induce (wholeKeptSet w)).degree ⟨v, hv⟩ =
      object.localDegree (wholeKeptSet w) v) ∧
    (∀ v, object.degree v = object.localDegree (wholeKeptSet w) v +
      object.localDegree (wholeDeletedSet w) v) ∧
    (∀ v, 3 - object.localDegree (wholeKeptSet w) v =
      object.localDegree (wholeDeletedSet w) v - (object.degree v - 3)) ∧
    (∃ v ∈ wholeKeptSet w, object.localDegree (wholeKeptSet w) v < 3) ∧
    (∀ v ∈ wholeKeptSet w, object.localDegree (wholeKeptSet w) v < 3 →
      v ∈ w.support ∧ v ∈ sparseDeclaredSupport data object w.second ∧
      v ∉ SupportAtom.cutBoundary object w.support ∧
      1 ≤ object.localDegree (wholeDeletedSet w) v) ∧
    (1 ≤ (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) ∧
      (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) =
        (wholeKeptSet w).sum
          (fun v => object.localDegree (wholeDeletedSet w) v - (object.degree v - 3)) ∧
      (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) ≤
        (wholeKeptSet w).sum (fun v => object.localDegree (wholeDeletedSet w) v) ∧
      ((∀ v ∈ wholeKeptSet w, 0 < object.localDegree (wholeDeletedSet w) v →
          object.degree v = 3) →
        (wholeKeptSet w).sum (fun v => 3 - object.localDegree (wholeKeptSet w) v) =
          (wholeKeptSet w).sum (fun v => object.localDegree (wholeDeletedSet w) v))) ∧
    (∀ s ∈ wholeDeletedSet w, ∀ v, object.graph.Adj s v →
      object.degree s = 3 ∨ object.degree v = 3) ∧
    (∀ x y : (object.induce (wholeKeptSet w)).Vertex, x ≠ y →
      MinimumDegreeAtLeast 3 (addEdgeObj (object.induce (wholeKeptSet w)) x y) →
      ∃ p : (object.induce (wholeKeptSet w)).graph.Walk y x, p.IsPath ∧
        data.LengthOK (p.length + 1)) ∧
    (∀ F : SimpleGraph (object.induce (wholeKeptSet w)).Vertex,
      MinimumDegreeAtLeast 3 (addEdgesObj (object.induce (wholeKeptSet w)) F) →
      ∃ c : CycleCertificate (addEdgesObj (object.induce (wholeKeptSet w)) F) data.LengthOK,
        ∃ e ∈ c.walk.edges, e ∈ F.edgeSet ∧
          e ∉ (object.induce (wholeKeptSet w)).graph.edgeSet) := by
  classical
  set S := wholeDeletedSet w with hS
  set T := object.vertexFinset \ S with hTdef
  have memS : ∀ x, x ∈ S ↔ x ∈ w.support ∧ x ∉ sparseDeclaredSupport data object w.second := by
    intro x; rw [hS, Finset.mem_sdiff]
  obtain ⟨⟨s0, hs0Z, hs0B⟩, each⟩ := whole_case_deficit_set avoid spec whole
  have Sne : S.Nonempty := ⟨s0, (memS s0).2 ⟨hs0Z, hs0B⟩⟩
  have base3 : ∀ v, 3 ≤ object.degree v := fun v => by
    have := object.minDegree_le_degree v
    have b : data.threshold ≤ object.minDegree := baseline
    omega
  have noProper3 : ∀ sub : ProperSubgraph object, ¬ MinimumDegreeAtLeast 3 sub.value := by
    intro sub; rw [← three]; exact noProper.1 sub
  have Tlt := deleted_card_lt object Sne
  have smallerK : (object.induce T).LexicographicallySmaller object :=
    (ProperSubgraph.ofInducedSupport object T Tlt).decreases
  have freeK : ¬ HasCycleWithLength data.LengthOK (object.induce T) :=
    fun c => avoid (FiniteObject.hasCycleWithLength_of_induce object _ c)
  -- a vertex outside S: any boundary vertex
  have two := support_two spec avoid
  obtain ⟨b0, hb0⟩ : (SupportAtom.cutBoundary object w.support).Nonempty := by
    have sep := spec.2.2.2.2.2.2
    unfold Graph.canonicalCoordinateResponse at sep
    change ¬ (HasCycleWithLength _ (glue (w.reading w.first) w.outside) ↔
      HasCycleWithLength _ (glue (w.reading w.second) w.outside)) at sep
    have := two_le_cutBoundary_of_geometryAt avoid (boundTargetDefectGeometryAt_of_separated sep avoid)
    exact Finset.card_pos.1 (lt_of_lt_of_le (by norm_num) this)
  have hb0S : b0 ∉ S := fun h => by
    obtain ⟨hZ, hB⟩ := (memS b0).1 h
    exact (each b0 hZ hB).1 hb0
  have split := degree_split object S
  have defEq := fun v => deleted_deficit_eq object S v (base3 v)
  have exists_def := deleted_exists_deficient object noProper3 Sne hb0S
  have tot := deleted_total_deficit object S base3
  refine ⟨⟨smallerK, freeK, ?_⟩, fun v hv => FiniteObject.degree_induce_eq_localDegree object T ⟨v, hv⟩,
    split, defEq, exists_def, ?_, ⟨?_, tot.1, tot.2.1, tot.2.2⟩, ?_, ?_, ?_⟩
  · exact noProper3 (ProperSubgraph.ofInducedSupport object T Tlt)
  · intro v hvT hlt
    have d1 := (deleted_deficit_bounds object S v (base3 v)).2.2 hlt
    have d1' : 0 < object.localDegree S v := d1
    unfold FiniteObject.localDegree at d1'
    obtain ⟨s, hs⟩ := Finset.card_pos.1 d1'
    have hs' := (@Finset.mem_filter _ (fun o => object.graph.Adj v o) (fun o => object.decideAdj v o) S s).1 hs
    obtain ⟨hsZ, hsB⟩ := (memS s).1 hs'.1
    obtain ⟨hsbd, noBd, -⟩ := each s hsZ hsB
    have hvZ : v ∈ w.support := by
      by_contra hvZ
      exact hsbd ((SupportAtom.mem_cutBoundary_iff object w.support s).2
        ⟨hsZ, v, hs'.2.symm, hvZ⟩)
    have hvB : v ∈ sparseDeclaredSupport data object w.second := by
      by_contra hvB
      exact (Finset.mem_sdiff.1 hvT).2 ((memS v).2 ⟨hvZ, hvB⟩)
    exact ⟨hvZ, hvB, fun hvbd => noBd v hvbd hs'.2.symm, d1⟩
  · obtain ⟨v, hvT, hlt⟩ := exists_def
    have hpos : 1 ≤ 3 - object.localDegree T v := Nat.sub_pos_of_lt hlt
    exact le_trans hpos (Finset.single_le_sum (f := fun v => 3 - object.localDegree T v)
      (fun _ _ => Nat.zero_le _) hvT)
  · intro s _ v adj
    have := tight ⟨(s, v), adj⟩
    rw [three] at this
    exact this
  · intro x y hxy base
    have smaller : (addEdgeObj (object.induce T) x y).LexicographicallySmaller object :=
      FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
        change (object.induce T).vertexCount < object.vertexCount
        rw [FiniteObject.vertexCount_induce]; exact Tlt)
    have cyc := minimal _ smaller (by rw [three]; exact base)
    exact addEdge_accepted_path (object.induce T) hxy freeK cyc
  · intro F base
    have smaller : (addEdgesObj (object.induce T) F).LexicographicallySmaller object :=
      FiniteObject.lexicographicallySmaller_of_vertexCount_lt (by
        change (object.induce T).vertexCount < object.vertexCount
        rw [FiniteObject.vertexCount_induce]; exact Tlt)
    obtain ⟨c⟩ := minimal _ smaller (by rw [three]; exact base)
    exact ⟨c, addEdges_cycle_uses_new (object.induce T) F freeK c⟩


theorem deletedSupportReduction_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DeletedSupportReductionStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun whole => (deleted_core three avoid minimal baseline noProper tight spec whole).1, fun whole => (deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).1⟩

theorem deletedSupportDeficientVertex_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DeletedSupportDeficientVertexStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun whole => ⟨(deleted_core three avoid minimal baseline noProper tight spec whole).2.2.2.2.1, (deleted_core three avoid minimal baseline noProper tight spec whole).2.2.2.2.2.1⟩, fun whole => ⟨(deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).2.2.2.2.1, (deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).2.2.2.2.2.1⟩⟩

theorem deletedSupportDeficitSums_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DeletedSupportDeficitSumsStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun whole => (deleted_core three avoid minimal baseline noProper tight spec whole).2.2.2.2.2.2.1, fun whole => (deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).2.2.2.2.2.2.1⟩

theorem deletedSupportEdgeRestoration_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DeletedSupportEdgeRestorationStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun whole => (deleted_core three avoid minimal baseline noProper tight spec whole).2.2.2.2.2.2.2.2.1, fun whole => (deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).2.2.2.2.2.2.2.2.1⟩

theorem deletedSupportEdgeSetRestoration_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    DeletedSupportEdgeSetRestorationStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun whole => (deleted_core three avoid minimal baseline noProper tight spec whole).2.2.2.2.2.2.2.2.2, fun whole => (deleted_core three avoid minimal baseline noProper tight (swap_spec spec) whole).2.2.2.2.2.2.2.2.2⟩

theorem firstKeepsAllNotWhole_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    FirstKeepsAllNotWholeStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun keep nw => keepsAll_notWhole_first_global avoid spec keep nw⟩

theorem secondKeepsAllNotWhole_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    SecondKeepsAllNotWholeStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun keep nw => keepsAll_notWhole_first_global avoid (swap_spec spec) keep nw⟩

end Deleted

section BoundaryPositive

open Classical

theorem boundary_two_in_positive (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (two : (SupportAtom.cutBoundary object w.support).card = 2) :
    SupportAtom.cutBoundary object w.support ⊆ sparseDeclaredSupport data object w.first ∨
      SupportAtom.cutBoundary object w.support ⊆ sparseDeclaredSupport data object w.second := by
  have key : ∀ X : Finset object.Vertex,
      2 ≤ (SupportAtom.cutBoundary object w.support ∩ X).card →
      SupportAtom.cutBoundary object w.support ⊆ X := by
    intro X h
    have eq : SupportAtom.cutBoundary object w.support ∩ X =
        SupportAtom.cutBoundary object w.support :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    rw [← eq]
    exact Finset.inter_subset_right
  rcases positive_support_two_boundary avoid spec with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

end BoundaryPositive

/-! ## The combination: pair arm, two-boundary arm (i), Steiner support,
whole-case counts, high-degree range -/

section Combination

open Classical

end Combination

/-! ## The combination: pair arm, two-boundary arm (i), Steiner support,
whole-case counts, high-degree range -/

section Combination

open Classical

theorem highDegreePositive_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object) :
    HighDegreePositiveStatement data object := by
  have base : ∀ v, 3 ≤ object.degree v := fun v =>
    three ▸ baseline.trans (object.minDegree_le_degree v)
  have tight3 : ∀ d : object.graph.Dart,
      object.degree d.fst = 3 ∨ object.degree d.snd = 3 := three ▸ tight
  have above' : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := above
  rw [three] at above'
  have hg := SparseOrderArithmetic.high_generic object base tight3 (by omega)
  unfold HighDegreePositiveStatement sparseHighDegreeCount
  rw [three]
  exact hg.1

theorem highDegreeSurplusCapacity_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object) :
    HighDegreeSurplusCapacityStatement data object := by
  have base : ∀ v, 3 ≤ object.degree v := fun v =>
    three ▸ baseline.trans (object.minDegree_le_degree v)
  have tight3 : ∀ d : object.graph.Dart,
      object.degree d.fst = 3 ∨ object.degree d.snd = 3 := three ▸ tight
  have above' : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := above
  rw [three] at above'
  have hg := SparseOrderArithmetic.high_generic object base tight3 (by omega)
  unfold HighDegreeSurplusCapacityStatement sparseHighDegreeCount
  rw [three]
  exact hg.2

/-- `Z = ∂Z = {a, b}` is impossible at a witness. -/
theorem pairArm_false {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    {a b : object.Vertex}
    (hB : SupportAtom.cutBoundary object w.support = {a, b})
    (hZ : w.support = {a, b}) : False := by
  have prof := spec.2.2.2.2.1
  have le1 := pair_le hZ hB prof
  have le2 := pair_le hZ hB prof.symm
  exact separated_of_spec spec ⟨glue_mono_of_le le1 w.outside, glue_mono_of_le le2 w.outside⟩

theorem pairArmExcluded_holds (residual : SparseTargetDefectResidualStatement data object) :
    PairArmExcludedStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun ⟨a, b, hB, hZ⟩ => pairArm_false spec hB hZ⟩

theorem spectrumArmOne_of_two
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec)
    (two : (SupportAtom.cutBoundary object w.support).card = 2) : w.SpectrumArmOne := by
  obtain ⟨P, hP, N, hN, pos, neg⟩ := positive_negative_of_spec spec
  rcases spectrum_split pos neg (retainedPiece_avoids avoid w.support P) with
    ⟨a, b, hab, π, hπ, σ, hσ, lab, ok, -, rest⟩ | many
  · refine ⟨P, hP, N, hN, pos, neg, a, b, hab, π, hπ, σ, hσ, lab,
      (Core.DyadicLength.powerOfTwoLength_iff _).mp ((lengthLaw _).mp ok),
      fun π' hπ' => ⟨(rest π' hπ').1, fun j hj eq => ?_⟩⟩
    by_cases hn : 1 < π'.length ∨ 1 < σ.length
    · exact (rest π' hπ').2 hn
        ((lengthLaw _).mpr ((Core.DyadicLength.powerOfTwoLength_iff _).mpr ⟨j, hj, eq⟩))
    · push Not at hn
      have : 4 ≤ 2 ^ j := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
  · exact (armII_two_false two pos many).elim

theorem twoBoundaryForcesArmOne_holds
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundaryForcesArmOneStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, fun two => ⟨spectrumArmOne_of_two lengthLaw avoid spec two, ?_⟩⟩
  obtain ⟨a, b, ab, hab, split⟩ := two_boundary_split object w.support two
  rcases split with pair | int
  · exact (pairArm_false spec hab pair).elim
  refine ⟨a, b, ab, hab, ?_, int⟩
  rw [← hab]
  exact boundary_two_in_positive avoid spec two

theorem armOne_path {w : SparseTargetDefectWitness data object} (h : w.SpectrumArmOne) :
    ∃ a b : object.Vertex, a ≠ b ∧
      a ∈ SupportAtom.cutBoundary object w.support ∧
      b ∈ SupportAtom.cutBoundary object w.support ∧
      ∃ p : object.graph.Walk a b, p.IsPath ∧
        (∀ v ∈ p.support, v ∈ w.support) ∧ p.length + 1 ≤ w.support.card ∧
        ∃ s k, 2 ≤ k ∧ p.length + s = 2 ^ k ∧ 1 ≤ s ∧ (p.length + s) % 4 = 0 := by
  obtain ⟨P, -, N, -, -, -, a, b, ab, π, hπ, σ, hσ, -, ⟨k, hk, hlen⟩, -⟩ := h
  have finj := readingHom_injective (object := object) w.support P
  let p : object.graph.Walk a.1 b.1 := π.map (readingHom w.support P)
  have hp : p.IsPath := SimpleGraph.Walk.map_isPath_of_injective finj hπ
  have plen : p.length = π.length := SimpleGraph.Walk.length_map _ _
  have pZ : ∀ v ∈ p.support, v ∈ w.support := by
    intro v hv
    have hsupp : p.support = π.support.map (readingHom w.support P) :=
      SimpleGraph.Walk.support_map _ _
    rw [hsupp] at hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hv
    rcases x with x | x
    · exact ((SupportAtom.mem_cutBoundary_iff _ _ x.1).1 x.2).1
    · exact x.2.1
  refine ⟨a.1, b.1, fun e => ab (Subtype.ext e), a.2, b.2, p, hp, pZ, ?_, σ.length, k, hk,
    by rw [plen]; exact hlen, ?_, ?_⟩
  · have nd := hp.support_nodup
    have sub : p.support.toFinset ⊆ w.support := fun v hv => pZ v (List.mem_toFinset.1 hv)
    have := Finset.card_le_card sub
    rw [List.toFinset_card_of_nodup nd, SimpleGraph.Walk.length_support] at this
    exact this
  · by_contra h0
    push Not at h0
    have : σ.length = 0 := by omega
    have := SimpleGraph.Walk.eq_of_length_eq_zero this
    exact ab (Sum.inl.inj this).symm
  · rw [plen, hlen]
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add]; simp [Nat.mul_mod_right]

theorem armOneForcedPath_holds (residual : SparseTargetDefectResidualStatement data object) :
    ArmOneForcedPathStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, armOne_path⟩

theorem twoBoundaryForcedPathCross_holds (three : data.threshold = 3)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (baseline : MinDegreeBaselineStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (residual : SparseTargetDefectResidualStatement data object) :
    TwoBoundaryForcedPathCrossStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, fun two => ?_⟩
  obtain ⟨a', b', ab', hab', interior⟩ : ∃ a b, a ≠ b ∧
      SupportAtom.cutBoundary object w.support = {a, b} ∧
      ∃ i ∈ w.support, i ∉ SupportAtom.cutBoundary object w.support := by
    obtain ⟨a, b, ab, hab, split⟩ := two_boundary_split object w.support two
    rcases split with pair | int
    · exact (pairArm_false spec hab pair).elim
    exact ⟨a, b, ab, hab, int.1⟩
  obtain ⟨a, b, ab, ha, hb, p, hp, pZ, -, s, k, hk, hlen, hs, -⟩ :=
    armOne_path (spectrumArmOne_of_two lengthLaw avoid spec two)
  have hab : SupportAtom.cutBoundary object w.support = {a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    · rw [hab', Finset.card_pair ab', Finset.card_pair ab]
  have noSum : ∀ q : object.graph.Walk b a, q.IsPath →
      (∀ v ∈ q.support, v ∈ outsideSide object w.support a b) →
      (1 < p.length ∨ 1 < q.length) → ¬ data.LengthOK (p.length + q.length) := by
    intro q hq qT long
    refine no_target_two_sides object avoid w.support
      (outsideSide object w.support a b) ?_ p hp pZ q hq qT long
    intro v vZ vT
    simp only [outsideSide, Finset.mem_filter] at vT
    rcases vT.2 with h | h | h
    · exact (h vZ).elim
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨a, b, ab, hab, p, hp, pZ, ⟨s, k, hk, hlen, hs⟩, noSum, ?_⟩
  intro nadj da db
  have iNot : ∃ i, i ∉ outsideSide object w.support a b := by
    obtain ⟨i, hi, hib⟩ := interior
    refine ⟨i, ?_⟩
    rw [hab] at hib
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hib
    simp [outsideSide, hi, hib.1, hib.2]
  obtain ⟨i, hi⟩ := iNot
  have lt : (outsideSide object w.support a b).card < object.vertexCount := by
    rw [← Graph.FiniteObject.card_vertexFinset]
    exact Finset.card_lt_card
      ⟨fun v _ => object.mem_vertexFinset v,
        fun h => hi (h (object.mem_vertexFinset i))⟩
  obtain ⟨q, hq, qT, ok⟩ := side_closure_path object (baseline_three three baseline) avoid
    (minimal_three three minimal) _ (by simp [outsideSide]) (by simp [outsideSide]) ab nadj
    lt (outsideSide_closed object w.support hab) da db
  refine ⟨q.reverse, hq.reverse, by rw [SimpleGraph.Walk.length_reverse]; exact ok, ?_⟩
  apply noSum q.reverse hq.reverse
  · intro v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact qT v hv
  · right
    have : 3 ≤ q.length + 1 := by
      obtain ⟨e, he, heq⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).1 ((lengthLaw _).1 ok)
      have : 4 ≤ 2 ^ e := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
      omega
    rw [SimpleGraph.Walk.length_reverse]
    omega

theorem supportSteinerMinimal_holds (residual : SparseTargetDefectResidualStatement data object) :
    SupportSteinerMinimalStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, fun Y hY conn => CanonicalSupport.select?_card_le spec.2.2.2.1
    (CanonicalSupport.mem_candidates_iff.2 ⟨fun v hv => hY v (Finset.mem_union.1 hv), conn⟩)⟩

theorem steinerVerticesCut_holds (residual : SparseTargetDefectResidualStatement data object) :
    SteinerVerticesCutStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  refine ⟨w, canon, fun v hv hA hB conn => ?_⟩
  have := CanonicalSupport.select?_card_le spec.2.2.2.1
    (CanonicalSupport.mem_candidates_iff.2 ⟨fun x hx => by
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl; rcases Finset.mem_union.1 hx with h | h
        · exact hA h
        · exact hB h
      · rcases Finset.mem_union.1 hx with h | h
        · exact first_subset_support spec h
        · exact second_subset_support spec h, conn⟩)
  have := Finset.card_erase_of_mem hv
  have : 0 < w.support.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

theorem wholeSupportEqual_holds (residual : SparseTargetDefectResidualStatement data object) :
    WholeSupportEqualStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon,
    fun whole => ⟨Finset.Subset.antisymm whole (first_subset_support spec),
      fun _ h => whole (second_subset_support spec h)⟩,
    fun whole => ⟨Finset.Subset.antisymm whole (second_subset_support spec),
      fun _ h => whole (first_subset_support spec h)⟩⟩

theorem wholeDeficitBoundaryCount_at (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    {w : SparseTargetDefectWitness data object} (spec : w.Spec) :
    WholeDeficitBoundaryCountAt w := by
  intro whole
  obtain ⟨-, each⟩ := whole_case_deficit_set avoid spec whole
  have disj : Disjoint (wholeDeletedSet w) (SupportAtom.cutBoundary object w.support) := by
    rw [Finset.disjoint_left]
    intro s hs hb
    obtain ⟨hsZ, hsB⟩ := Finset.mem_sdiff.1 hs
    exact (each s hsZ hsB).1 hb
  have sub : wholeDeletedSet w ∪ SupportAtom.cutBoundary object w.support ⊆ w.support := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact (Finset.mem_sdiff.1 h).1
    · exact ((SupportAtom.mem_cutBoundary_iff _ _ x).1 h).1
  have := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint disj] at this
  exact this

theorem wholeDeficitBoundaryCount_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WholeDeficitBoundaryCountStatement data object := by
  obtain ⟨w, canon, spec⟩ := residual
  exact ⟨w, canon, wholeDeficitBoundaryCount_at avoid spec,
    wholeDeficitBoundaryCount_at avoid (swap_spec spec)⟩

theorem wholeCutEdgeSurplusBound_at (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (w : SparseTargetDefectWitness data object) : WholeCutEdgeSurplusBoundAt w := by
  intro _
  have base : ∀ v, 3 ≤ object.degree v := fun v =>
    three ▸ baseline.trans (object.minDegree_le_degree v)
  set S := wholeDeletedSet w
  set T := wholeKeptSet w
  have step : ∀ v ∈ T, object.localDegree S v ≤
      (3 - object.localDegree T v) + (object.degree v - 3) := by
    intro v _
    have := deleted_deficit_eq object S v (base v)
    change object.localDegree S v ≤
      (3 - object.localDegree (object.vertexFinset \ S) v) + (object.degree v - 3)
    omega
  rw [three]
  calc T.sum (fun v => object.localDegree S v)
      ≤ T.sum (fun v => (3 - object.localDegree T v) + (object.degree v - 3)) :=
        Finset.sum_le_sum step
    _ = T.sum (fun v => 3 - object.localDegree T v) + T.sum (fun v => object.degree v - 3) :=
        Finset.sum_add_distrib
    _ ≤ T.sum (fun v => 3 - object.localDegree T v) + object.degreeSurplus 3 :=
        Nat.add_le_add_left (SparseOrderArithmetic.sum_sub_le_sigma object base T) _

theorem wholeCutEdgeSurplusBound_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (residual : SparseTargetDefectResidualStatement data object) :
    WholeCutEdgeSurplusBoundStatement data object := by
  obtain ⟨w, canon, -⟩ := residual
  exact ⟨w, canon, wholeCutEdgeSurplusBound_at three baseline w,
    wholeCutEdgeSurplusBound_at three baseline w.swap⟩

end Combination

/-! ## The canonical capacity presentation of G (K6 at the canonical objects) -/

section CanonicalCapacityContracts

open Hypostructure.Graph.SameTokenBlockerRoles

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}

/-- `C(σ,2)·2 = σ(σ−1)` over `ℤ`. -/
theorem choose_two_mul_two_int (σ : Nat) (hσ : 1 ≤ σ) :
    ((σ.choose 2 : ℕ) : ℤ) * 2 = (σ : ℤ) * ((σ : ℤ) - 1) := by
  have h := Nat.choose_two_right σ
  have hd : 2 ∣ σ * (σ - 1) := (Nat.even_mul_pred_self σ).two_dvd
  have e : σ.choose 2 * 2 = σ * (σ - 1) := by rw [h]; exact Nat.div_mul_cancel hd
  have := congrArg (fun x : ℕ => (x : ℤ)) e
  push_cast [Nat.cast_sub hσ] at this
  linarith

/-- `C_sp` at the cubic baseline: `C_sp = 2 + 20·M₀ + 2·S`. -/
theorem spineScale_at_three (three : data.threshold = 3) :
    data.spineScale = 2 + 20 * homogeneousTokenCap data.routingLabelBound +
      2 * data.surplusScale := by
  simp only [Parameters.spineScale, registeredSpineScale, registeredHomogeneousCap, three]
  ring

/-- `1 ≤ S` from the registered deficit safety. -/
theorem one_le_surplusScale
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale) :
    1 ≤ data.surplusScale := by
  have : 0 < Graph.baselineDeficitCoefficient data.threshold := by
    unfold Graph.baselineDeficitCoefficient; positivity
  omega

/-- The pair-deficit coefficient is positive at the cubic baseline:
`K = C² − 3C − 2M₀C − 2S − 16M₀ > 0` when `C = 2 + 20M₀ + 2S`, `S ≥ 1`. -/
theorem pairDeficitCoefficient_pos (three : data.threshold = 3)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale) :
    0 < pairDeficitCoefficient data := by
  have Ceq := spineScale_at_three (data := data) three
  have S1 := one_le_surplusScale deficitSafety
  unfold pairDeficitCoefficient
  rw [Ceq]
  push_cast
  nlinarith [Int.natCast_nonneg (homogeneousTokenCap data.routingLabelBound),
    (show (1 : ℤ) ≤ data.surplusScale by exact_mod_cast S1)]

/-- `ActiveSurplusDemands` at G from the `[20a]` facts (`[127]`, `[128]`,
`[125]`), with no survivor fact. -/
theorem active_of_selection (three : data.threshold = 3)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object) :
    Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold := by
  have witness : SingleOpenPortSuppressionWitnessStatement data object :=
    Graph.Contracts.TypeB.singleOpenPortSuppressionWitness baseline selection.1
      selection.2.sizeMinimal
  exact Graph.Contracts.SurplusPair.activeSurplusDemands_of_activation three
    (Graph.Contracts.SurplusPair.activeSurplusFamily_of_slackIndependent baseline slack)
    (Graph.Contracts.SurplusPair.sparsePortActivation_of_selection baseline selection witness)

theorem canonicalCapacity_eq_explicit_at (three : data.threshold = 3)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object) :
    canonicalCapacity data object =
      some (explicitCapacity (active_of_selection three selection baseline slack)
        selection.1 noProper.2) := by
  have above' : data.surplusThreshold object.vertexCount <
      object.degreeSurplus data.threshold := above
  have pos : 0 < object.degreeSurplus data.threshold := lt_of_le_of_lt (Nat.zero_le _) above'
  have env := object.edgeCount_add_two_le (threshold := data.threshold) (by omega) noProper.1
    tight (object.edgeCount_pos_of_degreeSurplus_pos pos)
  exact canonicalCapacity_eq_explicit _ _ _ baseline (by omega) env joinSlack

theorem canonicalCapacityExplicit_holds (three : data.threshold = 3)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object) :
    CanonicalCapacityExplicitStatement data object :=
  ⟨_, _, _, canonicalCapacity_eq_explicit_at three joinSlack selection baseline slack noProper
    tight above⟩

theorem primitiveCarrierCount_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object) :
    PrimitiveCarrierCountStatement data object := by
  have bdeg : ∀ v : object.Vertex, data.threshold ≤ object.degree v :=
    fun v => le_trans baseline (object.minDegree_le_degree v)
  have carrier := object.card_primitiveCarrier (threshold := data.threshold) bdeg
  have slackEq : 2 * object.edgeCount = data.threshold * object.vertexCount +
      object.degreeSurplus data.threshold :=
    Graph.Contracts.SurplusPair.sparseSlackSurplus_of_baseline baseline
  unfold PrimitiveCarrierCountStatement
  have h3 : data.threshold * object.vertexCount = 3 * object.vertexCount := by rw [three]
  omega

/-- **Every quantity at the canonical object ledger of the canonical
presentation**, at the cubic baseline, under the ledger's own facts. -/
theorem canonicalLedger_quantities (three : data.threshold = 3)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
    (capacity : SurplusCapacity data object)
    (spec : CapacityLedgerSpec data object capacity)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object) :
    ∃ L, canonicalObjectLedgerAt data object capacity = some L ∧
      L.presented.tokens = capacity.tokens ∧
      capacity.tokens.card + 2 * (data.windowOrder - 1) *
          (canonicalWindowPacking data object).card =
        4 * object.vertexCount + 3 * object.degreeSurplus data.threshold +
          3 * (data.windowOrder * (canonicalWindowPacking data object).card) ∧
      capacity.tokens.card ≤ 8 * object.vertexCount + object.degreeSurplus data.threshold ∧
      L.presented.blocked.card + freeCount data object capacity =
        (object.degreeSurplus data.threshold).choose 2 ∧
      L.presented.blocked.card = ∑ t ∈ L.presented.tokens, L.presented.load t ∧
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
              (capacity.tokens.card : ℤ)) ≤
        2 * ((freeCount data object capacity : ℤ) - (certificationBudget data object : ℤ)) +
          2 * ((L.presented.blocked.card : ℤ) -
            (homogeneousTokenCap data.routingLabelBound : ℤ) * capacity.tokens.card) ∧
      (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
          2 * (homogeneousTokenCap data.routingLabelBound : ℤ) *
            ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) : ℤ) ≤
        2 * (((object.degreeSurplus data.threshold).choose 2 : ℕ) -
          (certificationBudget data object : ℤ)) ∧
      ((canonicalCertifiedCapacityDataAt data object capacity).isSome ↔
        freeCount data object capacity ≤ certificationBudget data object) := by
  obtain ⟨h1, -, slackEq, σle, sq⟩ := budget_core three baseline tight noProper above
  set n := object.vertexCount
  set σ := object.degreeSurplus data.threshold
  set C := data.spineScale
  set S := data.surplusScale
  set M₀ := homogeneousTokenCap data.routingLabelBound
  set cs := Core.ceilSqrt n
  have Ceq : C = 2 + 20 * M₀ + 2 * S := spineScale_at_three three
  have S1 : 1 ≤ S := one_le_surplusScale deficitSafety
  have hcs : C + 1 ≤ cs := (SparseOrderArithmetic.sqrt_chain _ _ _ _ h1 σle sq).1
  have hlog : Nat.log2 n + 1 ≤ cs :=
    SparseOrderArithmetic.log2_succ_le_of_le_sq (by omega) sq
  have bdeg : ∀ v : object.Vertex, data.threshold ≤ object.degree v :=
    fun v => le_trans baseline (object.minDegree_le_degree v)
  obtain ⟨-, carrierEq, -, concrete, -, packEq⟩ := spec
  have sizePos : 0 < n := by omega
  obtain ⟨v0, -⟩ : object.vertexFinset.Nonempty :=
    Finset.card_pos.mp (by rw [object.card_vertexFinset]; exact sizePos)
  have inputs : ObjectLedgerInputs data object capacity :=
    ⟨object.card_portPairSchedule bdeg,
      object.capacityTokens_nonempty data.threshold capacity.packing v0, concrete.2.1⟩
  obtain ⟨L, hL, hLE⟩ := canonicalObjectLedgerAt_spec data object capacity inputs
  have tokId := concrete.1
  have e : capacity.tokens = object.capacityTokens data.threshold capacity.packing := rfl
  rw [carrierEq, packEq] at tokId
  have hmul : data.threshold * (data.windowOrder * (canonicalWindowPacking data object).card) =
      3 * (data.windowOrder * (canonicalWindowPacking data object).card) := by rw [three]
  have tokEq : capacity.tokens.card + 2 * (data.windowOrder - 1) *
      (canonicalWindowPacking data object).card =
      4 * n + 3 * σ + 3 * (data.windowOrder * (canonicalWindowPacking data object).card) := by
    rw [e, packEq]
    have : 2 * object.edgeCount = 3 * n + σ := slackEq
    omega
  have supply : object.capacityTokenSupply data.threshold = 8 * n := by
    simp only [FiniteObject.capacityTokenSupply, FiniteObject.primitiveCarrierSupply, three]
    ring
  have supplyT : capacity.tokens.card ≤ 8 * n + σ := by
    have := concrete.2.1
    rw [supply] at this
    exact this
  have partition := L.presented.blocked_card_add_free_card
  have freeEq : L.presented.free.card = freeCount data object capacity := ledger_free_card L
  rw [freeEq] at partition
  have schedCard := object.card_portPairSchedule bdeg
  have key : 1 + 2 * cs + 2 * M₀ ≤ C * cs := by
    rw [Ceq]; nlinarith
  have core := SparseOrderArithmetic.pairDeficit_lower (σ : ℤ) (cs : ℤ) (n : ℤ)
    ((S * n + (Nat.log2 n + 1) * σ : ℕ) : ℤ) ((8 * n + σ : ℕ) : ℤ) (M₀ : ℤ) (S : ℤ) (C : ℤ)
    (Nat.log2 n : ℤ) (by exact_mod_cast (by omega : 1 ≤ cs)) (by positivity) (by positivity)
    (by positivity) (by exact_mod_cast h1) (by positivity) (by exact_mod_cast sq)
    (by exact_mod_cast hlog) (by positivity) (by push_cast; linarith) (by push_cast; linarith)
    (by exact_mod_cast key)
  have c2 := choose_two_mul_two_int σ (by omega)
  have partZ : (L.presented.blocked.card : ℤ) + (freeCount data object capacity : ℤ) =
      ((σ.choose 2 : ℕ) : ℤ) := by exact_mod_cast partition
  have hK : (cs : ℤ) ^ 2 * pairDeficitCoefficient data ≤ (σ : ℤ) * ((σ : ℤ) - 1) -
      2 * (((S * n + (Nat.log2 n + 1) * σ : ℕ)) : ℤ) -
      2 * (M₀ : ℤ) * (((8 * n + σ : ℕ)) : ℤ) := core
  refine ⟨L, hL, L.tokens_eq, tokEq, supplyT, partition,
    L.presented.blocked_card_eq_sum_load, ?_, ?_,
    canonicalCertified_isSome_iff inputs sizePos S1⟩
  · unfold certificationBudget; push_cast at hK ⊢; linarith
  · unfold certificationBudget; push_cast at hK ⊢; linarith

section AtG

variable (three : data.threshold = 3)
  (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
  (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
  (selection : SelectionStatement BranchState Presentation presentation data object)
  (baseline : MinDegreeBaselineStatement data object)
  (slack : SlackIndependentStatement data object)
  (noProper : NoProperBaselineStatement data object)
  (tight : TightEndpointStatement data object)
  (above : SurplusAboveStatement data object)

include three joinSlack deficitSafety selection baseline slack noProper tight above

theorem canonicalLedger_exists :
    ∃ c, canonicalCapacity data object = some c ∧ CapacityLedgerSpec data object c := by
  have hc := canonicalCapacity_eq_explicit_at three joinSlack selection baseline slack
    noProper tight above
  exact ⟨_, hc, canonicalCapacity_spec_of_eq_some data object hc⟩

theorem canonicalTokenCount_holds : CanonicalTokenCountStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, -, tok, -⟩ := canonicalLedger_quantities three deficitSafety c spec baseline
    tight noProper above
  exact ⟨c, L, hc, hL, tok⟩

theorem canonicalBlockedFreePartition_holds :
    CanonicalBlockedFreePartitionStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, -, -, -, part, -⟩ := canonicalLedger_quantities three deficitSafety c spec
    baseline tight noProper above
  exact ⟨c, L, hc, hL, part⟩

theorem canonicalLedgerDeficit_holds : CanonicalLedgerDeficitStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, -, -, -, -, -, g2, -⟩ := canonicalLedger_quantities three deficitSafety c
    spec baseline tight noProper above
  exact ⟨c, L, hc, hL, g2⟩

theorem pairCountDeficit_holds : PairCountDeficitStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, -, -, -, -, -, -, -, g3, -⟩ := canonicalLedger_quantities three deficitSafety c
    spec baseline tight noProper above
  exact g3

theorem canonicalCertificationCriterion_holds :
    CanonicalCertificationCriterionStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, -, -, -, -, -, -, -, crit⟩ := canonicalLedger_quantities three deficitSafety
    c spec baseline tight noProper above
  exact ⟨c, L, hc, hL, crit⟩

theorem canonicalOverloadOfFits_holds : CanonicalOverloadOfFitsStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, tokEqL, -, supplyT, -, sumLoad, excess, -⟩ :=
    canonicalLedger_quantities three deficitSafety c spec baseline tight noProper above
  obtain ⟨-, -, -, -, sq⟩ := budget_core three baseline tight noProper above
  have Kpos := pairDeficitCoefficient_pos (data := data) three deficitSafety
  refine ⟨c, L, hc, hL, fun fits => ?_⟩
  set M₀ := homogeneousTokenCap data.routingLabelBound
  have fitsZ : ((freeCount data object c : ℕ) : ℤ) ≤ ((certificationBudget data object : ℕ) : ℤ) :=
    Nat.cast_le.mpr fits
  have supZ : (c.tokens.card : ℤ) ≤
      ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) : ℤ) :=
    Nat.cast_le.mpr supplyT
  have hb : (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data +
      2 * (M₀ : ℤ) * ((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) -
        (c.tokens.card : ℤ)) ≤
      2 * ((L.presented.blocked.card : ℤ) - M₀ * c.tokens.card) := by linarith
  refine ⟨hb, ?_⟩
  by_contra none
  have le : L.presented.blocked.card ≤ M₀ * L.presented.tokens.card := by
    rw [sumLoad]
    calc ∑ t ∈ L.presented.tokens, L.presented.load t
        ≤ ∑ _t ∈ L.presented.tokens, M₀ :=
          Finset.sum_le_sum fun t ht => by
            by_contra h
            push Not at h
            obtain ⟨role, pat⟩ :=
              L.presented.exists_homogeneous_pattern_of_capCharge_lt
                (fun _ => geometricPatternBound data.routingLabelBound) t
                (Nat.le_add_left 1 _) h
            exact none ⟨t, ht, h, role, pat⟩
      _ = M₀ * L.presented.tokens.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [tokEqL] at le
  have leZ : (L.presented.blocked.card : ℤ) ≤ ((M₀ * c.tokens.card : ℕ) : ℤ) :=
    Nat.cast_le.mpr le
  push_cast at leZ
  have cs1 : (1 : ℤ) ≤ (Core.ceilSqrt object.vertexCount : ℤ) := by
    have : 1 ≤ Core.ceilSqrt object.vertexCount := by
      rcases Nat.eq_zero_or_pos (Core.ceilSqrt object.vertexCount) with h | h
      · have := sq; rw [h] at this
        have := (budget_core three baseline tight noProper above).2.2.2.1; simp at *; omega
      · exact h
    exact_mod_cast this
  have p1 : (0 : ℤ) < (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data :=
    mul_pos (by positivity) Kpos
  have p2 : (0 : ℤ) ≤ 2 * (M₀ : ℤ) *
      (((8 * object.vertexCount + object.degreeSurplus data.threshold : ℕ) : ℤ) -
        (c.tokens.card : ℤ)) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

theorem canonicalFreeExcessOfCapped_holds :
    CanonicalFreeExcessOfCappedStatement data object := by
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, tokEqL, -, -, -, sumLoad, excess, -⟩ :=
    canonicalLedger_quantities three deficitSafety c spec baseline tight noProper above
  refine ⟨c, L, hc, hL, fun capped => ?_⟩
  set M₀ := homogeneousTokenCap data.routingLabelBound
  have le : L.presented.blocked.card ≤ M₀ * L.presented.tokens.card := by
    rw [sumLoad]
    calc ∑ t ∈ L.presented.tokens, L.presented.load t
        ≤ ∑ _t ∈ L.presented.tokens, M₀ := Finset.sum_le_sum capped
      _ = M₀ * L.presented.tokens.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [tokEqL] at le
  have leZ : (L.presented.blocked.card : ℤ) ≤ ((M₀ * c.tokens.card : ℕ) : ℤ) :=
    Nat.cast_le.mpr le
  push_cast at leZ
  linarith

end AtG

end CanonicalCapacityContracts

/-! ## The paper's budget, the `[131]` count, the pair-code chain, and the
structure of every witness -/

section Chain

open Hypostructure.Graph.SameTokenBlockerRoles

variable {BranchState : Graph.FiniteObject.{u} → Type v}
variable {Presentation : Type} {presentation : Presentation}

theorem paperBudget_le (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object)
    {spineCount : Nat}
    (deficitLe : Graph.spineDeficit object.vertexCount data.threshold spineCount ≤
      data.surplusScale * object.vertexCount) :
    paperBudget data object spineCount ≤ certificationBudget data object := by
  obtain ⟨-, -, slackEq, -, -⟩ := budget_core three baseline tight noProper above
  have he : object.edgeCount - Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
      object.degreeSurplus data.threshold := by
    have hc : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold =
        (3 * object.vertexCount + 1) / 2 := by simp [Graph.cubicBaselineEdgeCount, three]
    rw [hc]; omega
  have := Nat.mul_le_mul_right (Nat.log2 object.vertexCount + 1) he
  unfold paperBudget certificationBudget
  rw [Nat.mul_comm (object.degreeSurplus data.threshold)] at this
  omega

theorem paperBudgetBound_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (above : SurplusAboveStatement data object)
    (demand : BaselineSpineDemandStatement data object) :
    PaperBudgetBoundStatement data object := by
  obtain ⟨spine, hs, -, -, -, deficitLe⟩ := id demand
  exact ⟨spine, hs, paperBudget_le three baseline tight noProper above deficitLe⟩

theorem paperBudgetCertifies_holds (three : data.threshold = 3)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object)
    (demand : BaselineSpineDemandStatement data object) :
    PaperBudgetCertifiesStatement data object := by
  obtain ⟨spine, hs, -, -, -, deficitLe⟩ := id demand
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, -, -, -, -, -, -, -, -, crit⟩ := canonicalLedger_quantities three deficitSafety c
    spec baseline tight noProper above
  exact ⟨spine, c, hs, hc, fun hf => crit.2
    (hf.trans (paperBudget_le three baseline tight noProper above deficitLe))⟩

theorem freePairCountFails_at (three : data.threshold = 3)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (above : SurplusAboveStatement data object)
    (demand : BaselineSpineDemandStatement data object) :
    FreePairCountFailsStatement data object := by
  rintro ⟨activation, spine, hA, hS, count⟩
  obtain ⟨spine', hs', -, -, demandIneq, deficitLe⟩ := id demand
  rw [hS] at hs'; cases hs'
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, -, -, -, -, -, -, -, gap, -⟩ := canonicalLedger_quantities three deficitSafety c
    spec baseline tight noProper above
  obtain ⟨h1, -, slackEq, σle, sq⟩ := budget_core three baseline tight noProper above
  rw [Graph.FiniteObject.DemandActivation.card_pairFamily] at count
  have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
      object.edgeCount := by
    have hc : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold =
        (3 * object.vertexCount + 1) / 2 := by simp [Graph.cubicBaselineEdgeCount, three]
    rw [hc]; omega
  have le := Graph.freeCount_le_of_sandwich object (by omega) aboveEdges count demandIneq
  have bdeg : ∀ v : object.Vertex, data.threshold ≤ object.degree v :=
    fun v => le_trans baseline (object.minDegree_le_degree v)
  have sched : (codeSchedule data object).card =
      (object.degreeSurplus data.threshold).choose 2 := object.card_portPairSchedule bdeg
  rw [sched] at le
  have leB := le.trans (paperBudget_le three baseline tight noProper above deficitLe)
  have leZ := (Nat.cast_le (α := ℤ)).mpr leB
  have Kpos := pairDeficitCoefficient_pos (data := data) three deficitSafety
  have hcs := (SparseOrderArithmetic.sqrt_chain _ _ _ _ h1 σle sq).1
  have cs1 : (1 : ℤ) ≤ (Core.ceilSqrt object.vertexCount : ℤ) := by
    exact_mod_cast (show 1 ≤ Core.ceilSqrt object.vertexCount by omega)
  have sqpos : (1 : ℤ) ≤ (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 := by nlinarith
  have M0 : (0 : ℤ) ≤ (homogeneousTokenCap data.routingLabelBound : ℤ) := Int.natCast_nonneg _
  have p8 : (0 : ℤ) ≤ ((8 * object.vertexCount +
      object.degreeSurplus data.threshold : ℕ) : ℤ) := Int.natCast_nonneg _
  have prod : 0 < (Core.ceilSqrt object.vertexCount : ℤ) ^ 2 * pairDeficitCoefficient data :=
    mul_pos (by positivity) Kpos
  unfold paperBudget certificationBudget at *
  push_cast at leZ gap ⊢
  nlinarith

theorem not_capped_of_above (above : SurplusAboveStatement data object)
    (safety : TokenLoad.quadraticSafetyScale ≤ data.spineScale)
    {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    ¬ SparsePressureCappedAt certified data.routingLabelBound := fun capped =>
  absurd (Contracts.SurplusPair.spineSurplusEstimate_of_capped capacity certified
    capped above safety) (not_le.mpr above)

theorem coupledExcess_pos_of_above (above : SurplusAboveStatement data object)
    (safety : TokenLoad.quadraticSafetyScale ≤ data.spineScale)
    {capacity : SurplusCapacity data object}
    (certified : SurplusCertified data object capacity) :
    0 < sparseCoupledExcess data certified := by
  by_contra h
  apply not_capped_of_above above safety certified
  exact certified.ledger.presented.demand_le_sparsePressureBound
    certified.ledger.presented.tokenClass
    (fun _ => geometricPatternBound data.routingLabelBound)
    (homogeneousTokenCap data.routingLabelBound)
    (object.capacityTokenSupply data.threshold)
    (fun _ => Nat.le_refl _) certified.ledger.tokens_card_le
    (Nat.eq_zero_of_not_pos h)

/-- **The pair-code chain from the canonical first failure, survivor-free.** -/
theorem pairChain_outcome
    (firstFailure : PairOverlapFirstFailureStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (repl : ReplacementExclusionStatement data object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairConditionalFactorizationResidualStatement data object ∨
      (∃ returns, canonicalPairDemandReturns data object = some returns ∧
        Graph.ResidualTargetDefect (Graph.HasCycleWithLength data.LengthOK) object
          returns.obstructionCoordinates pairCoordinateSupport) ∨
      (∃ returns, canonicalPairDemandReturns data object = some returns ∧
        PairObstructionHandoff data object returns) := by
  classical
  have system := Contracts.SurplusPair.pairOverlapSystem_of_firstFailure firstFailure noProper
  by_cases fact : PairConditionalFactorizationStatement data object
  swap
  · exact Or.inl (Contracts.SurplusPair.pairUncovered_of_factorizationFails system fact)
  obtain ⟨returns, hr⟩ := Contracts.SurplusPair.pairDemandReturns_of_failureOverlap
    (Contracts.SurplusPair.pairFailureOverlap_of_factorization fact)
  by_cases covered : Nonempty (PairSystemRealizabilityOutcome returns)
  swap
  · exact Or.inl ⟨.systemRealizability returns hr covered⟩
  obtain ⟨outcome⟩ := covered
  cases outcome with
  | early early =>
      cases early with
      | targetCycle cycle => exact (avoids cycle).elim
      | targetDefect defect => exact Or.inr (Or.inl ⟨returns, hr, defect⟩)
      | compression support _ replacement => exact (repl support replacement).elim
      | typeB handoff => exact Or.inr (Or.inr ⟨returns, hr, handoff⟩)
  | serial sys same =>
      obtain ⟨serial, hs, sameR⟩ := canonicalPairSerialSystem_spec data object hr same
      by_cases inc : Nonempty (PairIncrementOutcome serial)
      swap
      · exact Or.inl ⟨.incrementArithmetic serial hs inc⟩
      obtain ⟨inc⟩ := inc
      cases inc with
      | arithmetic input =>
          exact (avoids (Contracts.SurplusPair.pairPowerOfTwoCycle_of_arithmetic
            ⟨serial, hs, ⟨input⟩⟩ lengthOK_iff)).elim
      | early early =>
          cases early with
          | targetDefect defect =>
              exact Or.inr (Or.inl ⟨returns, hr, sameR ▸ defect⟩)
          | compression support _ replacement => exact (repl support replacement).elim
          | typeB handoff => exact Or.inr (Or.inr ⟨returns, hr, sameR ▸ handoff⟩)

set_option maxHeartbeats 1000000 in
theorem pairCodeConfiguration_holds (three : data.threshold = 3)
    (joinSlack : data.threshold * data.windowOrder + 2 ≤ 4 * data.windowOrder)
    (deficitSafety : Graph.baselineDeficitCoefficient data.threshold ≤ data.surplusScale)
    (safety : TokenLoad.quadraticSafetyScale ≤ data.spineScale)
    (labelCount : data.routingLabelBound = Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder)))
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (selection : SelectionStatement BranchState Presentation presentation data object)
    (baseline : MinDegreeBaselineStatement data object)
    (slack : SlackIndependentStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (exclusion : ReplacementExclusionStatement data object)
    (above : SurplusAboveStatement data object)
    (demand : BaselineSpineDemandStatement data object) :
    PairCodeConfigurationStatement data object := by
  classical
  obtain ⟨c, hc, spec⟩ := canonicalLedger_exists three joinSlack deficitSafety selection
    baseline slack noProper tight above
  obtain ⟨L, hL, -, -, -, partition, -, -, -, crit⟩ :=
    canonicalLedger_quantities three deficitSafety c spec baseline tight noProper above
  obtain ⟨spine, hs, -, -, demandIneq, deficitLe⟩ := id demand
  obtain ⟨-, -, slackEq, -, -⟩ := budget_core three baseline tight noProper above
  have aboveEdges : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold ≤
      object.edgeCount := by
    have hc : Graph.cubicBaselineEdgeCount object.vertexCount data.threshold =
        (3 * object.vertexCount + 1) / 2 := by simp [Graph.cubicBaselineEdgeCount, three]
    rw [hc]; omega
  have Ele := paperBudget_le three baseline tight noProper above deficitLe
  have countImp : 2 ^ (spine.family.card + freeCount data object c) ≤
      Graph.skeletonBudget object →
      freeCount data object c ≤ paperBudget data object spine.family.card :=
    fun ent => Graph.freeCount_le_of_sandwich object (by omega) aboveEdges ent demandIneq
  have countIff : BlockedPairEntropySandwichStatement data object ↔
      2 ^ (spine.family.card + freeCount data object c) ≤ Graph.skeletonBudget object := by
    constructor
    · rintro ⟨c', hc', spine', hs', ent⟩
      rw [hc] at hc'; cases hc'
      rw [hs] at hs'; cases hs'
      exact ent
    · intro ent
      exact ⟨c, hc, spine, hs, ent⟩
  have capLedger : CapacityTokenLedgerStatement data object := ⟨c, hc, spec⟩
  have entry : PairOverlapFirstFailureStatement data object ∨
      (DependentPairFamilyStatement data object ∧
        BlockedPairEntropySandwichStatement data object ∧
        HomogeneousBottleneckPatternSchema data object ∧
        SparsePressureOverloadSchema data object ∧
        ¬ HomogeneousCapsHoldStatement data object) := by
    by_cases dep : DependentPairFamilyStatement data object
    · by_cases count : BlockedPairEntropySandwichStatement data object
      · right
        have fits : freeCount data object c ≤ certificationBudget data object :=
          (countImp (countIff.1 count)).trans Ele
        obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp (crit.2 fits)
        have sel : canonicalCertifiedCapacityData data object = some ⟨c, cert⟩ :=
          (canonicalCertifiedCapacityData_eq_some_iff data object c cert).2 ⟨hc, hcert⟩
        have overload : SparsePressureOverloadSchema data object :=
          ⟨c, cert, sel, coupledExcess_pos_of_above above safety cert⟩
        obtain ⟨value, classified⟩ :=
          Contracts.SurplusPair.canonicalOverloadClass_of_overload overload
        have pattern := Contracts.SurplusPair.homogeneousBottleneckPattern_of_class
          classified capLedger labelCount
        exact ⟨dep, count, pattern, overload,
          fun caps => Contracts.SurplusPair.not_homogeneousCapsHold_of_pattern pattern caps⟩
      · left
        have fails : BlockedPairCountFailsStatement data object := count
        exact Contracts.SurplusPair.pairOverlapFirstFailure_of_blockedCodeUnrealized
          (Contracts.SurplusPair.blockedPairCodeUnrealized_of_countFails fails
            ⟨c, spine, hc, hs, object.card_portPairSchedule
              (fun v => le_trans baseline (object.minDegree_le_degree v))⟩
            demand) dep noProper
    · left
      have indep : IndependentPairFamilyStatement data object := by
        have act := canonicalPairActivation_eq data object
          (active_of_selection three selection baseline slack)
        exact ⟨_, act, fun blocked => dep ⟨_, act, blocked⟩⟩
      exact Contracts.SurplusPair.pairOverlapFirstFailure_of_freeCodeUnrealized
        (Contracts.SurplusPair.freePairCodeUnrealized_of_countFails baseline
          (freePairCountFails_at three joinSlack deficitSafety selection baseline slack noProper
            tight above demand)
          demand indep)
        noProper
  rcases entry with ff | other
  · right
    refine ⟨ff, ?_⟩
    rcases pairChain_outcome ff noProper selection.1 exclusion lengthLaw with r | d | h
    · exact Or.inl r
    · exact Or.inr (Or.inl d)
    · exact Or.inr (Or.inr ⟨h,
        Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff above h⟩)
  · exact Or.inl other

theorem specWitnessStructure_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SpecWitnessStructureStatement data object := by
  intro w spec
  refine ⟨⟨fun r => separated_of_spec spec
      ⟨fun h => (realized_context_negative avoid r _ h).elim,
        fun h => (realized_context_negative avoid r _ h).elim⟩⟩,
    geometryAt_of_spec avoid spec, two_le_cutBoundary_of_spec avoid spec,
    proper_of_spec avoid spec, ?_, fun ⟨a, b, hB, hZ⟩ => pairArm_false spec hB hZ,
    fun whole => ⟨larger_reading_positive spec (fun x hx => whole (second_subset_support spec hx)),
      (whole_case_deficit_set avoid spec whole).1⟩, fun Y hY conn => ?_⟩
  · convert positive_support_two_boundary avoid spec
  · exact CanonicalSupport.select?_card_le spec.2.2.2.1
      (CanonicalSupport.mem_candidates_iff.2 ⟨by convert hY, conn⟩)

end Chain

end Hypostructure.Graph.Contracts.Spine.SparseExitResidual
