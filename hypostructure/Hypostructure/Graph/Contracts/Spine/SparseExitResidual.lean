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
import Hypostructure.Graph.GluedReadingMaps

/-!
# Contracts: the strict-surplus facts of `[20]` and the pair-code chain

Proof-agnostic contract lemmas for `Statements/SparseExitResidual.lean`.  Each
is stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every hypothesis explicit; the hypotheses are exactly facts the
strict arm of `[19]` carries (selection, the presentation laws, the baseline,
noProperBaseline, tightEndpoint, the replacement exclusion, the maximal
packing, surplusAbove).  One contract per statement: `<statement>_holds`.

Exit (b) of `[125]`, stated about G, is empty at G (lem:sparse-exit-b-empty),
so the `[20a]` exit is closed and no contract is stated at `[125]`'s pinned
witness.

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

/-! ## Exit (e) at G -/

section WitnessFacts

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
      ¬ Graph.HasCycleWithLength data.LengthOK representative → False)
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
        ⟨representative, smaller, baseline, noTarget⟩
      · exact noCompression declared.support replacement
      · exact noDelocalization representative smaller baseline noTarget
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


/-- **`[129]`'s baseline spine demand at the top of the strict arm**: its
survivor premise is used only against exits (c) and (d), which G's replacement
exclusion and minimality refute (exit (d), stated about G: a strictly smaller
baseline representative with no target cycle, which minimality forbids). -/
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
    (fun representative smaller b noTarget =>
      noTarget (minimal representative smaller b))
    above noProper tight (by omega) deficitSafety

end Capacity

/-! ## Admissible quotients of G (K7) -/

section Quotients


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


end Boundary

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

/-- **The pair-code chain from the canonical first failure, survivor-free**,
stated about G: the target-defect outcome of `[179]`/`[180]` (exit (b) at the
obstruction coordinates) is empty at G (`Graph.not_residualTargetDefect_of_avoids`:
two readings of G agree in `G − Z`), so the chain ends at the `[182]` residual
or at the obstruction handoff. -/
theorem pairChain_outcome
    (firstFailure : PairOverlapFirstFailureStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (repl : ReplacementExclusionStatement data object)
    (lengthOK_iff : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    PairConditionalFactorizationResidualStatement data object ∨
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
      | targetDefect defect =>
          exact (Graph.not_residualTargetDefect_of_avoids avoids _ _ defect).elim
      | compression support _ replacement => exact (repl support replacement).elim
      | typeB handoff => exact Or.inr ⟨returns, hr, handoff⟩
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
              exact (Graph.not_residualTargetDefect_of_avoids avoids _ _ defect).elim
          | compression support _ replacement => exact (repl support replacement).elim
          | typeB handoff => exact Or.inr ⟨returns, hr, sameR ▸ handoff⟩

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
    rcases pairChain_outcome ff noProper selection.1 exclusion lengthLaw with r | h
    · exact Or.inl r
    · exact Or.inr ⟨h,
        Contracts.SurplusPair.typeBFanEntry_of_pairObstructionHandoff above h⟩
  · exact Or.inl other

open Classical in
/-- **The entry-prefix witness fact, stated about G** (the `[20a]` structure at
every clause-(b) witness): at every witness triple
`w = (A, B, Z)` of G whose `Z` is the canonical support of `A ∪ B`, `Z` is
connected, contains `A` and `B`, and is a minimum connected set containing
`A ∪ B`; and no witness of G satisfies clause (b) (`G − Z` never separates two
readings of G). -/
theorem specWitnessStructure_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SpecWitnessStructureStatement data object := by
  intro w selected
  have cand := CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates selected)
  refine ⟨cand.2, fun v hv => cand.1 (Finset.mem_union.2 (Or.inl hv)),
    fun v hv => cand.1 (Finset.mem_union.2 (Or.inr hv)), fun Y hY conn => ?_,
    SparseTargetDefectWitness.not_spec avoid w⟩
  exact CanonicalSupport.select?_card_le selected
    (CanonicalSupport.mem_candidates_iff.2 ⟨by convert hY, conn⟩)

end Chain

end Hypostructure.Graph.Contracts.Spine.SparseExitResidual
