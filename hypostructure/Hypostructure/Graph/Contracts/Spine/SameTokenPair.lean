import Hypostructure.Graph.Statements.SameTokenPair
import Hypostructure.Graph.Statements.SurplusPair
import Hypostructure.Graph.Contracts.SurplusPair.Routing

/-!
# Contracts: G's same-token pattern pair, made exact

Proof-agnostic contract lemmas for `Statements/SameTokenPair.lean`, one
`<statement>_holds` per statement.  The hypotheses are exactly facts the
`[144]`/`[144a]` ledgers carry: the routed pattern (`K .bottleneckRouting`)
and the survivor (`K .sparseSurplusSurvivor`), which pin G's canonical routing;
`K .noProperBaseline` (G connected); `K .tightEndpoint`; the unresolved pair
(`K .sameTokenPatternUnresolved`); the selection and the presentation laws.
The mathematics is the vocabulary-free library (`Graph/ReadingProfiles.lean`,
`Graph/ActualContext.lean`).  The equal-count readings agree in G's own
surroundings `G − Z`.  The transplant facts (Lean improvement) read the partition, `K .noProperBaseline`, the selection (G avoids
the target and is minimal) and `K .minDegreeBaseline`; their mathematics is
`Graph/Transplant.lean`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SameTokenPair

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ReadingProfiles

universe u v

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- The declared support of a selected demand contains two distinct shoulders. -/
theorem declaredSupport_two {Baseline Target : FiniteObject.{u} → Prop}
    {LengthOK : Nat → Prop} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    {d : object.Vertex × object.Vertex} (hd : d ∈ object.excessPorts threshold) :
    ∃ a b, a ≠ b ∧
      a ∈ (recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) pairs).declaredSupport d ∧
      b ∈ (recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) pairs).declaredSupport d := by
  classical
  obtain ⟨left, right, desc, ne⟩ := active.shoulderPair d hd
  let act := recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
    (pairResponseActivation active) pairs
  have buf : act.localBuffer d = (object.surplusPortOfMem hd).support := by
    show (pairResponseActivation active).localBuffer d = _
    unfold pairResponseActivation
    simp only [dif_pos hd]
  have sub : act.localBuffer d ⊆ act.declaredSupport d := by
    rw [act.declaredSupport_eq]
    intro v hv
    unfold FiniteObject.vertexSupportUnion
    letI : DecidableEq object.Vertex := object.vertices.decEq
    exact Finset.mem_union_left _ hv
  refine ⟨left, right, ne, sub ?_, sub ?_⟩
  · rw [buf]
    exact FiniteObject.SurplusPort.mem_support_of_mem_shoulders _ ((desc left).2 (Or.inl rfl))
  · rw [buf]
    exact FiniteObject.SurplusPort.mem_support_of_mem_shoulders _ ((desc right).2 (Or.inr rfl))

/-- **Every pattern support of G's canonical routing has two distinct
vertices.** -/
theorem routing_support_two (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (connected : object.graph.Connected)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairMem : pair = routing.demands.first ∨ pair = routing.demands.second) :
    ∃ a b, a ≠ b ∧ a ∈ sameTokenPairSupport routing pair ∧
      b ∈ sameTokenPairSupport routing pair := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨hOverload, -, hDemands, -⟩ :=
    canonicalSameTokenRouting_spec_of_eq_some data object routingEq
  obtain ⟨hLedger, -⟩ := (canonicalOverload_eq_some_iff data object).1 hOverload
  obtain ⟨hCap, -⟩ := (canonicalCertifiedCapacityData_eq_some_iff data object _ _).1 hLedger
  obtain ⟨⟨active, actEq⟩, -⟩ := canonicalCapacity_spec_of_eq_some data object hCap
  have dspec := canonicalChoice_spec_of_eq_some hDemands
  obtain ⟨-, active', cubic, subset, firstMem, secondMem, -⟩ := dspec
  have inPattern : pair ∈ routing.pattern := by
    rcases pairMem with rfl | rfl
    · exact firstMem
    · exact secondMem
  have fibreMem := subset inPattern
  have scheduleMem : pair ∈ object.portPairSchedule data.threshold :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp fibreMem).1).1
  have pairFacts : pair ⊆ object.excessPorts data.threshold ∧ pair.card = 2 :=
    Finset.mem_powersetCard.mp scheduleMem
  obtain ⟨d, hd⟩ : pair.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a, b, ne, ha, hb⟩ := declaredSupport_two
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
    (LengthOK := data.LengthOK) active (object.portPairSchedule data.threshold) (pairFacts.1 hd)
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1
    (FiniteObject.DemandActivation.pairSupport_isSome_of_connected routing.capacity.activation
      pair (SupportComponents.Connected.connectedOn_vertexFinset object connected))
  have seedX := (FiniteObject.DemandActivation.pairSupport_mem_candidates hX).1
  have suppEq : sameTokenPairSupport routing pair = X := by
    change (routing.capacity.activation.pairSupport pair).getD ∅ = X
    rw [hX]; rfl
  rw [suppEq]
  have inSeed : ∀ v, v ∈ routing.capacity.activation.declaredSupport d → v ∈ X := fun v hv =>
    seedX (FiniteObject.DemandActivation.declaredSupport_subset_pairSeed _ hd hv)
  rw [actEq] at inSeed
  exact ⟨a, b, ne, inSeed a ha, inSeed b hb⟩

/-- A pattern support of G's canonical routing is the canonical selection of
its pair seed. -/
theorem routing_support_selected (routing : SameTokenRouting data object)
    (connected : object.graph.Connected) (pair : Finset (object.Vertex × object.Vertex)) :
    CanonicalSupport.select? object (routing.capacity.activation.pairSeed pair) =
      some (sameTokenPairSupport routing pair) := by
  obtain ⟨X, hX, hget⟩ := pairSupport_selected connected routing.capacity.activation pair
  have : sameTokenPairSupport routing pair = X := hget
  rw [this]
  exact hX

/-- G's canonical routing exists on the routed, surviving ledger: the routed
pattern is a handoff (whose separator pins the routing) or the unresolved pair
(which pins it). -/
theorem canonicalRouting_exists (routed : BottleneckRoutingStatement data object)
    (survivor : SparseSurplusSurvivorStatement data object) :
    ∃ routing, canonicalSameTokenRouting data object = some routing := by
  rcases routed.2.resolve_left survivor with handoff | unresolved
  · obtain ⟨core, centres, routing, split, envelope, sepEq, -⟩ := handoff
    exact ⟨routing, (canonicalSameTokenSeparator_spec_of_eq_some data object sepEq).1⟩
  · obtain ⟨routing, routingEq, -⟩ := unresolved
    exact ⟨routing, routingEq⟩

/-- **The pattern supports of G's canonical routing**, from the routed pattern,
the survivor and `K .noProperBaseline`. -/
theorem sameTokenPatternSupports_holds (routed : BottleneckRoutingStatement data object)
    (survivor : SparseSurplusSurvivorStatement data object)
    (noProper : NoProperBaselineStatement data object) :
    SameTokenPatternSupportsStatement data object := by
  obtain ⟨routing, routingEq⟩ := canonicalRouting_exists routed survivor
  refine ⟨routing, routingEq, fun pair pairMem => ⟨?_, ?_, ?_⟩⟩
  · exact routing_support_selected routing noProper.2 pair
  · exact (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates
      (routing_support_selected routing noProper.2 pair))).2
  · exact routing_support_two routing routingEq noProper.2 pairMem

/-- **The swaps of G's two pattern readings**, from the routed pattern, the
survivor and the tight-endpoint law. -/
theorem sameTokenPatternSwap_holds (routed : BottleneckRoutingStatement data object)
    (survivor : SparseSurplusSurvivorStatement data object)
    (tight : TightEndpointStatement data object) :
    SameTokenPatternSwapStatement data object := by
  obtain ⟨routing, routingEq⟩ := canonicalRouting_exists routed survivor
  exact ⟨routing, routingEq, swap_exact tight _ _, swap_exact tight _ _⟩

/-- **Node `[144a]`: the exact partition of G's unresolved pattern pair**, from
the unresolved pair, `K .noProperBaseline`, the selection (G avoids the
target) and the dyadic target law of the presentation. -/
theorem sameTokenPairPartition_holds
    (unresolved : SameTokenPatternPairUnresolvedStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (dyadic : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) :
    SameTokenPairPartitionStatement data object := by
  have lengths : data.LengthOK = Core.DyadicLength.PowerOfTwoLength :=
    funext fun length => propext (dyadic length)
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, different, Z, selected, alternative⟩ := unresolved
  have connected := noProper.2
  have selP := routing_support_selected routing connected routing.demands.first
  have selQ := routing_support_selected routing connected routing.demands.second
  set Xp := sameTokenPairSupport routing routing.demands.first with hXp
  set Xq := sameTokenPairSupport routing routing.demands.second with hXq
  have cand := CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates selected)
  have pZ : Xp ⊆ Z := fun v hv => cand.1 (Finset.mem_union_left _ hv)
  have qZ : Xq ⊆ Z := fun v hv => cand.1 (Finset.mem_union_right _ hv)
  refine ⟨routing, routingEq, Xp, Xq, Z, rfl, rfl, different, selP, selQ, selected,
    pZ, qZ, cand.2, ?_⟩
  have connP : SupportComponents.Connected.ConnectedOn object Xp :=
    (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates selP)).2
  have connQ : SupportComponents.Connected.ConnectedOn object Xq :=
    (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates selQ)).2
  by_cases profile : (SupportAtom.retainedPiece object Z Xp).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object Z Xq).boundaryDegreeProfile
  · -- equal counts
    right
    have counts := (profile_eq_iff_counts Z Xp Xq).1 profile
    have tp : ∀ b : (SupportAtom.boundary object Z).Vertex, b.1 ∈ Xp →
        ∀ w ∈ Xp, object.graph.Adj b.1 w → b.1 ∈ Xq :=
      fun b hb w hw adj => mem_of_profile_eq profile b hb (pZ hw) hw adj
    have tq : ∀ b : (SupportAtom.boundary object Z).Vertex, b.1 ∈ Xq →
        ∀ w ∈ Xq, object.graph.Adj b.1 w → b.1 ∈ Xp :=
      fun b hb w hw adj => mem_of_profile_eq profile.symm b hb (qZ hw) hw adj
    refine ⟨counts, tp, tq, ActualContext.actualGlue_agree avoids Z Xp Xq, ?_⟩
    by_cases free : (∀ w ∈ Xp, w ∉ SupportAtom.cutBoundary object Z) ∧
        (∀ w ∈ Xq, w ∉ SupportAtom.cutBoundary object Z)
    · left
      have selectedC : @CanonicalSupport.select? object
          (@Union.union _ (@Finset.instUnion _ (fun a b => Classical.propDecidable (a = b)))
            Xp Xq) = some Z := by
        convert selected
      refine ⟨free.1, free.2, fun b => boundaryFree_boundary_cut selectedC free.1 free.2 b, ?_⟩
      rintro w n (hw | hw) adj
      · exact boundaryFree_neighbours_inside pZ free.1 hw adj
      · exact boundaryFree_neighbours_inside qZ free.2 hw adj
    · right
      by_contra shared
      push Not at shared
      push Not at free
      -- one-sided: a support on `∂Z` collapses to a singleton, contradicting two vertices
      have single : ∃ b ∈ SupportAtom.cutBoundary object Z, Xp = {b} ∨ Xq = {b} := by
        by_cases allP : ∀ w ∈ Xp, w ∉ SupportAtom.cutBoundary object Z
        · obtain ⟨w, wq, wb⟩ := free allP
          have wp : w ∉ Xp := fun h => allP w h wb
          exact ⟨w, wb, Or.inr (onesided_singleton (Z := Z) (X := Xq) (Y := Xp) tq connQ
            ⟨w, wb⟩ wq wp)⟩
        · push Not at allP
          obtain ⟨w, wp, wb⟩ := allP
          have wq : w ∉ Xq := fun h => shared w wb wp h
          exact ⟨w, wb, Or.inl (onesided_singleton (Z := Z) (X := Xp) (Y := Xq) tp connP
            ⟨w, wb⟩ wp wq)⟩
      obtain ⟨b, -, single | single⟩ := single
      · obtain ⟨x, y, ne, hx, hy⟩ := routing_support_two routing routingEq connected
          (pair := routing.demands.first) (Or.inl rfl)
        rw [← hXp, single] at hx hy
        exact ne ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm)
      · obtain ⟨x, y, ne, hx, hy⟩ := routing_support_two routing routingEq connected
          (pair := routing.demands.second) (Or.inr rfl)
        rw [← hXq, single] at hx hy
        exact ne ((Finset.mem_singleton.1 hx).trans (Finset.mem_singleton.1 hy).symm)
  · -- separating count
    left
    have none : ¬ ∀ b, readingCount Z Xp b = readingCount Z Xq b := fun h =>
      profile ((profile_eq_iff_counts Z Xp Xq).2 h)
    push Not at none
    obtain ⟨b, differ⟩ := none
    refine ⟨b, differ, readingCount_add_one_le Z Xp b, readingCount_add_one_le Z Xq b, ?_⟩
    rcases U1_exact selP selQ b differ with ⟨pos, alt⟩ | ⟨pos, alt⟩
    · obtain ⟨bR, w, wR, adj⟩ := readingCount_pos pos
      exact Or.inl ⟨pos, bR, ⟨w, wR, adj⟩, alt⟩
    · obtain ⟨bR, w, wR, adj⟩ := readingCount_pos pos
      exact Or.inr ⟨pos, bR, ⟨w, wR, adj⟩, alt⟩

/-! ## The transplants of the pattern supports into `Z` -/

/-- **The transplant conditions (i)--(iv) and the size equality at G**, for a
`Y` with a vertex: G avoids the target and every strictly smaller baseline
object has one. -/
theorem sameTokenTransplantAt_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (Z Y : Finset object.Vertex) (nonempty : ∃ y, y ∈ Y) :
    SameTokenTransplantAt data object Z Y := by
  obtain ⟨y, hy⟩ := nonempty
  have kept : ∃ v, ¬ Graph.Transplant.Removed object Z Y v := ⟨y, fun h => h.2.2 hy⟩
  refine ⟨Graph.Transplant.transplant_internalVertexCount_le Z Y,
    Graph.Transplant.transplant_linkageIncluded Z Y,
    Graph.Transplant.transplant_profile_eq_iff Z Y,
    Graph.Transplant.transplant_baseline_iff Z Y kept, fun base included =>
      ⟨Graph.Transplant.transplant_size_eq avoids minimal Z Y base included, ?_⟩⟩
  intro v vZ vb
  by_contra vY
  exact Graph.Transplant.transplant_fills_of_baseline avoids minimal Z Y base v ⟨vZ, vb, vY⟩

/-- **The exact transplant at G**, for a `Y` with a vertex, from the selection
and the baseline. -/
theorem sameTokenTransplantExactAt_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (base : Graph.MinimumDegreeAtLeast data.threshold object)
    (Z Y : Finset object.Vertex) (nonempty : ∃ y, y ∈ Y) :
    SameTokenTransplantExactAt data object Z Y := by
  obtain ⟨y, hy⟩ := nonempty
  exact Graph.Transplant.transplant_exact avoids minimal base Z Y ⟨y, fun h => h.2.2 hy⟩

/-- The two pattern supports of the partition each have a vertex. -/
theorem partition_supports_nonempty (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (connected : object.graph.Connected) {Xp Xq : Finset object.Vertex}
    (hXp : Xp = sameTokenPairSupport routing routing.demands.first)
    (hXq : Xq = sameTokenPairSupport routing routing.demands.second) :
    (∃ y, y ∈ Xp) ∧ ∃ y, y ∈ Xq := by
  obtain ⟨p, -, -, hp, -⟩ := routing_support_two routing routingEq connected
    (pair := routing.demands.first) (Or.inl rfl)
  obtain ⟨q, -, -, hq, -⟩ := routing_support_two routing routingEq connected
    (pair := routing.demands.second) (Or.inr rfl)
  exact ⟨⟨p, by rw [hXp]; exact hp⟩, ⟨q, by rw [hXq]; exact hq⟩⟩

/-- **Node `[144a]`: the transplants of G's pattern supports into `Z`, with the
size equality**, from the partition (which pins `X_p`, `X_q`, `Z`),
`K .noProperBaseline` and the selection. -/
theorem sameTokenTransplantSize_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H) :
    SameTokenTransplantSizeStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, -, -, selected, -⟩ := partition
  obtain ⟨neP, neQ⟩ := partition_supports_nonempty routing routingEq noProper.2 hXp hXq
  exact ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, selected,
    sameTokenTransplantAt_holds avoids minimal Z Xq neQ,
    sameTokenTransplantAt_holds avoids minimal Z Xp neP⟩

/-- **Node `[144a]`: the exact failure of the transplants of G's pattern
supports**, from the partition, `K .noProperBaseline`, the selection and the
baseline. -/
theorem sameTokenTransplantDeficit_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (base : MinDegreeBaselineStatement data object) :
    SameTokenTransplantDeficitStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, -, -, selected, -⟩ := partition
  obtain ⟨neP, neQ⟩ := partition_supports_nonempty routing routingEq noProper.2 hXp hXq
  exact ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, selected,
    sameTokenTransplantExactAt_holds avoids minimal base Z Xq neQ,
    sameTokenTransplantExactAt_holds avoids minimal base Z Xp neP⟩

end Hypostructure.Graph.Contracts.Spine.SameTokenPair
