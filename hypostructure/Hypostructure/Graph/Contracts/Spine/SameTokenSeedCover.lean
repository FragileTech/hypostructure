import Hypostructure.Graph.Statements.SameTokenSwap
import Hypostructure.Graph.Contracts.Spine.SameTokenPair
import Hypostructure.Graph.PortPathCover
import Hypostructure.Graph.Statements.JointHubs

/-!
# Contracts: the pair seeds are three-vertex supports and canonical port paths

Proof-agnostic contract lemmas for the seed-cover statement of `[144a]`.
-/

namespace Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.PortPathCover

universe u v

section Demand

variable {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
  {object : FiniteObject.{u}} {threshold : Nat}

/-- **The declared support of an active demand is its port support and one canonical
port path.** -/
theorem demand_declaredSupport_cover
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    {d : object.Vertex × object.Vertex} (hd : d ∈ object.excessPorts threshold) :
    ∃ P, PortPathSupport object LengthOK P ∧
      (recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        (pairResponseActivation active) pairs).declaredSupport d =
        (by letI : DecidableEq object.Vertex := object.vertices.decEq
            exact (object.surplusPortOfMem hd).support ∪ P) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let act := recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
    (pairResponseActivation active) pairs
  let port := object.surplusPortOfMem hd
  let shoulders := active.shoulderPair d hd
  let left := shoulders.choose
  let right := shoulders.choose_spec.choose
  have description := shoulders.choose_spec.choose_spec.1
  have distinct := shoulders.choose_spec.choose_spec.2
  let activated := active.activated d hd left right description distinct
  have hl : object.graph.Adj port.endpoint left := by
    have : left ∈ port.shoulders := (description left).2 (Or.inl rfl)
    exact ((FiniteObject.SurplusPort.mem_shoulders_iff port left).1 this).2
  have hr : object.graph.Adj port.endpoint right := by
    have : right ∈ port.shoulders := (description right).2 (Or.inr rfl)
    exact ((FiniteObject.SurplusPort.mem_shoulders_iff port right).1 this).2
  have buf : act.localBuffer d = port.support := by
    show (pairResponseActivation active).localBuffer d = _
    unfold pairResponseActivation
    simp only [dif_pos hd]
    rfl
  have resp : act.responseSupport d = port.responseSupport activated.1 activated.2.1 := by
    show (pairResponseActivation active).responseSupport d = _
    unfold pairResponseActivation
    simp only [dif_pos hd]
    rfl
  obtain ⟨P, hP, heq⟩ := declaredSupport_pathSupport avoids port activated.1 activated.2.1 hl hr
  refine ⟨P, hP, ?_⟩
  rw [act.declaredSupport_eq]
  unfold FiniteObject.vertexSupportUnion
  rw [buf, resp]
  unfold FiniteObject.SurplusPort.declaredSupport at heq
  exact heq

end Demand


section Cubic

variable {object : Graph.FiniteObject.{u}}

/-- **The cubic vertices are at least `3n/5`**, so a cover of them has at least that
many vertices: from `5|H| + σ ≤ 2n`. -/
theorem cubic_card_bound [DecidableEq object.Vertex]
    (hb : Graph.JointObject.HubCountBound object)
    {S : Finset object.Vertex} (cover : ∀ v, object.degree v = 3 → v ∈ S) :
    3 * object.vertexCount ≤ 5 * S.card := by
  classical
  letI : Fintype object.Vertex := by letI := object.vertices; infer_instance
  have hn : object.vertexCount = Fintype.card object.Vertex :=
    Graph.JointObject.vertexCount_eq object
  have split := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset object.Vertex)) (fun v => object.graph.degree v = 3)
  have hubs : (Graph.JointObject.hubs object).card =
      (Finset.univ.filter fun v => ¬ object.graph.degree v = 3).card := by
    unfold Graph.JointObject.hubs
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> convert h
  have sub : Finset.univ.filter (fun v => object.graph.degree v = 3) ⊆ S := by
    intro v hv
    have h3 := (Finset.mem_filter.1 hv).2
    refine cover v ?_
    unfold Graph.FiniteObject.degree
    convert h3
  have hle := Finset.card_le_card sub
  unfold Graph.JointObject.HubCountBound at hb
  rw [hn] at hb ⊢
  rw [Finset.card_univ] at split
  omega

end Cubic

section Pair

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **A pair seed of G's canonical routing is at most `2δ` vertices and two canonical
port paths.** -/
theorem pairSeedCover
    (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairMem : pair = routing.demands.first ∨ pair = routing.demands.second) :
    PairSeedCover data object (routing.capacity.activation.pairSeed pair) := by
  classical
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨hOverload, -, hDemands, -⟩ := canonicalSameTokenRouting_spec_of_eq_some data object routingEq
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
  obtain ⟨d1, d2, ne, hpair⟩ := Finset.card_eq_two.1 pairFacts.2
  have hd1 : d1 ∈ object.excessPorts data.threshold :=
    pairFacts.1 (by rw [hpair]; simp)
  have hd2 : d2 ∈ object.excessPorts data.threshold :=
    pairFacts.1 (by rw [hpair]; simp)
  obtain ⟨P1, hP1, e1⟩ := demand_declaredSupport_cover
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
    active avoids (object.portPairSchedule data.threshold) hd1
  obtain ⟨P2, hP2, e2⟩ := demand_declaredSupport_cover
    (Baseline := Graph.MinimumDegreeAtLeast data.threshold) (LengthOK := data.LengthOK)
    active avoids (object.portPairSchedule data.threshold) hd2
  have supportCard : ∀ (d : object.Vertex × object.Vertex)
      (hd : d ∈ object.excessPorts data.threshold),
      (object.surplusPortOfMem hd).support.card ≤ data.threshold := by
    intro d hd
    have := (family.2 d hd).2.2
    unfold Graph.FiniteObject.SurplusPort.support
    calc (insert (object.surplusPortOfMem hd).endpoint (object.surplusPortOfMem hd).shoulders).card
        ≤ (object.surplusPortOfMem hd).shoulders.card + 1 := Finset.card_insert_le _ _
      _ ≤ data.threshold := by omega
  refine ⟨(object.surplusPortOfMem hd1).support ∪ (object.surplusPortOfMem hd2).support,
    P1, P2, ?_, hP1, hP2, ?_⟩
  · calc _ ≤ (object.surplusPortOfMem hd1).support.card +
          (object.surplusPortOfMem hd2).support.card := Finset.card_union_le _ _
      _ ≤ 2 * data.threshold := by
        have := supportCard d1 hd1; have := supportCard d2 hd2; omega
  · unfold Graph.FiniteObject.DemandActivation.pairSeed
    rw [actEq, hpair]
    generalize (recordSparsePairDEBlockers (Baseline := Graph.MinimumDegreeAtLeast data.threshold)
        (LengthOK := data.LengthOK) (pairResponseActivation active)
        (object.portPairSchedule data.threshold)).declaredSupport = F at e1 e2 ⊢
    ext v
    have m1 := congrArg (fun S => v ∈ S) e1
    have m2 := congrArg (fun S => v ∈ S) e2
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
      eq_iff_iff] at m1 m2 ⊢
    constructor
    · rintro ⟨d, hd, hv⟩
      rcases hd with rfl | rfl
      · rcases m1.1 hv with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inr h)
      · rcases m2.1 hv with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr h
    · intro h
      rcases h with ((h | h) | h) | h
      · exact ⟨d1, Or.inl rfl, m1.2 (Or.inl h)⟩
      · exact ⟨d2, Or.inr rfl, m2.2 (Or.inl h)⟩
      · exact ⟨d1, Or.inl rfl, m1.2 (Or.inr h)⟩
      · exact ⟨d2, Or.inr rfl, m2.2 (Or.inr h)⟩

/-- **The pair seeds are covered by their canonical port paths.** -/
theorem sameTokenSeedCover_holds
    (partition : SameTokenPairPartitionStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    (hubBound : HubCountBoundStatement object) :
    SameTokenSeedCoverStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, -⟩ := partition
  have cp := pairSeedCover routing routingEq avoids family threshold (Or.inl rfl)
  have cq := pairSeedCover routing routingEq avoids family threshold (Or.inr rfl)
  refine ⟨routing, routingEq, cp, cq, fun hyp v h3 => ?_⟩
  obtain ⟨T, P1, P2, hT, hP1, hP2, eP⟩ := cp
  obtain ⟨T', Q1, Q2, hT', hQ1, hQ2, eQ⟩ := cq
  obtain ⟨vp, vq⟩ := hyp v h3
  refine ⟨T, P1, P2, T', Q1, Q2, hT, hT', hP1, hP2, hQ1, hQ2, eP, eQ, ?_, ?_, ?_, ?_⟩
  · rw [← eP]; exact vp
  · rw [← eQ]; exact vq
  · have hc := cubic_card_bound (S := T ∪ P1 ∪ P2) hubBound (fun v h3 => by
      rw [← eP]; exact (hyp v h3).1)
    have := Finset.card_union_le (T ∪ P1) P2
    have := Finset.card_union_le T P1
    omega
  · have hc := cubic_card_bound (S := T' ∪ Q1 ∪ Q2) hubBound (fun v h3 => by
      rw [← eQ]; exact (hyp v h3).2)
    have := Finset.card_union_le (T' ∪ Q1) Q2
    have := Finset.card_union_le T' Q1
    omega

end Pair

end Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover
