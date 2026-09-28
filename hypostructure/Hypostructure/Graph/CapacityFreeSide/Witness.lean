import Hypostructure.Graph.CapacityFreeSide.Singleton

/-!
# Blocked side: separated pairs carry both single-port chord sets

For two selected open ports with disjoint declared supports `T ∪ Γ`, distinct
centres and each centre outside the other's `T`, both `{p}` and `{q}` are
clause-(f) obstructions of `{p,q}`: `Q_p ⊆ Γ(p)` avoids `x_q ∈ T(q)`.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- The activation's own suppression path `Q_p` lies in `Γ(p) ⊆ T(p) ∪ Γ(p)`. -/
theorem exists_openWitness_in_declared
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p : object.Vertex × object.Vertex} (hp : p ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2) :
    ∃ W : FiniteObject.SurplusPort.OpenPortWitness object LengthOK p.2
        (pairResponseChordEnds active p).1 (pairResponseChordEnds active p).2,
      ∀ z ∈ W.path.support, z ∈ (pairResponseActivation active).declaredSupport p := by
  classical
  have e : pairResponseChordEnds active p =
      ((active.shoulderPair p hp).choose, (active.shoulderPair p hp).choose_spec.choose) := by
    simp only [pairResponseChordEnds, dif_pos hp]
  rw [e] at openP ⊢
  have act := active.activated p hp (active.shoulderPair p hp).choose
    (active.shoulderPair p hp).choose_spec.choose
    (active.shoulderPair p hp).choose_spec.choose_spec.1
    (active.shoulderPair p hp).choose_spec.choose_spec.2
  refine ⟨(act.2.1 openP).some, fun z hz => ?_⟩
  apply FiniteObject.DemandActivation.responseSupport_subset_declaredSupport
  simp only [pairResponseActivation, dif_pos hp]
  unfold FiniteObject.SurplusPort.responseSupport
  rw [dif_neg openP]
  simp only [List.mem_toFinset]
  exact hz

/-- **Both singletons are clause-(f) chord sets of a separated open pair.** -/
theorem both_singletons_chordObstruction
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjD : Disjoint ((pairResponseActivation active).declaredSupport p)
        ((pairResponseActivation active).declaredSupport q))
    (disjT : Disjoint (portT hp) (portT hq))
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (pair : Finset (object.Vertex × object.Vertex)) (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q) :
    ({p} : Finset (object.Vertex × object.Vertex)) ∈
        (pairResponseActivation active).chordObstructions pair ∧
      ({q} : Finset (object.Vertex × object.Vertex)) ∈
        (pairResponseActivation active).chordObstructions pair := by
  classical
  have xD : ∀ {d} (hd : d ∈ object.excessPorts threshold),
      d.2 ∈ (pairResponseActivation active).declaredSupport d := by
    intro d hd
    have := FiniteObject.DemandActivation.localBuffer_subset_declaredSupport
      (pairResponseActivation active) d
    rw [pairResponseActivation_localBuffer_of_mem active hd] at this
    exact this (FiniteObject.SurplusPort.endpoint_mem_support _)
  obtain ⟨Wp, hWp⟩ := exists_openWitness_in_declared active hp openP
  obtain ⟨Wq, hWq⟩ := exists_openWitness_in_declared active hq openQ
  refine ⟨singleton_chordObstruction active hp hq openP openQ disjT hpT hqT pair hpair Wp
      (fun h => Finset.disjoint_left.1 disjD (hWp _ h) (xD hq)), ?_⟩
  have hpair' : ∀ x, x ∈ pair ↔ x = q ∨ x = p := fun x => (hpair x).trans or_comm
  exact singleton_chordObstruction active hq hp openQ openP disjT.symm hqT hpT pair hpair' Wq
      (fun h => Finset.disjoint_right.1 disjD (hWq _ h) (xD hp))

end Hypostructure.Graph.CapacityFreeSide
