import Hypostructure.Graph.CapacityFreeSide.CanonicalCharge
import Hypostructure.Graph.CapacityFreeSide.Free

/-!
# Old charge of a chord-only separated pair: the earlier port's token

For a scheduled pair `{p,q}` whose blockers are all chord sets, both ports open,
each centre outside the other's `T`, and `p` before `q` in chord order:
`Θ_cap({p,q})` is the port token of `p`, or a remainder unit of a high remainder
shoulder of `p`.  So `load(port p) ≥ #{later chord-only separated partners of p
without a high remainder shoulder interception}` — the forward degree of `p`.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

theorem separated_charge
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (hpq : p ≠ q)
    {pair : Finset (object.Vertex × object.Vertex)} (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (hno : ∀ b ∈ data.activation.blockers pair,
      b.kind = SameTokenBlockerRoles.BlockerKind.arithmeticChordSet)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (A B : List (object.Vertex × object.Vertex)) (hL : chordOrder active = A ++ p :: B)
    (hqA : q ∉ A) :
    FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair =
        some (.primitive (.inr (.inr p))) ∨
      ∃ v k, (v = (pairResponseChordEnds active p).1 ∨ v = (pairResponseChordEnds active p).2) ∧
        FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair =
          some (.remainder (v, k)) := by
  classical
  have pm : p ∈ pair := (hpair p).2 (Or.inl rfl)
  have qm : q ∈ pair := (hpair q).2 (Or.inr rfl)
  have notKind : ∀ k, k ≠ SameTokenBlockerRoles.BlockerKind.arithmeticChordSet →
      ¬ data.activation.Blocks k pair := by
    rintro k hk ⟨b, hb, rfl⟩
    exact hk (hno b hb)
  have declEq : data.activation.declaredSupport =
      (pairResponseActivation active).declaredSupport := by rw [hact]; rfl
  have dD : Disjoint ((pairResponseActivation active).declaredSupport p)
      ((pairResponseActivation active).declaredSupport q) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [← declEq] at h1 h2
    exact notKind _ (by decide) (data.activation.blocks_sharedDeclaredSupport pm qm hpq h1 h2)
  have Tsub : ∀ {d} (hd : d ∈ object.excessPorts threshold),
      portT hd ⊆ (pairResponseActivation active).declaredSupport d := by
    intro d hd
    unfold portT
    rw [← pairResponseActivation_localBuffer_of_mem active hd]
    exact FiniteObject.DemandActivation.localBuffer_subset_declaredSupport _ d
  have dT : Disjoint (portT hp) (portT hq) :=
    Finset.disjoint_of_subset_left (Tsub hp) (Finset.disjoint_of_subset_right (Tsub hq) dD)
  obtain ⟨sp, -⟩ := both_singletons_chordObstruction active hp hq openP openQ dD dT hpT hqT
    pair hpair
  have head := chordObstructions_head active avoids hpair A B hL hqA sp
  have chordEq : data.activation.chordObstructions = (pairResponseActivation active).chordObstructions := by
    rw [hact]; rfl
  have hcan := canonicalBlocker_eq_chord data.activation pair hno (by rw [chordEq]; exact head)
  have hport : data.carrier.chordPort p = p := by
    show data.activation.chordPort p = p
    rw [hact]; rfl
  have hends : data.carrier.chordEnds p = pairResponseChordEnds active p := by
    show data.activation.chordEnds p = _
    rw [hact]; rfl
  have := capacityCharge_of_singleton_chord data.activation data.carrier threshold data.packing
    pair hcan hport hp (by rw [hends]; exact openP)
  rw [hends] at this
  exact this

end Hypostructure.Graph.CapacityFreeSide
