import Hypostructure.Graph.CapacityFreeSide.Canonical

/-!
# The canonical blocker and charge of a chord-only pair

If every blocker of `π` is a chord set, the canonical blocker is the FIRST chord
obstruction; if that is `{e}` with `e`'s chord ends non-adjacent, the old charge
`Θ_cap(π)` is the port token `e` or a remainder unit at one of `e`'s shoulders.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {Coordinate Chord : Type u}

theorem canonicalBlocker_eq_chord (A : FiniteObject.DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex))
    (hno : ∀ b ∈ A.blockers pair, b.kind = SameTokenBlockerRoles.BlockerKind.arithmeticChordSet)
    {S : Finset Chord} (hhead : (A.chordObstructions pair).head? = some S) :
    FiniteObject.canonicalBlocker A pair = some (.arithmeticChordSet S) := by
  classical
  rw [FiniteObject.canonicalBlocker]
  rw [List.filter_append]
  rw [List.filter_eq_nil_iff.2]
  · rw [List.nil_append]
    rw [List.filter_eq_self.2]
    · cases hc : A.chordObstructions pair with
      | nil => rw [hc] at hhead; cases hhead
      | cons a l => rw [hc] at hhead; cases hhead; rfl
    · intro b hb
      obtain ⟨S', hS', rfl⟩ := List.mem_map.1 hb
      simp only [decide_eq_true_eq]
      unfold FiniteObject.DemandActivation.blockers
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (by simpa using hS'))))
  · intro b hb h
    have hmem : b ∈ A.blockers pair := by simpa using h
    have hk := hno b hmem
    simp only [List.mem_append, List.mem_map] at hb
    rcases hb with ((((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;>
      simp [FiniteObject.Blocker.kind] at hk

/-- **The old charge of a pair whose canonical blocker is a singleton chord set
`{e}` with non-adjacent chord ends `a, b`**: the port token `e`, or a remainder
unit of a high remainder vertex among `a, b`.  (No window token: `{a,b}` spans
no edge.) -/
theorem capacityCharge_of_singleton_chord
    (A : FiniteObject.DemandActivation object Coordinate (object.Vertex × object.Vertex))
    (pres : FiniteObject.CarrierPresentation object Coordinate (object.Vertex × object.Vertex))
    (threshold : Nat) (packing : Finset (Finset object.Vertex))
    (pair : Finset (object.Vertex × object.Vertex)) {e : object.Vertex × object.Vertex}
    (hcan : FiniteObject.canonicalBlocker A pair = some (.arithmeticChordSet {e}))
    (hport : pres.chordPort e = e) (he : e ∈ object.excessPorts threshold)
    (hopen : ¬ object.graph.Adj (pres.chordEnds e).1 (pres.chordEnds e).2) :
    FiniteObject.capacityCharge A pres threshold packing pair = some (.primitive (.inr (.inr e))) ∨
      ∃ v k, (v = (pres.chordEnds e).1 ∨ v = (pres.chordEnds e).2) ∧
        FiniteObject.capacityCharge A pres threshold packing pair =
          some (.remainder (v, k)) := by
  classical
  have supp : FiniteObject.chargeSupport A pres pair =
      {(pres.chordEnds e).1, (pres.chordEnds e).2} := by
    unfold FiniteObject.chargeSupport
    rw [hcan]
    simp [FiniteObject.Blocker.declaredSupport]
  have noEdge : ∀ c : object.Vertex × object.Vertex, object.graph.Adj c.1 c.2 →
      ¬ (c.1 ∈ FiniteObject.chargeSupport A pres pair ∧
        c.2 ∈ FiniteObject.chargeSupport A pres pair) := by
    rintro c hc ⟨h1, h2⟩
    rw [supp] at h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hne := object.graph.ne_of_adj hc
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hne (h1.trans h2.symm)
    · exact hopen (h1 ▸ h2 ▸ hc)
    · exact hopen (h2 ▸ h1 ▸ hc.symm)
    · exact hne (h1.trans h2.symm)
  have wj : FiniteObject.windowJoinChoice A pres packing pair = none := by
    unfold FiniteObject.windowJoinChoice
    rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro c hc
      exact noEdge c ((object.mem_windowRemainderIncidences_iff packing c).1 hc).1
  have cw : FiniteObject.crossWindowChoice A pres packing pair = none := by
    unfold FiniteObject.crossWindowChoice
    rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro c hc
      exact noEdge c ((object.mem_crossWindowIncidences_iff packing c).1 hc).1
  unfold FiniteObject.capacityCharge
  rw [wj, cw]
  rcases hr : FiniteObject.remainderVertexChoice A pres threshold packing pair with _ | v
  · left
    simp only [hcan, Option.map_some]
    unfold FiniteObject.Blocker.carrier
    simp [hport, he]
  · right
    refine ⟨v, _, ?_, rfl⟩
    unfold FiniteObject.remainderVertexChoice at hr
    have hm := List.mem_of_mem_head? hr
    rw [Finset.mem_toList, Finset.mem_filter] at hm
    have := hm.2.1
    rw [supp] at this
    simpa using this

end Hypostructure.Graph.CapacityFreeSide
