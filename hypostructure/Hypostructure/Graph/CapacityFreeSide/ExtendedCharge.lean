import Hypostructure.Graph.CapacityFreeSide.ExtendedBlockers
/-!
# Extended charge `Θ_ext`: old charge first, then (g) and (h) on port tokens

EXTENSION of `capacityCharge` (unchanged): `Θ_ext(π) = Θ_cap(π)` whenever the old
charge is defined; otherwise a (g) pair is charged to the port token of its
first configuration `c₁` (the port whose hub is a shoulder of the other), and an
(h) pair to its triangular port.  The token universe is NOT enlarged: port
tokens `𝒫_exc ⊆ 𝔘_sp(G) ⊆ 𝔗_cap` already exist, so `𝔗_ext = 𝔗_cap` and
`|𝔗_ext| = |𝔗_cap|`.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold order : Nat}

/-- The port token of a selected port. -/
abbrev portToken (p : object.Vertex × object.Vertex) : FiniteObject.CapacityToken object :=
  .primitive (.inr (.inr p))

/-- **`Θ_ext`**. -/
noncomputable def extCharge (LengthOK : Nat → Prop)
    (data : CapacityPresentation object threshold order)
    (pair : Finset (object.Vertex × object.Vertex)) : Option (FiniteObject.CapacityToken object) :=
  match FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair with
  | some t => some t
  | none => by
      classical
      exact if hg : CentreShoulderBlocks LengthOK object pair then
          some (portToken (hg.choose.center, hg.choose.vertex))
        else if hh : TriangularBlocks object pair then some (portToken hh.choose)
        else none

variable (LengthOK : Nat → Prop) (data : CapacityPresentation object threshold order)

/-- **Refinement**: every pair charged by `Θ_cap` keeps its charge. -/
theorem extCharge_of_old {pair} {t : FiniteObject.CapacityToken object}
    (h : FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair =
      some t) : extCharge LengthOK data pair = some t := by
  unfold extCharge; rw [h]

theorem extCharge_of_none {pair}
    (h : FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair =
      none) :
    extCharge LengthOK data pair = (by
      classical
      exact if hg : CentreShoulderBlocks LengthOK object pair then
          some (portToken (hg.choose.center, hg.choose.vertex))
        else if hh : TriangularBlocks object pair then some (portToken hh.choose)
        else none) := by
  unfold extCharge; rw [h]

/-- A port token of a selected port is a token of `𝔗_cap`. -/
theorem portToken_mem {p : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) : portToken p ∈ data.tokens := by
  classical
  unfold CapacityPresentation.tokens FiniteObject.capacityTokens
  refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ ?_))
  refine Finset.mem_image.2 ⟨.inr (.inr p), ?_, rfl⟩
  unfold FiniteObject.primitiveCarrier
  simpa using hp

/-- **`Θ_ext` lands in `𝔗_ext = 𝔗_cap`** on the schedule. -/
theorem extCharge_mem_tokens {pair} (sched : pair ∈ object.portPairSchedule threshold)
    {t : FiniteObject.CapacityToken object} (h : extCharge LengthOK data pair = some t) :
    t ∈ data.tokens := by
  classical
  have sub := object.subset_excessPorts_of_mem_portPairSchedule threshold sched
  rcases hc : FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair
    with _ | t'
  · rw [extCharge_of_none LengthOK data hc] at h
    split_ifs at h with hg hh
    · cases h
      obtain ⟨c₂, hpair, -⟩ := hg.choose_spec
      exact portToken_mem data (sub ((hpair _).2 (Or.inl rfl)))
    · cases h
      exact portToken_mem data (sub hh.choose_spec.1)
  · rw [extCharge_of_old LengthOK data hc] at h
    cases h
    exact FiniteObject.capacityCharge_mem_capacityTokens _ _ _ _ hc

/-- `load_ext(t)`. -/
noncomputable def extLoad (t : FiniteObject.CapacityToken object) : Nat := by
  classical
  exact ((object.portPairSchedule threshold).filter fun pair =>
    extCharge LengthOK data pair = some t).card

/-- `Π_free^ext`: scheduled pairs with no extended charge. -/
noncomputable def extFree : Finset (Finset (object.Vertex × object.Vertex)) := by
  classical
  exact (object.portPairSchedule threshold).filter fun pair => extCharge LengthOK data pair = none

/-- **Partition**: `|Π(𝒜₀)| = Σ_{t∈𝔗_ext} load_ext(t) + |Π_free^ext|`. -/
theorem extPartition :
    (object.portPairSchedule threshold).card =
      ∑ t ∈ data.tokens, extLoad LengthOK data t + (extFree LengthOK data).card := by
  classical
  set S := object.portPairSchedule threshold
  have split := Finset.card_filter_add_card_filter_not (s := S)
    (fun pair => (extCharge LengthOK data pair).isSome)
  have bu : (S.filter fun pair => (extCharge LengthOK data pair).isSome) =
      data.tokens.biUnion (fun t => S.filter fun pair => extCharge LengthOK data pair = some t) := by
    ext pair
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h2
      exact ⟨t, extCharge_mem_tokens LengthOK data h1 ht, h1, ht⟩
    · rintro ⟨t, -, h1, ht⟩
      exact ⟨h1, by rw [ht]; rfl⟩
  have cb : (S.filter fun pair => (extCharge LengthOK data pair).isSome).card =
      ∑ t ∈ data.tokens, extLoad LengthOK data t := by
    rw [bu, Finset.card_biUnion]
    · rfl
    · intro t _ t' _ htt'
      rw [Function.onFun, Finset.disjoint_left]
      intro pair h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact htt' (Option.some_injective _ (h1.2.symm.trans h2.2))
  have cf : (S.filter fun pair => ¬ (extCharge LengthOK data pair).isSome).card =
      (extFree LengthOK data).card := by
    unfold extFree; congr 1; ext pair; simp [S]
  omega

/-- **Extended free side is empty** under extended coverage. -/
theorem extFree_eq_empty
    (cover : ∀ pair ∈ object.portPairSchedule threshold,
      (data.activation.blockers pair).Nonempty ∨ CentreShoulderBlocks LengthOK object pair ∨
        TriangularBlocks object pair) :
    extFree LengthOK data = ∅ := by
  classical
  unfold extFree
  refine Finset.filter_eq_empty_iff.2 fun pair hpair h => ?_
  rcases hc : FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair
    with _ | t
  · rw [extCharge_of_none LengthOK data hc] at h
    rcases cover pair hpair with blk | hg | hh
    · have := FiniteObject.isSome_capacityCharge data.activation data.carrier threshold
        data.packing blk (data.carrierComplete pair hpair)
      rw [hc] at this; exact Bool.false_ne_true this
    · rw [dif_pos hg] at h; cases h
    · by_cases hg : CentreShoulderBlocks LengthOK object pair
      · rw [dif_pos hg] at h; cases h
      · rw [dif_neg hg, dif_pos hh] at h; cases h
  · rw [extCharge_of_old LengthOK data hc] at h; cases h

end Hypostructure.Graph.CapacityFreeSide
