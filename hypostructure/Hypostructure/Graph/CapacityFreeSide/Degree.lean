import Hypostructure.Graph.CapacityFreeSide.Free

/-!
# Ports per centre and local buffers

Vocabulary-free.  For an object and a threshold:

* `sAt v = #{p ∈ 𝒜₀ : c(p) = v}`, the selected excess ports centred at `v`; it equals
  `d(v) − δ` (`card_ports_centred`);
* `tauAt`, the triangular selected ports (`a_p b_p` an edge);
* the local buffer `T(q) = {x(q)} ∪ s(q)` of a selected port has at most `3` vertices
  (`card_localBuffer_le`).
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

/-- `s(v) = #{p ∈ 𝒜₀ : c(p) = v}`. -/
noncomputable def sAt (G : Graph.FiniteObject.{u}) (threshold : Nat) (v : G.Vertex) : Nat := by
  classical exact ((G.excessPorts threshold).filter fun p => p.1 = v).card

/-- `τ = #{p ∈ 𝒜₀ : a_p b_p ∈ E(G)}`, the triangular selected ports. -/
noncomputable def tauAt {G : Graph.FiniteObject.{u}} {threshold : Nat}
    (ends : G.Vertex × G.Vertex → G.Vertex × G.Vertex) : Nat := by
  classical exact ((G.excessPorts threshold).filter fun p => G.graph.Adj (ends p).1 (ends p).2).card

/-- `s(v)`: the selected ports centred at `v` number exactly `d_G(v) − δ`. -/
theorem card_ports_centred (G : Graph.FiniteObject.{u}) (threshold : Nat) (v : G.Vertex) :
    sAt G threshold v = G.degree v - threshold := by
  classical
  unfold sAt
  have e : ((G.excessPorts threshold).filter fun p => p.1 = v) =
      (G.selectedPortEndpoints threshold v).toFinset.image (Prod.mk v) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, List.mem_toFinset,
      Graph.FiniteObject.mem_excessPorts_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨b, h, rfl, rfl⟩
    · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨hx, rfl⟩
  rw [e, Finset.card_image_of_injective _ (Prod.mk_right_injective v),
    List.toFinset_card_of_nodup (G.selectedPortEndpoints_nodup v),
    G.selectedPortEndpoints_length]

/-- The local buffer of a port has at most three vertices. -/
theorem card_localBuffer_le {object : Graph.FiniteObject.{u}} {threshold : Nat}
    {Baseline Target : Graph.FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    (active : Graph.ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (q : object.Vertex × object.Vertex) :
    ((pairResponseActivation active).localBuffer q).card ≤ 3 := by
  classical
  letI : DecidableEq object.Vertex := @FinEnum.decEq _ object.vertices
  by_cases hq : q ∈ object.excessPorts threshold
  · rw [pairResponseActivation_localBuffer_of_mem active hq]
    obtain ⟨l, r, iff, -⟩ := active.shoulderPair q hq
    have hs : (object.surplusPortOfMem hq).shoulders ⊆ {l, r} := by
      intro v hv
      rcases (iff v).1 hv with rfl | rfl <;> simp
    unfold Graph.FiniteObject.SurplusPort.support
    calc (insert (object.surplusPortOfMem hq).endpoint
          (object.surplusPortOfMem hq).shoulders).card
        ≤ (object.surplusPortOfMem hq).shoulders.card + 1 := Finset.card_insert_le _ _
      _ ≤ ({l, r} : Finset object.Vertex).card + 1 := by
          have := Finset.card_le_card hs; omega
      _ ≤ 2 + 1 := by have := Finset.card_le_two (a := l) (b := r); omega
  · simp [pairResponseActivation, hq]

end Hypostructure.Graph.CapacityFreeSide
