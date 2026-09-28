import Hypostructure.Graph.CapacityFreeSide.ExtendedCharge
/-!
# Loads of the extended charge on port tokens

`newLoad(p)`: pairs the old charge leaves uncharged and `Θ_ext` puts on the port
token `p`.  From structure:

* (g) part: `≤ #{q ∈ 𝒜₀ : c(p) ∼ x_q, c(q) ≠ c(p)} ≤ |H| − 1` (`C₄`-freeness:
  `q ↦ c(q)` is injective, two `q` with one centre `h'` give `c(p) x_q h' x_{q'}`);
* (h) part: `≤ |𝒜₀|`, and `0` unless `p` is a triangular port.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold order : Nat}

/-- The triangle certificate of a single port (the body of an (h) blocker). -/
def TriPortAt (object : FiniteObject.{u}) (p : object.Vertex × object.Vertex) : Prop :=
  ∃ a b : object.Vertex,
    object.graph.Adj p.1 p.2 ∧ object.graph.Adj p.2 a ∧ object.graph.Adj p.2 b ∧
    object.graph.Adj a b ∧ a ≠ p.1 ∧ b ≠ p.1 ∧
    (∀ o, object.graph.Adj p.2 o → o = p.1 ∨ o = a ∨ o = b) ∧
    ¬ object.graph.Adj p.1 a ∧ ¬ object.graph.Adj p.1 b

variable (LengthOK : Nat → Prop) (data : CapacityPresentation object threshold order)

/-- `newLoad(p)`. -/
noncomputable def newLoad (p : object.Vertex × object.Vertex) : Nat := by
  classical
  exact ((object.portPairSchedule threshold).filter fun pair =>
    FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair = none ∧
      extCharge LengthOK data pair = some (portToken p)).card

open Classical in
theorem newLoad_le (p : object.Vertex × object.Vertex) :
    newLoad LengthOK data p ≤
      ((object.excessPorts threshold).filter fun (q : object.Vertex × object.Vertex) =>
          object.graph.Adj p.1 q.2 ∧ q.1 ≠ p.1).card +
        (if TriPortAt object p then (object.excessPorts threshold).card else 0) := by
  classical
  set P := object.excessPorts threshold
  let A := (P.filter fun q => object.graph.Adj p.1 q.2 ∧ q.1 ≠ p.1).image
    (fun q => ({p, q} : Finset (object.Vertex × object.Vertex)))
  let B := if TriPortAt object p then P.image
    (fun q => ({p, q} : Finset (object.Vertex × object.Vertex))) else ∅
  have sub : ((object.portPairSchedule threshold).filter fun pair =>
      FiniteObject.capacityCharge data.activation data.carrier threshold data.packing pair = none ∧
        extCharge LengthOK data pair = some (portToken p)) ⊆ A ∪ B := by
    intro pair hpair
    simp only [Finset.mem_filter] at hpair
    obtain ⟨sched, hnone, hch⟩ := hpair
    have subP := object.subset_excessPorts_of_mem_portPairSchedule threshold sched
    rw [extCharge_of_none LengthOK data hnone] at hch
    split_ifs at hch with hg hh
    · -- (g)
      have e : (hg.choose.center, hg.choose.vertex) = p := by
        simpa [portToken] using hch
      obtain ⟨c₂, hiff, hl, -⟩ := hg.choose_spec
      set q := (c₂.center, c₂.vertex)
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨q, ?_, ?_⟩)
      · refine Finset.mem_filter.2 ⟨subP ((hiff q).2 (Or.inr rfl)), ?_, ?_⟩
        · rw [← e]; show object.graph.Adj hg.choose.center c₂.vertex
          rw [← hl]; exact c₂.vertex_left.symm
        · rw [← e]; show c₂.center ≠ hg.choose.center
          rw [← hl]; exact c₂.center_ne_left
      · ext x; rw [hiff, e]; simp [q]
    · -- (h)
      have e : hh.choose = p := by simpa [portToken] using hch
      obtain ⟨pm, a, b, tri⟩ := hh.choose_spec
      rw [e] at pm tri
      obtain ⟨p', q', hp', hq', hpq', hmem⟩ := pair_of_schedule sched
      have tp : TriPortAt object p := ⟨a, b, tri⟩
      refine Finset.mem_union_right _ ?_
      simp only [B, if_pos tp]
      rcases (hmem p).1 pm with rfl | rfl
      · exact Finset.mem_image.2 ⟨q', hq', by ext x; rw [hmem]; simp⟩
      · exact Finset.mem_image.2 ⟨p', hp', by ext x; rw [hmem]; simp; tauto⟩
  unfold newLoad
  refine (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans ?_)
  refine add_le_add Finset.card_image_le ?_
  by_cases tp : TriPortAt object p
  · simp only [B, if_pos tp]; exact Finset.card_image_le
  · simp [B, if_neg tp]

open Classical in
/-- **`C₄` hub injection**: `#{q ∈ 𝒜₀ : c(p) ∼ x_q, c(q) ≠ c(p)} ≤ |H| − 1`. -/
theorem adjEndpoint_le {LengthOK : Nat → Prop} (hL4 : LengthOK 4)
    (noC4 : ¬ HasCycleWithLength LengthOK object) (v : object.Vertex) :
    letI : FinEnum object.Vertex := object.vertices
    ((object.excessPorts threshold).filter fun (q : object.Vertex × object.Vertex) =>
        object.graph.Adj v q.2 ∧ q.1 ≠ v).card ≤
      ((Finset.univ.filter fun w => object.degree w ≠ threshold).erase v).card := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    have high := FiniteObject.centre_high_of_mem_excessPorts hq.1
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨by omega, hq.2.2⟩
  · intro q hq q' hq' e
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
    obtain ⟨hq, a1, n1⟩ := hq
    obtain ⟨hq', a1', -⟩ := hq'
    have adj := FiniteObject.adj_of_mem_excessPorts hq
    have adj' := FiniteObject.adj_of_mem_excessPorts hq'
    by_contra hne
    have hx : q.2 ≠ q'.2 := fun hx => hne (Prod.ext e hx)
    apply noC4
    exact FiniteObject.hasC4_of_square hL4 (x := v) (y := q.1) (z := q.2) (w := q'.2)
      n1.symm (object.graph.ne_of_adj a1) (object.graph.ne_of_adj a1')
      (object.graph.ne_of_adj adj) (e ▸ object.graph.ne_of_adj adj') hx
      a1 adj.symm (e ▸ adj') a1'.symm

end Hypostructure.Graph.CapacityFreeSide
