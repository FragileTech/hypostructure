import Hypostructure.Graph.CapacityFreeSide.Congestion

/-!
# Separated pairs are blocked only by target responses or chord sets

Vocabulary-free.  On a pair with disjoint declared supports and disjoint returns, every
blocker of the recorded activation of an active family is of kind (e) or (f)
(`sep_blockers_kind`).
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

/-- On a pair with disjoint declared supports and disjoint returns, every blocker
of the recorded activation is of kind (e) or (f). -/
theorem sep_blockers_kind {object : Graph.FiniteObject.{u}} {threshold order : Nat}
    {Baseline Target : Graph.FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    (active : Graph.ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : Graph.CapacityPresentation object threshold order)
    (hact : data.activation = Graph.recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (Graph.pairResponseActivation active)
      (object.portPairSchedule threshold))
    {p q : object.Vertex × object.Vertex} (hp : p ∈ object.excessPorts threshold)
    {pair : Finset (object.Vertex × object.Vertex)} (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (dD : Disjoint ((Graph.pairResponseActivation active).declaredSupport p)
      ((Graph.pairResponseActivation active).declaredSupport q))
    (dR : Disjoint ((Graph.pairResponseActivation active).returnSupport p)
      ((Graph.pairResponseActivation active).returnSupport q)) :
    ∀ b ∈ data.activation.blockers pair,
      b.kind = SameTokenBlockerRoles.BlockerKind.targetResponse ∨
        b.kind = SameTokenBlockerRoles.BlockerKind.arithmeticChordSet := by
  classical
  have declEq : data.activation.declaredSupport =
      (Graph.pairResponseActivation active).declaredSupport := by rw [hact]; rfl
  have retEq : data.activation.returnSupport =
      (Graph.pairResponseActivation active).returnSupport := by rw [hact]; rfl
  have bufEq : data.activation.localBuffer =
      (Graph.pairResponseActivation active).localBuffer := by rw [hact]; rfl
  have profEmpty : ∀ c, c ∉ data.activation.profileObstructions pair := by
    intro c hc
    rw [hact] at hc
    have := Graph.coordinate_eq_of_mem_recordedProfileObstructions _ _ hc
    simp only [Graph.recordSparsePairDEBlockers] at hc
    split at hc
    · exact Graph.not_sparsePairDEProfileObstructionAt _ _ _ ‹_›
    · simp at hc
  have sep : ∀ l ∈ pair, ∀ r ∈ pair, l ≠ r → ∀ {X : _ → Finset object.Vertex},
      Disjoint (X p) (X q) → Disjoint (X l) (X r) := by
    intro l hl r hr hlr X h
    rcases (hpair l).1 hl with rfl | rfl <;> rcases (hpair r).1 hr with rfl | rfl
    · exact (hlr rfl).elim
    · exact h
    · exact h.symm
    · exact (hlr rfl).elim
  intro b hb
  cases b with
  | sharedDeclaredSupport item =>
      exfalso
      obtain ⟨l, hl, r, hr, hlr, hsh⟩ :=
        (Graph.FiniteObject.DemandActivation.sharedDeclaredSupport_mem_blockers_iff _).1 hb
      rw [declEq] at hsh
      have d := sep l hl r hr hlr (X := (Graph.pairResponseActivation active).declaredSupport) dD
      cases item with
      | vertex v =>
          obtain ⟨h1, h2⟩ := Graph.FiniteObject.DemandActivation.mem_both_of_vertex_mem_sharedItems hsh
          exact Finset.disjoint_left.1 d h1 h2
      | incidence e =>
          obtain ⟨h1, -, h2, -⟩ :=
            Graph.FiniteObject.DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hsh
          exact Finset.disjoint_left.1 d h1 h2
  | sharedReturnSupport item =>
      exfalso
      obtain ⟨l, hl, r, hr, hlr, hsh⟩ :=
        (Graph.FiniteObject.DemandActivation.sharedReturnSupport_mem_blockers_iff _).1 hb
      rw [retEq] at hsh
      have d := sep l hl r hr hlr (X := (Graph.pairResponseActivation active).returnSupport) dR
      cases item with
      | vertex v =>
          obtain ⟨h1, h2⟩ := Graph.FiniteObject.DemandActivation.mem_both_of_vertex_mem_sharedItems hsh
          exact Finset.disjoint_left.1 d h1 h2
      | incidence e =>
          obtain ⟨h1, -, h2, -⟩ :=
            Graph.FiniteObject.DemandActivation.endpoints_mem_both_of_incidence_mem_sharedItems hsh
          exact Finset.disjoint_left.1 d h1 h2
  | sharedLocalBuffer v =>
      exfalso
      obtain ⟨l, hl, r, hr, hlr, h1, h2⟩ :=
        (Graph.FiniteObject.DemandActivation.sharedLocalBuffer_mem_blockers_iff _).1 hb
      have d := sep l hl r hr hlr (X := (Graph.pairResponseActivation active).declaredSupport) dD
      rw [bufEq] at h1 h2
      exact Finset.disjoint_left.1 d
        (Graph.FiniteObject.DemandActivation.localBuffer_subset_declaredSupport _ _ h1)
        (Graph.FiniteObject.DemandActivation.localBuffer_subset_declaredSupport _ _ h2)
  | boundaryProfile c =>
      exfalso
      exact profEmpty c (by simpa [Graph.FiniteObject.DemandActivation.blockers] using hb)
  | targetResponse c => exact Or.inl rfl
  | arithmeticChordSet s => exact Or.inr rfl

end Hypostructure.Graph.CapacityFreeSide
