import Hypostructure.Graph.Route8HubFree

/-!
# A hub-free copy of `X15` in the remainder lands long on two windows

Let `packing` be a window packing of order `13` with remainder `R`, such that for every packed
`P` no window packing inside `P ∪ R` has two members, and let `S ⊆ R` be closed under
neighbours inside `R` (a union of components of `G[R]`), with all degrees `3` in G, spanning a
copy `e` of `X15`.  For any placement system of the packing:

* every exit of the copy has exactly one neighbour outside `S`; it lies on a packed window
  (`exitLand`);
* on each packed window the landing lemmas of `DensityCert.X15Landing` hold
  (`landings_at`): no three exits land on it, and two exits land at distance `≥ 10`;
* hence each landing of an exit is a clean `11`-landing (`longLanding_of_exit`), and the three
  exits land on at least two distinct windows (`two_le_longLandingWindows`).
-/

namespace Hypostructure.Graph.Route8HubFree

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.DensityCert
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

/-- **The landing lemmas on one packed window.** -/
theorem landings_at {packing : Finset (Finset object.Vertex)}
    (exchange : ∀ P ∈ packing, ∀ W : Finset (Finset object.Vertex),
      object.IsWindowPacking 13 W →
      (∀ T ∈ W, ∀ v ∈ T, v ∈ P ∨ v ∈ object.remainderSupport packing) → W.card ≤ 1)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    {S : Finset object.Vertex} (hSR : S ⊆ object.remainderSupport packing)
    (hdeg : ∀ v ∈ S, object.degree v = 3)
    (e : CG.x15.graph ↪g object.graph) (he : ∀ v, v ∈ S ↔ ∃ i, e i = v)
    {P : Finset object.Vertex} (hP : P ∈ packing) {p : Fin 13 → object.Vertex}
    (hp : LocalRigidity.IsWindowPlacement object P p) (offS : ∀ k, p k ∉ S) :
    (∀ i j k : Fin 13, ∀ a b c : Fin CG.x15.n, a ≠ b → a ≠ c → b ≠ c →
      object.graph.Adj (e a) (p i) → object.graph.Adj (e b) (p j) →
      object.graph.Adj (e c) (p k) → False) ∧
    (∀ a b : Fin CG.x15.n, a ≠ b → ∀ i j : Fin 13,
      object.graph.Adj (e a) (p i) → object.graph.Adj (e b) (p j) →
      10 ≤ Nat.dist i.1 j.1) := by
  letI : FinEnum object.Vertex := object.vertices
  refine x15_exit_landings object.graph S e he p hp.1 hp.2.2 offS
    (fun i k h => exit_of_adj_outside e he hdeg i (offS k) h)
    (fun i k k' h h' => hp.1 (outside_unique e he hdeg i (offS k) (offS k') h h'))
    (fun l _ hl => not_forbiddenLen_of_isCycleList avoid hl) ?_
  intro S₁ T₁ hdisj hS₁ hT₁ h₁ h₂
  have w₁ := inducesWindow_of_isInducedThirteen h₁
  have w₂ := inducesWindow_of_isInducedThirteen h₂
  have hne : S₁ ≠ T₁ := by
    rintro rfl
    have hempty := Finset.disjoint_self_iff_empty _ |>.1 hdisj
    have h13 := w₁.2
    rw [hempty, Finset.card_empty] at h13
    omega
  have hW : object.IsWindowPacking 13 {S₁, T₁} := by
    refine ⟨fun T hT => ?_, fun l hl r hr hlr => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with hT | hT <;> subst hT
      · exact w₁
      · exact w₂
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl hr
      rcases hl with hl | hl <;> rcases hr with hr | hr <;> subst hl <;> subst hr
      · exact absurd rfl hlr
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hlr
  have inside : ∀ T ∈ ({S₁, T₁} : Finset (Finset object.Vertex)), ∀ v ∈ T,
      v ∈ P ∨ v ∈ object.remainderSupport packing := by
    intro T hT v hv
    have hv' : v ∈ S ∨ ∃ k, p k = v := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with hT | hT <;> subst hT
      · exact hS₁ v hv
      · exact hT₁ v hv
    rcases hv' with hvS | ⟨k, rfl⟩
    · exact Or.inr (hSR hvS)
    · exact Or.inl (hp.2.1 k)
  have hcard := exchange P hP {S₁, T₁} hW inside
  rw [Finset.card_pair hne] at hcard
  omega

/-- **Each landing of an exit is a clean `11`-landing.** -/
theorem longLanding_of_exit {S P : Finset object.Vertex}
    (hdeg : ∀ v ∈ S, object.degree v = 3)
    (e : CG.x15.graph ↪g object.graph) (he : ∀ v, v ∈ S ↔ ∃ i, e i = v)
    {p : Fin 13 → object.Vertex} (hp : LocalRigidity.IsWindowPlacement object P p)
    (offS : ∀ k, p k ∉ S)
    (far : ∀ a b : Fin CG.x15.n, a ≠ b → ∀ i j : Fin 13,
      object.graph.Adj (e a) (p i) → object.graph.Adj (e b) (p j) → 10 ≤ Nat.dist i.1 j.1)
    (a : Fin CG.x15.n) (k : Fin 13) (ha : a.1 ∈ x15Exits)
    (hadj : object.graph.Adj (e a) (p k)) :
    PackingExchange.LongLanding object S p k (e a) := by
  obtain ⟨α, hαinj, hαlaw, hαlast⟩ := x15_exit_arm a ha
  refine ⟨11, Or.inl rfl, (he _).2 ⟨a, rfl⟩, hadj, 10, rfl, fun j => e (α j),
    ⟨fun i j h => hαinj (e.injective h), fun j => (he _).2 ⟨α j, rfl⟩,
      fun i j => e.map_adj_iff.trans (hαlaw i j)⟩, ?_, ?_⟩
  · show e (α ⟨10, by omega⟩) = e a
    rw [hαlast]
  · intro j t hdist hadj'
    have hadj₂ : object.graph.Adj (e (α j)) (p t) := hadj'
    by_cases hja : α j = a
    · have hjl : j = Fin.last 10 := hαinj (hja.trans hαlast.symm)
      refine ⟨hjl, ?_⟩
      rw [hja] at hadj₂
      exact hp.1 (outside_unique e he hdeg a (offS t) (offS k) hadj₂ hadj)
    · exfalso
      have h10 := far a (α j) (Ne.symm hja) k t hadj hadj₂
      simp only [Nat.dist] at h10 hdist
      omega

/-- **A copy of `X15` closed in `R` lands long on two windows.** -/
theorem two_le_longLandingWindows_of {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking 13 packing)
    (exchange : ∀ P ∈ packing, ∀ W : Finset (Finset object.Vertex),
      object.IsWindowPacking 13 W →
      (∀ T ∈ W, ∀ v ∈ T, v ∈ P ∨ v ∈ object.remainderSupport packing) → W.card ≤ 1)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (place : Finset object.Vertex → Fin 13 → object.Vertex)
    (hplace : ∀ P ∈ packing, LocalRigidity.IsWindowPlacement object P (place P))
    {S : Finset object.Vertex} (hSR : S ⊆ object.remainderSupport packing)
    (hclosed : ∀ v ∈ S, ∀ w ∈ object.remainderSupport packing, object.graph.Adj v w → w ∈ S)
    (hdeg : ∀ v ∈ S, object.degree v = 3)
    (hemb : EmbOnto CG.x15.graph object.graph S)
    (target : Finset (Finset object.Vertex))
    (htarget : ∀ P ∈ packing, (∃ i x, PackingExchange.LongLanding object S (place P) i x) →
      P ∈ target) :
    2 ≤ target.card := by
  obtain ⟨e, he⟩ := hemb
  have offS : ∀ P ∈ packing, ∀ k, place P k ∉ S := fun P hP k hk =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport (hSR hk)
      (FiniteObject.mem_windowSupport hP ((hplace P hP).2.1 k))
  have exitLand : ∀ a : Fin CG.x15.n, a.1 ∈ x15Exits →
      ∃ P ∈ packing, ∃ k, object.graph.Adj (e a) (place P k) := by
    intro a ha
    obtain ⟨w, hw, hwS⟩ := exists_outside e he hdeg a ha
    have hwR : w ∉ object.remainderSupport packing := fun hwR =>
      hwS (hclosed _ ((he _).2 ⟨a, rfl⟩) w hwR hw)
    obtain ⟨P, hP, hwP⟩ :=
      FiniteObject.exists_mem_packing_of_notMem_remainderSupport object hwR
    obtain ⟨k, hk⟩ := (hplace P hP).surjective (valid.1 P hP).2 w hwP
    exact ⟨P, hP, k, hk ▸ hw⟩
  have mem : ∀ a : Fin CG.x15.n, a.1 ∈ x15Exits → ∀ P ∈ packing, ∀ k,
      object.graph.Adj (e a) (place P k) → P ∈ target := fun a ha P hP k hadj =>
    htarget P hP ⟨k, e a, longLanding_of_exit hdeg e he (hplace P hP) (offS P hP)
      (landings_at exchange avoid hSR hdeg e he hP (hplace P hP) (offS P hP)).2 a k ha hadj⟩
  have n15 : 9 < CG.x15.n := by decide
  obtain ⟨a₁, ha₁⟩ : ∃ a : Fin CG.x15.n, a.1 = 4 := ⟨⟨4, by omega⟩, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a : Fin CG.x15.n, a.1 = 6 := ⟨⟨6, by omega⟩, rfl⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a : Fin CG.x15.n, a.1 = 9 := ⟨⟨9, by omega⟩, rfl⟩
  have h₁ : a₁.1 ∈ x15Exits := by rw [ha₁]; decide
  have h₂ : a₂.1 ∈ x15Exits := by rw [ha₂]; decide
  have h₃ : a₃.1 ∈ x15Exits := by rw [ha₃]; decide
  have d₁₂ : a₁ ≠ a₂ := fun h => by rw [h] at ha₁; omega
  have d₁₃ : a₁ ≠ a₃ := fun h => by rw [h] at ha₁; omega
  have d₂₃ : a₂ ≠ a₃ := fun h => by rw [h] at ha₂; omega
  obtain ⟨P₁, hP₁, k₁, hk₁⟩ := exitLand a₁ h₁
  obtain ⟨P₂, hP₂, k₂, hk₂⟩ := exitLand a₂ h₂
  obtain ⟨P₃, hP₃, k₃, hk₃⟩ := exitLand a₃ h₃
  have m₁ := mem a₁ h₁ P₁ hP₁ k₁ hk₁
  have m₂ := mem a₂ h₂ P₂ hP₂ k₂ hk₂
  have m₃ := mem a₃ h₃ P₃ hP₃ k₃ hk₃
  have two : 1 < target.card := by
    rw [Finset.one_lt_card]
    by_cases e12 : P₁ = P₂
    · by_cases e13 : P₁ = P₃
      · rw [← e12] at hk₂
        rw [← e13] at hk₃
        exact ((landings_at exchange avoid hSR hdeg e he hP₁ (hplace P₁ hP₁)
          (offS P₁ hP₁)).1 k₁ k₂ k₃ a₁ a₂ a₃ d₁₂ d₁₃ d₂₃ hk₁ hk₂ hk₃).elim
      · exact ⟨P₁, m₁, P₃, m₃, e13⟩
    · exact ⟨P₁, m₁, P₂, m₂, e12⟩
  exact two

open Classical in
/-- **A hub-free copy of `X15` in the remainder lands long on two windows**: the component
form, for a window packing of order `n = 13` and any placement system. -/
theorem two_le_longLandingWindows {n : ℕ} (hn : n = 13)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking n packing)
    (exchange : ∀ P ∈ packing, ∀ W : Finset (Finset object.Vertex),
      object.IsWindowPacking n W →
      (∀ T ∈ W, ∀ v ∈ T, v ∈ P ∨ v ∈ object.remainderSupport packing) → W.card ≤ 1)
    (avoid : ¬ HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object)
    (place : Finset object.Vertex → Fin n → object.Vertex)
    (hplace : ∀ P ∈ packing, LocalRigidity.IsWindowPlacement object P (place P))
    (X : SupportComponents.Connected.Component object (object.remainderSupport packing))
    (hdeg : ∀ v ∈ object.pieceSupport (object.remainderSupport packing) X,
      object.degree v = 3)
    (hemb : EmbOnto CG.x15.graph object.graph
      (object.pieceSupport (object.remainderSupport packing) X)) :
    2 ≤ (packing.filter fun P => ∃ i x, PackingExchange.LongLanding object
      (object.pieceSupport (object.remainderSupport packing) X) (place P) i x).card := by
  subst hn
  exact two_le_longLandingWindows_of valid exchange avoid place hplace
    (object.pieceSupport_subset _ X)
    (fun v hv w hw hadj => SupportComponents.Connected.neighbor_mem_vertices object _ X
      (show v ∈ SupportComponents.Connected.vertices object _ X from hv) hw hadj)
    hdeg hemb _ (fun P hP h => Finset.mem_filter.2 ⟨hP, h⟩)

end Hypostructure.Graph.Route8HubFree
