import Hypostructure.Graph.DensityCert.Basic

/-!
# Density certificate: heredity and transport along embeddings

* `AdmIn.mono`: admissibility passes to subsets.
* Transport of `IsIndPath`, `IsCycleList`, `AdmIn`, `degIn`, `dIn`, `lamIn`,
  `LIn`, `ConnIn`, `TwoConnIn` along a graph embedding `e : H ↪g G`, first for
  an arbitrary finset `S` and its image `S.map e`, then for an embedding onto a
  finset `W` (`∀ v, v ∈ W ↔ ∃ i, e i = v`).
* `EmbOnto` is invariant under isomorphism of the source graph.
* Basic induced-path lemmas: reverse, `take`, `drop`, short lists, and the
  length bound `≤ 12` inside an admissible set.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

section Hered

variable {V : Type*} {G : SimpleGraph V}

theorem degIn_mono {W W' : Finset V} (h : W' ⊆ W) (v : V) :
    degIn G W' v ≤ degIn G W v := by
  classical
  unfold degIn
  exact card_le_card (filter_subset_filter _ h)

/-- Heredity of admissibility. -/
theorem AdmIn.mono {W W' : Finset V} (hA : AdmIn G W) (h : W' ⊆ W) : AdmIn G W' := by
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨fun v hv => (degIn_mono h v).trans (h1 v (h hv)), fun l hl => h2 l fun x hx => h (hl x hx),
    fun l hl => h3 l fun x hx => h (hl x hx)⟩

end Hered

section Paths

variable {V : Type*} {G : SimpleGraph V}

theorem IsIndPath.nil : IsIndPath G ([] : List V) := by
  refine ⟨List.nodup_nil, fun i j hi _ => ?_⟩
  simp at hi

theorem IsIndPath.singleton (a : V) : IsIndPath G [a] := by
  refine ⟨List.nodup_singleton a, fun i j hi hj => ?_⟩
  simp only [List.length_singleton] at hi hj
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 0 := by omega
  simp

theorem IsIndPath.pair {a b : V} (h : G.Adj a b) : IsIndPath G [a, b] := by
  refine ⟨by simp [h.ne], fun i j hi hj => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi hj
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [h, h.symm]

theorem IsIndPath.reverse {l : List V} (h : IsIndPath G l) : IsIndPath G l.reverse := by
  refine ⟨List.nodup_reverse.2 h.1, fun i j hi hj => ?_⟩
  simp only [List.length_reverse] at hi hj
  rw [List.getElem_reverse, List.getElem_reverse, h.2 _ _ (by omega) (by omega)]
  omega

theorem isIndPath_reverse_iff {l : List V} : IsIndPath G l.reverse ↔ IsIndPath G l :=
  ⟨fun h => by simpa using h.reverse, fun h => h.reverse⟩

theorem IsIndPath.take {l : List V} (h : IsIndPath G l) (k : ℕ) : IsIndPath G (l.take k) := by
  refine ⟨h.1.sublist (List.take_sublist k l), fun i j hi hj => ?_⟩
  simp only [List.length_take] at hi hj
  rw [List.getElem_take, List.getElem_take]
  exact h.2 _ _ _ _

theorem IsIndPath.drop {l : List V} (h : IsIndPath G l) (k : ℕ) : IsIndPath G (l.drop k) := by
  refine ⟨h.1.sublist (List.drop_sublist k l), fun i j hi hj => ?_⟩
  simp only [List.length_drop] at hi hj
  rw [List.getElem_drop, List.getElem_drop, h.2 _ _ (by omega) (by omega)]
  omega

theorem IsIndPath.infix {l l' : List V} (h : IsIndPath G l) (hl : l' <:+: l) :
    IsIndPath G l' := by
  obtain ⟨a, b, rfl⟩ := hl
  have h1 : IsIndPath G (a ++ l') := by
    have := h.take (a ++ l').length
    rwa [List.take_left] at this
  have := h1.drop a.length
  rwa [List.drop_left] at this

/-- In an admissible set every induced path has at most `12` vertices. -/
theorem AdmIn.length_le {W : Finset V} (hA : AdmIn G W) {l : List V} (hl : ∀ x ∈ l, x ∈ W)
    (hp : IsIndPath G l) : l.length ≤ 12 := by
  by_contra hlt
  push Not at hlt
  apply hA.2.2 (l.take 13) (fun x hx => hl x (List.mem_of_mem_take hx)) (hp.take 13)
  simp only [List.length_take]
  omega

end Paths

section Transport

variable {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}

theorem isIndPath_map_iff (e : H ↪g G) (l : List U) :
    IsIndPath H l ↔ IsIndPath G (l.map e) := by
  unfold IsIndPath
  rw [List.nodup_map_iff e.injective]
  simp only [List.length_map, List.getElem_map, e.map_adj_iff]

theorem isCycleList_map_iff (e : H ↪g G) (l : List U) :
    IsCycleList H l ↔ IsCycleList G (l.map e) := by
  unfold IsCycleList
  rw [List.nodup_map_iff e.injective]
  simp only [List.length_map, List.getElem_map, e.map_adj_iff]

theorem exists_list_map_of_mem (e : H ↪g G) (S : Finset U) (l : List V)
    (hl : ∀ x ∈ l, x ∈ S.map e.toEmbedding) :
    ∃ l' : List U, l = l'.map e ∧ ∀ x ∈ l', x ∈ S := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons a l ih =>
    obtain ⟨l', rfl, hl'⟩ := ih fun x hx => hl x (List.mem_cons_of_mem a hx)
    obtain ⟨b, hb, rfl⟩ := mem_map.1 (hl a List.mem_cons_self)
    refine ⟨b :: l', rfl, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact hl' x hx

theorem degIn_map (e : H ↪g G) (S : Finset U) (u : U) :
    degIn G (S.map e.toEmbedding) (e u) = degIn H S u := by
  unfold degIn
  rw [← card_map e.toEmbedding]
  congr 1
  ext v
  simp only [mem_filter, mem_map, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hadj⟩
    exact ⟨a, ⟨ha, e.map_adj_iff.1 hadj⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hadj⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, e.map_adj_iff.2 hadj⟩

theorem dIn_map (e : H ↪g G) (S : Finset U) :
    dIn G (S.map e.toEmbedding) = dIn H S := by
  unfold dIn
  rw [card_map]
  congr 3
  rw [← card_map (e.toEmbedding.prodMap e.toEmbedding)]
  congr 1
  ext ⟨v, w⟩
  simp only [mem_filter, mem_map, mem_product, Function.Embedding.coe_prodMap,
    RelEmbedding.coe_toEmbedding, Prod.exists, Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hadj⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, e.map_adj_iff.1 hadj⟩, rfl, rfl⟩
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hadj⟩, rfl, rfl⟩
    exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, e.map_adj_iff.2 hadj⟩

theorem admIn_map_iff (e : H ↪g G) (S : Finset U) :
    AdmIn H S ↔ AdmIn G (S.map e.toEmbedding) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, fun l hl hc => ?_, fun l hl hp => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := mem_map.1 hv
      rw [RelEmbedding.coe_toEmbedding, degIn_map]
      exact h1 a ha
    · obtain ⟨l', rfl, hl'⟩ := exists_list_map_of_mem e S l hl
      rw [List.length_map]
      exact h2 l' hl' ((isCycleList_map_iff e l').2 hc)
    · obtain ⟨l', rfl, hl'⟩ := exists_list_map_of_mem e S l hl
      rw [List.length_map]
      exact h3 l' hl' ((isIndPath_map_iff e l').2 hp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun v hv => ?_, fun l hl hc => ?_, fun l hl hp => ?_⟩
    · rw [← degIn_map e]
      exact h1 _ (mem_map_of_mem _ hv)
    · have := h2 (l.map e) (fun x hx => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact mem_map_of_mem e.toEmbedding (hl a ha)) ((isCycleList_map_iff e l).1 hc)
      rwa [List.length_map] at this
    · have := h3 (l.map e) (fun x hx => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact mem_map_of_mem e.toEmbedding (hl a ha)) ((isIndPath_map_iff e l).1 hp)
      rwa [List.length_map] at this

/-- The predicate "an induced path in `S` from `u` with `k` vertices", transported. -/
theorem lamPred_map_iff (e : H ↪g G) (S : Finset U) (u : U) (k : ℕ) :
    (∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ S.map e.toEmbedding) ∧
        l.head? = some (e u) ∧ l.length = k) ↔
      ∃ l : List U, IsIndPath H l ∧ (∀ x ∈ l, x ∈ S) ∧ l.head? = some u ∧ l.length = k := by
  constructor
  · rintro ⟨l, hl, hW, hh, hlen⟩
    obtain ⟨l', rfl, hl'⟩ := exists_list_map_of_mem e S l hW
    refine ⟨l', (isIndPath_map_iff e l').2 hl, hl', ?_, by simpa using hlen⟩
    rw [List.head?_map, Option.map_eq_some_iff] at hh
    obtain ⟨a, ha, hae⟩ := hh
    rwa [e.injective hae] at ha
  · rintro ⟨l, hl, hW, hh, hlen⟩
    refine ⟨l.map e, (isIndPath_map_iff e l).1 hl, fun x hx => ?_, by simp [hh], by simpa using hlen⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact mem_map_of_mem e.toEmbedding (hW a ha)

theorem LPred_map_iff (e : H ↪g G) (S : Finset U) (u u' : U) (k : ℕ) :
    (∃ l : List V, IsIndPath G l ∧ (∀ x ∈ l, x ∈ S.map e.toEmbedding) ∧
        l.head? = some (e u) ∧ l.getLast? = some (e u') ∧ l.length = k) ↔
      ∃ l : List U, IsIndPath H l ∧ (∀ x ∈ l, x ∈ S) ∧ l.head? = some u ∧
        l.getLast? = some u' ∧ l.length = k := by
  constructor
  · rintro ⟨l, hl, hW, hh, ht, hlen⟩
    obtain ⟨l', rfl, hl'⟩ := exists_list_map_of_mem e S l hW
    refine ⟨l', (isIndPath_map_iff e l').2 hl, hl', ?_, ?_, by simpa using hlen⟩
    · rw [List.head?_map, Option.map_eq_some_iff] at hh
      obtain ⟨a, ha, hae⟩ := hh
      rwa [e.injective hae] at ha
    · rw [List.getLast?_map, Option.map_eq_some_iff] at ht
      obtain ⟨a, ha, hae⟩ := ht
      rwa [e.injective hae] at ha
  · rintro ⟨l, hl, hW, hh, ht, hlen⟩
    refine ⟨l.map e, (isIndPath_map_iff e l).1 hl, fun x hx => ?_, by simp [hh], by simp [ht],
      by simpa using hlen⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact mem_map_of_mem e.toEmbedding (hW a ha)

theorem lamIn_map (e : H ↪g G) (S : Finset U) (u : U) :
    lamIn G (S.map e.toEmbedding) (e u) = lamIn H S u := by
  unfold lamIn
  rw [card_map]
  congr 1
  funext k
  exact propext (lamPred_map_iff e S u k)

theorem LIn_map (e : H ↪g G) (S : Finset U) (u u' : U) :
    LIn G (S.map e.toEmbedding) (e u) (e u') = LIn H S u u' := by
  unfold LIn
  rw [card_map]
  congr 1
  funext k
  exact propext (LPred_map_iff e S u u' k)

theorem reachIn_map_of (e : H ↪g G) (S : Finset U) {u v : U} (h : ReachIn H S u v) :
    ReachIn G (S.map e.toEmbedding) (e u) (e v) :=
  Relation.ReflTransGen.lift e (fun _ _ ⟨ha, hb, hab⟩ =>
    ⟨mem_map_of_mem e.toEmbedding ha, mem_map_of_mem e.toEmbedding hb, e.map_adj_iff.2 hab⟩) h

theorem reachIn_of_map (e : H ↪g G) (S : Finset U) {u : U} {b : V}
    (h : ReachIn G (S.map e.toEmbedding) (e u) b) : ∃ w, e w = b ∧ ReachIn H S u w := by
  induction h with
  | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hcb ih =>
    obtain ⟨w, rfl, hw⟩ := ih
    obtain ⟨hc, hb, hadj⟩ := hcb
    obtain ⟨w', hw', rfl⟩ := mem_map.1 hb
    have hc' : w ∈ S := by
      obtain ⟨a, ha, hae⟩ := mem_map.1 hc
      obtain rfl : a = w := e.injective hae
      exact ha
    exact ⟨w', rfl, hw.tail ⟨hc', hw', e.map_adj_iff.1 hadj⟩⟩

theorem reachIn_map_iff (e : H ↪g G) (S : Finset U) (u v : U) :
    ReachIn H S u v ↔ ReachIn G (S.map e.toEmbedding) (e u) (e v) := by
  refine ⟨reachIn_map_of e S, fun h => ?_⟩
  obtain ⟨w, hw, h⟩ := reachIn_of_map e S h
  rwa [← e.injective hw]

theorem connIn_map_iff (e : H ↪g G) (S : Finset U) :
    ConnIn H S ↔ ConnIn G (S.map e.toEmbedding) := by
  unfold ConnIn
  rw [map_nonempty]
  simp only [forall_mem_map, RelEmbedding.coe_toEmbedding, ← reachIn_map_iff]

theorem twoConnIn_map_iff [DecidableEq U] [DecidableEq V] (e : H ↪g G) (S : Finset U) :
    TwoConnIn H S ↔ TwoConnIn G (S.map e.toEmbedding) := by
  unfold TwoConnIn
  simp only [card_map, forall_mem_map, ← connIn_map_iff, RelEmbedding.coe_toEmbedding]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun u _ => ?_))
  rw [connIn_map_iff e, map_erase]
  rfl

/-! ### Embeddings onto a finset -/

variable [Fintype U]

theorem eq_map_of_onto (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) :
    W = univ.map e.toEmbedding := by
  ext v
  simp [hW]

theorem admIn_onto_iff (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) :
    AdmIn H univ ↔ AdmIn G W := by
  rw [eq_map_of_onto e hW]; exact admIn_map_iff e univ

theorem degIn_onto (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) (u : U) :
    degIn H univ u = degIn G W (e u) := by
  rw [eq_map_of_onto e hW, degIn_map]

theorem dIn_onto (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) :
    dIn H univ = dIn G W := by
  rw [eq_map_of_onto e hW, dIn_map]

theorem lamIn_onto (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) (u : U) :
    lamIn H univ u = lamIn G W (e u) := by
  rw [eq_map_of_onto e hW, lamIn_map]

theorem LIn_onto (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) (u u' : U) :
    LIn H univ u u' = LIn G W (e u) (e u') := by
  rw [eq_map_of_onto e hW, LIn_map]

theorem connIn_onto_iff (e : H ↪g G) {W : Finset V} (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) :
    ConnIn H univ ↔ ConnIn G W := by
  rw [eq_map_of_onto e hW]; exact connIn_map_iff e univ

theorem twoConnIn_onto_iff [DecidableEq U] [DecidableEq V] (e : H ↪g G) {W : Finset V}
    (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) : TwoConnIn H univ ↔ TwoConnIn G W := by
  rw [eq_map_of_onto e hW]; exact twoConnIn_map_iff e univ

end Transport

section Iso

variable {U U' V : Type*} {H : SimpleGraph U} {H' : SimpleGraph U'} {G : SimpleGraph V}

/-- Compose an isomorphism `H ≃g H'` with an embedding of `H'` onto `W`. -/
theorem onto_comp_iso (f : H ≃g H') (e : H' ↪g G) {W : Finset V}
    (hW : ∀ v, v ∈ W ↔ ∃ i, e i = v) :
    ∀ v, v ∈ W ↔ ∃ i, (e.comp f.toEmbedding) i = v := by
  intro v
  rw [hW]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f.symm i, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨f i, rfl⟩

theorem EmbOnto.of_iso (f : H ≃g H') {W : Finset V} (h : EmbOnto H' G W) : EmbOnto H G W := by
  obtain ⟨e, hW⟩ := h
  exact ⟨e.comp f.toEmbedding, onto_comp_iso f e hW⟩

theorem EmbOnto.of_iso' (f : H' ≃g H) {W : Finset V} (h : EmbOnto H' G W) : EmbOnto H G W :=
  h.of_iso f.symm

/-- `EmbOnto` of `M.graph` from `EmbOnto` of `M'.graph` and `M.graph ≃g M'.graph`. -/
theorem CG.embOnto_of_iso {M M' : CG} (f : M.graph ≃g M'.graph) {W : Finset V}
    (h : EmbOnto M'.graph G W) : EmbOnto M.graph G W :=
  h.of_iso f

end Iso

section Reach

variable {V : Type*} {G : SimpleGraph V}

theorem reachIn_mono {W W' : Finset V} (hW : W ⊆ W') {a b : V} (h : ReachIn G W a b) :
    ReachIn G W' a b :=
  Relation.ReflTransGen.mono (fun _ _ h' => ⟨hW h'.1, hW h'.2.1, h'.2.2⟩) h

theorem reachIn_symm {W : Finset V} {a b : V} (h : ReachIn G W a b) : ReachIn G W b a := by
  induction h with
  | refl => exact .refl
  | tail _ h' ih => exact Relation.ReflTransGen.head ⟨h'.2.1, h'.1, h'.2.2.symm⟩ ih

theorem reachIn_step {W : Finset V} {a b : V} (ha : a ∈ W) (hb : b ∈ W) (h : G.Adj a b) :
    ReachIn G W a b :=
  Relation.ReflTransGen.single ⟨ha, hb, h⟩

end Reach

end Hypostructure.Graph.DensityCert
