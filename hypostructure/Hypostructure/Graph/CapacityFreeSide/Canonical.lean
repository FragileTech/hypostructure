import Hypostructure.Graph.CapacityFreeSide.Witness

/-!
# The canonical chord blocker of a separated pair is its earlier singleton

`chordObstructions π` lists the obstruction chord sets in the order of
`lexicographicSublists` of the insertion-sorted ports.  Every obstruction chord
set of `π = {p,q}` is a nonempty subset of `π`; among the sublists whose support
is a nonempty subset of `{p,q}`, the first one is `[p]` when `p` precedes `q`.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

open Classical in
/-- In `lexicographicSublists (A ++ p :: B)` with `q ∉ A`, the first nonempty
sublist supported in `{p,q}` is `[p]`. -/
theorem lexSublists_first (p q : object.Vertex × object.Vertex) :
    ∀ (A B : List (object.Vertex × object.Vertex)), q ∉ A →
      ((pairResponseActivation.lexicographicSublists (A ++ p :: B)).filter
        (fun s => decide (s ≠ [] ∧ ∀ x ∈ s, x = p ∨ x = q))).head? = some [p] := by
  set P : List (object.Vertex × object.Vertex) → Bool :=
    fun s => decide (s ≠ [] ∧ ∀ x ∈ s, x = p ∨ x = q) with hP
  have hnil : P [] = false := by simp [P]
  have hp1 : P [p] = true := by simp only [P, decide_eq_true_eq]; exact ⟨List.cons_ne_nil _ _, fun x hx => Or.inl (List.mem_singleton.1 hx)⟩
  have start : ∀ T : List (object.Vertex × object.Vertex),
      ((pairResponseActivation.lexicographicSublists (p :: T)).filter
        (fun s => decide (s ≠ [] ∧ ∀ x ∈ s, x = p ∨ x = q))).head? = some [p] := by
    intro T
    obtain ⟨rest, hr⟩ := lexSublists_head (object := object) T
    rw [pairResponseActivation.lexicographicSublists.eq_2, hr, List.filter_cons_of_neg (p := P)
      (by rw [hnil]; exact Bool.false_ne_true), List.map_cons, List.cons_append,
      List.filter_cons_of_pos (p := P) hp1]
    rfl
  intro A
  induction A with
  | nil => intro B _; exact start B
  | cons h A ih =>
    intro B hq
    have hhq : h ≠ q := fun e => hq (e ▸ List.mem_cons_self)
    have hqA : q ∉ A := fun m => hq (List.mem_cons_of_mem _ m)
    by_cases hp : h = p
    · subst hp; exact start _
    · have ih' := ih B hqA
      rw [List.cons_append, pairResponseActivation.lexicographicSublists.eq_2]
      obtain ⟨rest, hr⟩ := lexSublists_head (object := object) (A ++ p :: B)
      rw [hr, List.filter_cons_of_neg (p := P) (by rw [hnil]; exact Bool.false_ne_true)] at ih'
      rw [hr, List.filter_cons_of_neg (p := P) (by rw [hnil]; exact Bool.false_ne_true),
        List.tail_cons, List.filter_append]
      have hmap : (List.map (fun x => h :: x) ([] :: rest)).filter P = [] := by
        rw [List.filter_eq_nil_iff]
        intro s hs
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hs
        simp only [P, decide_eq_true_eq, not_and, not_forall]
        intro _
        exact ⟨h, List.mem_cons_self, by tauto⟩
      rw [hmap, List.nil_append]
      exact ih'

/-- Transfer of "first element" through a map when the target predicate implies
the source predicate. -/
theorem head_filter_map {α β : Type*} (g : α → β) (P : α → Bool) (Q : β → Bool)
    (hQP : ∀ a, Q (g a) = true → P a = true) :
    ∀ (l : List α) (a₀ : α), (l.filter P).head? = some a₀ → Q (g a₀) = true →
      ((l.map g).filter Q).head? = some (g a₀)
  | [], _, h, _ => by simp at h
  | a :: l, a₀, h, hq => by
      by_cases hPa : P a = true
      · rw [List.filter_cons_of_pos hPa] at h
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        simp [hq]
      · rw [List.filter_cons_of_neg hPa] at h
        have hQa : ¬ Q (g a) = true := fun hq' => hPa (hQP a hq')
        rw [List.map_cons, List.filter_cons_of_neg hQa]
        exact head_filter_map g P Q hQP l a₀ h hq

variable {threshold : Nat} {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- The ports in chord order: the list whose sublists enumerate the chord sets. -/
noncomputable def chordOrder
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    List (object.Vertex × object.Vertex) := by
  classical
  exact List.insertionSort
    (fun left right =>
      ((min (List.idxOf (pairResponseChordEnds active left).1 object.orderedVertices)
                    (List.idxOf (pairResponseChordEnds active left).2 object.orderedVertices) *
                  (object.orderedVertices.length + 1) +
                max (List.idxOf (pairResponseChordEnds active left).1 object.orderedVertices)
                  (List.idxOf (pairResponseChordEnds active left).2 object.orderedVertices)) *
              (object.orderedVertices.length + 1) +
            List.idxOf left.1 object.orderedVertices) *
          (object.orderedVertices.length + 1) +
        List.idxOf left.2 object.orderedVertices ≤
      ((min (List.idxOf (pairResponseChordEnds active right).1 object.orderedVertices)
                    (List.idxOf (pairResponseChordEnds active right).2 object.orderedVertices) *
                  (object.orderedVertices.length + 1) +
                max (List.idxOf (pairResponseChordEnds active right).1 object.orderedVertices)
                  (List.idxOf (pairResponseChordEnds active right).2 object.orderedVertices)) *
              (object.orderedVertices.length + 1) +
            List.idxOf right.1 object.orderedVertices) *
          (object.orderedVertices.length + 1) +
        List.idxOf right.2 object.orderedVertices)
    (List.flatMap
      (fun centre =>
        List.map (fun endpoint => (centre, endpoint)) (object.selectedPortEndpoints threshold centre))
      object.orderedVertices)

/-- **The first chord obstruction of `{p,q}` is `{p}`** when `{p}` is one, `p`
precedes `q` in chord order (`chordOrder = A ++ p :: B`, `q ∉ A`), and `G` has
no accepted cycle. -/
theorem chordObstructions_head
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    {p q : object.Vertex × object.Vertex} {pair : Finset (object.Vertex × object.Vertex)}
    (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (A B : List (object.Vertex × object.Vertex)) (hL : chordOrder active = A ++ p :: B)
    (hqA : q ∉ A)
    (single : ({p} : Finset (object.Vertex × object.Vertex)) ∈
      (pairResponseActivation active).chordObstructions pair) :
    ((pairResponseActivation active).chordObstructions pair).head? = some {p} := by
  classical
  have mem := single
  unfold pairResponseActivation at mem ⊢
  dsimp only at mem ⊢
  rw [List.filter_filter]
  unfold chordOrder at hL
  rw [hL] at mem ⊢
  have key := head_filter_map (g := List.toFinset)
    (P := fun s => decide (s ≠ [] ∧ ∀ x ∈ s, x = p ∨ x = q))
    (Q := fun chords => decide (SparsePairSuppressionChordObstruction active pair chords) &&
      decide (chords ∈ (object.excessPorts threshold).powerset)) ?_
    _ [p] (lexSublists_first p q A B hqA) ?_
  · have e1 : [p].toFinset = ({p} : Finset (object.Vertex × object.Vertex)) := by simp
    rw [e1] at key; exact key
  · intro s hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
    obtain ⟨obs, -⟩ := hs
    have sub := chords_subset_pair_of_suppressionObstruction obs
    obtain ⟨-, family, cert, -, -, used⟩ := obs
    have ne := family.usedChords_nonempty_of_avoids avoids cert
    simp only [decide_eq_true_eq]
    refine ⟨fun h => ?_, fun x hx => (hpair x).1 (sub (by simpa using hx))⟩
    subst h
    have hne := ne.image (fun index => ((family.configuration index).center,
      (family.configuration index).vertex))
    rw [used] at hne
    simp at hne
  · have m1 := List.mem_filter.1 mem
    have m2 := List.mem_filter.1 m1.1
    have e1 : [p].toFinset = ({p} : Finset (object.Vertex × object.Vertex)) := by simp
    rw [e1]
    simp only [Bool.and_eq_true]
    exact ⟨m1.2, m2.2⟩

end Hypostructure.Graph.CapacityFreeSide
