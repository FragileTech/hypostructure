import Hypostructure.Graph.Strategy.SpineVocabulary

/-!
Diagnostic check of the state-count obstruction definition.

Fix any finite current fibre of joint states. A family is good when some
ordering bounds every next-state image by the budget at every reached prefix.
A cardinality-minimal non-good family must be a singleton. Thus this
definition cannot construct a dependency among several windows. This is not
a producer or a closure of the selected graph's residual.
-/

example {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    (states : Finset (I → V)) (budget : Nat) (family : Finset I) :
    let good : Finset I → Prop := fun selected =>
      ∃ rank : I → Nat, Set.InjOn rank (selected : Set I) ∧
        ∀ coordinate ∈ selected, ∀ reference ∈ states,
          ((states.filter fun candidate =>
            ∀ earlier ∈ selected, rank earlier < rank coordinate →
              candidate earlier = reference earlier).image
                (fun candidate => candidate coordinate)).card ≤ budget
    (¬ good family ∧
      ∀ proper, proper ⊂ family → proper.Nonempty → good proper) →
        ∃ coordinate, family = {coordinate} := by
  classical
  intro good minimal
  have largeMarginal : ∃ coordinate ∈ family,
      budget < (states.image fun candidate => candidate coordinate).card := by
    by_contra noLarge
    push Not at noLarge
    apply minimal.1
    let rank : I → Nat := fun coordinate => (Fintype.equivFin I coordinate).val
    refine ⟨rank, ?_, ?_⟩
    · intro left _ right _ equal
      exact (Fintype.equivFin I).injective (Fin.ext equal)
    · intro coordinate member reference referenceMem
      exact (Finset.card_le_card (Finset.image_subset_image
        (Finset.filter_subset _ _))).trans (noLarge coordinate member)
  obtain ⟨coordinate, member, large⟩ := largeMarginal
  refine ⟨coordinate, ?_⟩
  by_contra different
  have proper : {coordinate} ⊂ family := by
    exact (Finset.ssubset_iff_subset_ne).2
      ⟨Finset.singleton_subset_iff.mpr member, Ne.symm different⟩
  obtain ⟨rank, _injective, bounded⟩ :=
    minimal.2 {coordinate} proper (Finset.singleton_nonempty coordinate)
  have statesNonempty : states.Nonempty := by
    by_contra empty
    have statesEmpty := Finset.not_nonempty_iff_eq_empty.mp empty
    simp [statesEmpty] at large
  obtain ⟨reference, referenceMem⟩ := statesNonempty
  have bound := bounded coordinate (Finset.mem_singleton_self coordinate)
    reference referenceMem
  have whole : (states.filter fun candidate =>
      ∀ earlier ∈ ({coordinate} : Finset I), rank earlier < rank coordinate →
        candidate earlier = reference earlier) = states := by
    ext candidate
    simp
  rw [whole] at bound
  exact Nat.not_le_of_gt large bound

-- Replacing "too many state values" by a failed product bound does not yet
-- produce graph overlap. Two individually uniform tests on separate
-- coordinates can be coupled by the realization domain itself. Both tests
-- here have survival ratio 1/2; jointly the ratio is 1/2 rather than 1/4.
example :
    let domain : Finset (Bool × Bool) := {(false, false), (true, true)}
    let first := domain.filter fun state => state.1 = false
    let second := domain.filter fun state => state.2 = false
    let joint := domain.filter fun state => state.1 = false ∧ state.2 = false
    (domain.image Prod.fst).card = 2 ∧
      (domain.image Prod.snd).card = 2 ∧
      2 * first.card = domain.card ∧
      2 * second.card = domain.card ∧
      domain.card < 4 * joint.card := by
  decide
