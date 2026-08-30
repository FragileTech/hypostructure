import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite relabelling-orbit counting

Small proof-agnostic cardinality lemmas for counting a finite class that is
closed under relabelling.  The statements deliberately stop at exact natural
number inequalities: application-specific entropy estimates and asymptotic
arithmetic belong to the atomic strategy row that consumes them.
-/

namespace Hypostructure.Core.FiniteRelabelingOrbit

universe u v w

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- If a set contains the orbit of `x`, its cardinality, multiplied by the
cardinality of the stabilizer of `x`, covers the acting group.  This is the
division-free form of the orbit lower bound used in relabelling arguments. -/
theorem card_group_le_card_mul_card_stabilizer
    [Finite G] [Finite X] (x : X) (accepted : Set X)
    (orbit_subset : MulAction.orbit G x ⊆ accepted) :
    Nat.card G ≤ Nat.card accepted * Nat.card (MulAction.stabilizer G x) := by
  classical
  have orbitCard :
      Nat.card (MulAction.orbit G x) ≤ Nat.card accepted :=
    Nat.card_le_card_of_injective
      (fun y : MulAction.orbit G x =>
        (⟨y.1, orbit_subset y.2⟩ : accepted))
      (fun left right equal => by
        apply Subtype.ext
        exact congrArg (fun z : accepted => z.1) equal)
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)]
  rw [Nat.card_prod]
  exact Nat.mul_le_mul_right _ orbitCard

/-- A relabelling-invariant fibre contains the entire orbit of each of its
points.  This packages only that elementary inclusion, leaving the choice of
state map and group to the caller. -/
theorem orbit_subset_fibre_of_invariant
    {State : Type w} (state : X → State) (x : X)
    (invariant : ∀ g : G, state (g • x) = state x) :
    MulAction.orbit G x ⊆ {y | state y = state x} := by
  rintro y ⟨g, rfl⟩
  exact invariant g

/-- Exact division-free lower bound for a relabelling-invariant fibre. -/
theorem card_group_le_fibre_card_mul_card_stabilizer
    [Finite G] [Finite X] {State : Type w} (state : X → State) (x : X)
    (invariant : ∀ g : G, state (g • x) = state x) :
    Nat.card G ≤
      Nat.card {y | state y = state x} *
        Nat.card (MulAction.stabilizer G x) :=
  card_group_le_card_mul_card_stabilizer x _
    (orbit_subset_fibre_of_invariant state x invariant)

/-- A finite family of symmetries is bounded by a permutation of its component
indices together with one local code on each component.  Graph-specific work
only has to construct the injective encoding and bound each local-code type. -/
theorem card_le_factorial_mul_prod_of_component_encoding
    {Symmetry : Type u} {Index : Type v} {LocalCode : Index → Type w}
    [Finite Symmetry] [Fintype Index] [∀ i, Fintype (LocalCode i)]
    (encode : Symmetry → Equiv.Perm Index × (∀ i, LocalCode i))
    (injective : Function.Injective encode) :
    Nat.card Symmetry ≤
      Nat.factorial (Fintype.card Index) *
        ∏ i, Fintype.card (LocalCode i) := by
  classical
  calc
    Nat.card Symmetry ≤
      Nat.card (Equiv.Perm Index × (∀ i, LocalCode i)) :=
      Nat.card_le_card_of_injective encode injective
    _ = Nat.card (Equiv.Perm Index) * Nat.card (∀ i, LocalCode i) :=
      Nat.card_prod _ _
    _ = Nat.factorial (Fintype.card Index) *
          ∏ i, Fintype.card (LocalCode i) := by
      rw [Nat.card_perm]
      have indexCard : Nat.card Index = Fintype.card Index :=
        Nat.card_eq_fintype_card
      have piCard : Nat.card (∀ i, LocalCode i) =
          ∏ i, Fintype.card (LocalCode i) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_pi]
      rw [indexCard, piCard]

/-- Arithmetic endpoint for component encodings: replace every local-code
cardinality by a caller-supplied bound without changing the permutation cost. -/
theorem factorial_mul_prod_mono
    {Index : Type v} [Fintype Index] (localCard localBound : Index → Nat)
    (bounded : ∀ i, localCard i ≤ localBound i) :
    Nat.factorial (Fintype.card Index) * ∏ i, localCard i ≤
      Nat.factorial (Fintype.card Index) * ∏ i, localBound i := by
  exact Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun i _ => bounded i))

/-- Stabilizer-specialized component encoding bound.  An automorphism fixing a
declared support is determined by its permutation of the complementary
components and one local rooted code for each component. -/
theorem card_stabilizer_le_factorial_mul_prod_of_component_encoding
    {Acting : Type u} {Object : Type v} {Index : Type w}
    {LocalCode : Index → Type*}
    [Group Acting] [MulAction Acting Object] [Finite Acting]
    [Fintype Index] [∀ i, Fintype (LocalCode i)]
    (object : Object)
    (encode : MulAction.stabilizer Acting object →
      Equiv.Perm Index × (∀ i, LocalCode i))
    (injective : Function.Injective encode) :
    Nat.card (MulAction.stabilizer Acting object) ≤
      Nat.factorial (Fintype.card Index) *
        ∏ i, Fintype.card (LocalCode i) :=
  card_le_factorial_mul_prod_of_component_encoding encode injective

/-- If every component contributes at least one unit to an additive statistic,
the number of components is at most the total statistic. -/
theorem card_le_sum_of_one_le
    {Index : Type v} [Fintype Index] (weight : Index → Nat)
    (positive : ∀ i, 1 ≤ weight i) :
    Fintype.card Index ≤ ∑ i, weight i := by
  have summed : ∑ _i : Index, 1 ≤ ∑ i, weight i :=
    Finset.sum_le_sum (fun i _ => positive i)
  simpa using summed

/-- Cardinality endpoint for the rooted breadth-first encoding used for
bounded-degree connected structures: one image of the root and one of six
local continuation codes at every point. -/
theorem card_le_card_mul_six_pow_of_rooted_local_encoding
    {Symmetry : Type u} {Point : Type v} [Finite Symmetry] [Finite Point]
    (encode : Symmetry → Point × (Point → Fin 6))
    (injective : Function.Injective encode) :
    Nat.card Symmetry ≤ Nat.card Point * 6 ^ Nat.card Point := by
  calc
    Nat.card Symmetry ≤ Nat.card (Point × (Point → Fin 6)) :=
      Nat.card_le_card_of_injective encode injective
    _ = Nat.card Point * Nat.card (Point → Fin 6) := Nat.card_prod _ _
    _ = Nat.card Point * 6 ^ Nat.card Point := by
      rw [Nat.card_fun, Nat.card_fin]

/-- Exact block lower bound replacing the Stirling estimate in eventual
relabelling-entropy arguments: the final `n - n/2` factorial factors are each
at least `n/2`. -/
theorem half_pow_le_factorial (n : Nat) :
    (n / 2) ^ (n - n / 2) ≤ Nat.factorial n := by
  have block := Nat.factorial_mul_pow_sub_le_factorial (Nat.div_le_self n 2)
  calc
    (n / 2) ^ (n - n / 2) = 1 * (n / 2) ^ (n - n / 2) := by simp
    _ ≤ Nat.factorial (n / 2) * (n / 2) ^ (n - n / 2) :=
      Nat.mul_le_mul_right _ (Nat.factorial_pos _)
    _ ≤ Nat.factorial n := block

/-- Division-free summation of a uniform lower bound over the nonempty fibres
of a finite state map. -/
theorem card_image_mul_le_card_mul_of_fibre_bounds
    {X : Type u} {State : Type v} [DecidableEq State]
    (accepted : Finset X) (state : X → State) (groupBound stabilizerBound : Nat)
    (fibreBound : ∀ value ∈ accepted.image state,
      groupBound ≤
        (accepted.filter fun object => state object = value).card * stabilizerBound) :
    (accepted.image state).card * groupBound ≤
      accepted.card * stabilizerBound := by
  calc
    (accepted.image state).card * groupBound =
        ∑ value ∈ accepted.image state, groupBound := by simp
    _ ≤ ∑ value ∈ accepted.image state,
          (accepted.filter fun object => state object = value).card *
            stabilizerBound := by
      exact Finset.sum_le_sum fun value member => fibreBound value member
    _ = (∑ value ∈ accepted.image state,
          (accepted.filter fun object => state object = value).card) *
            stabilizerBound := by
      exact (Finset.sum_mul (accepted.image state)
        (fun value => (accepted.filter fun object => state object = value).card)
        stabilizerBound).symm
    _ = accepted.card * stabilizerBound := by
      have partition := Finset.card_eq_sum_card_fiberwise
        (s := accepted) (t := accepted.image state)
        (f := state) (by
          intro object member
          exact Finset.mem_image.mpr ⟨object, member, rfl⟩)
      rw [← partition]

/-- Exact invariant-state orbit cap for a finite relabelling-closed family. -/
theorem card_image_mul_card_group_le_card_mul_stabilizerBound
    {G : Type u} {X : Type v} {State : Type w}
    [Group G] [MulAction G X] [Finite G] [Finite X]
    [DecidableEq X] [DecidableEq State]
    (accepted : Finset X) (state : X → State) (stabilizerBound : Nat)
    (closed : ∀ g : G, ∀ object ∈ accepted, g • object ∈ accepted)
    (invariant : ∀ g : G, ∀ object ∈ accepted,
      state (g • object) = state object)
    (bounded : ∀ object ∈ accepted,
      Nat.card (MulAction.stabilizer G object) ≤ stabilizerBound) :
    (accepted.image state).card * Nat.card G ≤
      accepted.card * stabilizerBound := by
  apply card_image_mul_le_card_mul_of_fibre_bounds accepted state
  intro value valueMem
  rcases Finset.mem_image.mp valueMem with ⟨object, objectMem, stateEq⟩
  let fibre : Set X := {candidate | candidate ∈ accepted ∧ state candidate = value}
  have orbitSubset : MulAction.orbit G object ⊆ fibre := by
    rintro candidate ⟨g, rfl⟩
    exact ⟨closed g object objectMem, (invariant g object objectMem).trans stateEq⟩
  have orbitBound := card_group_le_card_mul_card_stabilizer object fibre orbitSubset
  have fibreCard : Nat.card fibre =
      (accepted.filter fun candidate => state candidate = value).card := by
    let equivalence : fibre ≃
        {candidate // candidate ∈
          (accepted.filter fun candidate => state candidate = value)} :=
      { toFun := fun candidate => ⟨candidate.1,
          Finset.mem_filter.mpr candidate.2⟩
        invFun := fun candidate => ⟨candidate.1,
          (Finset.mem_filter.mp candidate.2)⟩
        left_inv := fun candidate => by rfl
        right_inv := fun candidate => by rfl }
    rw [Nat.card_congr equivalence]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [fibreCard] at orbitBound
  exact orbitBound.trans (Nat.mul_le_mul_left _ (bounded object objectMem))

end Hypostructure.Core.FiniteRelabelingOrbit
