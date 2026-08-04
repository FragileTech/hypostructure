import Mathlib

/-!
# Sobolev-graded solution operator for the Helmholtz operator

The framework's second solution-library entry, and the first that works in
any dimension.

`PDE/Solution/Interval.lean` provides the one-dimensional entry for
`d²/dx²`, built by hand from the fundamental theorem of calculus.  This
module provides the analogue for `1 − (2π)⁻² Δ` on tempered distributions,
where mathlib already supplies both halves:

* `besselPotential 2` is the operator, and it lowers the Sobolev grade by two;
* `besselPotential (-2)` is its exact inverse, and it raises the grade by two.

Both facts come straight from
`memSobolev_besselPotential_iff` and `besselPotential_besselPotential_apply`,
so nothing analytic is assumed here and nothing is proved twice.

The grading is the point.  A solution operator is only worth having if it
gains regularity, and here that gain is carried by the *type*: `potential`
goes from `sobolev s` to `sobolev (s + 2)`, so an entry that gains nothing
cannot be written in its place.
-/

namespace Hypostructure.PDE.Solution.Bessel

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

variable {Point Value : Type*}
  [NormedAddCommGroup Point] [NormedAddCommGroup Value]
  [InnerProductSpace ℝ Point] [FiniteDimensional ℝ Point]
  [MeasurableSpace Point] [BorelSpace Point]
  [NormedSpace ℂ Value] [CompleteSpace Value]

/-! ## The graded carrier -/

/-- The Sobolev space of order `grade`, as an additive subgroup of the
tempered distributions.  This is the graded carrier the elliptic split
consumes. -/
def sobolev (grade : ℝ) : AddSubgroup 𝓢'(Point, Value) where
  carrier := {value | MemSobolev grade 2 value}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact MemSobolev.add ha hb
  zero_mem' := by
    show MemSobolev grade 2 (0 : 𝓢'(Point, Value))
    apply memSobolev_fun_zero
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact MemSobolev.neg ha

@[simp] theorem mem_sobolev {grade : ℝ} {value : 𝓢'(Point, Value)} :
    value ∈ sobolev grade ↔ MemSobolev grade 2 value := Iff.rfl

/-! ## The operator and its exact inverse

`besselPotential r` shifts the Sobolev grade by `r`, which
`memSobolev_besselPotential_iff` states exactly.  Instantiating it at
`r = 2` and `r = -2` gives the two halves of the entry. -/

theorem memSobolev_besselPotential_two {grade : ℝ} {value : 𝓢'(Point, Value)}
    (member : MemSobolev (grade + 2) 2 value) :
    MemSobolev grade 2 (besselPotential Point Value 2 value) := by
  rw [memSobolev_besselPotential_iff]
  simpa [add_comm] using member

theorem memSobolev_besselPotential_neg_two {grade : ℝ}
    {value : 𝓢'(Point, Value)} (member : MemSobolev grade 2 value) :
    MemSobolev (grade + 2) 2 (besselPotential Point Value (-2) value) := by
  rw [memSobolev_besselPotential_iff]
  simpa using member

/-- The Helmholtz operator `1 − (2π)⁻² Δ`, lowering the grade by two. -/
noncomputable def helmholtz (grade : ℝ) :
    sobolev (Point := Point) (Value := Value) (grade + 2) →+
      sobolev (Point := Point) (Value := Value) grade where
  toFun value :=
    ⟨besselPotential Point Value 2 value.val,
      memSobolev_besselPotential_two value.2⟩
  map_zero' := by
    apply Subtype.ext
    show besselPotential Point Value 2 (0 : 𝓢'(Point, Value)) = 0
    simp
  map_add' := by
    intro a b
    apply Subtype.ext
    show besselPotential Point Value 2 (a.val + b.val) =
      besselPotential Point Value 2 a.val + besselPotential Point Value 2 b.val
    simp

/-- The Bessel potential, raising the grade by two.  This is the solution
operator: its type is the guarantee that it gains regularity. -/
noncomputable def potential (grade : ℝ) :
    sobolev (Point := Point) (Value := Value) grade →+
      sobolev (Point := Point) (Value := Value) (grade + 2) where
  toFun value :=
    ⟨besselPotential Point Value (-2) value.val,
      memSobolev_besselPotential_neg_two value.2⟩
  map_zero' := by
    apply Subtype.ext
    show besselPotential Point Value (-2) (0 : 𝓢'(Point, Value)) = 0
    simp
  map_add' := by
    intro a b
    apply Subtype.ext
    show besselPotential Point Value (-2) (a.val + b.val) =
      besselPotential Point Value (-2) a.val +
        besselPotential Point Value (-2) b.val
    simp

/--
The solution law: the Helmholtz operator undoes the Bessel potential exactly.

This is the entry's whole content, and mathlib proves it — composition of
Bessel potentials adds their orders, and order zero is the identity.
-/
theorem helmholtz_potential (grade : ℝ)
    (value : sobolev (Point := Point) (Value := Value) grade) :
    helmholtz grade (potential grade value) = value := by
  apply Subtype.ext
  show besselPotential Point Value 2
      (besselPotential Point Value (-2) value.val) = value.val
  rw [besselPotential_besselPotential_apply]
  norm_num

end Hypostructure.PDE.Solution.Bessel
