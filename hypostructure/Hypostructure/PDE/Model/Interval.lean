import Hypostructure.PDE.EllipticLocalTail
import Hypostructure.PDE.Solution.Interval

/-!
# Canonical one-dimensional PDE registration

This is the PDE counterpart of `Graph.FiniteObject` / `Graph.problem`.

On the graph side the framework owns the ambient object and the problem
constructor, and an application supplies only a baseline and a branch state.
The same holds here: `Object` is the framework's ambient object, `problem` is
the registration, and `atlas`, `equation`, `model`, `Admissible` and
`ellipticOperator` are all derived.  An application registers a baseline and
a target and nothing else --- in particular it supplies no window, no focus,
no solution operator and no split.

Everything is local: a `Window` carries its own base point, restriction is
the atlas's, and the solution operator is based at the window's endpoint, so
no recentering or change of coordinates is performed by hand.
-/

namespace Hypostructure.PDE.Interval

open Hypostructure
open Hypostructure.PDE.Solution

/-! ## Windows -/

/-- A window of the real line, carrying its own base point. -/
structure Window where
  base : ℝ
  top : ℝ

/-- Membership of a point in a window. -/
def Window.Mem (window : Window) (place : ℝ) : Prop :=
  window.base ≤ place ∧ place ≤ window.top

/-- One window sits inside another. -/
def Window.Nested (small large : Window) : Prop :=
  large.base ≤ small.base ∧ small.top ≤ large.top

theorem Window.nested_refl (window : Window) : window.Nested window :=
  ⟨le_refl _, le_refl _⟩

theorem Window.nested_trans {small middle large : Window}
    (inner : small.Nested middle) (outer : middle.Nested large) :
    small.Nested large :=
  ⟨outer.1.trans inner.1, inner.2.trans outer.2⟩

/-- Membership transfers along nesting: a point of a smaller window is a
point of the larger one.  This is what lets a local fact survive
restriction. -/
theorem Window.Mem.mono {small large : Window} (nested : small.Nested large)
    {place : ℝ} (mem : small.Mem place) : large.Mem place :=
  ⟨nested.1.trans mem.1, mem.2.trans nested.2⟩

/-! ## The ambient object

The model is indexed by the grade of its elliptic source: an object carries a
`C^(grade+2)` function, which is exactly the regularity the second-derivative
operator can act on.  Grading the object rather than fixing it smooth is what
lets `rebuild` be honest --- a local child really can be put back.
-/

variable (grade : ℕ)

/-- The framework's one-dimensional ambient object. -/
structure Object (grade : ℕ) where
  domain : Window
  value : ℝ → ℝ
  smooth : ContDiff ℝ (((grade + 2 : ℕ) : ℕ∞) : WithTop ℕ∞) value

/-- The local reading of an object, at the component's grade. -/
def Object.local' {grade : ℕ} (object : Object grade) :
    contDiffFunctions (grade + 2) :=
  ⟨object.value, object.smooth⟩

/-! ## Registration

`problem` is the exact analogue of `Graph.problem`: an application supplies a
baseline and a branch state, and nothing else. -/

variable (Baseline : Object grade → Prop) (BranchState : Object grade → Type)

/-- Register a one-dimensional PDE problem. -/
def problem : Core.Problem where
  Ambient := Object grade
  Baseline := Baseline
  BranchState := BranchState

/-- The canonical atlas: windows of the line, with the atlas `core` the
identity and restriction the local reading of the object. -/
def atlas : PDE.LocalAtlas (problem grade Baseline BranchState) where
  Point := ℝ
  Window := Window
  contains := fun place window => window.Mem place
  nested := Window.Nested
  nested_refl := Window.nested_refl
  nested_trans := Window.nested_trans
  core := id
  core_nested := Window.nested_refl
  LocalObject := fun _window => contDiffFunctions (grade + 2)
  restrict := fun object _window => object.local'
  restrictLocal := fun _nested value => value
  restrict_refl := fun _window _value => rfl
  restrict_trans := fun _inner _outer _value => rfl
  restrict_global := fun _object _inner _outer _nested => rfl

/--
The represented equation: the second-order equation `u'' = source` on the
window, with the source living one grade below the object.

The source is retained as equation data and validity is the equation itself,
so an `EquationState` carries the actual mathematical fact rather than a
placeholder.  `restrict_satisfies` is the statement that restricting a state
to a smaller window keeps both the source and the equation --- nothing is
discarded when a residual is localized.
-/
def equation : PDE.RepresentedEquation (problem grade Baseline BranchState)
    (atlas grade Baseline BranchState) where
  EquationData := fun _window _value => contDiffFunctions grade
  satisfies := fun {window} {value} source =>
    ∀ place, window.Mem place →
      deriv (deriv value.val) place = source.val place
  restrictEquation := fun {_U} {_V} _nested {_value} source => source
  restrict_satisfies := by
    intro small large nested value source valid place mem
    exact valid place (Window.Mem.mono nested mem)

/-- The canonical one-dimensional local model. -/
def model : PDE.LocalModel where
  problem := problem grade Baseline BranchState
  atlas := atlas grade Baseline BranchState
  equation := equation grade Baseline BranchState

/-! ## Admissibility and the elliptic split -/

/-- A window is a legitimate localization site when it sits inside the
object's own domain. -/
def Admissible (object : Object grade) (window : Window) : Prop :=
  window.Nested object.domain

/--
The canonical elliptic operator of the one-dimensional model.

Every field is derived.  `operator` is the graded second derivative and
`solve` is the graded local solution based at the *window's own* endpoint ---
nothing is recentered by hand, and nothing that fails to gain two grades
could be written in `solve`'s slot.
-/
noncomputable def ellipticOperator :
    PDE.ComponentEllipticOperator (model grade Baseline BranchState)
      (model grade Baseline BranchState) ℕ (Admissible grade)
      (fun _object _window g => contDiffFunctions g) where
  grade := grade
  step := fun g => g + 2
  component := fun object _window => object.local'
  rebuild := fun object _window value =>
    { domain := object.domain, value := value.val, smooth := value.2 }
  rebuild_component := fun _object _window => rfl
  operator := fun _object _window g => secondDerivGraded g
  solve := fun _object window g => solutionOnGraded window.base g
  operator_solve := fun _object window g value =>
    secondDerivGraded_solutionOnGraded window.base g value
  tailWindow := id
  tailObject := fun _object _window _target value => value
  tailData := fun _object _window _target _value =>
    show contDiffFunctions grade from 0
  tailValid := by
    intro _object _window target value homogeneous place _mem
    have zero : deriv (deriv value.val) = 0 :=
      congrArg Subtype.val homogeneous
    show deriv (deriv value.val) place =
      (show contDiffFunctions grade from 0).val place
    rw [zero]
    rfl

/-! ## The equation the residual carries is the one the split reads -/

/-- The elliptic source of the split is exactly the source the equation state
already carries: nothing is recomputed and nothing is discarded. -/
theorem operator_component_eq_source (object : Object grade) (window : Window)
    (source : contDiffFunctions grade)
    (valid : ∀ place, window.Mem place →
      deriv (deriv object.value) place = source.val place) :
    ∀ place, window.Mem place →
      (secondDerivGraded grade object.local').val place = source.val place :=
  valid

/-- Restricting to a nested window keeps the equation, so a localized
residual still knows its own source. -/
theorem satisfies_of_nested {small large : Window} (nested : small.Nested large)
    (object : Object grade) (source : contDiffFunctions grade)
    (valid : ∀ place, large.Mem place →
      deriv (deriv object.value) place = source.val place) :
    ∀ place, small.Mem place →
      deriv (deriv object.value) place = source.val place :=
  fun place mem => valid place (Window.Mem.mono nested mem)

/-! ## The split is genuinely two-term -/

/-- The local child is the model's own solution of its own source. -/
theorem localTermAt_eq (object : Object grade)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model grade Baseline BranchState)
      (Admissible := Admissible grade) object) :
    (ellipticOperator grade Baseline BranchState).localTermAt object site =
      solutionOnGraded site.val.base grade
        (secondDerivGraded grade object.local') :=
  rfl

/-- The homogeneous child is the exact complementary remainder. -/
theorem tailTermAt_eq (object : Object grade)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model grade Baseline BranchState)
      (Admissible := Admissible grade) object) :
    ((ellipticOperator grade Baseline BranchState).tailTermAt object site).val =
      object.value -
        (solutionOnGraded site.val.base grade
          (secondDerivGraded grade object.local')).val :=
  rfl

/-- Its homogeneity is derived by the framework from the solution law. -/
theorem secondDeriv_tailTermAt (object : Object grade)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model grade Baseline BranchState)
      (Admissible := Admissible grade) object) :
    secondDerivGraded grade
      ((ellipticOperator grade Baseline BranchState).tailTermAt object site)
        = 0 :=
  (ellipticOperator grade Baseline BranchState).operator_tailTermAt object site

end Hypostructure.PDE.Interval
