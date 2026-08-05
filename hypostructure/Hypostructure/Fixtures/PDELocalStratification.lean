import Hypostructure.PDE.Focus
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.TailContinuation
import Hypostructure.PDE.EllipticLocalTail
import Hypostructure.PDE.Strategy.AtomContextObstructionDichotomy
import Hypostructure.PDE.CT1
import Hypostructure.PDE.CT7

/-!
# PDE local tail fixtures

These fixtures exercise the reusable local-tail and coordinate plumbing.
-/

namespace Hypostructure.Fixtures.PDELocalStratification

open Hypostructure

def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def atlas : PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _ _ => True
  nested := fun _ _ => True
  nested_refl := fun _ => trivial
  nested_trans := fun _ _ => trivial
  core := id
  core_nested := fun _ => trivial
  LocalObject := fun _ => Nat
  restrict := fun object _ => object
  restrictLocal := fun _ object => object
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro object small large nested
    rfl

def equation : PDE.RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := by
    intro small large nested object data
    exact data
  restrict_satisfies := by
    intro small large nested object data valid
    exact valid

def model : PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def nestedFocus : PDE.NestedFocus model () where
  inner := ()
  middle := ()
  outer := ()
  point_mem_inner := trivial
  inner_middle := trivial
  middle_outer := trivial

def outerEquationState : PDE.EquationState equation nestedFocus.outer where
  object := by
    change Nat
    exact 3
  data := ()
  valid := trivial

#check nestedFocus.outerToMiddle
#check nestedFocus.middleToInner
#check nestedFocus.outerToInner

example :
    ((nestedFocus.restrictToMiddle outerEquationState).restrict
      nestedFocus.inner_middle).object =
        (nestedFocus.restrictToInner outerEquationState).object :=
  nestedFocus.restrict_inner_object_eq outerEquationState

section LocalTail

def wholeQuery : Core.Residual.Query Unit fun _ => Nat :=
  fun _ => 5

def splitQuery :
    Core.Residual.Query Unit fun previous =>
      PDE.ExactLocalTail Nat (wholeQuery previous) :=
  fun _ => {
    localPart := 2
    tailPart := 3
    exact_reconstruction := rfl
  }

example :
    (PDE.ExactLocalTail.localQuery wholeQuery splitQuery) () = 2 :=
  rfl

example :
    (PDE.ExactLocalTail.tailQuery wholeQuery splitQuery) () = 3 :=
  rfl

example :
    (PDE.ExactLocalTail.localQuery wholeQuery splitQuery) () +
        (PDE.ExactLocalTail.tailQuery wholeQuery splitQuery) () =
      wholeQuery () :=
  PDE.ExactLocalTail.queries_reconstruct wholeQuery splitQuery ()

def sameOn (_ : Unit) (left right : Nat) : Prop :=
  left = right

def localSplitQuery :
    Core.Residual.Query Unit fun previous =>
      PDE.ExactLocalTailOn Nat (sameOn previous)
        (wholeQuery previous) :=
  fun _ => {
    localPart := 2
    tailPart := 3
    exact_reconstruction := rfl
  }

example :
    sameOn ()
      ((PDE.ExactLocalTailOn.localQuery wholeQuery sameOn
          localSplitQuery) () +
        (PDE.ExactLocalTailOn.tailQuery wholeQuery sameOn
          localSplitQuery) ())
      (wholeQuery ()) :=
  PDE.ExactLocalTailOn.queries_reconstruct wholeQuery sameOn localSplitQuery ()

end LocalTail

section RecenteredTail

def identityRecentering : PDE.RecenteringInterface model where
  Shift := Unit
  targetWindow := fun _ window => window
  coordinate := fun _ _ => {
    transform := id
    transformEquation := id
    preservesEquation := fun _ valid => valid
    realize := id
    realizes := fun _ => rfl
    preservesBaseline := fun baseline => baseline
  }

def identityRescaling : PDE.RescalingInterface model where
  Scale := Unit
  targetWindow := fun _ window => window
  coordinate := fun _ _ => {
    transform := id
    transformEquation := id
    preservesEquation := fun _ valid => valid
    realize := id
    realizes := fun _ => rfl
    preservesBaseline := fun baseline => baseline
  }

def tailFocus : PDE.TailFocus model () :=
  PDE.TailFocus.ofInterfaces
    () trivial identityRecentering ()
    (some ⟨identityRescaling, ()⟩)

def representedTail :
    PDE.RepresentedTail model (wholeQuery ()) (splitQuery ()) where
  sourceWindow := ()
  interpretTail := id
  equationState := outerEquationState
  equationState_object := by
    change (3 : Nat) = 3
    rfl

def localClosedQuery :
    Core.Residual.Query Unit fun _ => PUnit :=
  fun _ => PUnit.unit

def representedTailQuery :
    Core.Residual.Query Unit fun previous =>
      PDE.RepresentedTail model (wholeQuery previous)
        (splitQuery previous) :=
  fun _ => representedTail

def tailFocusQuery :
    Core.Residual.Query Unit fun previous =>
      PDE.TailFocus model
        (representedTailQuery previous).sourceWindow :=
  fun _ => tailFocus

def tailProfile :
    PDE.TailContinuation.Profile Unit model (fun _ => Nat) wholeQuery where
  LocalClosed := fun _ _ => PUnit.{1}
  splitQuery := splitQuery
  localClosedQuery := localClosedQuery
  representedTailQuery := representedTailQuery
  focusQuery := tailFocusQuery

example :
    (tailProfile.recenteredEquationQuery ()).object =
      (tailProfile.tailQuery ()) :=
  by
    change (3 : Nat) = 3
    rfl

example :
    (tailProfile.originalReconstructionQuery ()) =
      (splitQuery ()).exact_reconstruction :=
  rfl

example :
    equation.satisfies (representedTail.recenter tailFocus).state.data :=
  PDE.RecenteredTail.state_valid (representedTail.recenter tailFocus)

example :
    (outerEquationState.transportPath tailFocus.coordinatePath).object =
      atlas.restrict (tailFocus.coordinatePath.run outerEquationState.object)
        tailFocus.targetWindow :=
  PDE.EquationState.transportPath_object_eq_restrict_run
    tailFocus.coordinatePath outerEquationState outerEquationState.object rfl

example :
    outerEquationState.transportPath
        (nestedFocus.outerToMiddlePath.append
          (Core.CoordinatePath.nil
            (C := PDE.coordinateSystem model))) =
      (outerEquationState.transportPath nestedFocus.outerToMiddlePath
        ).transportPath
        (Core.CoordinatePath.nil (C := PDE.coordinateSystem model)) :=
  PDE.EquationState.transportPath_append
    nestedFocus.outerToMiddlePath outerEquationState
      (Core.CoordinatePath.nil (C := PDE.coordinateSystem model))

/-!
The same recentered equation query is accepted unchanged by existing PDE
adapters.  Neither adapter can observe whether the state originated at the
root or from a local tail handoff.
-/

def candidateSchedule :
    Core.Residual.Query Unit fun _ =>
      Core.Finite.Enumeration Unit :=
  fun _ =>
    Core.Finite.Enumeration.singleton ()

noncomputable def recenteredCT1Capability :=
  PDE.CT1.capabilityOfEquationState model
    (fun _ => tailFocus.targetWindow)
    tailProfile.recenteredEquationQuery
    (fun _ => Unit)
    (fun _ state _ => state.object)
    (fun _ _ _ => True)
    candidateSchedule
    (fun _ _ _ => isTrue trivial)
    (fun _ => 0) 1 1
    (by
      intro previous
      rfl)

#check _root_.Hypostructure.CT1.execute
  (PDE.CT1.targetSpec model (fun _ : Unit => Unit)
    (fun previous _ =>
      (tailProfile.recenteredEquationQuery previous).object)
    (fun _ _ _ => True))
  recenteredCT1Capability
  ()

def contextSchedule :
    Core.Residual.Query Unit fun _ =>
      Core.Finite.Enumeration Unit :=
  fun _ =>
    Core.Finite.Enumeration.singleton ()

noncomputable def recenteredCT7Capability :=
  letI : Add model.problem.Ambient := by
    change Add Nat
    infer_instance
  PDE.CT7.targetCapabilityOfEquationState model
    (fun _ => tailFocus.targetWindow)
    tailProfile.recenteredEquationQuery
    (Target := fun _ => True)
    (fun _ => isTrue trivial)
    (Context := Unit)
    (tail := fun _ => (0 : Nat))
    (Coordinate := Unit)
    (decode := id)
    (fun _ state =>
      { source := state.object
        replacement := state.object })
    contextSchedule
    (by
      intro previous context
      refine ⟨⟨0, ?_⟩, ?_⟩
      · simp [contextSchedule, Core.Finite.Enumeration.card,
          Core.Finite.Enumeration.singleton,
          Core.Finite.Enumeration.ofNodupList]
      · cases context
        rfl)

end RecenteredTail

section LocalEllipticDichotomy

def threeAmbient : model.problem.Ambient := by
  change Nat
  exact 3

def threeLocal (window : model.atlas.Window) :
    model.atlas.LocalObject window := by
  change Nat
  exact 3

def globalRealization : PDE.GlobalEquationRealization model Unit where
  object := fun _ => threeAmbient
  state := fun _ _ => {
    object := threeLocal _
    data := ()
    valid := trivial
  }
  state_object := fun _ _ => rfl
  restrict_state := fun _ {inner outer} _ => by
    cases inner
    cases outer
    rfl

/-- The only localization datum: one base window per atlas point.  The nested
tower and the focus are assembled by the framework. -/
def pointLocalization : PDE.PointLocalization model where
  Admissible := fun _ _ => True
  site := fun _ => ()
  base := fun _ => ()
  point_mem_core_core := fun _ => trivial
  base_admissible := fun _ => trivial

/-- The active residual as Core's selection path would expose it: the
selected object, its baseline, its target avoidance, and the minimality
kernel of the canonical empty PDE progress. -/
def activeResidual : PDE.ActiveResidual model where
  Target := fun _ => False
  Smaller := fun _ _ => False
  object := threeAmbient
  baseline := trivial
  avoids := fun absurd => absurd
  minimal := fun _ smaller _ => smaller.elim

def activeResidualQuery :
    Core.Residual.Query Unit fun _ => PDE.ActiveResidual model :=
  fun _ => activeResidual

def publicPresentation : PDE.PublicPresentation model where
  localization := pointLocalization
  state := fun residual _ => {
    object := residual.object
    data := ()
    valid := trivial
  }
  state_object := by
    intro residual window
    rfl
  restrict_state := by
    intro residual inner outer nested
    cases inner
    cases outer
    rfl

def publicGlobalRealization : PDE.GlobalEquationRealization model Unit :=
  PDE.GlobalEquationRealization.ofPublicPresentation publicPresentation
    activeResidualQuery

def ellipticComponent {W : atlas.Window}
    (state : PDE.EquationState equation W) : Int :=
  Int.ofNat state.object

def elliptic :
    PDE.LocalEllipticConstraint model model (fun _ _ => True) Unit
    (fun _ => Int) (fun _ => Int) where
  tailWindow := id
  ComponentSite := fun _ => Unit
  componentInterface := fun _ _ => ()
  selectSite := fun _ {_} _ _ => ()
  rebuildComponent := fun _ _ value => value.toNat
  interpretCarrier := fun _ value => value.toNat
  constraint := AddMonoidHom.id Int
  carrierRestrict := fun _ => AddMonoidHom.id Int
  sourceRestrict := fun _ => AddMonoidHom.id Int
  constraint_restrict := fun _ _ => rfl
  component := fun _ _ {_} state => ellipticComponent state
  source := fun _ _ {_} state => ellipticComponent state
  component_constraint := fun _ _ _ _ => rfl
  rebuild_component := by
    intro ambient point focus admissible state stateObject
    change Int.toNat (Int.ofNat state.object) = ambient
    rw [stateObject]
    simp
    change ambient = ambient
    rfl
  homogeneousState := fun _ value homogeneous => {
    object := value.toNat
    data := ()
    valid := trivial
  }
  homogeneousState_object := fun _ _ _ => rfl
  cutoff := fun _ => AddMonoidHom.id Int
  cutoff_interior := fun _ _ => rfl
  localSolution := fun _ambient _site {_U} {_V} _nested state =>
    ellipticComponent state
  localSolution_constraint := fun _ _ {_} {_} _ _ => rfl

def currentElliptic :
    PDE.CurrentLocalEllipticResidual model model (fun _ _ => True) Unit
      (fun _ => Int) (fun _ => Int) elliptic :=
  PDE.CurrentLocalEllipticResidual.ofGlobal globalRealization
    () nestedFocus trivial

def currentEllipticQuery :
    Core.Residual.Query Unit fun _ =>
      PDE.CurrentLocalEllipticResidual model model (fun _ _ => True) Unit
      (fun _ => Int) (fun _ => Int) elliptic :=
  fun _ => currentElliptic

def publicCurrentElliptic :
    PDE.CurrentLocalEllipticResidual model model (fun _ _ => True) Unit
      (fun _ => Int) (fun _ => Int) elliptic :=
  PDE.CurrentLocalEllipticResidual.ofActiveResidual
    (N := model) (Admissible := fun _ _ => True) (Interface := Unit)
    (Carrier := fun _ => Int) (Source := fun _ => Int) (elliptic := elliptic)
    publicPresentation activeResidual trivial

def publicCurrentEllipticQuery :
    Core.Residual.Query Unit fun _ =>
      PDE.CurrentLocalEllipticResidual model model (fun _ _ => True) Unit
      (fun _ => Int) (fun _ => Int) elliptic :=
  PDE.CurrentLocalEllipticResidual.ofActiveResidualQuery
    (N := model) (Admissible := fun _ _ => True) (Interface := Unit)
    (Carrier := fun _ => Int) (Source := fun _ => Int) (elliptic := elliptic)
    publicPresentation activeResidualQuery (fun _ => trivial)

example : publicCurrentEllipticQuery () = publicCurrentElliptic :=
  rfl

example : publicCurrentElliptic.ambient = threeAmbient :=
  rfl

example : publicCurrentElliptic.outerState.object =
    atlas.restrict publicCurrentElliptic.ambient
      publicCurrentElliptic.focus.outer :=
  publicCurrentElliptic.outerState_object

def localClosure :
    PDE.Strategy.LocalTailObstructionDichotomy.Presentation.LocalEllipticClosure
      model model (fun _ _ => True) Unit (fun _ => Int) (fun _ => Int)
      elliptic where
  closes := fun _ value => value = 3

def ellipticLocalClosedQuery :
    Core.Residual.Query Unit (fun previous =>
      PLift (localClosure.closes (currentEllipticQuery previous)
        ((PDE.CurrentLocalEllipticResidual.splitQuery currentEllipticQuery)
          previous).localPart)) :=
  fun _ => ⟨by
    show (_ : Int) = 3
    rfl⟩

def ellipticFocusQuery :
    Core.Residual.Query Unit (fun previous =>
      PDE.TailFocus model
        (PDE.CurrentLocalEllipticResidual.representedTail
          (currentEllipticQuery previous)).sourceWindow) :=
  fun _ => tailFocus

noncomputable def ellipticTailProfile :=
  PDE.Strategy.LocalTailObstructionDichotomy.Presentation.tailContinuationProfile
    currentEllipticQuery localClosure ellipticLocalClosedQuery
      ellipticFocusQuery

/-- The complete atom/tail profile derived from the public presentation and
the active-residual query alone. -/
noncomputable def publicDichotomyProfile :=
  PDE.Strategy.LocalTailObstructionDichotomy.Registration.profileFromPublicPresentation
    (N := model) (Admissible := fun _ _ => True) (Interface := Unit)
    (Carrier := fun _ => Int) (Source := fun _ => Int) (elliptic := elliptic)
    publicPresentation localClosure activeResidualQuery (fun _ => trivial)

example :
    (publicDichotomyProfile.presentation ()).object = threeAmbient :=
  rfl

/-- The framework derives the focus; the fixture supplies no `NestedFocus`. -/
example : publicPresentation.focus activeResidual = nestedFocus :=
  rfl

noncomputable def ellipticProfile :=
  PDE.Strategy.LocalTailObstructionDichotomy.Presentation.profileFromCurrentLocalElliptic
    currentEllipticQuery localClosure

example :
    ellipticProfile.presentation () =
      PDE.Strategy.LocalTailObstructionDichotomy.Presentation.currentLocalEllipticToCore
        localClosure currentElliptic :=
  rfl

example :
    (currentElliptic.recenterTail tailFocus).state =
      currentElliptic.representedTail.equationState.transportPath
        tailFocus.coordinatePath :=
  (currentElliptic.recenterTail tailFocus).state_eq

end LocalEllipticDichotomy

section LocalToGlobal

/-!
The exhaustion path, end to end, on an arbitrary represented PDE.

Only two things appear: `PDE.ComponentEllipticOperator`, which supplies the
component and its local solvability, and Core's own
`AtomContextAssembly.PointwiseCertificate` / `LocalToGlobalProfile`.  There is
no PDE-side exhaustion, gluing, or closure implementation.
-/

def componentOperator :
    PDE.ComponentEllipticOperator model model (fun _ _ => True)
      (fun _ _ => Int) where
  component := fun object _window => Int.ofNat object
  rebuild := fun _object _window value => value.toNat
  rebuild_component := fun object _window => by
    change (Int.ofNat object).toNat = object
    simp
  operator := fun _object _window => AddMonoidHom.id Int
  kernelPart := fun _object _window => 0
  tailWindow := id
  tailObject := fun _object _window _target value => value.toNat
  tailData := fun _object _window _target _value => ()
  tailValid := fun _object _window _target _value _homogeneous => trivial

/-- The framework's assembly ranges over *every* admissible window, which is
the site space Core's pointwise certificate quantifies over. -/
example (object : model.problem.Ambient)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model) (Admissible := fun _ _ => True) object) :
    componentOperator.assembly.atom object site =
      componentOperator.localTermAt object site :=
  rfl

/-- The homogeneity of every complementary child is supplied by the
framework; the fixture proves nothing. -/
noncomputable def pointwise (object : model.problem.Ambient) :
    componentOperator.assembly.PointwiseCertificate
      (fun {interface} _atom context =>
        componentOperator.operator interface.1 interface.2.val context = 0)
      object :=
  componentOperator.homogeneousCertificate object

/-- The registered domain theorem: pointwise facts over all admissible
windows imply the global statement.  Core owns its application. -/
def globalProfile :
    componentOperator.assembly.LocalToGlobalProfile
      (fun {interface} _atom context =>
        componentOperator.operator interface.1 interface.2.val context = 0)
      (fun object => ∀ site : PDE.ComponentEllipticOperator.Site
          (M := model) (Admissible := fun _ _ => True) object,
        componentOperator.operator object site.val
          (componentOperator.tailTermAt object site) = 0) where
  close := fun _object certificate => fun site => certificate.localAt site

/-- The global conclusion, produced by Core's `LocalToGlobalProfile.run` from
the framework-supplied pointwise certificate. -/
noncomputable def globalConclusion (object : model.problem.Ambient) :=
  globalProfile.run object (pointwise object)

example (object : model.problem.Ambient)
    (site : PDE.ComponentEllipticOperator.Site
      (M := model) (Admissible := fun _ _ => True) object) :
    componentOperator.operator object site.val
      (componentOperator.tailTermAt object site) = 0 :=
  globalConclusion object site

/-- The same closure appended to an ordinary Core ledger, again by Core. -/
noncomputable def globalNode :=
  Core.AtomContextAssembly.LocalToGlobalProfile.globalize globalProfile
    (Previous := Unit) (fun _ => threeAmbient)
    (fun _ => pointwise threeAmbient)

end LocalToGlobal

end Hypostructure.Fixtures.PDELocalStratification
