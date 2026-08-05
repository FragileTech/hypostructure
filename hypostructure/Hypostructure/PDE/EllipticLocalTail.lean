import Hypostructure.Core.Assembly.Amalgamation
import Hypostructure.Core.Assembly.LocalToGlobal
import Hypostructure.PDE.Focus
import Hypostructure.PDE.LocalTail
import Hypostructure.PDE.TailContinuation

/-!
# Local elliptic cutoff--parametrix splitting

This module formalizes the local algebra behind a Calderón--Zygmund split.
From one represented equation state on an outer window, a nested inner
window, a cutoff of its elliptic source, and a local parametrix, it *defines*
the local term and complementary tail.  Exact reconstruction and the
inner-window homogeneous tail equation follow from the local operator laws.

There is no whole-space object, exterior datum, global norm, ledger, route,
or Strategy execution here.
-/

namespace Hypostructure.PDE

universe u v

/-! ## Window amalgamation

A specialization of Core's `CompatibleFamily` to atlas windows: local
witnesses attached to windows, agreeing wherever two windows overlap,
amalgamate into one global witness.  Nothing here mentions an equation, an
operator, or a problem --- it is the sheaf step every PDE needs in order to
turn per-window certificates into the single global witness that
`AtomContextAssembly.LocalToGlobalProfile` closes over.
-/

structure WindowAmalgamation (M : LocalModel.{u}) (Value : Type v) where
  /-- Which points a window contains. -/
  Mem : M.atlas.Window → M.atlas.Point → Prop
  /-- The windows of one object that carry a local witness. -/
  Index : M.problem.Ambient → Type u
  windowOf : (object : M.problem.Ambient) → Index object → M.atlas.Window
  localWitness : (object : M.problem.Ambient) → Index object →
    M.atlas.Point → Value
  compatible : ∀ (object : M.problem.Ambient) (left right : Index object)
    (place : M.atlas.Point),
    Mem (windowOf object left) place → Mem (windowOf object right) place →
      localWitness object left place = localWitness object right place
  fallback : Value

namespace WindowAmalgamation

variable {M : LocalModel.{u}} {Value : Type v}
  (data : WindowAmalgamation M Value)

/-- The Core family this specializes.  All the work is Core's. -/
def family (object : M.problem.Ambient) :
    Core.CompatibleFamily (data.Index object) M.atlas.Point Value where
  Mem := fun index place => data.Mem (data.windowOf object index) place
  localSection := data.localWitness object
  compatible := data.compatible object
  fallback := data.fallback

/-- The single global witness of one object, built by Core's amalgamation. -/
noncomputable def witness (object : M.problem.Ambient) :
    M.atlas.Point → Value :=
  (data.family object).amalgamate

/-- The global witness restricts to each local one on its own window. -/
theorem witness_eq (object : M.problem.Ambient) {index : data.Index object}
    {place : M.atlas.Point}
    (mem : data.Mem (data.windowOf object index) place) :
    data.witness object place = data.localWitness object index place :=
  (data.family object).amalgamate_eq mem

/-- Any property depending only on the values taken on one window transports
from the local witnesses to the global one.  This is what produces a
pointwise certificate over the whole family of windows. -/
theorem witness_property
    {Property : (object : M.problem.Ambient) → data.Index object →
      (M.atlas.Point → Value) → Prop}
    (congruent : ∀ (object : M.problem.Ambient) (index : data.Index object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf object index) place →
        left place = right place) →
        Property object index left → Property object index right)
    (localProperty : ∀ (object : M.problem.Ambient) (index : data.Index object),
      Property object index (data.localWitness object index))
    (object : M.problem.Ambient) (index : data.Index object) :
    Property object index (data.witness object) :=
  (data.family object).amalgamate_property (Property := Property object)
    (congruent object) (localProperty object) index

end WindowAmalgamation

/--
**A pointwise admissible-window selector.**

Every relevant point of an object lies in an admissible window of that object.
This is the same datum a `PointLocalization` already carries for the one
residual it selects, stated at every point rather than at one; it is what
turns "each window certifies its own points" into "every relevant point is
certified", i.e. the cover hypothesis of the framework's exhaustive closure.

It is model data: no residual, ledger, route, branch or target appears.
-/
structure AdmissibleWindowCover (M : LocalModel.{u})
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (Relevant : M.problem.Ambient → M.atlas.Point → Prop) where
  window : (object : M.problem.Ambient) → M.atlas.Point → M.atlas.Window
  admissible : ∀ object point, Relevant object point →
    Admissible object (window object point)
  contains : ∀ object point, Relevant object point →
    M.atlas.contains point (window object point)

/--
Reusable local elliptic data for a represented PDE model.

`Carrier` and `Source` are the represented distribution spaces.  They are
indexed by `Interface`, the retained source data of one component split site,
because the space a component lives in generally depends on the object being
split: a PDE whose ambient objects carry their own domain has a different
distribution space over each domain.  Nothing here is domain independent by
assumption, and no application has to flatten its carrier into a single type.

The restriction, cutoff, and parametrix maps are indexed by the current
nested windows, so every operation remains local to the incoming equation
state.
-/
structure LocalEllipticConstraint
    (M N : LocalModel.{u})
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (Interface : Type u)
    (Carrier Source : Interface → Type u)
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)] where
  /-- The window of the tail model carrying the homogeneous complementary
  child.  The tail generally satisfies a *different* represented equation
  from the source: the complementary child of a Calderon--Zygmund split
  satisfies the homogeneous equation, not the original inhomogeneous one. -/
  tailWindow : M.atlas.Window → N.atlas.Window
  ComponentSite : M.problem.Ambient → Type u
  componentInterface :
    (ambient : M.problem.Ambient) → ComponentSite ambient → Interface
  /-- The split site of one *admissible* focus.  A window the localization
  step has not certified never reaches the elliptic layer. -/
  selectSite : (ambient : M.problem.Ambient) →
    {point : M.atlas.Point} → (focus : NestedFocus M point) →
      Admissible ambient focus.outer → ComponentSite ambient
  rebuildComponent : (ambient : M.problem.Ambient) →
    (site : ComponentSite ambient) →
      Carrier (componentInterface ambient site) → M.problem.Ambient
  interpretCarrier : {i : Interface} → (window : N.atlas.Window) →
    Carrier i → N.atlas.LocalObject window
  constraint : {i : Interface} → Carrier i →+ Source i
  carrierRestrict : {i : Interface} → ∀ {U V : M.atlas.Window},
    M.atlas.nested U V → Carrier i →+ Carrier i
  sourceRestrict : {i : Interface} → ∀ {U V : M.atlas.Window},
    M.atlas.nested U V → Source i →+ Source i
  constraint_restrict : ∀ {i : Interface} {U V : M.atlas.Window}
    (nested : M.atlas.nested U V) (value : Carrier i),
    constraint (carrierRestrict nested value) =
      sourceRestrict nested (constraint value)
  component : (ambient : M.problem.Ambient) →
    (site : ComponentSite ambient) → {W : M.atlas.Window} →
      EquationState M.equation W → Carrier (componentInterface ambient site)
  source : (ambient : M.problem.Ambient) →
    (site : ComponentSite ambient) → {W : M.atlas.Window} →
      EquationState M.equation W → Source (componentInterface ambient site)
  component_constraint : ∀ (ambient : M.problem.Ambient)
    (site : ComponentSite ambient) {W : M.atlas.Window}
    (state : EquationState M.equation W),
    constraint (component ambient site state) = source ambient site state
  rebuild_component : ∀ (ambient : M.problem.Ambient)
    {point : M.atlas.Point} (focus : NestedFocus M point)
    (admissible : Admissible ambient focus.outer)
    (state : EquationState M.equation focus.outer),
    state.object = M.atlas.restrict ambient focus.outer →
      rebuildComponent ambient (selectSite ambient focus admissible)
        (component ambient (selectSite ambient focus admissible) state) =
          ambient
  homogeneousState : {i : Interface} → (window : N.atlas.Window) →
    (value : Carrier i) → constraint value = 0 →
      EquationState N.equation window
  homogeneousState_object : ∀ {i : Interface} (window : N.atlas.Window)
    (value : Carrier i) (homogeneous : constraint value = 0),
    (homogeneousState window value homogeneous).object =
      interpretCarrier window value
  cutoff : {i : Interface} → ∀ {U V : M.atlas.Window},
    (nested : M.atlas.nested U V) → Source i →+ Source i
  cutoff_interior : ∀ {i : Interface} {U V : M.atlas.Window}
    (nested : M.atlas.nested U V) (value : Source i),
    sourceRestrict nested (cutoff nested value) = sourceRestrict nested value
  /-- The local child on one window: an element whose constraint matches the
  cutoff source *of that same window*.

  This is the only solution the split ever needs.  It is deliberately not a
  right inverse of `constraint`: demanding one would be a statement about the
  operator on the whole carrier, whereas the split only ever solves for the
  one source it constructed itself. -/
  localSolution : (ambient : M.problem.Ambient) →
    (site : ComponentSite ambient) → {U V : M.atlas.Window} →
      M.atlas.nested U V → EquationState M.equation V →
        Carrier (componentInterface ambient site)
  localSolution_constraint : ∀ (ambient : M.problem.Ambient)
    (site : ComponentSite ambient) {U V : M.atlas.Window}
    (nested : M.atlas.nested U V) (state : EquationState M.equation V),
    sourceRestrict nested
        (constraint (localSolution ambient site nested state)) =
      sourceRestrict nested (cutoff nested (source ambient site state))

namespace LocalEllipticConstraint

variable {M N : LocalModel.{u}}
  {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
  {Interface : Type u}
  {Carrier Source : Interface → Type u}
  [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
  (elliptic : LocalEllipticConstraint M N Admissible Interface Carrier Source)
  (ambient : M.problem.Ambient)

/-- The cutoff/parametrix local term on the current outer window. -/
def localTerm (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    Carrier (elliptic.componentInterface ambient site) :=
  elliptic.localSolution ambient site nested state

/-- The tail is defined as the complementary local residual. -/
def tailTerm (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    Carrier (elliptic.componentInterface ambient site) :=
  elliptic.component ambient site state -
    elliptic.localTerm ambient site nested state

/-- The exact local/tail decomposition of the current represented component. -/
def split (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    ExactLocalTail (Carrier (elliptic.componentInterface ambient site))
      (elliptic.component ambient site state) where
  localPart := elliptic.localTerm ambient site nested state
  tailPart := elliptic.tailTerm ambient site nested state
  exact_reconstruction := by
    simp only [tailTerm]
    abel

/-- The parametrix solves the cutoff local source *on the nested window*. -/
theorem sourceRestrict_constraint_localTerm
    (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    elliptic.sourceRestrict nested
        (elliptic.constraint (elliptic.localTerm ambient site nested state)) =
      elliptic.sourceRestrict nested
        (elliptic.cutoff nested (elliptic.source ambient site state)) :=
  elliptic.localSolution_constraint ambient site nested state

/--
The complementary tail is homogeneous after restriction to the nested inner
window.  This is the local tail equation available to the next residual.
-/
theorem constraint_restrict_tailTerm_zero
    (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    elliptic.constraint
        (elliptic.carrierRestrict nested
          (elliptic.tailTerm ambient site nested state)) =
      0 := by
  rw [elliptic.constraint_restrict]
  simp only [tailTerm, map_sub, elliptic.component_constraint,
    elliptic.sourceRestrict_constraint_localTerm, elliptic.cutoff_interior]
  exact sub_self _

/-- The exact split retains the computed cutoff/parametrix local term. -/
@[simp] theorem split_localPart (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    (elliptic.split ambient site nested state).localPart =
      elliptic.localTerm ambient site nested state :=
  rfl

/-- The exact split retains the derived complementary tail. -/
@[simp] theorem split_tailPart (site : elliptic.ComponentSite ambient)
    {U V : M.atlas.Window} (nested : M.atlas.nested U V)
    (state : EquationState M.equation V) :
    (elliptic.split ambient site nested state).tailPart =
      elliptic.tailTerm ambient site nested state :=
  rfl

end LocalEllipticConstraint

/-! ## Generic Calderon--Zygmund input

The structure below is the whole mathematical input a PDE has to supply in
order to obtain the local elliptic atom/tail split.  Everything else --- the
sites, the interfaces, the restriction and cutoff maps, the homogeneity of
the complementary child, and the exact reconstruction --- is derived by
`toConstraint`.

Three things make the input honest and local.

* `Carrier` is indexed by the *window*, so a component lives over the region
  the localization step selected rather than over the whole object.
* `Carrier` is also indexed by a **grade**.  The elliptic operator lowers the
  grade and the solution operator raises it, so `solve`'s signature is itself
  the guarantee that it gains regularity: an entry that gains nothing cannot
  inhabit `Carrier g → Carrier (step g)` at all.  This is what rules out the
  identity solution and "component minus a kernel element", which satisfy the
  equation but answer a different question.
* Every obligation is stated one window at a time and only for *admissible*
  windows, so no PDE ever has to say anything off the region it is working on.
-/
structure ComponentEllipticOperator
    (M N : LocalModel.{u}) (Grade : Type)
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (Carrier : M.problem.Ambient → M.atlas.Window → Grade → Type u)
    [∀ object window grade, AddCommGroup (Carrier object window grade)] where
  /-- The grade of the model's elliptic source. -/
  grade : Grade
  /-- How much regularity the solution operator gains. -/
  step : Grade → Grade
  /-- The additive component of the object, localized to one window, at the
  grade the operator can act on. -/
  component : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    Carrier object window (step grade)
  /-- Putting a local component back into its own object. -/
  rebuild : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    Carrier object window (step grade) → M.problem.Ambient
  rebuild_component : ∀ object window,
    rebuild object window (component object window) = object
  /-- The elliptic operator, lowering the grade. -/
  operator : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    (g : Grade) → Carrier object window (step g) →+ Carrier object window g
  /--
  The local solution operator, raising the grade.

  This is the whole problem-specific datum, and its type is the honest
  statement of what a solution operator is: it solves the equation *and*
  gains regularity.  Nothing that fails to gain a grade can be written here.
  -/
  solve : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    (g : Grade) → Carrier object window g → Carrier object window (step g)
  operator_solve : ∀ object window g value,
    operator object window g (solve object window g value) = value
  /-- Where the homogeneous complementary child lives. -/
  tailWindow : M.atlas.Window → N.atlas.Window
  tailObject : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    (target : N.atlas.Window) → Carrier object window (step grade) →
      N.atlas.LocalObject target
  tailData : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    (target : N.atlas.Window) →
    (value : Carrier object window (step grade)) →
      N.equation.EquationData target (tailObject object window target value)
  /-- A component annihilated by the local operator satisfies the tail
  equation.  This is the meaning of the tail model, not a strategy fact. -/
  tailValid : ∀ (object : M.problem.Ambient) (window : M.atlas.Window)
    (target : N.atlas.Window) (value : Carrier object window (step grade)),
    operator object window grade value = 0 →
      N.equation.satisfies (tailData object window target value)

namespace ComponentEllipticOperator

variable {M N : LocalModel.{u}} {Grade : Type}
  {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
  {Carrier : M.problem.Ambient → M.atlas.Window → Grade → Type u}
  [∀ object window grade, AddCommGroup (Carrier object window grade)]
  (data : ComponentEllipticOperator M N Grade Admissible Carrier)

/-- The site of the derived constraint is an *admissible* window: the
localization step has already proved the window it selected is one. -/
abbrev Site (object : M.problem.Ambient) : Type u :=
  { window : M.atlas.Window // Admissible object window }

/-- The retained interface of one split site: the object together with the
admissible window its component lives over. -/
abbrev Interface : Type u :=
  Sigma fun object : M.problem.Ambient => Site (Admissible := Admissible) object

/-! ### The split, entirely derived

`localTermAt` is the model's own solution of its own local source, and
`tailTermAt` is what is left over.  Both live at the component's grade, and
the homogeneity of the second is a consequence of `operator_solve` rather
than a supplied fact. -/

/-- The elliptic source of the component on one window. -/
def sourceAt (object : M.problem.Ambient) (window : M.atlas.Window) :
    Carrier object window data.grade :=
  data.operator object window data.grade (data.component object window)

/-- The local child: the model's solution for its own source. -/
def localTermAt (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    Carrier object site.val (data.step data.grade) :=
  data.solve object site.val data.grade (data.sourceAt object site.val)

/-- The complementary homogeneous child. -/
def tailTermAt (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    Carrier object site.val (data.step data.grade) :=
  data.component object site.val - data.localTermAt object site

theorem localTermAt_add_tailTermAt (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    data.localTermAt object site + data.tailTermAt object site =
      data.component object site.val := by
  simp only [tailTermAt]
  abel

/-- The Calderon--Zygmund conclusion at *every* admissible window, derived
once for every PDE from the solution law. -/
theorem operator_tailTermAt (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    data.operator object site.val data.grade
      (data.tailTermAt object site) = 0 := by
  simp only [tailTermAt, localTermAt, map_sub, data.operator_solve]
  exact sub_self _

/--
The full local elliptic constraint derived from one component operator.

The interface is the object together with the admissible window; the carrier
sits at the component's grade and the source one step below, which is exactly
the shape `LocalEllipticConstraint` already expects.  The cutoff and both
restriction maps are the identity because everything already lives over the
selected window.
-/
noncomputable def toConstraint :
    LocalEllipticConstraint M N Admissible
      (Interface (M := M) (Admissible := Admissible))
      (fun interface =>
        Carrier interface.1 interface.2.val (data.step data.grade))
      (fun interface => Carrier interface.1 interface.2.val data.grade) where
  tailWindow := data.tailWindow
  ComponentSite := fun object => Site (Admissible := Admissible) object
  componentInterface := fun object site => ⟨object, site⟩
  selectSite := fun _object {_point} focus admissible =>
    ⟨focus.outer, admissible⟩
  rebuildComponent := fun object site value =>
    data.rebuild object site.val value
  interpretCarrier := fun {interface} target value =>
    data.tailObject interface.1 interface.2.val target value
  constraint := fun {interface} =>
    data.operator interface.1 interface.2.val data.grade
  carrierRestrict := fun {interface} {_U} {_V} _nested =>
    AddMonoidHom.id (Carrier interface.1 interface.2.val (data.step data.grade))
  sourceRestrict := fun {interface} {_U} {_V} _nested =>
    AddMonoidHom.id (Carrier interface.1 interface.2.val data.grade)
  constraint_restrict := fun _nested _value => rfl
  component := fun object site {_W} _state => data.component object site.val
  source := fun object site {_W} _state => data.sourceAt object site.val
  component_constraint := fun _object _site {_W} _state => rfl
  rebuild_component := fun object {_point} focus _admissible _state
      _object_eq =>
    data.rebuild_component object focus.outer
  homogeneousState := fun {interface} target value homogeneous =>
    { object := data.tailObject interface.1 interface.2.val target value
      data := data.tailData interface.1 interface.2.val target value
      valid :=
        data.tailValid interface.1 interface.2.val target value homogeneous }
  homogeneousState_object := fun _target _value _homogeneous => rfl
  cutoff := fun {interface} {_U} {_V} _nested =>
    AddMonoidHom.id (Carrier interface.1 interface.2.val data.grade)
  cutoff_interior := fun _nested _value => rfl
  localSolution := fun object site {_U} {_V} _nested _state =>
    data.localTermAt object site
  localSolution_constraint := fun object site {_U} {_V} _nested _state => by
    show data.operator object site.val data.grade
        (data.localTermAt object site) = data.sourceAt object site.val
    exact data.operator_solve object site.val data.grade _

/-! ### The exhaustive assembly consumed by Core's local-to-global closure

`toConstraint` produces the split at the *one* window a localization step
selected.  The assembly below instead ranges over **every** admissible window
of an object, which is exactly the site space Core's
`AtomContextAssembly.PointwiseCertificate` quantifies over.  A domain theorem
registered as `AtomContextAssembly.LocalToGlobalProfile` then closes the
global statement from those pointwise facts, using
`LocalToGlobalProfile.run` / `node` / `globalize` / `globalizeOpenResult`.

Nothing new is implemented here: the exhaustion, the certificate, the ledger
node, and the live-stage transport are all Core's. -/

def assembly :
    Core.AtomContextAssembly M.problem
      (RepresentationSemantics.equality M.problem) where
  Interface := Interface (M := M) (Admissible := Admissible)
  Site := fun object => Site (Admissible := Admissible) object
  interface := fun object site => ⟨object, site⟩
  Atom := fun interface =>
    Carrier interface.1 interface.2.val (data.step data.grade)
  Context := fun interface =>
    Carrier interface.1 interface.2.val (data.step data.grade)
  compatible := fun {interface} atom context =>
    atom + context = data.component interface.1 interface.2.val
  atom := fun object site => data.localTermAt object site
  context := fun object site => data.tailTermAt object site
  assemble := fun {interface} atom context =>
    data.rebuild interface.1 interface.2.val (atom + context)
  extractedCompatible := fun object site =>
    data.localTermAt_add_tailTermAt object site
  reconstruct := fun object site => by
    show data.rebuild object site.val
        (data.localTermAt object site + data.tailTermAt object site) = object
    rw [data.localTermAt_add_tailTermAt object site]
    exact data.rebuild_component object site.val

@[simp] theorem assembly_atom (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    data.assembly.atom object site = data.localTermAt object site :=
  rfl

@[simp] theorem assembly_context (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    data.assembly.context object site = data.tailTermAt object site :=
  rfl

/-- The homogeneity certificate, for free, at every site. -/
def homogeneousCertificate (object : M.problem.Ambient) :
    data.assembly.PointwiseCertificate
      (fun {interface} _atom context =>
        data.operator interface.1 interface.2.val data.grade context = 0)
      object :=
  ⟨fun site => data.operator_tailTermAt object site⟩

/-! ### The window family of an operator, derived

A `WindowAmalgamation` has five fields, and four of them are already fixed by
the operator: its `Index` is `Site`, its `windowOf` is the underlying window
of a site, its `Mem` is the atlas' own `contains`, and its `localWitness` is
the reading of the object's own component on that window.  So the only thing
an amalgamation additionally needs is what a carrier value *means* pointwise
--- model data, in exactly the sense `operator` and `solve` are --- and
`windowAmalgamation` produces the rest with no further supplied field.
-/

/--
**The pointwise reading of a graded carrier.**

A carrier value over a window determines a value at each atlas point, and two
windows read *the object's own component* identically wherever they overlap.
That is the interpretation of the carrier and nothing more: there is no
residual, ledger, route, branch or target here.
-/
structure PointwiseReading (Value : Type v) where
  read : (object : M.problem.Ambient) → (window : M.atlas.Window) →
    Carrier object window (data.step data.grade) → M.atlas.Point → Value
  read_component_agree : ∀ (object : M.problem.Ambient)
    (left right : M.atlas.Window) (point : M.atlas.Point),
    M.atlas.contains point left → M.atlas.contains point right →
      read object left (data.component object left) point =
        read object right (data.component object right) point

/-- The window amalgamation of a component elliptic operator.  Sites, windows,
membership and the per-window witnesses are all read off the operator; only
the pointwise meaning of a carrier value is supplied. -/
def windowAmalgamation {Value : Type v} (reading : PointwiseReading data Value)
    (fallback : Value) : WindowAmalgamation M Value where
  Mem := fun window point => M.atlas.contains point window
  Index := fun object => Site (Admissible := Admissible) object
  windowOf := fun _object site => site.val
  localWitness := fun object site =>
    reading.read object site.val (data.component object site.val)
  compatible := fun object left right place leftMem rightMem =>
    reading.read_component_agree object left.val right.val place leftMem
      rightMem
  fallback := fallback

@[simp] theorem windowAmalgamation_mem {Value : Type v}
    (reading : PointwiseReading data Value) (fallback : Value)
    (window : M.atlas.Window) (point : M.atlas.Point) :
    (data.windowAmalgamation reading fallback).Mem window point =
      M.atlas.contains point window :=
  rfl

@[simp] theorem windowAmalgamation_windowOf {Value : Type v}
    (reading : PointwiseReading data Value) (fallback : Value)
    (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    (data.windowAmalgamation reading fallback).windowOf object site =
      site.val :=
  rfl

@[simp] theorem windowAmalgamation_localWitness {Value : Type v}
    (reading : PointwiseReading data Value) (fallback : Value)
    (object : M.problem.Ambient)
    (site : Site (Admissible := Admissible) object) :
    (data.windowAmalgamation reading fallback).localWitness object site =
      reading.read object site.val (data.component object site.val) :=
  rfl

/--
The cover obligation of the framework's exhaustive closure, discharged from a
pointwise admissible-window selector.  Nothing is assumed about the operator:
a relevant point's own admissible window *is* a site, and it contains it.
-/
theorem exists_index_mem_of_cover
    {Relevant : M.problem.Ambient → M.atlas.Point → Prop}
    (cover : AdmissibleWindowCover M Admissible Relevant)
    {Value : Type v} (reading : PointwiseReading data Value) (fallback : Value)
    (object : M.problem.Ambient) (point : M.atlas.Point)
    (relevant : Relevant object point) :
    ∃ index : (data.windowAmalgamation reading fallback).Index object,
      (data.windowAmalgamation reading fallback).Mem
        ((data.windowAmalgamation reading fallback).windowOf object index)
        point :=
  ⟨⟨cover.window object point, cover.admissible object point relevant⟩,
    cover.contains object point relevant⟩

end ComponentEllipticOperator

/-! ## Global-to-local equation realization -/

/--
The public represented-equation bridge from an ambient PDE object to its
valid equation state on every local window.  It is mathematical model data:
it has no Strategy input, residual, route, or execution field.
-/
structure GlobalEquationRealization (M : LocalModel.{u}) (Previous : Type u) where
  object : Core.Residual.Query Previous fun _ => M.problem.Ambient
  state : (previous : Previous) →
    (window : M.atlas.Window) → EquationState M.equation window
  state_object : ∀ (previous : Previous)
    (window : M.atlas.Window),
    (state previous window).object =
      M.atlas.restrict (object previous) window
  restrict_state : ∀ (previous : Previous)
    {inner outer : M.atlas.Window} (nested : M.atlas.nested inner outer),
    (state previous outer).restrict nested = state previous inner

namespace GlobalEquationRealization

/-- Derive a query-indexed realization from the generic public PDE
presentation and the framework's active-residual query.  No strategy
callback, stage value, or unselected ambient object is supplied. -/
def ofPublicPresentation {M : LocalModel.{u}} {Previous : Type u}
    (presentation : PublicPresentation M)
    (active : Core.Residual.Query Previous fun _ => ActiveResidual M) :
    GlobalEquationRealization M Previous where
  object := active.map fun _ residual => residual.object
  state := fun previous window =>
    presentation.state (active previous) window
  state_object := fun previous window =>
    presentation.state_object (active previous) window
  restrict_state := fun previous _inner _outer nested =>
    presentation.restrict_state (active previous) nested

end GlobalEquationRealization

namespace GlobalEquationRealization

variable {M : LocalModel.{u}} {Previous : Type u}
  (realization : GlobalEquationRealization M Previous)

/-- Restrict the ambient equation only to the outer window selected by the
current local focus. -/
def outerState {point : M.atlas.Point}
    (previous : Previous)
    (focus : NestedFocus M point) : EquationState M.equation focus.outer :=
  realization.state previous focus.outer

/-- The inner equation state is derived by the registered outer-to-inner
restriction, not independently selected. -/
def innerState {point : M.atlas.Point}
    (previous : Previous)
    (focus : NestedFocus M point) : EquationState M.equation focus.inner :=
  focus.restrictToInner (realization.outerState previous focus)

/-- Restriction through the selected focus agrees with direct local
realization of the same ambient equation. -/
theorem innerState_eq {point : M.atlas.Point}
    (previous : Previous)
    (focus : NestedFocus M point) :
    realization.innerState previous focus =
      realization.state previous focus.inner :=
  realization.restrict_state previous focus.inner_outer

/-- The existing Core coordinate path for recentering the selected inner
window.  This is a one-primitive path, not a PDE-owned path language. -/
def innerRecenterPath {point : M.atlas.Point}
    {focus : NestedFocus M point} (recentered : RecenteredFocus M focus) :
    Core.CoordinatePath (coordinateSystem M) focus.inner
      (recentered.interface.targetWindow recentered.shift focus.inner) :=
  .cons recentered.innerCoordinate .nil

/-- Transport the focused inner equation along the registered recentering
coordinate using Core's path executor. -/
def recenteredInnerState {point : M.atlas.Point}
    (previous : Previous)
    {focus : NestedFocus M point} (recentered : RecenteredFocus M focus) :
    EquationState M.equation
      (recentered.interface.targetWindow recentered.shift focus.inner) :=
  (realization.innerState previous focus).transportPath
    (GlobalEquationRealization.innerRecenterPath recentered)

/-- The recentered object is exactly the restriction of the ambient object
after Core executes the registered coordinate path. -/
theorem recenteredInnerState_object_eq_restrict_run
    {point : M.atlas.Point}
    (previous : Previous)
    {focus : NestedFocus M point} (recentered : RecenteredFocus M focus) :
    (realization.recenteredInnerState previous recentered).object =
      M.atlas.restrict
        ((GlobalEquationRealization.innerRecenterPath recentered).run
          (realization.object previous))
        (recentered.interface.targetWindow recentered.shift focus.inner) := by
  apply EquationState.transportPath_object_eq_restrict_run
  rw [realization.innerState_eq]
  exact realization.state_object previous focus.inner

/-- Equation validity is preserved by the same existing Core coordinate-path
transport. -/
theorem recenteredInnerState_valid
    {point : M.atlas.Point}
    (previous : Previous)
    {focus : NestedFocus M point} (recentered : RecenteredFocus M focus) :
    M.equation.satisfies
      (realization.recenteredInnerState previous recentered).data :=
  (realization.recenteredInnerState previous recentered).valid

end GlobalEquationRealization

/-! ## Residual-ledger exposure -/

/-- One current local PDE residual, already selected by a preceding generic
localization step and therefore suitable for storage in Core's ordinary
ledger.  It contains only the selected focus and its valid outer equation
state; the cutoff split is deliberately not a field. -/
structure CurrentLocalEllipticResidual
    (M N : LocalModel.{u})
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (Interface : Type u)
    (Carrier Source : Interface → Type u)
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    (elliptic :
      LocalEllipticConstraint M N Admissible Interface Carrier Source) where
  ambient : M.problem.Ambient
  point : M.atlas.Point
  focus : NestedFocus M point
  admissible : Admissible ambient focus.outer
  componentSite : elliptic.ComponentSite ambient
  componentSite_eq : componentSite = elliptic.selectSite ambient focus admissible
  outerState : EquationState M.equation focus.outer
  outerState_object :
    outerState.object = M.atlas.restrict ambient focus.outer

namespace CurrentLocalEllipticResidual

variable {M N : LocalModel.{u}}
  {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
  {Interface : Type u}
  {Carrier Source : Interface → Type u}
  [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
  {elliptic :
    LocalEllipticConstraint M N Admissible Interface Carrier Source}

/-- The retained component interface of this exact residual.  It is derived
from the stored ambient object and site, never supplied separately, and it is
what makes the carrier space of a domain-carrying PDE well typed. -/
def interface
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    Interface :=
  elliptic.componentInterface residual.ambient residual.componentSite

/-- The component actually decomposed by this residual. -/
def whole
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    Carrier residual.interface :=
  elliptic.component residual.ambient residual.componentSite residual.outerState

/--
Read the current local elliptic residual from the literal incoming Core
stage.  This is the sole entry point used by downstream PDE strategies: the
residual is not reconstructed from the ambient problem input or copied from
an earlier stage.
-/
def residualQuery {Previous : Type u}
    [Core.Residual.HasResidual Previous
      (CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic)] :
    Core.Residual.Query Previous fun _ =>
      CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic :=
  Core.Residual.Query.residual

@[simp] theorem residualQuery_read {Previous : Type u}
    [Core.Residual.HasResidual Previous
      (CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic)]
    (previous : Previous) :
    (residualQuery (M := M) (N := N) (Interface := Interface)
      (Carrier := Carrier) (Source := Source) (elliptic := elliptic))
        previous =
      Core.Residual.residualOf previous :=
  rfl

/-- Derive the exact local/tail split from this one current local residual. -/
def split
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    ExactLocalTail (Carrier residual.interface) residual.whole :=
  LocalEllipticConstraint.split elliptic residual.ambient residual.componentSite
    residual.focus.inner_outer residual.outerState

/-- The complementary child of the derived split satisfies the homogeneous
elliptic constraint on the exact nested inner window. -/
theorem tail_homogeneous
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    elliptic.constraint
        (elliptic.carrierRestrict residual.focus.inner_outer
          residual.split.tailPart) = 0 :=
  LocalEllipticConstraint.constraint_restrict_tailTerm_zero
    elliptic residual.ambient residual.componentSite
    residual.focus.inner_outer residual.outerState

/-- Rebuilding the ambient object from this residual's own component returns
that exact object.  This is the reconstruction law consumed by Core's
atom/context assembly, restated at the residual's stored site. -/
theorem rebuild_whole
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    elliptic.rebuildComponent residual.ambient residual.componentSite
        residual.whole = residual.ambient := by
  obtain ⟨ambient, point, focus, admissible, componentSite, componentSite_eq,
    outerState, outerState_object⟩ := residual
  subst componentSite_eq
  exact elliptic.rebuild_component ambient focus admissible outerState
    outerState_object

/-- Interpret the exact complementary child as the homogeneous represented
equation on the selected inner window. -/
noncomputable def representedTail
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :
    RepresentedTail N residual.whole residual.split where
  sourceWindow := elliptic.tailWindow residual.focus.inner
  interpretTail := fun value =>
    elliptic.interpretCarrier (elliptic.tailWindow residual.focus.inner)
      (elliptic.carrierRestrict residual.focus.inner_outer value)
  equationState :=
    elliptic.homogeneousState (elliptic.tailWindow residual.focus.inner)
      (elliptic.carrierRestrict residual.focus.inner_outer
        residual.split.tailPart)
      residual.tail_homogeneous
  equationState_object :=
    elliptic.homogeneousState_object (elliptic.tailWindow residual.focus.inner)
      (elliptic.carrierRestrict residual.focus.inner_outer
        residual.split.tailPart)
      residual.tail_homogeneous

/-- Recenter the represented tail only through the existing Core coordinate
path derived by `TailFocus`. -/
noncomputable def recenterTail
    (residual : CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic)
    (focus : TailFocus N residual.representedTail.sourceWindow) :
    RecenteredTail residual.representedTail focus :=
  residual.representedTail.recenter focus

/-- Read the derived exact split from any literal Core ledger stage carrying
the current local residual. `dependentMap` retains the source occurrence, so
a newer local residual yields a newer split without copying a predecessor. -/
def splitQuery {Previous : Sort*}
    (current : Core.Residual.Query Previous
      (fun _ => CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic)) :
    Core.Residual.Query Previous (fun previous =>
      ExactLocalTail (Carrier (current previous).interface)
        (current previous).whole) :=
  current.dependentMap fun _ residual => residual.split

/-- Build the current local residual from the public ambient-to-local
equation realization and one selected nested focus. The outer state is
obtained by restriction of the ambient equation, never supplied separately. -/
def ofGlobal {Previous : Type u}
    (realization : GlobalEquationRealization M Previous)
    (previous : Previous) {point : M.atlas.Point}
    (focus : NestedFocus M point)
    (admissible :
      Admissible (realization.object previous) focus.outer) :
    CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic where
  ambient := realization.object previous
  point := point
  focus := focus
  admissible := admissible
  componentSite :=
    elliptic.selectSite (realization.object previous) focus admissible
  componentSite_eq := rfl
  outerState := realization.outerState previous focus
  outerState_object := realization.state_object previous focus.outer

/-! The public-presentation bridge is the canonical constructor used by PDE
adapters.  Focus selection and outer equation realization are both derived
from the same active residual: the site is read off the exact selected
context, the nested tower is assembled by the atlas `core` operator, and the
outer state is the restriction of the selected object to that tower's outer
window.  Nothing here is supplied as an execution callback, and no ambient
object is localized before Core has selected it. -/
def ofActiveResidual
    (presentation : PublicPresentation M) (residual : ActiveResidual M)
    (admissible :
      Admissible residual.object (presentation.focus residual).outer) :
    CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic where
  ambient := residual.object
  point := presentation.siteOf residual
  focus := presentation.focus residual
  admissible := admissible
  componentSite :=
    elliptic.selectSite residual.object (presentation.focus residual)
      admissible
  componentSite_eq := rfl
  outerState := presentation.outerState residual
  outerState_object := presentation.outerState_object residual

/-- The same constructor lifted along the active-residual query exported by
the framework's localization step.  No ledger is read twice and no residual is
reconstructed. -/
def ofActiveResidualQuery {Previous : Sort*}
    (presentation : PublicPresentation M)
    (active : Core.Residual.Query Previous fun _ => ActiveResidual M)
    (admissible : ∀ residual : ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer) :
    Core.Residual.Query Previous (fun _ =>
      CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic) :=
  active.map fun _ residual =>
    ofActiveResidual (N := N) (Interface := Interface) (Carrier := Carrier)
      (Source := Source) (elliptic := elliptic) presentation residual
      (admissible residual)

@[simp] theorem ofActiveResidualQuery_read {Previous : Sort*}
    (presentation : PublicPresentation M)
    (active : Core.Residual.Query Previous fun _ => ActiveResidual M)
    (admissible : ∀ residual : ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer)
    (previous : Previous) :
    (ofActiveResidualQuery (N := N) (Interface := Interface)
      (Carrier := Carrier) (Source := Source) (elliptic := elliptic)
      presentation active admissible) previous =
      ofActiveResidual (N := N) (Interface := Interface)
        (Carrier := Carrier) (Source := Source) (elliptic := elliptic)
        presentation (active previous)
        (admissible (active previous)) :=
  rfl

@[simp] theorem splitQuery_read {Previous : Sort*}
    (current : Core.Residual.Query Previous
      (fun _ =>
        CurrentLocalEllipticResidual M N Admissible Interface Carrier Source
      elliptic))
    (previous : Previous) :
    (splitQuery current) previous = (current previous).split :=
  rfl

end CurrentLocalEllipticResidual

end Hypostructure.PDE
