import Hypostructure.Core.Strategy.Dag
import Hypostructure.PDE.Model
import Hypostructure.PDE.EllipticLocalTail

/-!
# Local closure for represented PDEs

This module is the PDE-facing adapter for Core's existing dichotomy.

* `closureDichotomy` turns a public pointwise local presentation into the
  exhaustive alternative "the local certificates assemble the target" or
  "the exact local-closure proposition fails".

The adapter owns no route, ledger, CT execution, or target proof.  Core
performs the dichotomy routing and retains the selected branch witness.
-/

namespace Hypostructure.PDE.Strategy.LocalClosureAlgebra

open Hypostructure
open scoped ContDiff

universe u v w

variable (M : PDE.LocalModel.{u}) (T : Core.Target M.problem)

/-- The stable problem residual consumed by the public PDE presentation. -/
abbrev Input := Core.Strategy.ProblemInput M.problem

/--
A global PDE target presented as one admissible representative together with
pointwise local facts at every relevant point.

`localize` and `assemble` state the exact mathematical equivalence.  They do
not execute a strategy: the sealed Core dichotomy below decides which side is
present and appends that side to the literal predecessor ledger.
-/
structure Presentation where
  Witness : Input M → Type u
  admissible : (input : Input M) → Witness input → Prop
  relevant : Input M → M.atlas.Point → Prop
  localAt : (input : Input M) → Witness input → M.atlas.Point → Prop
  localize : ∀ input, T.Predicate input.object →
    ∃ witness, admissible input witness ∧
      ∀ point, relevant input point → localAt input witness point
  assemble : ∀ input,
    (∃ witness, admissible input witness ∧
      ∀ point, relevant input point → localAt input witness point) →
        T.Predicate input.object
  metadata : Core.Documentation := {}
  localMetadata : Core.Documentation := {}
  failureMetadata : Core.Documentation := {}

namespace Presentation

variable {M T}

/-- The exact local formulation of the registered global target. -/
def LocalClosure (presentation : Presentation M T) (input : Input M) : Prop :=
  ∃ witness, presentation.admissible input witness ∧
    ∀ point, presentation.relevant input point →
      presentation.localAt input witness point

theorem target_iff_localClosure
    (presentation : Presentation M T) (input : Input M) :
    T.Predicate input.object ↔ presentation.LocalClosure input :=
  ⟨presentation.localize input, presentation.assemble input⟩

/--
Register the target/local-closure alternative as an ordinary Core
dichotomy.  The closing arm contains the literal pointwise certificate; the
open arm contains its exact negation.  No point, branch, or outcome is chosen
by the application.
-/
noncomputable def closureDichotomy
    (presentation : Presentation M T) :
    Core.DichotomyData M.problem T where
  LeftPayload := fun input => PLift (presentation.LocalClosure input)
  RightPayload := fun input => PLift (¬ presentation.LocalClosure input)
  classify := fun input =>
    letI := Classical.propDecidable (presentation.LocalClosure input)
    if closure : presentation.LocalClosure input then
      .inl ⟨closure⟩
    else
      .inr ⟨closure⟩
  closeLeft := some ⟨fun input closure =>
    presentation.assemble input closure.down⟩
  metadata := presentation.metadata
  leftMetadata := presentation.localMetadata
  rightMetadata := presentation.failureMetadata

/-! ## Exhaustive local-to-global closure

The only local-to-global argument the framework performs, and it is the same
for every equation: every relevant point lies in some window of an
amalgamated family, the amalgamated witness inherits each window's local
property at the points of that window, and the registered pointwise
formulation of the target then yields the global statement --- which
contradicts the residual's target avoidance.

Nothing below is equation specific, and nothing is assumed: `assemble` is the
application's already-registered equivalence between the target and its
pointwise form, `witness` is Core's amalgamation, and the remaining inputs
are the local certificates themselves.
-/

/--
**The amalgamated witness inherits any window-transportable pointwise fact.**

The predicate is left free, so one exhaustion serves *every* pointwise
component of a presentation --- its local predicate and its admissibility
alike.  This is what removes the last global hypothesis from the framework's
local closure: nothing below ever quantifies over a whole object.
-/
theorem witness_pointwise
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (input : Input M) {Carrier : Type w}
    (toWitness : (M.atlas.Point → Value) → Carrier)
    (Pointwise : Carrier → M.atlas.Point → Prop)
    (congruent : ∀ (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          Pointwise (toWitness left) point →
            Pointwise (toWitness right) point)
    {point : M.atlas.Point} {index : data.Index input.object}
    (mem : data.Mem (data.windowOf input.object index) point)
    (localCertificate :
      Pointwise (toWitness (data.localWitness input.object index)) point) :
    Pointwise (toWitness (data.witness input.object)) point :=
  congruent index _ _
    (fun _place placeMem => (data.witness_eq input.object placeMem).symm)
    point mem localCertificate

/--
The amalgamated witness satisfies the presentation's local predicate at every
point of any window containing that point.
-/
theorem witness_localAt
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (presentation : Presentation M T) (input : Input M)
    (toWitness : (M.atlas.Point → Value) → presentation.Witness input)
    (congruent : ∀ (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness left) point →
            presentation.localAt input (toWitness right) point)
    {point : M.atlas.Point} {index : data.Index input.object}
    (mem : data.Mem (data.windowOf input.object index) point)
    (localCertificate : presentation.localAt input
      (toWitness (data.localWitness input.object index)) point) :
    presentation.localAt input (toWitness (data.witness input.object)) point :=
  congruent index _ _
    (fun _place placeMem => (data.witness_eq input.object placeMem).symm)
    point mem localCertificate

/--
The registered global target, obtained from exhaustion of the local windows
alone.
-/
theorem target_of_exhaustion
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (presentation : Presentation M T) (input : Input M)
    (toWitness : (M.atlas.Point → Value) → presentation.Witness input)
    (admissible : presentation.admissible input
      (toWitness (data.witness input.object)))
    (congruent : ∀ (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness left) point →
            presentation.localAt input (toWitness right) point)
    (localCertificate : ∀ (index : data.Index input.object)
      (point : M.atlas.Point), presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        presentation.localAt input
          (toWitness (data.localWitness input.object index)) point)
    (cover : ∀ point, presentation.relevant input point →
      ∃ index : data.Index input.object,
        data.Mem (data.windowOf input.object index) point) :
    T.Predicate input.object :=
  presentation.assemble input
    ⟨toWitness (data.witness input.object), admissible, fun point relevant =>
      (cover point relevant).elim fun index mem =>
        witness_localAt data presentation input toWitness congruent mem
          (localCertificate index point relevant mem)⟩

/-! ### Admissibility, presented pointwise

`Presentation.admissible` is the last field that speaks about a witness as a
whole.  A presentation that says *where* its witness has to be admissible
turns that field into one more pointwise fact, and the amalgamated witness
then acquires it by the same exhaustion that gives it the local predicate.

The consequence is the point of this section: after `LocalAdmissibility`, the
framework's exhaustive closure has **no** hypothesis about a whole object.
Every input is a statement about one window of one residual.
-/

/--
**Admissibility presented pointwise.**

`admissibleAt` says what admissibility means at a single point, and
`admissible_of_pointwise` records that the presentation's own admissibility
follows from
the conjunction of those facts over the relevant points.  For a target
presented as "this representative represents that datum", the pointwise form
is the representation read on one window --- a local residual, not a global
identity.
-/
structure LocalAdmissibility (presentation : Presentation M T) where
  admissibleAt : (input : Input M) → presentation.Witness input →
    M.atlas.Point → Prop
  admissible_of_pointwise : ∀ (input : Input M)
    (witness : presentation.Witness input),
    (∀ point, presentation.relevant input point →
      admissibleAt input witness point) →
        presentation.admissible input witness

/--
The amalgamated witness is admissible, from per-window admissibility alone.

Same shape as `target_of_exhaustion`, same proof, and no global input: the
cover reduces admissibility at a point to admissibility on one window, and
`witness_pointwise` transports it.
-/
theorem admissible_of_exhaustion
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    {presentation : Presentation M T}
    (localAdmissibility : LocalAdmissibility presentation) (input : Input M)
    (toWitness : (M.atlas.Point → Value) → presentation.Witness input)
    (congruent : ∀ (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          localAdmissibility.admissibleAt input (toWitness left) point →
            localAdmissibility.admissibleAt input (toWitness right) point)
    (localCertificate : ∀ (index : data.Index input.object)
      (point : M.atlas.Point), presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        localAdmissibility.admissibleAt input
          (toWitness (data.localWitness input.object index)) point)
    (cover : ∀ point, presentation.relevant input point →
      ∃ index : data.Index input.object,
        data.Mem (data.windowOf input.object index) point) :
    presentation.admissible input (toWitness (data.witness input.object)) :=
  localAdmissibility.admissible_of_pointwise input _ fun point relevant =>
    (cover point relevant).elim fun index mem =>
      witness_pointwise data input toWitness
        (fun witness place => localAdmissibility.admissibleAt input witness place)
        congruent mem (localCertificate index point relevant mem)

/-! ### Admissibility, presented as a germ

`LocalAdmissibility` says *where* a witness has to be admissible; it does not
by itself make the pointwise statement local.  The shape below does, and it is
the shape every represented PDE has: at a point, a witness is admissible when
the point's own witness-independent obligation holds and the witness agrees,
*near that point*, with the representative the equation already names.

Both obligations of the exhaustive closure then discharge with no application
proof.  `admissible_of_pointwise` is `Filter.EventuallyEq.eq_of_nhds` --- germ
agreement at a point is agreement at that point --- and the congruence is the
argument of `congruent_of_germ` read on the admissibility component.

Nothing here quantifies over an object: `Fixed` is a predicate on one point and
the germ is a statement about one neighbourhood.
-/

section GermAdmissibility

variable {Place : Type w} {Value : Type v}

/--
**Admissibility at a point, as a germ.**

`Fixed` is the part that does not depend on the representative at all, and
`canonical` is the representative the application's own data names.  An
application states its pointwise admissibility *as* this definition and thereby
inherits both discharges below without writing a proof.
-/
def germAdmissibleAt (topology : TopologicalSpace Place) (Fixed : Place → Prop)
    (canonical witness : Place → Value) (point : Place) : Prop :=
  Fixed point ∧
    ∀ᶠ place in @nhds Place topology point, witness place = canonical place

/-- The germ condition for `germAdmissibleAt`, proved once for every PDE: two
witnesses that agree near the point are admissible there together. -/
theorem germAdmissibleAt_congr (topology : TopologicalSpace Place)
    {Fixed : Place → Prop} {canonical left right : Place → Value} {point : Place}
    (agree : ∀ᶠ place in @nhds Place topology point, left place = right place) :
    germAdmissibleAt topology Fixed canonical left point →
      germAdmissibleAt topology Fixed canonical right point :=
  fun germ => ⟨germ.1, germ.2.mp (agree.mono fun _place agreePlace equal =>
    agreePlace.symm.trans equal)⟩

/-- The named representative is admissible wherever its fixed obligation holds:
the germ is `rfl`.  This is the whole per-window admissibility certificate of an
amalgamation whose reading is the named representative. -/
theorem germAdmissibleAt_canonical (topology : TopologicalSpace Place)
    {Fixed : Place → Prop} (canonical : Place → Value) {point : Place}
    (fixed : Fixed point) :
    germAdmissibleAt topology Fixed canonical canonical point :=
  ⟨fixed, Filter.Eventually.of_forall fun _place => rfl⟩

end GermAdmissibility

/--
**Pointwise admissibility, built from the germ shape.**

The application supplies no proof about a whole object: `admissible_of_agree`
consumes only the pointwise facts at the relevant points, and it is where the
equation --- not a gluing --- names the representative.
-/
noncomputable def LocalAdmissibility.ofGerm
    (topology : TopologicalSpace M.atlas.Point)
    {Value : Type v} {presentation : Presentation M T}
    (ofWitness : (input : Input M) → presentation.Witness input →
      M.atlas.Point → Value)
    (Fixed : Input M → M.atlas.Point → Prop)
    (canonical : (input : Input M) → M.atlas.Point → Value)
    (admissible_of_agree : ∀ (input : Input M)
      (witness : presentation.Witness input),
      (∀ place, presentation.relevant input place → Fixed input place) →
      (∀ place, presentation.relevant input place →
          ofWitness input witness place = canonical input place) →
        presentation.admissible input witness) :
    LocalAdmissibility presentation where
  admissibleAt := fun input witness point =>
    germAdmissibleAt topology (Fixed input) (canonical input)
      (ofWitness input witness) point
  admissible_of_pointwise := fun input witness pointwise =>
    admissible_of_agree input witness
      (fun place relevant => (pointwise place relevant).1)
      (fun place relevant =>
        Filter.EventuallyEq.eq_of_nhds (pointwise place relevant).2)

/--
**Generic discharge of the admissibility congruence.**

The exact analogue of `congruent_of_germ` for the admissibility component: on a
topology in which the windows are open, agreement on a window is agreement near
each of its points, and `germAdmissibleAt` sees nothing else.
-/
theorem ofGerm_congruentAdmissible (topology : TopologicalSpace M.atlas.Point)
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    {presentation : Presentation M T}
    (toWitness : (input : Input M) →
      (M.atlas.Point → Value) → presentation.Witness input)
    (ofWitness : (input : Input M) → presentation.Witness input →
      M.atlas.Point → Value)
    (retract : ∀ (input : Input M) (values : M.atlas.Point → Value),
      ofWitness input (toWitness input values) = values)
    (Fixed : Input M → M.atlas.Point → Prop)
    (canonical : (input : Input M) → M.atlas.Point → Value)
    (admissible_of_agree : ∀ (input : Input M)
      (witness : presentation.Witness input),
      (∀ place, presentation.relevant input place → Fixed input place) →
      (∀ place, presentation.relevant input place →
          ofWitness input witness place = canonical input place) →
        presentation.admissible input witness)
    (isOpen : ∀ (object : M.problem.Ambient) (index : data.Index object),
      IsOpen (X := M.atlas.Point)
        {place | data.Mem (data.windowOf object index) place}) :
    ∀ (input : Input M) (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          (LocalAdmissibility.ofGerm topology ofWitness Fixed canonical
              admissible_of_agree).admissibleAt input (toWitness input left)
              point →
            (LocalAdmissibility.ofGerm topology ofWitness Fixed canonical
              admissible_of_agree).admissibleAt input (toWitness input right)
              point := by
  intro input index left right agree point mem germ
  have germLeft :
      germAdmissibleAt topology (Fixed input) (canonical input) left point := by
    have base :
        germAdmissibleAt topology (Fixed input) (canonical input)
          (ofWitness input (toWitness input left)) point := germ
    rwa [retract] at base
  have nearby :
      ∀ᶠ place in @nhds M.atlas.Point topology point, left place = right place := by
    filter_upwards [(isOpen input.object index).mem_nhds mem] with place placeMem
    exact agree place placeMem
  show germAdmissibleAt topology (Fixed input) (canonical input)
    (ofWitness input (toWitness input right)) point
  rw [retract]
  exact germAdmissibleAt_congr topology nearby germLeft

/--
**The fully local closing dichotomy.**

`exhaustiveClosureDichotomy` still asked for the amalgamated witness to be
admissible, which is a statement about a whole object.  With admissibility
presented pointwise that hypothesis disappears: every remaining input is a
per-window certificate, a per-window congruence, or the cover.  Both arms
close, and no application supplies a global fact or a proof of the target.
-/
noncomputable def exhaustiveLocalClosureDichotomy
    (presentation : Presentation M T)
    (localAdmissibility : LocalAdmissibility presentation)
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (toWitness : (input : Input M) →
      (M.atlas.Point → Value) → presentation.Witness input)
    (congruentAdmissible : ∀ (input : Input M) (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          localAdmissibility.admissibleAt input (toWitness input left) point →
            localAdmissibility.admissibleAt input (toWitness input right) point)
    (congruentLocal : ∀ (input : Input M) (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness input left) point →
            presentation.localAt input (toWitness input right) point)
    (admissibleCertificate : ∀ (input : Input M)
      (index : data.Index input.object) (point : M.atlas.Point),
      presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        localAdmissibility.admissibleAt input
          (toWitness input (data.localWitness input.object index)) point)
    (localCertificate : ∀ (input : Input M) (index : data.Index input.object)
      (point : M.atlas.Point), presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        presentation.localAt input
          (toWitness input (data.localWitness input.object index)) point)
    (cover : ∀ (input : Input M) (point : M.atlas.Point),
      presentation.relevant input point →
        ∃ index : data.Index input.object,
          data.Mem (data.windowOf input.object index) point) :
    Core.DichotomyData M.problem T :=
  { presentation.closureDichotomy with
    closeRight := some ⟨fun input _failure =>
      target_of_exhaustion data presentation input (toWitness input)
        (admissible_of_exhaustion data localAdmissibility input (toWitness input)
          (congruentAdmissible input) (admissibleCertificate input)
          (cover input))
        (congruentLocal input) (localCertificate input) (cover input)⟩ }

/-! ### Classical interior regularity, and its congruence discharge

Essentially every PDE target is presented pointwise in the same shape: a fact
that does not depend on the representative, together with classical smoothness
of the representative on the object's own domain.  The framework owns that
shape and its germ-locality, so no application ever proves a congruence
lemma. -/

section ClassicalRegularity

variable {Place : Type*} [NormedAddCommGroup Place] [NormedSpace Real Place]
  {Value : Type*} [NormedAddCommGroup Value] [NormedSpace Real Value]

/-- Classical smoothness at a point sees only the germ of the representative
there.  This is mathlib's `ContDiffWithinAt.congr_of_eventuallyEq`, stated as
the germ condition the exhaustive closure consumes. -/
theorem contDiffWithinAt_congr_of_eventuallyEq {domain : Set Place}
    {left right : Place → Value} {point : Place}
    (agree : left =ᶠ[nhds point] right)
    (smooth : ContDiffWithinAt Real ∞ left domain point) :
    ContDiffWithinAt Real ∞ right domain point :=
  smooth.congr_of_eventuallyEq (agree.symm.filter_mono nhdsWithin_le_nhds)
    agree.symm.eq_of_nhds

/-- **The classical interior-regularity local predicate.**

`Fixed` is whatever the point has to satisfy independently of the chosen
representative; the second conjunct is the representative's own smoothness.
An application states its local predicate *as* this definition and thereby
inherits the congruence discharge below without writing a proof. -/
def classicalRegularityAt (Fixed : Prop) (domain : Set Place)
    (witness : Place → Value) (point : Place) : Prop :=
  Fixed ∧ ContDiffWithinAt Real ∞ witness domain point

/-- The germ condition for `classicalRegularityAt`, proved once for every
PDE.  Feed it to `congruent_of_germ` and the congruence obligation of
`target_of_exhaustion` is discharged with no application input. -/
theorem classicalRegularityAt_congr {Fixed : Prop} {domain : Set Place}
    {left right : Place → Value} {point : Place}
    (agree : left =ᶠ[nhds point] right) :
    classicalRegularityAt Fixed domain left point →
      classicalRegularityAt Fixed domain right point :=
  fun regular =>
    ⟨regular.1, contDiffWithinAt_congr_of_eventuallyEq agree regular.2⟩

end ClassicalRegularity

/--
**Generic discharge of the congruence obligation.**

`target_of_exhaustion` asks that the local predicate transfer between two
witnesses that agree on a whole window.  Whenever the atlas points carry a
topology in which the windows are open, agreement on a window already implies
agreement *near* each of its points, so the obligation collapses to the germ
condition "the local predicate only sees the witness near the point".

That germ condition is what every classical local regularity predicate
satisfies by construction --- `ContDiffWithinAt.congr_of_eventuallyEq` and its
relatives --- so no application ever has to reason about windows here.
-/
theorem congruent_of_germ
    (topology : TopologicalSpace M.atlas.Point)
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (presentation : Presentation M T)
    (toWitness : (input : Input M) →
      (M.atlas.Point → Value) → presentation.Witness input)
    (isOpen : ∀ (object : M.problem.Ambient) (index : data.Index object),
      IsOpen (X := M.atlas.Point)
        {place | data.Mem (data.windowOf object index) place})
    (germ : ∀ (input : Input M) (left right : M.atlas.Point → Value)
      (point : M.atlas.Point),
      (∀ᶠ place in @nhds M.atlas.Point topology point, left place = right place) →
        presentation.localAt input (toWitness input left) point →
          presentation.localAt input (toWitness input right) point) :
    ∀ (input : Input M) (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness input left) point →
            presentation.localAt input (toWitness input right) point := by
  intro input index left right agree point mem
  refine germ input left right point ?_
  filter_upwards [(isOpen input.object index).mem_nhds mem] with place placeMem
  exact agree place placeMem

/--
The closing dichotomy: **both** arms are discharged by the framework.

`closureDichotomy` fills only `closeLeft`, because the left payload already
carries the pointwise local closure and `assemble` turns it into the target.
The right arm is closed here from exactly the same window data: a
`WindowAmalgamation`, the per-window local certificates, and a cover of the
relevant points.  `target_of_exhaustion` turns those into the target outright,
so neither arm ever needs a problem-specific proof and the registered
dichotomy closes.

Every hypothesis is *local*: each speaks about one window of one residual.
Nothing here quantifies over a global object, and no application supplies a
proof of the registered statement.
-/
noncomputable def exhaustiveClosureDichotomy
    (presentation : Presentation M T)
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (toWitness : (input : Input M) →
      (M.atlas.Point → Value) → presentation.Witness input)
    (admissible : ∀ input : Input M, presentation.admissible input
      (toWitness input (data.witness input.object)))
    (congruent : ∀ (input : Input M) (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness input left) point →
            presentation.localAt input (toWitness input right) point)
    (localCertificate : ∀ (input : Input M) (index : data.Index input.object)
      (point : M.atlas.Point), presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        presentation.localAt input
          (toWitness input (data.localWitness input.object index)) point)
    (cover : ∀ (input : Input M) (point : M.atlas.Point),
      presentation.relevant input point →
        ∃ index : data.Index input.object,
          data.Mem (data.windowOf input.object index) point) :
    Core.DichotomyData M.problem T :=
  { presentation.closureDichotomy with
    closeRight := some ⟨fun input _failure =>
      target_of_exhaustion data presentation input (toWitness input)
        (admissible input) (congruent input) (localCertificate input)
        (cover input)⟩ }

/--
Exhaustion closes a target-avoiding residual.

This is the contradiction the whole local pipeline exists to produce: the
windows are exhausted, the global statement follows, and it contradicts the
avoidance carried by the active residual Core selected.
-/
theorem exhaustion_contradiction
    {Value : Type v} (data : PDE.WindowAmalgamation M Value)
    (presentation : Presentation M T) (input : Input M)
    (toWitness : (M.atlas.Point → Value) → presentation.Witness input)
    (admissible : presentation.admissible input
      (toWitness (data.witness input.object)))
    (congruent : ∀ (index : data.Index input.object)
      (left right : M.atlas.Point → Value),
      (∀ place, data.Mem (data.windowOf input.object index) place →
        left place = right place) →
        ∀ point, data.Mem (data.windowOf input.object index) point →
          presentation.localAt input (toWitness left) point →
            presentation.localAt input (toWitness right) point)
    (localCertificate : ∀ (index : data.Index input.object)
      (point : M.atlas.Point), presentation.relevant input point →
      data.Mem (data.windowOf input.object index) point →
        presentation.localAt input
          (toWitness (data.localWitness input.object index)) point)
    (cover : ∀ point, presentation.relevant input point →
      ∃ index : data.Index input.object,
        data.Mem (data.windowOf input.object index) point)
    (avoids : ¬ T.Predicate input.object) : False :=
  avoids
    (target_of_exhaustion data presentation input toWitness admissible
      congruent localCertificate cover)

end Presentation

end Hypostructure.PDE.Strategy.LocalClosureAlgebra
