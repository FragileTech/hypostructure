import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Residual.Focus
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Representation

/-!
# Exact additive local/tail assembly
-/

namespace Hypostructure.PDE

universe u v uPrevious

/--
An exact additive split of one represented local quantity.

Both summands are retained.  This is deliberately not a `Sum`: a local/tail
decomposition produces the local term and the tail simultaneously.
-/
structure ExactLocalTail (Carrier : Type v) [Add Carrier] (whole : Carrier) where
  localPart : Carrier
  tailPart : Carrier
  exact_reconstruction : localPart + tailPart = whole

namespace ExactLocalTail

/--
**The canonical split of a whole by one of its parts.**

Only the local term is chosen.  The tail is then *defined* as what is left
over, so the reconstruction law is an identity of the ambient additive group
rather than a hypothesis anybody has to supply --- which is exactly the move
`ComponentEllipticOperator.tailTermAt` makes for its graded carrier, available
here to any carrier that subtracts.

An application that has produced a local child of a distribution, a function
or a state therefore never states, and never proves, its own reconstruction
lemma: it applies this.
-/
def ofSub {Carrier : Type v} [AddCommGroup Carrier]
    (whole localPart : Carrier) : ExactLocalTail Carrier whole where
  localPart := localPart
  tailPart := whole - localPart
  exact_reconstruction := by abel

@[simp] theorem ofSub_localPart {Carrier : Type v} [AddCommGroup Carrier]
    (whole localPart : Carrier) :
    (ofSub whole localPart).localPart = localPart := rfl

@[simp] theorem ofSub_tailPart {Carrier : Type v} [AddCommGroup Carrier]
    (whole localPart : Carrier) :
    (ofSub whole localPart).tailPart = whole - localPart := rfl

/-- Read the local summand on the exact framework-owned active branch. -/
def activeLocalQuery
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTail (Carrier previous active)
        (whole previous active)) :
    Core.Residual.Focus.ActiveQuery focus Carrier :=
  split.map fun _previous _active decomposition =>
    decomposition.localPart

/-- Read the tail summand from the same exact active decomposition. -/
def activeTailQuery
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTail (Carrier previous active)
        (whole previous active)) :
    Core.Residual.Focus.ActiveQuery focus Carrier :=
  split.map fun _previous _active decomposition =>
    decomposition.tailPart

/-- Both active children reconstruct the exact active incoming quantity. -/
theorem activeQueries_reconstruct
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTail (Carrier previous active)
        (whole previous active))
    (previous : Previous) (active : focus.Active previous) :
    (activeLocalQuery whole split) previous active +
        (activeTailQuery whole split) previous active =
      whole previous active :=
  (split previous active).exact_reconstruction

/-- Read the local summand from an exact split on the current residual. -/
def localQuery
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTail (Carrier previous) (whole previous)) :
    Core.Residual.Query Previous Carrier :=
  split.map fun _ decomposition => decomposition.localPart

/-- Read the tail summand from the same exact residual split. -/
def tailQuery
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTail (Carrier previous) (whole previous)) :
    Core.Residual.Query Previous Carrier :=
  split.map fun _ decomposition => decomposition.tailPart

/--
The two queried children reconstruct the incoming quantity.  This theorem is
indexed by the exact source residual, so neither child can be detached from
the decomposition that produced it.
-/
theorem queries_reconstruct
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTail (Carrier previous) (whole previous))
    (previous : Previous) :
    (localQuery whole split) previous +
        (tailQuery whole split) previous =
      whole previous :=
  (split previous).exact_reconstruction

end ExactLocalTail

/--
An exact local/tail split modulo a caller-supplied local equivalence.

This is the appropriate form for PDE germs: the two represented summands need
only reconstruct the incoming object against tests supported in the selected
window.  The relation is mathematical presentation data; it does not choose a
route or execute a strategy.
-/
structure ExactLocalTailOn
    (Carrier : Type v) [Add Carrier]
    (SameOn : Carrier → Carrier → Prop) (whole : Carrier) where
  localPart : Carrier
  tailPart : Carrier
  exact_reconstruction : SameOn (localPart + tailPart) whole

namespace ExactLocalTailOn

/-- Read the germ-local child on the exact framework-owned active branch. -/
def activeLocalQuery
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (SameOn : (previous : Previous) -> (active : focus.Active previous) ->
      Carrier previous active -> Carrier previous active -> Prop)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTailOn (Carrier previous active)
        (SameOn previous active) (whole previous active)) :
    Core.Residual.Focus.ActiveQuery focus Carrier :=
  split.map fun _previous _active decomposition =>
    decomposition.localPart

/-- Read the germ-tail child from the same exact active decomposition. -/
def activeTailQuery
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (SameOn : (previous : Previous) -> (active : focus.Active previous) ->
      Carrier previous active -> Carrier previous active -> Prop)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTailOn (Carrier previous active)
        (SameOn previous active) (whole previous active)) :
    Core.Residual.Focus.ActiveQuery focus Carrier :=
  split.map fun _previous _active decomposition =>
    decomposition.tailPart

/-- Both active germ children reconstruct the active incoming germ locally. -/
theorem activeQueries_reconstruct
    {Previous : Type uPrevious}
    {focus : Core.Residual.Focus.Profile Previous}
    {Carrier : (previous : Previous) ->
      focus.Active previous -> Type v}
    [∀ previous active, Add (Carrier previous active)]
    (whole : Core.Residual.Focus.ActiveQuery focus Carrier)
    (SameOn : (previous : Previous) -> (active : focus.Active previous) ->
      Carrier previous active -> Carrier previous active -> Prop)
    (split : Core.Residual.Focus.ActiveQuery focus fun previous active =>
      ExactLocalTailOn (Carrier previous active)
        (SameOn previous active) (whole previous active))
    (previous : Previous) (active : focus.Active previous) :
    SameOn previous active
      ((activeLocalQuery whole SameOn split) previous active +
        (activeTailQuery whole SameOn split) previous active)
      (whole previous active) :=
  (split previous active).exact_reconstruction

/-- Read the local child of a residual-indexed germ decomposition. -/
def localQuery
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (SameOn : (previous : Previous) →
      Carrier previous → Carrier previous → Prop)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTailOn (Carrier previous) (SameOn previous)
        (whole previous)) :
    Core.Residual.Query Previous Carrier :=
  split.map fun _ decomposition => decomposition.localPart

/-- Read the tail child of the same residual-indexed germ decomposition. -/
def tailQuery
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (SameOn : (previous : Previous) →
      Carrier previous → Carrier previous → Prop)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTailOn (Carrier previous) (SameOn previous)
        (whole previous)) :
    Core.Residual.Query Previous Carrier :=
  split.map fun _ decomposition => decomposition.tailPart

/-- The two queried children reconstruct the incoming germ locally. -/
theorem queries_reconstruct
    {Previous : Type uPrevious}
    {Carrier : Previous → Type v}
    [∀ previous, Add (Carrier previous)]
    (whole : Core.Residual.Query Previous Carrier)
    (SameOn : (previous : Previous) →
      Carrier previous → Carrier previous → Prop)
    (split : Core.Residual.Query Previous fun previous =>
      ExactLocalTailOn (Carrier previous) (SameOn previous)
        (whole previous))
    (previous : Previous) :
    SameOn previous
      ((localQuery whole SameOn split) previous +
        (tailQuery whole SameOn split) previous)
      (whole previous) :=
  (split previous).exact_reconstruction

end ExactLocalTailOn

/--
An exact local/tail split of one additive component of an ambient PDE
object.

`Interface` retains the source object data needed to rebuild the ambient
object, while `Carrier` is the component actually decomposed.  Thus a field
may retain its velocity, forcing, and domain in the interface while only its
pressure distribution is split into atom and context.
-/
structure ComponentLocalTailAssembly
    (P : Core.Problem.{u, u}) (S : RepresentationSemantics P) where
  Interface : Type u
  Site : P.Ambient -> Type u
  interface : (object : P.Ambient) -> Site object -> Interface
  Carrier : Interface -> Type v
  add : (source : Interface) -> Add (Carrier source)
  SameOn : (source : Interface) ->
    Carrier source -> Carrier source -> Prop
  whole : (source : Interface) -> Carrier source
  split : (object : P.Ambient) -> (site : Site object) ->
    let source := interface object site
    letI := add source
    ExactLocalTailOn (Carrier source) (SameOn source) (whole source)
  rebuild : {source : Interface} -> Carrier source -> P.Ambient
  rebuild_equivalent : (object : P.Ambient) -> (site : Site object) ->
    let source := interface object site
    (component : Carrier source) ->
      SameOn source component (whole source) ->
        S.equivalent (rebuild component) object

namespace ComponentLocalTailAssembly

/--
Expose a component split through Core's existing exact atom/context
assembly.  Both Core children are values of the component carrier; the
assembled ambient value is rebuilt from their sum and the retained source
interface.
-/
def toCoreAssembly
    {P : Core.Problem.{u, u}} {S : RepresentationSemantics P}
    (A : ComponentLocalTailAssembly.{u, v} P S) :
    Core.AtomContextAssembly.{u, u, u, u, v, v} P S where
  Interface := A.Interface
  Site := A.Site
  interface := A.interface
  Atom := A.Carrier
  Context := A.Carrier
  compatible := fun {source} localPart tailPart =>
    letI := A.add source
    A.SameOn source (localPart + tailPart) (A.whole source)
  atom := fun object site =>
    let source := A.interface object site
    letI := A.add source
    (A.split object site).localPart
  context := fun object site =>
    let source := A.interface object site
    letI := A.add source
    (A.split object site).tailPart
  assemble := fun {source} localPart tailPart =>
    letI := A.add source
    A.rebuild (localPart + tailPart)
  extractedCompatible := fun object site =>
    let source := A.interface object site
    letI := A.add source
    (A.split object site).exact_reconstruction
  reconstruct := fun object site =>
    let source := A.interface object site
    letI := A.add source
    A.rebuild_equivalent object site
      ((A.split object site).localPart + (A.split object site).tailPart)
      (A.split object site).exact_reconstruction

end ComponentLocalTailAssembly

/--
Primitive local/tail data. Reconstruction is literal equality; Core owns the
resulting atom/context assembly and its execution interfaces.
-/
structure LocalTailAssembly (P : Core.Problem.{u, u}) [Add P.Ambient] where
  Localizer : Type u
  localPart : Localizer -> P.Ambient -> P.Ambient
  tailPart : Localizer -> P.Ambient -> P.Ambient
  compatible : Localizer -> P.Ambient -> Prop
  exact_reconstruction : forall (localizer : Localizer) (G : P.Ambient),
    compatible localizer G ->
      localPart localizer G + tailPart localizer G = G

namespace LocalTailAssembly

/-- Register exact additive splitting as Core atom/context assembly. -/
def toCoreAssembly {P : Core.Problem.{u, u}} [Add P.Ambient]
    (A : LocalTailAssembly P) (S : RepresentationSemantics P) :
    Core.AtomContextAssembly P S where
  Interface := A.Localizer
  Site := fun object => {localizer : A.Localizer // A.compatible localizer object}
  interface := fun _ site => site.1
  Atom := fun _ => P.Ambient
  Context := fun _ => P.Ambient
  compatible := fun {localizer} atomPart tail =>
    Exists fun object =>
      A.compatible localizer object ∧
      atomPart = A.localPart localizer object ∧
      tail = A.tailPart localizer object
  atom := fun object site => A.localPart site.1 object
  context := fun object site => A.tailPart site.1 object
  assemble := fun atom context => atom + context
  extractedCompatible := fun object site =>
    ⟨object, site.2, rfl, rfl⟩
  reconstruct := by
    intro object site
    rw [A.exact_reconstruction site.1 object site.2]

end LocalTailAssembly

end Hypostructure.PDE
