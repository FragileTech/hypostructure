import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
import Hypostructure.PDE.EllipticLocalTail
import Hypostructure.PDE.LocalTail

/-!
# Local-term/tail obstruction presentation

This module is a thin PDE interpretation of Core's pointwise atom--context
presentation.  A caller owns a typed query on its literal predecessor; this
module only maps each queried local PDE presentation to the corresponding
Core presentation.  It introduces no registration, stage, ledger operation,
route, executor, or closure.
-/

namespace Hypostructure.PDE.Strategy.LocalTailObstructionDichotomy

open Hypostructure

universe u

/-- The exact component carrier selected by one local split site. -/
abbrev ComponentCarrier
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    (assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics)
    (object : P.Ambient) (site : assembly.Site object) :=
  assembly.Carrier (assembly.interface object site)

/-- The local component derived from the exact split at one local site. -/
def localTerm
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    (assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics)
    (object : P.Ambient) (site : assembly.Site object) :
    ComponentCarrier assembly object site :=
  let source := assembly.interface object site
  letI := assembly.add source
  (assembly.split object site).localPart

/-- The complementary tail derived from that same exact split. -/
def tailTerm
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    (assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics)
    (object : P.Ambient) (site : assembly.Site object) :
    ComponentCarrier assembly object site :=
  let source := assembly.interface object site
  letI := assembly.add source
  (assembly.split object site).tailPart

/--
The inert local PDE meaning of one exact atom/context split.

The object and site are already fixed values for the current residual.  The
two components are derived by `ComponentLocalTailAssembly`; a PDE consumer
may state local predicates on them, but cannot supply a selected branch,
route, successor, or execution result.
-/
structure Presentation
    (P : Core.Problem.{u, u})
    (semantics : PDE.RepresentationSemantics P)
    (assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics) where
  object : P.Ambient
  site : assembly.Site object
  LocalObstruction : ComponentCarrier assembly object site → Prop
  TailObstruction : ComponentCarrier assembly object site → Prop
  localDecidable : Decidable
    (LocalObstruction (localTerm assembly object site))
  tailOfLocalFailure :
    Not (LocalObstruction (localTerm assembly object site)) →
      TailObstruction (tailTerm assembly object site)

/-! ## Residual-indexed backend registration -/

/-- Thin PDE registration for the generic Core Strategy.  It interprets one
exact PDE residual as the already-defined local/tail presentation and carries
no execution or routing data. -/
structure Registration
    (P : Core.Problem.{u, u})
    (semantics : PDE.RepresentationSemantics P)
    (assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics)
    (Residual : Type u) where
  presentation : Residual → Presentation P semantics assembly

namespace Presentation

/-- Forget PDE names while retaining exactly the local split and local
obstruction law.  Core owns classification and all execution mechanics. -/
def toCore
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    (presentation : Presentation P semantics assembly) :
    Core.Strategy.AtomContextObstructionDichotomy.Presentation.{u, u, u} P where
  semantics := semantics
  assembly := assembly.toCoreAssembly
  object := presentation.object
  site := presentation.site
  AtomLocal := ComponentCarrier assembly presentation.object presentation.site
  atomRepresented :=
    localTerm assembly presentation.object presentation.site
  ContextLocal :=
    ComponentCarrier assembly presentation.object presentation.site
  contextRepresented :=
    tailTerm assembly presentation.object presentation.site
  AtomObstruction := presentation.LocalObstruction
  ContextObstruction := presentation.TailObstruction
  atomDecidable := presentation.localDecidable
  contextOfAtomFailure := presentation.tailOfLocalFailure

/-- Transport a residual-owned local PDE presentation through the official
Core query API.  No residual is reconstructed or copied. -/
def query
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    {Previous : Type u}
    (presentations : Core.Residual.Query Previous
      (fun _ => Presentation P semantics assembly)) :
    Core.Residual.Query Previous (fun _ =>
      Core.Strategy.AtomContextObstructionDichotomy.Presentation.{u, u, u} P) :=
  presentations.map fun _ presentation => presentation.toCore

/-- Primitive local-closure meaning for the cutoff/parametrix child.  It
contains no split, tail fact, route, terminal, or completed presentation. -/
structure LocalEllipticClosure
    (M N : PDE.LocalModel.{u})
    (Admissible : M.problem.Ambient → M.atlas.Window → Prop)
    (Interface : Type u)
    (Carrier Source : Interface → Type u)
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    (elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source) where
  closes : (residual :
    PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic) →
      Carrier residual.interface → Prop

/-! The tail handoff is assembled from the same current-residual query. The
only independent input is the certificate query produced by the preceding
local-closure continuation; all split and represented-tail queries are
derived here with the existing residual combinators. -/
noncomputable def tailContinuationProfile
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    {Previous : Type u}
    (current : Core.Residual.Query Previous (fun _ =>
      PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic))
    (closure : LocalEllipticClosure M N Admissible Interface Carrier Source elliptic)
    (localClosed : Core.Residual.Query Previous (fun previous =>
      PLift (closure.closes (current previous)
        ((PDE.CurrentLocalEllipticResidual.splitQuery current)
          previous).localPart)))
    (focus : Core.Residual.Query Previous (fun previous =>
      PDE.TailFocus N
        (PDE.CurrentLocalEllipticResidual.representedTail
          (current previous)).sourceWindow)) :
    PDE.TailContinuation.Profile Previous N
      (fun previous => Carrier (current previous).interface)
      (current.dependentMap fun _ residual => residual.whole) where
  LocalClosed := fun previous split =>
    PLift (closure.closes (current previous) split.localPart)
  splitQuery := PDE.CurrentLocalEllipticResidual.splitQuery current
  localClosedQuery := localClosed
  representedTailQuery := current.dependentMap fun _ residual =>
    residual.representedTail
  focusQuery := focus

/-- Core assembly derived from the exact split stored by one current local
elliptic residual.

`Atom` and `Context` are the *constant* family at the residual's own
interface, so the assembly stays well typed for a PDE whose carrier space
depends on the object being split. -/
def currentLocalEllipticAssembly
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    (residual :
      PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic) :
    Core.AtomContextAssembly M.problem
      (PDE.RepresentationSemantics.equality M.problem) where
  Interface := Interface
  Site := fun object => ULift.{u} (PLift (object = residual.ambient))
  interface := fun _ _ => residual.interface
  Atom := fun _ => Carrier residual.interface
  Context := fun _ => Carrier residual.interface
  compatible := fun localPart tailPart =>
    localPart + tailPart = residual.whole
  atom := fun object site => by
    have equal := site.down.down
    subst object
    exact residual.split.localPart
  context := fun object site => by
    have equal := site.down.down
    subst object
    exact residual.split.tailPart
  assemble := fun localPart tailPart =>
    elliptic.rebuildComponent residual.ambient residual.componentSite
      (localPart + tailPart)
  extractedCompatible := by
    intro object site
    have equal := site.down.down
    subst object
    exact residual.split.exact_reconstruction
  reconstruct := by
    intro object site
    have equal := site.down.down
    subst object
    rw [residual.split.exact_reconstruction]
    exact residual.rebuild_whole

/-- Construct Core's presentation directly from the current residual. -/
noncomputable def currentLocalEllipticToCore
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    (closure : LocalEllipticClosure M N Admissible Interface Carrier Source elliptic)
    (residual :
      PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic) :
    Core.Strategy.AtomContextObstructionDichotomy.Presentation M.problem where
  semantics := PDE.RepresentationSemantics.equality M.problem
  assembly := currentLocalEllipticAssembly residual
  object := residual.ambient
  site := ULift.up ⟨rfl⟩
  AtomLocal := Carrier residual.interface
  atomRepresented := residual.split.localPart
  ContextLocal := Carrier residual.interface
  contextRepresented := residual.split.tailPart
  AtomObstruction := fun localPart =>
    Not (closure.closes residual localPart)
  ContextObstruction := fun tail =>
    elliptic.constraint
      (elliptic.carrierRestrict residual.focus.inner_outer tail) = 0
  atomDecidable := Classical.propDecidable _
  contextOfAtomFailure := fun _ => residual.tail_homogeneous

noncomputable def fromCurrentLocalElliptic
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    {Previous : Type u}
    (current : Core.Residual.Query Previous
      (fun _ =>
        PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic))
    (closure : LocalEllipticClosure M N Admissible Interface Carrier Source elliptic) :
    Core.Residual.Query Previous (fun _ =>
      Core.Strategy.AtomContextObstructionDichotomy.Presentation.{u, u, u}
        M.problem) :=
  current.map fun _ residual =>
    currentLocalEllipticToCore closure residual

/-- The executable Core profile over the exact current-residual query. -/
noncomputable def profileFromCurrentLocalElliptic
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    {Previous : Type u}
    (current : Core.Residual.Query Previous
      (fun _ =>
        PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic))
    (closure : LocalEllipticClosure M N Admissible Interface Carrier Source elliptic) :
    Core.Strategy.AtomContextObstructionDichotomy.Profile
      M.problem Previous where
  presentation := fromCurrentLocalElliptic current closure

@[simp] theorem fromCurrentLocalElliptic_read
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    {Previous : Type u}
    (current : Core.Residual.Query Previous
      (fun _ =>
        PDE.CurrentLocalEllipticResidual M N Admissible Interface Carrier
        Source elliptic))
    (closure : LocalEllipticClosure M N Admissible Interface Carrier Source elliptic)
    (previous : Previous) :
    (fromCurrentLocalElliptic current closure) previous =
      currentLocalEllipticToCore closure (current previous) :=
  rfl

end Presentation

namespace Registration

/-! ## Canonical local-elliptic registration

The following constructor is the framework boundary for PDEs whose current
residual carries one local elliptic component.  It is indexed by the *active
residual* produced by Core's selection path, never by `ProblemInput`: the
site, the nested focus, the outer equation state, and the exact split are all
derived from that residual together with the public presentation.  The
resulting Core registration remains inert; the sealed Core atom/context
strategy still owns CT1, ledger extension, and route selection. -/

noncomputable def fromPublicPresentation
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    (presentation : PDE.PublicPresentation M)
    (closure :
      Presentation.LocalEllipticClosure M N Admissible Interface Carrier Source
        elliptic)
    (admissible : ∀ residual : PDE.ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer) :
    Core.Strategy.AtomContextObstructionDichotomy.Registration
      M.problem (PDE.ActiveResidual M) where
  presentation := fun residual =>
    Presentation.currentLocalEllipticToCore closure
      (PDE.CurrentLocalEllipticResidual.ofActiveResidual
        (N := N) (Interface := Interface) (Carrier := Carrier)
        (Source := Source) (elliptic := elliptic) presentation residual
        (admissible residual))

/-- The executable Core profile obtained from a public presentation alone.
Its only other input is the active-residual query that the framework's
localization step already exports, so an application registers no strategy,
route, focus, or theorem of its own. -/
noncomputable def profileFromPublicPresentation
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    {Previous : Type u}
    (presentation : PDE.PublicPresentation M)
    (closure :
      Presentation.LocalEllipticClosure M N Admissible Interface Carrier Source
        elliptic)
    (active : Core.Residual.Query Previous fun _ => PDE.ActiveResidual M)
    (admissible : ∀ residual : PDE.ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer) :
    Core.Strategy.AtomContextObstructionDichotomy.Profile
      M.problem Previous where
  presentation := active.map fun _ residual =>
    (fromPublicPresentation (N := N) (Interface := Interface)
      (Carrier := Carrier) (Source := Source) (elliptic := elliptic)
      presentation closure admissible).presentation residual

/--
View a branch input as an active residual against the trivial target.

This asserts nothing: the target is `False`, so `avoids` is `id` and the
minimality kernel is vacuous.  It is the correct reading when target
avoidance is supplied *positionally* --- by a preceding
`counterexampleLocalization` vertex, whose `MinimalSelectionStage` residual
instance makes the downstream `ProblemInput` the selected minimal
counterexample --- rather than by a field of the presentation.
-/
def activeResidualOfInput {M : PDE.LocalModel.{u}}
    (input : Core.Strategy.ProblemInput M.problem) : PDE.ActiveResidual M where
  Target := fun _ => False
  Smaller := fun _ _ => False
  object := input.object
  baseline := input.baseline
  avoids := fun absurd => absurd
  minimal := fun _ smaller _ => smaller.elim

/--
The registered atom/context family for the sealed DAG.

`Core.AtomContextObstructionDichotomyData` indexes its registration by
`ProblemInput`, which is exactly what the sealed family consumes on any stage.
Placed after a localization vertex, that input is the selected residual, so
the split still runs only where Core has selected.
-/
noncomputable def strategyDataFromPublicPresentation
    {M N : PDE.LocalModel.{u}}
    {Admissible : M.problem.Ambient → M.atlas.Window → Prop}
    {Interface : Type u}
    {Carrier Source : Interface → Type u}
    [∀ i, AddCommGroup (Carrier i)] [∀ i, AddCommGroup (Source i)]
    {elliptic :
      PDE.LocalEllipticConstraint M N Admissible Interface Carrier Source}
    (presentation : PDE.PublicPresentation M)
    (closure :
      Presentation.LocalEllipticClosure M N Admissible Interface Carrier Source
        elliptic)
    (admissible : ∀ residual : PDE.ActiveResidual M,
      Admissible residual.object (presentation.focus residual).outer)
    (metadata : Core.Documentation := {})
    (components : List Core.Documentation := [])
    (atomMetadata : Core.Documentation := {})
    (contextMetadata : Core.Documentation := {}) :
    Core.AtomContextObstructionDichotomyData.{u, u, u} M.problem where
  registration :=
    { presentation := fun input =>
        (fromPublicPresentation (N := N) (Interface := Interface)
          (Carrier := Carrier) (Source := Source) (elliptic := elliptic)
          presentation closure admissible).presentation
          (activeResidualOfInput input) }
  metadata := metadata
  components := components
  atomMetadata := atomMetadata
  contextMetadata := contextMetadata

/-- Forget PDE terminology while preserving the residual index. -/
def toCore
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    {Residual : Type u}
    (registration : Registration P semantics assembly Residual) :
    Core.Strategy.AtomContextObstructionDichotomy.Registration P Residual where
  presentation := fun residual =>
    (registration.presentation residual).toCore

/-- Package the thin PDE specialization in the ordinary registered Strategy
family.  This is the same inert registration boundary used by the generic
Core dichotomy: it adds documentation only and supplies no execution,
terminal, route, or ledger value. -/
def toStrategyData
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    (registration :
      Registration P semantics assembly (Core.Strategy.ProblemInput P))
    (metadata : Core.Documentation := {})
    (components : List Core.Documentation := [])
    (localMetadata : Core.Documentation := {})
    (tailMetadata : Core.Documentation := {}) :
    Core.AtomContextObstructionDichotomyData.{u, u, u} P where
  registration := registration.toCore
  metadata := metadata
  components := components
  atomMetadata := localMetadata
  contextMetadata := tailMetadata

/-- Map the exact current residual query through the ordinary Core
registration API. -/
def query
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    {Residual Previous : Type u}
    (registration : Registration P semantics assembly Residual)
    (residual : Core.Residual.Query Previous (fun _ => Residual)) :
    Core.Residual.Query Previous (fun _ =>
      Core.Strategy.AtomContextObstructionDichotomy.Presentation.{u, u, u} P) :=
  registration.toCore.query residual

@[simp] theorem query_read
    {P : Core.Problem.{u, u}}
    {semantics : PDE.RepresentationSemantics P}
    {assembly : PDE.ComponentLocalTailAssembly.{u, u} P semantics}
    {Residual Previous : Type u}
    (registration : Registration P semantics assembly Residual)
    (residual : Core.Residual.Query Previous (fun _ => Residual))
    (previous : Previous) :
    (registration.query residual) previous =
      (registration.presentation (residual previous)).toCore :=
  rfl

end Registration

end Hypostructure.PDE.Strategy.LocalTailObstructionDichotomy
