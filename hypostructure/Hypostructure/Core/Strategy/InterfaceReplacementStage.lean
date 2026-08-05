import Hypostructure.Core.Strategy.InterfaceReplacement
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Residual.Stage

/-!
# Interface replacement: the legacy stage plumbing

**Legacy.**  `Core/Strategy/InterfaceReplacement.lean` holds the mathematics of
`lem:replacement` and `cor:uncompressible`; this file holds the stage machinery
that used to carry it -- `InterfaceSupportStage`, `ClosurePayload`, and the
`Ledger.Extension` chain that threads them.

They are separated so that a consumer of the mathematics does not import the
legacy ledger.  The ported spine's row `[11]`--`[14]` calls
`Profile.strictReplacementImpossible` directly on the selected context and
reaches nothing in this file; `ClosurePayload` in particular is a payload
threaded between strategies, which the canonical API does not permit.

This file goes when its remaining consumers port.
-/

namespace Hypostructure.Core.Strategy.InterfaceReplacement

open Hypostructure.Core.Residual

universe uAmbient uBranch uMeasure uInterface uSite uAtom uContext uSignature

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-! ## Literal accumulated-ledger execution -/

variable {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
variable (profile : Profile (P := P) (T := T) progress)
variable {Previous : Type*}
variable (context : Query Previous fun _ =>
  Core.MinimalCounterexampleContext P T.Predicate progress)

abbrev InterfaceSupportStage :=
  Ledger.Extension Previous fun previous =>
    profile.Registration (context previous)

def interfaceSupportDecomposition (previous : Previous) :
    InterfaceSupportStage profile context :=
  (StageNode.create fun previous =>
    profile.registration (context previous)).run previous

def contextAfterInterfaceSupport :
    Query (InterfaceSupportStage profile context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate progress :=
  context.preserve

def registrationQuery :
    Query (InterfaceSupportStage profile context) fun stage =>
      profile.Registration (context stage.previous) :=
  Query.latest

abbrev ContextUniversalStage :=
  Ledger.Extension (InterfaceSupportStage profile context) fun stage =>
    profile.UniversalReplacement
      ((contextAfterInterfaceSupport profile context) stage)
      ((registrationQuery profile context) stage)

def contextUniversalReplacement
    (previous : InterfaceSupportStage profile context) :
    ContextUniversalStage profile context :=
  (StageNode.create fun stage =>
    profile.universalReplacement
      ((contextAfterInterfaceSupport profile context) stage)
      ((registrationQuery profile context) stage)).run previous

def contextAfterUniversal :
    Query (ContextUniversalStage profile context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate progress :=
  (contextAfterInterfaceSupport profile context).preserve

def registrationAfterUniversal :
    Query (ContextUniversalStage profile context) fun stage =>
      profile.Registration
        ((contextAfterUniversal profile context) stage) :=
  (registrationQuery profile context).preserve

def universalReplacementQuery :
    Query (ContextUniversalStage profile context) fun stage =>
      profile.UniversalReplacement
        ((contextAfterUniversal profile context) stage)
        ((registrationAfterUniversal profile context) stage) :=
  Query.latest

abbrev UncompressibleStage :=
  Ledger.Extension (ContextUniversalStage profile context) fun stage =>
    profile.Uncompressible
      ((contextAfterUniversal profile context) stage)
      ((registrationAfterUniversal profile context) stage)
      ((universalReplacementQuery profile context) stage)

/-- Stable, stage-shape-free view of the three dependent facts produced by
`closure`.  This is a projection of the literal accumulated ledger, not a
second registration: downstream Strategies retain this value through the
ordinary `Query` preservation API. -/
structure ClosurePayload
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress) where
  registration : profile.Registration ctx
  universal : profile.UniversalReplacement ctx registration
  uncompressible : profile.Uncompressible ctx registration universal

/-- The retained closure rejects every replacement satisfying the paper's
one-way obstruction inclusion. -/
theorem ClosurePayload.noStrictReplacement
    {ctx : Core.MinimalCounterexampleContext P T.Predicate progress}
    (closure : ClosurePayload profile ctx)
    (site : profile.assembly.Site ctx.G) :
    ¬ Nonempty (profile.StrictReplacement ctx site) :=
  closure.uncompressible.noStrictReplacement site

/-- Public query-native view of one exact interface-replacement closure
producer.  A compiler indexes this value by its registered producer; domain
strategies receive only these ordinary queries and cannot supply a context,
closure proof, or transport callback. -/
structure ExactClosureQueries
    (Stage : Type*) where
  context : Query Stage fun _ =>
    Core.MinimalCounterexampleContext P T.Predicate progress
  closure : Query Stage fun stage =>
    ClosurePayload profile (context stage)

/-- The retained closure ledger rejects every context-free compression
candidate at the exact selected object.  Downstream CTs need only recover the
site and candidate from their ordinary ledger; Core performs the conversion
to the already-proved uncompressibility theorem. -/
theorem ClosurePayload.noCompressionCandidate
    {ctx : Core.MinimalCounterexampleContext P T.Predicate progress}
    (closure : ClosurePayload profile ctx)
    (site : profile.assembly.Site ctx.G) :
    ¬ Nonempty (profile.CompressionCandidate ctx.G site) := by
  rintro ⟨candidate⟩
  exact closure.uncompressible.noCompression site
    ⟨candidate.toCompression profile ctx site⟩

/-- Close a G3-neutral structural frame at the exact inherited context. -/
theorem ClosurePayload.noNeutralCompressionFrame
    {ctx : Core.MinimalCounterexampleContext P T.Predicate progress}
    (closure : ClosurePayload profile ctx)
    (site : profile.assembly.Site ctx.G)
    (frame : profile.CompressionFrame ctx.G site)
    (contextUniversal : ∀ context :
      profile.assembly.Context (profile.assembly.interface ctx.G site),
      profile.assembly.compatible (profile.assembly.atom ctx.G site) context →
      profile.assembly.compatible frame.replacement.atom context →
      (T.Predicate (profile.assembly.assemble frame.replacement.atom context) ↔
        T.Predicate (profile.assembly.assemble
          (profile.assembly.atom ctx.G site) context))) : False :=
  closure.noCompressionCandidate profile site
    ⟨frame.toCandidateOfContextUniversal profile contextUniversal⟩

/-- The selected minimal-counterexample context at the completed closure
stage. -/
def contextAfterClosure :
    Query (UncompressibleStage profile context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate progress :=
  (contextAfterUniversal profile context).preserve

/-- Project the exact interface registration already present in the closure
ledger. -/
def registrationAfterClosure :
    Query (UncompressibleStage profile context) fun stage =>
      profile.Registration
        ((contextAfterClosure profile context) stage) :=
  (registrationAfterUniversal profile context).preserve

/-- Project the exact universal-replacement theorem already present in the
closure ledger. -/
def universalAfterClosure :
    Query (UncompressibleStage profile context) fun stage =>
      profile.UniversalReplacement
        ((contextAfterClosure profile context) stage)
        ((registrationAfterClosure profile context) stage) :=
  (universalReplacementQuery profile context).preserve

/-- Project hereditary uncompressibility from the newest closure entry. -/
def uncompressibleAfterClosure :
    Query (UncompressibleStage profile context) fun stage =>
      profile.Uncompressible
        ((contextAfterClosure profile context) stage)
        ((registrationAfterClosure profile context) stage)
        ((universalAfterClosure profile context) stage) :=
  Query.latest

/-- Collapse the dependent closure ledger into one typed capability payload.
All four values are read at the same literal stage. -/
def closurePayload (stage : UncompressibleStage profile context) :
    ClosurePayload profile ((contextAfterClosure profile context) stage) :=
  { registration := (registrationAfterClosure profile context) stage
    universal := (universalAfterClosure profile context) stage
    uncompressible := (uncompressibleAfterClosure profile context) stage }

def closurePayloadQuery :
    Query (UncompressibleStage profile context) fun stage =>
      ClosurePayload profile ((contextAfterClosure profile context) stage) :=
   (closurePayload profile context)

def hereditaryTargetUncompressibility
    (previous : ContextUniversalStage profile context) :
    UncompressibleStage profile context :=
  (StageNode.create fun stage =>
    profile.uncompressible
      ((contextAfterUniversal profile context) stage)
      ((registrationAfterUniversal profile context) stage)
      ((universalReplacementQuery profile context) stage)).run previous

/-- Sealed high-level Strategy combining interface registration, universal
replacement, and hereditary uncompressibility.  The implementation is
domain-neutral and consumes only its incoming stage and declared context
query; it neither knows nor selects a predecessor Strategy. -/
noncomputable def closure (previous : Previous) :
    UncompressibleStage profile context :=
  let support := interfaceSupportDecomposition profile context previous
  let universal := contextUniversalReplacement profile context support
  hereditaryTargetUncompressibility profile context universal

@[simp] theorem interfaceSupport_previous (previous : Previous) :
    (interfaceSupportDecomposition profile context previous).previous = previous :=
  rfl

@[simp] theorem contextUniversal_previous
    (previous : InterfaceSupportStage profile context) :
    (contextUniversalReplacement profile context previous).previous = previous :=
  rfl

@[simp] theorem uncompressible_previous
    (previous : ContextUniversalStage profile context) :
    (hereditaryTargetUncompressibility profile context previous).previous =
      previous :=
  rfl

end Hypostructure.Core.Strategy.InterfaceReplacement
