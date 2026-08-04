import Hypostructure.Core.Assembly.AtomContext
import Hypostructure.Core.Context
import Hypostructure.Core.Residual.Query
import Hypostructure.Core.Residual.Stage

/-!
# Interface-local replacement strategies

The three stages in this file are domain independent.  A domain supplies an
interface-indexed assembly and primitive signature/baseline/progress laws.
Core derives registration, context universality, strict-replacement
exclusion, and hereditary uncompressibility, appending each result to the
literal predecessor ledger.
-/

namespace Hypostructure.Core.Strategy.InterfaceReplacement

open Hypostructure.Core.Residual

universe uAmbient uBranch uMeasure uInterface uSite uAtom uContext uSignature

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-- Domain semantics consumed by the reusable strategy family.  This record
contains no executor, branch choice, ledger value, or authored outcome. -/
structure Profile
    (progress : Core.Progress.{uAmbient, uBranch, uMeasure} P) where
  semantics : Core.SemanticEquivalence P
  targetInvariant : Core.TargetInvariant semantics T.Predicate
  assembly : Core.AtomContextAssembly.{uAmbient, uBranch, uInterface, uSite,
    uAtom, uContext} P semantics
  Signature : assembly.Interface → Type uSignature
  signature : {interface : assembly.Interface} →
    assembly.Atom interface → Signature interface

namespace Profile

variable {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
variable (profile : Profile (P := P) (T := T) progress)

/-- Equality of the exact interface signature together with equality of target
response in every compatible outside context. -/
structure TargetComplete {interface : profile.assembly.Interface}
    (source replacement : profile.assembly.Atom interface) : Prop where
  signature_eq : profile.signature replacement = profile.signature source
  contextUniversal :
    ∀ context : profile.assembly.Context interface,
      profile.assembly.compatible source context →
      profile.assembly.compatible replacement context →
      (T.Predicate (profile.assembly.assemble replacement context) ↔
        T.Predicate (profile.assembly.assemble source context))

/-- The paper's one-way obstruction-profile inclusion.  A replacement is at
most as obstructing as the source when every compatible outside context that
produces the target with the replacement also produces it with the source.
No reverse implication is required. -/
def ObstructionProfileLE {interface : profile.assembly.Interface}
    (source replacement : profile.assembly.Atom interface) : Prop :=
  ∀ context : profile.assembly.Context interface,
    profile.assembly.compatible source context →
    profile.assembly.compatible replacement context →
    T.Predicate (profile.assembly.assemble replacement context) →
      T.Predicate (profile.assembly.assemble source context)

/-- Target-completeness is stronger than the one-way obstruction inclusion
used by the replacement lemma. -/
theorem TargetComplete.obstructionProfileLE
    {interface : profile.assembly.Interface}
    {source replacement : profile.assembly.Atom interface}
    (complete : profile.TargetComplete source replacement) :
    profile.ObstructionProfileLE source replacement := by
  intro context sourceCompatible replacementCompatible replacementTarget
  exact (complete.contextUniversal context sourceCompatible
    replacementCompatible).mp replacementTarget

/-- A strict local compression at one literal site.  Baseline validity and
strict decrease are semantic provisions; target transport is derived from
`TargetComplete` and reconstruction. -/
structure Compression
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (site : profile.assembly.Site ctx.G) where
  replacement : profile.assembly.Replacement ctx.G site
  complete : profile.TargetComplete
    (profile.assembly.atom ctx.G site) replacement.atom
  baseline : P.Baseline (profile.assembly.replace replacement)
  smaller : progress.Smaller
    (profile.assembly.replace replacement) ctx.G

/-- A strict replacement in exactly the form required by the replacement
lemma: equal interface signature, one-way obstruction inclusion, preserved
baseline, and strict decrease. -/
structure StrictReplacement
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (site : profile.assembly.Site ctx.G) where
  replacement : profile.assembly.Replacement ctx.G site
  signature_eq : profile.signature replacement.atom =
    profile.signature (profile.assembly.atom ctx.G site)
  obstruction_le : profile.ObstructionProfileLE
    (profile.assembly.atom ctx.G site) replacement.atom
  baseline : P.Baseline (profile.assembly.replace replacement)
  smaller : progress.Smaller
    (profile.assembly.replace replacement) ctx.G

/-- Every existing target-complete compression is, in particular, a strict
replacement satisfying the paper's one-way hypothesis. -/
def Compression.toStrictReplacement
    {ctx : Core.MinimalCounterexampleContext P T.Predicate progress}
    {site : profile.assembly.Site ctx.G}
    (compression : profile.Compression ctx site) :
    profile.StrictReplacement ctx site where
  replacement := compression.replacement
  signature_eq := compression.complete.signature_eq
  obstruction_le := compression.complete.obstructionProfileLE profile
  baseline := compression.baseline
  smaller := compression.smaller

/-- Context-free carrier of the exact mathematical data later consumed as a
`Compression` at a selected minimal-counterexample context.  This is useful
for earlier CTs whose residual already fixes the current object but which do
not own the minimality proof: they retain the replacement, target-completeness,
baseline, and strict-decrease facts without copying the context or inventing
an application bridge. -/
structure CompressionCandidate
    (object : P.Ambient)
    (site : profile.assembly.Site object) where
  replacement : profile.assembly.Replacement object site
  complete : profile.TargetComplete
    (profile.assembly.atom object site) replacement.atom
  baseline : P.Baseline (profile.assembly.replace replacement)
  smaller : progress.Smaller
    (profile.assembly.replace replacement) object

/-- Structural part of a compression retained before a response scan.  It
contains the exact site, replacement, baseline, and strict decrease, but no
claim about target responses.  A neutral response certificate supplies that
last field; this prevents a CT registration from assuming its own answer. -/
structure CompressionFrame
    (object : P.Ambient)
    (site : profile.assembly.Site object) where
  replacement : profile.assembly.Replacement object site
  signature_eq : profile.signature replacement.atom =
    profile.signature (profile.assembly.atom object site)
  baseline : P.Baseline (profile.assembly.replace replacement)
  smaller : progress.Smaller
    (profile.assembly.replace replacement) object

/-- Complete the exact retained frame with universal target semantics derived
by the response CT. -/
def CompressionFrame.toCandidate
    {object : P.Ambient} {site : profile.assembly.Site object}
    (frame : profile.CompressionFrame object site)
    (complete : profile.TargetComplete
      (profile.assembly.atom object site) frame.replacement.atom) :
    profile.CompressionCandidate object site where
  replacement := frame.replacement
  complete := complete
  baseline := frame.baseline
  smaller := frame.smaller

/-- Assemble the target-completeness field from the frame's retained exact
signature and CT7's universal context-response equivalence. -/
def CompressionFrame.targetComplete
    {object : P.Ambient} {site : profile.assembly.Site object}
    (frame : profile.CompressionFrame object site)
    (contextUniversal : ∀ context :
      profile.assembly.Context (profile.assembly.interface object site),
      profile.assembly.compatible (profile.assembly.atom object site) context →
      profile.assembly.compatible frame.replacement.atom context →
      (T.Predicate (profile.assembly.assemble frame.replacement.atom context) ↔
        T.Predicate (profile.assembly.assemble
          (profile.assembly.atom object site) context))) :
    profile.TargetComplete
      (profile.assembly.atom object site) frame.replacement.atom where
  signature_eq := frame.signature_eq
  contextUniversal := contextUniversal

/-- G3 completion: universal neutrality contributes exactly the context law,
and the retained frame contributes every structural field. -/
def CompressionFrame.toCandidateOfContextUniversal
    {object : P.Ambient} {site : profile.assembly.Site object}
    (frame : profile.CompressionFrame object site)
    (contextUniversal : ∀ context :
      profile.assembly.Context (profile.assembly.interface object site),
      profile.assembly.compatible (profile.assembly.atom object site) context →
      profile.assembly.compatible frame.replacement.atom context →
      (T.Predicate (profile.assembly.assemble frame.replacement.atom context) ↔
        T.Predicate (profile.assembly.assemble
          (profile.assembly.atom object site) context))) :
    profile.CompressionCandidate object site :=
  frame.toCandidate profile (frame.targetComplete profile contextUniversal)

/-- Interpret a retained candidate at the literal minimal context whose
object indexes it.  All fields are definitionally the existing `Compression`
fields; no equality transport or authored proof callback is involved. -/
def CompressionCandidate.toCompression
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (site : profile.assembly.Site ctx.G)
    (candidate : profile.CompressionCandidate ctx.G site) :
    profile.Compression ctx site where
  replacement := candidate.replacement
  complete := candidate.complete
  baseline := candidate.baseline
  smaller := candidate.smaller

/-- Canonical pointwise registration of every extracted support and its exact
interface signature. -/
structure Registration
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress) where
  signatureAt :
    ∀ site : profile.assembly.Site ctx.G,
      profile.Signature (profile.assembly.interface ctx.G site)
  signatureAt_eq :
    ∀ site, signatureAt site =
      profile.signature (profile.assembly.atom ctx.G site)
  mismatchRejected :
    ∀ (site : profile.assembly.Site ctx.G)
      (replacement : profile.assembly.Replacement ctx.G site),
      profile.signature replacement.atom ≠
        profile.signature (profile.assembly.atom ctx.G site) →
      ¬ profile.TargetComplete
        (profile.assembly.atom ctx.G site) replacement.atom

def registration
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress) :
    profile.Registration ctx where
  signatureAt := fun site =>
    profile.signature (profile.assembly.atom ctx.G site)
  signatureAt_eq := fun _ => rfl
  mismatchRejected := by
    intro site replacement different complete
    exact different complete.signature_eq

/-- Core's universal replacement conclusion. -/
structure UniversalReplacement
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (_registration : profile.Registration ctx) : Prop where
  contextUniversal :
    ∀ {interface : profile.assembly.Interface}
      {source replacement : profile.assembly.Atom interface},
      profile.TargetComplete source replacement →
      ∀ context : profile.assembly.Context interface,
        profile.assembly.compatible source context →
        profile.assembly.compatible replacement context →
        (T.Predicate (profile.assembly.assemble replacement context) ↔
          T.Predicate (profile.assembly.assemble source context))
  noStrictReplacement :
    ∀ (site : profile.assembly.Site ctx.G),
      ¬ Nonempty (profile.StrictReplacement ctx site)
  noCompression :
    ∀ (site : profile.assembly.Site ctx.G),
      ¬ Nonempty (profile.Compression ctx site)

private theorem strictReplacementImpossible
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (site : profile.assembly.Site ctx.G) :
    ¬ Nonempty (profile.StrictReplacement ctx site) := by
  rintro ⟨replacement⟩
  have replacementTarget : T.Predicate
      (profile.assembly.replace replacement.replacement) :=
    ctx.target_of_smaller replacement.smaller replacement.baseline
  have sourceTarget : T.Predicate
      (profile.assembly.assemble
        (profile.assembly.atom ctx.G site)
        (profile.assembly.context ctx.G site)) :=
    replacement.obstruction_le
      (profile.assembly.context ctx.G site)
      (profile.assembly.extractedCompatible ctx.G site)
      replacement.replacement.compatible replacementTarget
  exact ctx.avoids
    ((profile.targetInvariant.target_iff
      (profile.assembly.reconstruct ctx.G site)).mp sourceTarget)

def universalReplacement
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (registration : profile.Registration ctx) :
    profile.UniversalReplacement ctx registration where
  contextUniversal := fun complete => complete.contextUniversal
  noStrictReplacement := profile.strictReplacementImpossible ctx
  noCompression := by
    intro site
    rintro ⟨compression⟩
    exact profile.strictReplacementImpossible ctx site
      ⟨compression.toStrictReplacement profile⟩

/-- Hereditary form retained by all downstream residuals. -/
structure Uncompressible
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (registration : profile.Registration ctx)
    (replacement : profile.UniversalReplacement ctx registration) : Prop where
  noStrictReplacement :
    ∀ site : profile.assembly.Site ctx.G,
      ¬ Nonempty (profile.StrictReplacement ctx site)
  noCompression :
    ∀ site : profile.assembly.Site ctx.G,
      ¬ Nonempty (profile.Compression ctx site)
  defective :
    ∀ {interface : profile.assembly.Interface}
      {source candidate : profile.assembly.Atom interface},
      ¬ (∀ context : profile.assembly.Context interface,
          profile.assembly.compatible source context →
          profile.assembly.compatible candidate context →
          (T.Predicate (profile.assembly.assemble candidate context) ↔
            T.Predicate (profile.assembly.assemble source context))) →
      ¬ profile.TargetComplete source candidate

def uncompressible
    (ctx : Core.MinimalCounterexampleContext P T.Predicate progress)
    (registration : profile.Registration ctx)
    (replacement : profile.UniversalReplacement ctx registration) :
    profile.Uncompressible ctx registration replacement where
  noStrictReplacement := replacement.noStrictReplacement
  noCompression := replacement.noCompression
  defective := by
    intro interface source candidate notUniversal complete
    exact notUniversal complete.contextUniversal

end Profile

/-! ## Literal accumulated-ledger execution -/

variable {progress : Core.Progress.{uAmbient, uBranch, uMeasure} P}
variable (profile : Profile (P := P) (T := T) progress)
variable {Previous : Type*}
variable (context : Query Previous fun _ =>
  Core.MinimalCounterexampleContext P T.Predicate progress)

abbrev InterfaceSupportStage :=
  Ledger.Extension Previous fun previous =>
    profile.Registration (context.read previous)

def interfaceSupportDecomposition (previous : Previous) :
    InterfaceSupportStage profile context :=
  (StageNode.create fun previous =>
    profile.registration (context.read previous)).run previous

def contextAfterInterfaceSupport :
    Query (InterfaceSupportStage profile context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate progress :=
  context.preserve

def registrationQuery :
    Query (InterfaceSupportStage profile context) fun stage =>
      profile.Registration (context.read stage.previous) :=
  Query.latest

abbrev ContextUniversalStage :=
  Ledger.Extension (InterfaceSupportStage profile context) fun stage =>
    profile.UniversalReplacement
      ((contextAfterInterfaceSupport profile context).read stage)
      ((registrationQuery profile context).read stage)

def contextUniversalReplacement
    (previous : InterfaceSupportStage profile context) :
    ContextUniversalStage profile context :=
  (StageNode.create fun stage =>
    profile.universalReplacement
      ((contextAfterInterfaceSupport profile context).read stage)
      ((registrationQuery profile context).read stage)).run previous

def contextAfterUniversal :
    Query (ContextUniversalStage profile context) fun _ =>
      Core.MinimalCounterexampleContext P T.Predicate progress :=
  (contextAfterInterfaceSupport profile context).preserve

def registrationAfterUniversal :
    Query (ContextUniversalStage profile context) fun stage =>
      profile.Registration
        ((contextAfterUniversal profile context).read stage) :=
  (registrationQuery profile context).preserve

def universalReplacementQuery :
    Query (ContextUniversalStage profile context) fun stage =>
      profile.UniversalReplacement
        ((contextAfterUniversal profile context).read stage)
        ((registrationAfterUniversal profile context).read stage) :=
  Query.latest

abbrev UncompressibleStage :=
  Ledger.Extension (ContextUniversalStage profile context) fun stage =>
    profile.Uncompressible
      ((contextAfterUniversal profile context).read stage)
      ((registrationAfterUniversal profile context).read stage)
      ((universalReplacementQuery profile context).read stage)

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
    ClosurePayload profile (context.read stage)

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
        ((contextAfterClosure profile context).read stage) :=
  (registrationAfterUniversal profile context).preserve

/-- Project the exact universal-replacement theorem already present in the
closure ledger. -/
def universalAfterClosure :
    Query (UncompressibleStage profile context) fun stage =>
      profile.UniversalReplacement
        ((contextAfterClosure profile context).read stage)
        ((registrationAfterClosure profile context).read stage) :=
  (universalReplacementQuery profile context).preserve

/-- Project hereditary uncompressibility from the newest closure entry. -/
def uncompressibleAfterClosure :
    Query (UncompressibleStage profile context) fun stage =>
      profile.Uncompressible
        ((contextAfterClosure profile context).read stage)
        ((registrationAfterClosure profile context).read stage)
        ((universalAfterClosure profile context).read stage) :=
  Query.latest

/-- Collapse the dependent closure ledger into one typed capability payload.
All four values are read at the same literal stage. -/
def closurePayload (stage : UncompressibleStage profile context) :
    ClosurePayload profile ((contextAfterClosure profile context).read stage) :=
  { registration := (registrationAfterClosure profile context).read stage
    universal := (universalAfterClosure profile context).read stage
    uncompressible := (uncompressibleAfterClosure profile context).read stage }

def closurePayloadQuery :
    Query (UncompressibleStage profile context) fun stage =>
      ClosurePayload profile ((contextAfterClosure profile context).read stage) :=
  Query.ofFunction (closurePayload profile context)

def hereditaryTargetUncompressibility
    (previous : ContextUniversalStage profile context) :
    UncompressibleStage profile context :=
  (StageNode.create fun stage =>
    profile.uncompressible
      ((contextAfterUniversal profile context).read stage)
      ((registrationAfterUniversal profile context).read stage)
      ((universalReplacementQuery profile context).read stage)).run previous

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
