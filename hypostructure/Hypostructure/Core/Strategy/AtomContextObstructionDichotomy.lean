import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.AtomContextObstructionDichotomySemantics

/-!
# Atom--context obstruction dichotomy

The Strategy consumes one typed query on its literal predecessor.  The query
returns the pointwise mathematical presentation attached to that exact
residual.  Core derives the simultaneous atom/context decomposition, decides
the atom obstruction once, and returns the corresponding predecessor-indexed
branch payload.  The generic DAG compiler owns the successor ledger extension
and branch routing.

There is no stable problem-input projection in this module.
-/

namespace Hypostructure.Core.Strategy.AtomContextObstructionDichotomy

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uAmbient uBranch uPrevious uData uResidual

structure Profile
  (P : Core.Problem.{uAmbient, uBranch})
    (Previous : Type uPrevious) where
  presentation :
    Query Previous fun _ =>
      _root_.Hypostructure.Core.Strategy.AtomContextObstructionDichotomy.Presentation.{
        uAmbient, uBranch, uData} P

def Profile.ofRegistration
    {Residual : Type uResidual} [HasResidual Previous Residual]
    (registration :
      _root_.Hypostructure.Core.Strategy.AtomContextObstructionDichotomy.Registration.{
        uAmbient, uBranch, uData, uResidual} P Residual) :
    Profile P Previous where
  presentation := registration.query Query.residual

namespace Profile

variable
  {P : Core.Problem.{uAmbient, uBranch}}
  {Previous : Type uPrevious}
  (profile :
    Profile.{uAmbient, uBranch, uPrevious, uData} P Previous)

/-- Exact reconstruction data derived by Core from one queried pointwise
presentation. -/
structure ExactDecomposition
    (presentation :
      _root_.Hypostructure.Core.Strategy.AtomContextObstructionDichotomy.Presentation.{
        uAmbient, uBranch, uData} P) :
    Type uData where
  private mk ::
  atom :
    presentation.assembly.Atom
      (presentation.assembly.interface presentation.object presentation.site)
  context :
    presentation.assembly.Context
      (presentation.assembly.interface presentation.object presentation.site)
  compatible : presentation.assembly.compatible atom context
  reconstruct :
    presentation.semantics.equivalent
      (presentation.assembly.assemble atom context)
      presentation.object

/-- Core derives both children and their reconstruction from the same
pointwise presentation. -/
def exactDecomposition
    (presentation :
      _root_.Hypostructure.Core.Strategy.AtomContextObstructionDichotomy.Presentation.{
        uAmbient, uBranch, uData} P) :
    ExactDecomposition presentation where
  atom := presentation.assembly.atom presentation.object presentation.site
  context :=
    presentation.assembly.context presentation.object presentation.site
  compatible :=
    presentation.assembly.extractedCompatible
      presentation.object presentation.site
  reconstruct :=
    presentation.assembly.reconstruct presentation.object presentation.site

/-- The complete one-element schedule inspected by CT1. -/
def canonicalMembers : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.ofFinEnum (inferInstance : FinEnum Unit)

/-- CT1 realizes exactly the atom obstruction on the queried presentation. -/
def spec : CT1.Spec Previous where
  Candidate := fun _ => Unit
  Realizes := fun previous _ =>
    (profile.presentation.read previous).AtomObstruction
      (profile.presentation.read previous).atomRepresented

/-- The primitive decision procedure is interpreted only by CT1. -/
def capability : CT1.Capability profile.spec where
  schedule := Query.ofFunction fun _ => canonicalMembers
  realizesDecidable := fun previous _ =>
    (profile.presentation.read previous).atomDecidable
  inputSize := fun previous =>
    CT1.searchCheckBound profile.spec
      (Query.ofFunction fun _ => canonicalMembers) previous
  workCoefficient := Fintype.card Unit
  workDegree := Fintype.card Unit
  workBound := by
    intro previous
    simp [CT1.searchCheckBound, canonicalMembers]

/-- The one executable decision owned by the Strategy. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct1 profile.capability

/-- The atom obstruction at the literal predecessor.  Its types refer
definitionally to the exact value read from the incoming query. -/
structure AtomResidual (previous : Previous) : Type (max uData uPrevious) where
  private mk ::
  result : CT1.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  decomposition :
    ExactDecomposition (profile.presentation.read previous)
  obstruction :
    (profile.presentation.read previous).AtomObstruction
      (profile.presentation.read previous).atomRepresented

/-- The complementary context obstruction at the same predecessor.  The
negative atom decision is retained independently and remains queryable on
this branch. -/
structure ContextResidual (previous : Previous) : Type (max uData uPrevious) where
  private mk ::
  result : CT1.ExecutionResult profile.spec profile.capability
  previous_eq : result.stage.previous = previous
  decomposition :
    ExactDecomposition (profile.presentation.read previous)
  atomAbsent :
    Not ((profile.presentation.read previous).AtomObstruction
      (profile.presentation.read previous).atomRepresented)
  obstruction :
    (profile.presentation.read previous).ContextObstruction
      (profile.presentation.read previous).contextRepresented

/-- CT1 avoidance of the complete unit schedule is exactly atom failure. -/
private theorem absentOfAvoidance (previous : Previous)
    (avoids :
      Core.Finite.Search.Avoids canonicalMembers
        (profile.spec.Realizes previous)) :
    Not ((profile.presentation.read previous).AtomObstruction
      (profile.presentation.read previous).atomRepresented) := by
  intro obstruction
  have rejected := avoids ⟨0, by decide⟩
  exact rejected obstruction

/-- Route exclusively from CT1's retained branch constructor. -/
noncomputable def route (previous : Previous) :
    Sum (profile.AtomResidual previous)
      (profile.ContextResidual previous) :=
  let presentation := profile.presentation.read previous
  let decomposition := exactDecomposition presentation
  let result := profile.execution.run previous
  match result.stage.added.added with
  | .yesBranch hit =>
      let indexed := result.stage.added.previous.hitOfHasHit hit
      .inl
        ⟨result, rfl, decomposition, indexed.sound⟩
  | .noBranch avoids =>
      let absent := profile.absentOfAvoidance previous avoids
      .inr
        ⟨result, rfl, decomposition, absent,
          presentation.contextOfAtomFailure absent⟩

/-- Standard dichotomy view of the exact CT1 route. -/
noncomputable def dichotomy : Core.Strategy.Dichotomy Previous where
  LeftPayload := profile.AtomResidual
  RightPayload := profile.ContextResidual
  classify := profile.route

end Profile

end Hypostructure.Core.Strategy.AtomContextObstructionDichotomy
