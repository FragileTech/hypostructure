import Hypostructure.CT1.Automation
import Hypostructure.Core.Problem
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.ObstructionPackingData
import Hypostructure.Core.Strategy.ObstructionPackingSemantics

/-!
# Obstruction-free closure and canonical packing

This Strategy is domain neutral.  CT1 decides whether the exact incoming
occurrence schedule is empty.  The empty arm is converted to the registered
target, while the nonempty arm retains Core's canonical maximal packing.
-/

namespace Hypostructure.Core.Strategy.ObstructionPackingClosure

open Hypostructure
open Hypostructure.Core.Residual
open scoped BigOperators

universe uAmbient uBranch uData

variable {P : Core.Problem.{uAmbient, uBranch}} {T : Core.Target P}

/-- The executable profile specializes the inert semantics to Core's stable
problem residual and registered target. -/
abbrev Profile := Semantics
  (Core.Strategy.ProblemInput P)
  (fun input => T.Predicate input.object)

namespace Profile

variable (profile : Profile (P := P) (T := T))
variable {Previous : Type (max uAmbient uBranch uData)}
variable [HasResidual Previous (Core.Strategy.ProblemInput P)]

noncomputable def packingAt (previous : Previous) :=
  Packing.canonical
    (profile.occurrences (residualOf previous))
    (profile.conflict (residualOf previous))
    (profile.conflictDecidable (residualOf previous))
    (profile.conflictSymmetric (residualOf previous))

def spec : CT1.Spec Previous where
  Candidate := fun previous =>
    profile.Occurrence (residualOf previous)
  Realizes := fun _ _ => True

def capability : CT1.Capability (profile.spec (Previous := Previous)) where
  schedule := Query.ofFunction fun previous =>
    profile.occurrences (residualOf previous)
  realizesDecidable := fun _ _ => .isTrue trivial
  inputSize := fun previous =>
    (profile.occurrences (residualOf previous)).card
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp [CT1.searchCheckBound]
    exact Nat.le_add_right _ _

theorem packingAt_selected_nonempty
    (stage : CT1.Stage (profile.spec (Previous := Previous))
      (profile.capability (Previous := Previous)))
    (hasHit : stage.added.previous.HasHit) :
    (packingAt profile stage.previous).selected ≠ [] := by
  exact (packingAt profile stage.previous).selected_nonempty_of_schedule_member
    ((stage.added.previous.hitOfHasHit hasHit).member)

/-- Turn CT1's avoiding proof into the exact empty schedule fact required by
the registered obstruction-free implication. -/
private theorem schedule_empty_of_avoids
    (previous : Previous)
    (avoids : Core.Finite.Search.Avoids
      ((profile.capability (Previous := Previous)).scheduleAt previous)
      ((profile.spec (Previous := Previous)).Realizes previous)) :
    (profile.occurrences (residualOf previous)).values = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  obtain ⟨index, indexed⟩ :=
    (Core.Finite.Enumeration.mem_iff_exists_index
      ((profile.capability (Previous := Previous)).scheduleAt previous)
      occurrence).mp member
  exact (avoids index trivial)

/-- CT1's two outputs are advanced by the framework-owned dependent decision
continuation.  The hit arm records Core's canonical packing; the avoiding arm
records the target proof.  It consumes CT1's literal accumulated ledger
stage; CT1's route remains its direct predecessor. -/
abbrev Output
    (stage : CT1.Stage (profile.spec (Previous := Previous))
      (profile.capability (Previous := Previous))) :=
  Core.Residual.Decision.Continuation
    (fun _ _ => NonemptyPacking
      (profile.occurrences (residualOf stage.previous))
      (profile.conflict (residualOf stage.previous)))
    (fun _ _ => T.Predicate (residualOf stage.previous).object)
    stage.added.previous stage.added.added

noncomputable def continuation
    (stage : CT1.Stage (profile.spec (Previous := Previous))
      (profile.capability (Previous := Previous))) :
    Output profile stage :=
  (Core.Residual.Decision.advance stage.added
    (fun hasHit =>
      ⟨packingAt profile stage.previous,
        packingAt_selected_nonempty profile stage hasHit⟩)
    (fun avoids =>
      profile.freeForcesTarget (residualOf stage.previous)
        (schedule_empty_of_avoids profile stage.previous avoids))).added

/-- Exact accumulated output type of the strategy. -/
abbrev Stage :=
  Ledger.Extension
    (CT1.Stage (profile.spec (Previous := Previous))
      (profile.capability (Previous := Previous)))
    (fun stage => Output profile stage)

/-- Append the dependent continuation to the literal CT1 ledger stage.  The
only new entry is the framework-owned continuation indexed by CT1's actual
route; neither the scan nor a branch result is reconstructed. -/
noncomputable def execute (previous : Previous) :
    Stage profile (Previous := Previous) :=
  let ct1 := CT1.execute
    (profile.spec (Previous := Previous))
    (profile.capability (Previous := Previous)) previous
  Ledger.extend ct1.stage (continuation profile ct1.stage)

/-- Read the target certificate from the avoiding arm of the literal strategy
output.  The packing arm remains open. -/
def target? (stage : Stage profile (Previous := Previous)) :
    Option (PLift (T.Predicate (residualOf stage).object)) :=
  stage.added.mapNo? fun _ target => ⟨target⟩

/-- Public Strategy outcome.  Values are projected directly from the literal
dependent continuation produced by `execute`. -/
abbrev Outcome (previous : Previous) :=
  Sum (NonemptyPacking
    (profile.occurrences (residualOf previous))
    (profile.conflict (residualOf previous)))
    (PLift (T.Predicate (residualOf previous).object))

noncomputable def outcome (previous : Previous) : Outcome profile previous :=
  let stage := execute profile previous
  stage.added.fold
    (fun _ packed => Sum.inl packed)
    (fun _ target => Sum.inr ⟨target⟩)

/-- Standard Strategy contract over the exact Core-produced outcome. -/
noncomputable def contract : Core.Strategy.Contract Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Payload := fun previous _ => Outcome profile previous
  produce := fun previous => ⟨.completed, outcome profile previous⟩
  exhaustive := fun previous => ⟨⟨.completed, outcome profile previous⟩⟩

/-! ## Query-native specialization

The compiler may continue from a graph selected by an earlier localization
CT.  The following API consumes that graph through its retained query.  It is
the same CT1/canonical-packing execution as `contract`; only the input lookup
is generalized from `Query.residual` to an explicit ledger query. -/

noncomputable def packingAtQuery
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (previous : Previous) :=
  Packing.canonical
    (profile.occurrences (current.read previous))
    (profile.conflict (current.read previous))
    (profile.conflictDecidable (current.read previous))
    (profile.conflictSymmetric (current.read previous))

def specAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P) :
    CT1.Spec Previous where
  Candidate := fun previous => profile.Occurrence (current.read previous)
  Realizes := fun _ _ => True

def capabilityAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P) :
    CT1.Capability (profile.specAt current) where
  schedule := current.dependentMap fun _ input => profile.occurrences input
  realizesDecidable := fun _ _ => .isTrue trivial
  inputSize := fun previous => (profile.occurrences (current.read previous)).card
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp [CT1.searchCheckBound]
    exact Nat.le_add_right _ _

private theorem packingAtQuery_selected_nonempty
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (stage : CT1.Stage (profile.specAt current) (profile.capabilityAt current))
    (hasHit : stage.added.previous.HasHit) :
    (packingAtQuery profile current stage.previous).selected ≠ [] := by
  exact (packingAtQuery profile current stage.previous).selected_nonempty_of_schedule_member
    ((stage.added.previous.hitOfHasHit hasHit).member)

private theorem schedule_empty_of_avoidsAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (previous : Previous)
    (avoids : Core.Finite.Search.Avoids
      ((profile.capabilityAt current).scheduleAt previous)
      ((profile.specAt current).Realizes previous)) :
    (profile.occurrences (current.read previous)).values = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro occurrence member
  obtain ⟨index, indexed⟩ :=
    (Core.Finite.Enumeration.mem_iff_exists_index
      ((profile.capabilityAt current).scheduleAt previous) occurrence).mp member
  exact avoids index trivial

abbrev OutputAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (stage : CT1.Stage (profile.specAt current) (profile.capabilityAt current)) :=
  Core.Residual.Decision.Continuation
    (fun _ _ => NonemptyPacking
      (profile.occurrences (current.read stage.previous))
      (profile.conflict (current.read stage.previous)))
    (fun _ _ => T.Predicate (current.read stage.previous).object)
    stage.added.previous stage.added.added

noncomputable def continuationAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (stage : CT1.Stage (profile.specAt current) (profile.capabilityAt current)) :
    OutputAt profile current stage :=
  (Core.Residual.Decision.advance stage.added
    (fun hasHit =>
      ⟨packingAtQuery profile current stage.previous,
        packingAtQuery_selected_nonempty profile current stage hasHit⟩)
    (fun avoids =>
      profile.freeForcesTarget (current.read stage.previous)
        (schedule_empty_of_avoidsAt profile current stage.previous avoids))).added

abbrev StageAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P) :=
  Ledger.Extension
    (CT1.Stage (profile.specAt current) (profile.capabilityAt current))
    (fun stage => OutputAt profile current stage)

noncomputable def executeAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (previous : Previous) : StageAt profile current :=
  let ct1 := CT1.execute (profile.specAt current) (profile.capabilityAt current) previous
  Ledger.extend ct1.stage (continuationAt profile current ct1.stage)

abbrev OutcomeAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (previous : Previous) :=
  Sum (NonemptyPacking
    (profile.occurrences (current.read previous))
    (profile.conflict (current.read previous)))
    (PLift (T.Predicate (current.read previous).object))

noncomputable def outcomeAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P)
    (previous : Previous) : OutcomeAt profile current previous :=
  let stage := executeAt profile current previous
  stage.added.fold
    (fun _ packed => Sum.inl packed)
    (fun _ target => Sum.inr ⟨target⟩)

noncomputable def contractAt
    (current : Query Previous fun _ => Core.Strategy.ProblemInput P) :
    Core.Strategy.Contract Previous where
  Terminal := Core.Strategy.CompletedTerminal
  Payload := fun previous _ => OutcomeAt profile current previous
  produce := fun previous => ⟨.completed, outcomeAt profile current previous⟩
  exhaustive := fun previous => ⟨⟨.completed, outcomeAt profile current previous⟩⟩

@[simp] theorem execute_ct1_predecessor (previous : Previous) :
    (execute profile previous).previous.previous = previous := rfl

end Profile

end Hypostructure.Core.Strategy.ObstructionPackingClosure
