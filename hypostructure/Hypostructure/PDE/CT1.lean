import Hypostructure.CT1.Automation
import Hypostructure.PDE.Model
import Hypostructure.Core.Residual.Query

/-!
# PDE specialization of CT1

CT1 is used for epsilon-regularity certificates, Liouville profiles,
capacity witnesses, rigidity separators, and final local targets.  The PDE
adapter supplies only the represented candidate meaning; Core/CT1 owns the
complete scan and target residual.
-/

namespace Hypostructure.PDE.CT1

universe uPrevious uModel uCandidate

open Hypostructure

def targetSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (Candidate : Previous -> Type uCandidate)
    (candidateObject : (previous : Previous) -> Candidate previous ->
      M.problem.Ambient)
    (realizes : (previous : Previous) -> M.problem.Ambient ->
      Candidate previous -> Prop) :
    _root_.Hypostructure.CT1.Spec Previous where
  Candidate := Candidate
  Realizes := fun previous candidate =>
    realizes previous (candidateObject previous candidate) candidate

def capability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (Candidate : Previous -> Type uCandidate)
    (candidateObject : (previous : Previous) -> Candidate previous ->
      M.problem.Ambient)
    (realizes : (previous : Previous) -> M.problem.Ambient ->
      Candidate previous -> Prop)
    (schedule : Core.Residual.Query Previous
      (fun previous => Core.Finite.Enumeration (Candidate previous)))
    (realizesDecidable : (previous : Previous) ->
      (object : M.problem.Ambient) -> (candidate : Candidate previous) ->
      Decidable (realizes previous object candidate))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      (schedule previous).card <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT1.Capability
      (targetSpec M Candidate candidateObject realizes) where
  schedule := schedule
  realizesDecidable := fun previous candidate =>
    realizesDecidable previous (candidateObject previous candidate) candidate
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

/--
Build the ordinary PDE CT1 capability from a represented equation-state
query.  CT1 does not distinguish an initially restricted state from a
recentered tail: the caller's candidate interpretation receives exactly the
state read from the predecessor ledger.
-/
def capabilityOfEquationState {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (window : Previous → M.atlas.Window)
    (state : Core.Residual.Query Previous fun previous =>
      EquationState M.equation (window previous))
    (Candidate : Previous → Type uCandidate)
    (candidateObject :
      (previous : Previous) →
        EquationState M.equation (window previous) →
          Candidate previous → M.problem.Ambient)
    (realizes : (previous : Previous) → M.problem.Ambient →
      Candidate previous → Prop)
    (schedule : Core.Residual.Query Previous
      (fun previous => Core.Finite.Enumeration (Candidate previous)))
    (realizesDecidable : (previous : Previous) →
      (object : M.problem.Ambient) → (candidate : Candidate previous) →
      Decidable (realizes previous object candidate))
    (inputSize : Previous → Nat) (workCoefficient workDegree : Nat)
    (workBound : ∀ previous,
      (schedule previous).card ≤
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT1.Capability
      (targetSpec M Candidate
        (fun previous candidate =>
          candidateObject previous (state previous) candidate)
        realizes) :=
  capability M Candidate
    (fun previous candidate =>
      candidateObject previous (state previous) candidate)
    realizes schedule realizesDecidable inputSize workCoefficient workDegree
    workBound

theorem target_of_certificate {Previous : Type uPrevious}
    {M : LocalModel.{uModel}}
    {Candidate : Previous -> Type uCandidate}
    {candidateObject : (previous : Previous) -> Candidate previous ->
      M.problem.Ambient}
    {realizes : (previous : Previous) -> M.problem.Ambient ->
      Candidate previous -> Prop}
    {previous : Previous}
    {schedule : Core.Finite.Enumeration (Candidate previous)}
    (target : _root_.Hypostructure.CT1.Target
      (targetSpec M Candidate candidateObject realizes) previous schedule) :
    Exists fun candidate =>
      candidate ∈ schedule.values ∧
        realizes previous (candidateObject previous candidate) candidate := by
  exact target

end Hypostructure.PDE.CT1
