import Hypostructure.Core.Strategy

/-!
# Branch-aware dichotomy ledger fixture

The selected dichotomy witness enters the accumulated ledger before the
selected continuation runs.  The two continuation types are distinct and
share only their literal predecessor.
-/

namespace Hypostructure.Fixtures.DichotomyBranchLedger

open Hypostructure.Core.Residual
open Hypostructure.Core.Residual.Ledger
open Hypostructure.Core.Strategy

abbrev Previous := Ledger Bool

def split : Dichotomy Previous where
  LeftPayload previous := PLift (residualOf previous = true)
  RightPayload previous := PLift (residualOf previous = false)
  classify previous :=
    match h : residualOf previous with
    | true => .inl ⟨by simp⟩
    | false => .inr ⟨by simp⟩

/-- The hot continuation can consume the hot witness directly from its
incoming branch stage. -/
def hotContinuation (_stage : split.LeftStage) :
    Contract split.LeftStage where
  Terminal := PUnit
  Payload stage _ := PLift (residualOf stage = true)
  produce stage := ⟨⟨⟩, stage.added⟩
  exhaustive stage := ⟨⟨⟨⟩, stage.added⟩⟩

/-- The cold continuation has the analogous, but incompatible, input type. -/
def coldContinuation (_stage : split.RightStage) :
    Contract split.RightStage where
  Terminal := PUnit
  Payload stage _ := PLift (residualOf stage = false)
  produce stage := ⟨⟨⟩, stage.added⟩
  exhaustive stage := ⟨⟨⟨⟩, stage.added⟩⟩

@[simp] theorem hotContinuation_reads_hot_witness
    (stage : split.LeftStage) :
    ((hotContinuation stage).produce stage).snd.down =
      stage.added.down := rfl

@[simp] theorem coldContinuation_reads_cold_witness
    (stage : split.RightStage) :
    ((coldContinuation stage).produce stage).snd.down =
      stage.added.down := rfl

def hotRoot : Previous := Ledger.initial true
def coldRoot : Previous := Ledger.initial false

def hotRun :=
  runRouted split hotContinuation coldContinuation hotRoot

def coldRun :=
  runRouted split hotContinuation coldContinuation coldRoot

@[simp] theorem hotRun_previous : hotRun.previous = hotRoot := rfl
@[simp] theorem coldRun_previous : coldRun.previous = coldRoot := rfl

@[simp] theorem hotRun_residual : residualOf hotRun = true := rfl
@[simp] theorem coldRun_residual : residualOf coldRun = false := rfl

theorem hotRun_selected :
    ∃ payload, hotRun.added = Sum.inl payload := by
  simp [hotRun, hotRoot, split, runRouted]

theorem coldRun_selected :
    ∃ payload, coldRun.added = Sum.inr payload := by
  simp [coldRun, coldRoot, split, runRouted]

#print axioms hotRun_selected
#print axioms coldRun_selected

end Hypostructure.Fixtures.DichotomyBranchLedger
