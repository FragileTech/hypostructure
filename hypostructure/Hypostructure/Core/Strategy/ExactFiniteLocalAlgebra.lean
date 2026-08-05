import Hypostructure.CTAdapters
import Hypostructure.Core.Residual.Stage
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraSemantics

/-!
# Exact finite local algebra

CT9 classifies the exact residual-owned item schedule.  CT16 then exhausts
the complete generated relation table.  No cardinality, row, quotient, or
execution outcome is accepted from a caller.
-/

namespace Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uItem uLabel uRelation

/-- One exact ledger-backed use of the residual semantics.  The item schedule
is a typed query because it may be derived from a fact appended by an earlier
Strategy.  No predecessor value, trace, node identifier, or execution result
can enter through the semantic registration. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  Item : Residual → Type uItem
  items : Query Previous fun previous =>
    Core.Finite.Enumeration (Item (residualOf previous))
  semantics : Semantics.{uResidual, uLabel, uRelation} Residual
  label : (residual : Residual) →
    Item residual → semantics.Label residual

/-- Lift inert residual registration data to any literal accumulated ledger
stage.  The only stage operation is the canonical stable-residual query. -/
def Profile.ofRegistration
    [HasResidual Previous Residual]
    (registration :
      Registration.{uResidual, uItem, uLabel, uRelation} Residual) :
    Profile.{uPrevious, uResidual, uItem, uLabel, uRelation}
      Previous Residual where
  Item := registration.Item
  items :=
    (Query.residual (Source := Previous) (Residual := Residual)).dependentMap
      fun _ residual => registration.items residual
  semantics := registration.semantics
  label := registration.label

namespace Profile

variable [HasResidual Previous Residual]
variable (profile :
  Profile.{uPrevious, uResidual, uItem, uLabel, uRelation} Previous Residual)

def ct9Spec : CT9.Spec Previous where
  Item := fun previous => profile.Item (residualOf previous)
  Label := fun previous => profile.semantics.Label (residualOf previous)
  label := fun previous => profile.label (residualOf previous)
  capacity := fun previous =>
    profile.semantics.capacity (residualOf previous)

def ct9Capability : CT9.Capability profile.ct9Spec where
  items := profile.items
  labels := fun previous =>
    profile.semantics.labels (residualOf previous)
  inputSize := fun previous =>
    (profile.semantics.labels (residualOf previous)).card *
      ((profile.items previous).card + 1)
  workCoefficient := 1
  workDegree := 1
  workBound := by
    intro previous
    simp [CT9.localCheckBound]
    exact Nat.le_succ _

abbrev CT9Output (previous : Previous) :=
  CT9.ExecutionResult profile.ct9Spec profile.ct9Capability

abbrev LabelledStage :=
  Ledger.Extension Previous profile.CT9Output

def base (stage : profile.LabelledStage) : Previous :=
  stage.previous

abbrev Coordinate (stage : profile.LabelledStage) :=
  profile.semantics.RelationIndex (residualOf stage) ×
    (profile.semantics.Label (residualOf stage) ×
      profile.semantics.Label (residualOf stage))

def coordinates (stage : profile.LabelledStage) :
    Core.Finite.Enumeration (profile.Coordinate stage) :=
  (profile.semantics.relationIndices (residualOf stage)).toEnumeration.product
    ((profile.semantics.labels (residualOf stage)).toEnumeration.product
      (profile.semantics.labels (residualOf stage)).toEnumeration)

def code (stage : profile.LabelledStage) : List Bool :=
  (profile.coordinates stage).values.map fun coordinate =>
    profile.semantics.relation (residualOf stage) coordinate.1
      coordinate.2.1 coordinate.2.2

/-- A registered generated table cannot alter the closed code: its required
semantic audit identifies it with the code Core derives from the complete
coordinate schedule. -/
theorem targetCode_eq_code (stage : profile.LabelledStage) :
    profile.semantics.targetCode (residualOf stage) = profile.code stage := by
  exact profile.semantics.targetCode_exact (residualOf stage)

def ct16Spec : CT16.Spec profile.LabelledStage where
  Coordinate := profile.Coordinate
  InSupport := fun _ _ => True
  ClosedCode := fun _ => List Bool
  closedCode := profile.code
  targetCode := fun stage =>
    profile.semantics.targetCode (residualOf stage)

def codeComputation :
    CT16.ClosedCodeComputation profile.ct16Spec where
  run := fun stage => ⟨profile.code stage, (profile.coordinates stage).card⟩
  correct := fun _ => rfl
  budget := {
    size := fun stage => (profile.coordinates stage).card
    checks := fun stage => (profile.coordinates stage).card
    coefficient := 1
    degree := 1
    bounded := by intro stage; simp
  }
  checks_eq := fun _ => rfl

def equalityDecision :
    CT16.CodeEqualityDecision profile.ct16Spec :=
  CT16.CodeEqualityDecision.unitCost
    (fun stage => (profile.coordinates stage).card)
    (fun _ => inferInstanceAs (DecidableEq (List Bool)))

def ct16Capability : CT16.Capability profile.ct16Spec where
  coordinates :=
    (Query.residual (Source := profile.LabelledStage)
      (Residual := Residual)).map fun stage _ => profile.coordinates stage
  inSupportDecidable := fun _ _ => .isTrue trivial
  codeComputation := profile.codeComputation
  equalityDecision := profile.equalityDecision

/-- The Strategy is literally CT9 followed by CT16.  `compose` indexes CT16
by the exact ledger extension produced by CT9, so neither output is copied or
reconstructed. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  (CTAdapters.ct9 profile.ct9Capability).compose
    (CTAdapters.ct16 profile.ct16Capability)

noncomputable def run (previous : Previous) :=
  profile.execution.run previous

/-- Exact closed code projected from the literal CT16 result produced after
CT9.  The finite-local-algebra profile has total support and its registered
target code is definitionally the computed code, so the other CT16 terminals
are contradictory.  This projection never reruns either CT. -/
def codeOfExecution {previous : Previous}
    (result : profile.execution.Output previous) : List Bool := by
  let generated := result.2
  exact match terminalEq : generated.terminal, generated.outcome with
  | .properSupport, .properSupport residual =>
      False.elim (residual.absent trivial)
  | .exactCode, .exactCode certificate => certificate.state.code
  | .mismatch, .mismatch residual =>
      False.elim (residual.notEqual
        (residual.state.exact.trans
          (profile.targetCode_eq_code generated.stage.previous).symm))

@[simp] theorem run_first (previous : Previous) :
    (profile.run previous).fst =
      (CTAdapters.ct9 profile.ct9Capability).run previous := rfl

@[simp] theorem run_second (previous : Previous) :
    (profile.run previous).snd =
      (CTAdapters.ct16 profile.ct16Capability).run
        (Ledger.extend previous
          ((CTAdapters.ct9 profile.ct9Capability).run previous)) := rfl

end Profile

end Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra
