import Hypostructure.Core.Strategy.Dag
import Hypostructure.Fixtures.Budgets
import Hypostructure.Graph.Object
import Hypostructure.PDE.Model

/-!
# Homogeneous-bottleneck Graph/PDE transfer fixtures

The same inert registration constructor instantiates the Core
`HomogeneousBottleneck` Strategy over an actual finite-graph problem and a
represented finite PDE problem.  The two sealed blueprints place the Strategy
on opposite sides of an unrelated registered scan, so neither the Strategy
nor the generic DAG compiler prescribes its position.
-/

namespace Hypostructure.Fixtures.HomogeneousBottleneck

open Hypostructure
open Hypostructure.Core.Strategy.Dag

universe uResidual uAmbient uBranch

private def empty (α : Type uResidual) [DecidableEq α] :
    Core.Finite.Enumeration α :=
  Core.Finite.Enumeration.empty α

private def singleton : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

private def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

private abbrev unitResponseSystem : Core.Response.System Unit :=
  Core.Response.System.ofDecodedContexts Unit Unit Unit (fun _ _ => ()) id

private def unitTargetSemantics :
    Core.Response.TargetSemantics unitResponseSystem where
  TargetResponse := fun _ _ => True
  Accepts := fun _ => True
  target_iff_accepts := by simp

/-- One residual-indexed fixture presentation.  Every numeric observation is
read through `measure`; neither Core nor the Strategy supplies a bound. -/
noncomputable def registration
    {Residual : Type uResidual} (Target : Residual → Prop)
    (targetDecidable : (residual : Residual) → Decidable (Target residual))
    (measure : Residual → Nat) :
    Core.Strategy.HomogeneousBottleneck.Registration Residual Target where
  Item := fun _ => Unit
  HomogeneityCode := fun _ => Unit
  items := fun _ => singleton
  completeHomogeneityCodes := fun _ => completeUnit
  homogeneityCodeOf := fun _ _ => ()
  homogeneityCapacity := fun residual _ => measure residual

  CapacityLabel := fun _ => Unit
  codeCapacity := fun residual _ => some (measure residual)
  codeLabel := fun _ _ => some ()
  codeLabelDecidableEq := fun _ => inferInstance

  Datum := fun _ => Unit
  LocalClass := fun _ => Unit
  Promotion := fun _ => Unit
  data := fun _ => singleton
  completeLocalClasses := fun _ => completeUnit
  classOf := fun _ _ => ()
  Direct := fun _ _ => True
  promote := fun _ _ => ()
  directDecidable := fun _ _ => isTrue trivial

  LocalIndex := fun _ => Unit
  LocalFailureData := fun _ _ => Empty
  localOrder := fun _ => empty Unit
  LocalFailure := fun _ _ => False
  localFailureData := fun _ _ failure => failure.elim
  localFailureDecidable := fun _ _ => isFalse id
  localContribution := fun residual _ => measure residual

  Representative := Unit
  responseSystem := unitResponseSystem
  targetSemantics := unitTargetSemantics
  ResponseCandidate := Unit
  ResponseRow := Unit
  candidatePiece := fun _ => ()
  rowPiece := fun _ => ()
  rowResponse := fun _ _ => ()
  responseSource := fun _ => ()
  responseCoordinates := fun _ => empty Unit
  responseCandidates := fun _ => empty Unit
  responseRows := fun _ => empty Unit
  ResponseAdmissible := fun _ _ _ => True
  ResponseStrictlySmaller := fun _ _ _ => True
  responseValueDecEq := by
    change DecidableEq Unit
    infer_instance
  responseAdmissibleDecidable := fun _ _ _ => isTrue trivial
  responseSmallerDecidable := fun _ _ _ => isTrue trivial
  responseCandidateCoverage := by
    intro _ _ member
    change _ ∈ [] at member
    simp at member
  responseRowCoverage := by
    intro _ _ member
    change _ ∈ [] at member
    simp at member

  AdmissibilityField := fun _ => Unit
  AdmissibilityFailureData := fun _ _ => Empty
  admissibilityOrder := fun _ => empty Unit
  AdmissibilityFailure := fun _ _ => False
  admissibilityFailureData := fun _ _ failure => failure.elim
  admissibilityFailureDecidable := fun _ _ => isFalse id
  admissibilityContribution := fun residual _ => measure residual

  TargetCandidate := fun _ => Unit
  ExceptionalCandidate := fun _ => Unit
  outcomeCandidates := fun _ => empty (Sum Unit Unit)
  RealizesTarget := fun residual _ => Target residual
  RealizesException := fun _ _ => False
  targetRealizationDecidable := fun residual _ => targetDecidable residual
  exceptionRealizationDecidable := fun _ _ => isFalse id
  targetOfRealization := fun _ _ realizes => realizes

  supportBudget := Hypostructure.Fixtures.Budgets.naturalResource
  SupportSite := fun _ => Unit
  SupportWitness := fun _ _ => Unit
  supportFamily := fun _ =>
    { indices := empty Unit
      fibres := fun _ => singleton }
  SupportActive := fun _ _ => True
  SupportRelation := fun _ _ _ => True
  supportContribution := fun residual _ _ => measure residual
  supportRequired := measure
  supportCapacity := measure
  supportActiveDecidable := fun _ _ => isTrue trivial
  supportRelationDecidable := fun _ _ _ => isTrue trivial
  supportResourceLEDecidable := Nat.decLe

  BoundedMember := fun _ => Unit
  BoundedLabel := fun _ => Unit
  boundedMembers := fun _ => singleton
  boundedLowerMass := fun residual _ => measure residual
  boundedCapacity := fun residual _ => some (measure residual)
  boundedLabel := fun _ _ => some ()
  boundedLabelDecidableEq := fun _ => inferInstance

  localFailureScheduled := by
    intro _ _ _ failure
    exact failure.elim
  responseDefectScheduled := by
    intro _ _ _ rowMember
    change _ ∈ [] at rowMember
    simp at rowMember
  admissibilityFailureScheduled := by
    intro _ _ _ failure
    exact failure.elim
  supportDeficitScheduled := by
    intro _ _ member
    change _ ∈ [] at member
    simp at member
  supportCapacityFailureScheduled := by
    intro residual failure
    exact (failure (Nat.le_refl (measure residual))).elim
  boundedCapacityTotal := by
    intro residual _ _
    exact ⟨measure residual, rfl⟩
  boundedLabelTotal := by
    intro _ _ _
    exact ⟨(), rfl⟩

private def scanData
    (P : Core.Problem.{uAmbient, uBranch}) : Core.ScanData P where
  Item := fun _ => Unit
  schedule := fun _ => empty Unit
  witness := fun _ _ => False
  witnessDecidable := fun _ _ => isFalse id

/-! ## Finite-graph instantiation -/

private def graphProblem :=
  Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit)

private def graphMeasure
    (input : Core.Strategy.ProblemInput graphProblem) : Nat :=
  input.object.vertices.card

private def graphTarget : Core.Target graphProblem where
  Predicate := fun object => object.vertices.card ≠ Nat.zero
  Statement := ∀ object, object.vertices.card ≠ Nat.zero
  statement_to_target := fun statement object _ => statement object
  target_to_statement := fun proof object => proof object trivial

private def graphSplit : Core.DichotomyData graphProblem graphTarget where
  LeftPayload := fun _ => PUnit
  RightPayload := fun _ => PUnit
  classify := fun _ => .inl ⟨⟩

noncomputable def graphDefinition : Core.ProblemDefinition where
  problem := graphProblem
  target := graphTarget
  initialState := fun _ => ()
  data := {
    targetDecidable :=
      fun (input : Core.Strategy.ProblemInput graphProblem) => by
        change Decidable (input.object.vertices.card ≠ Nat.zero)
        infer_instance
    scans := [scanData graphProblem]
    dichotomies := [graphSplit]
    homogeneousBottlenecks :=
      [registration
        (Residual := Core.Strategy.ProblemInput graphProblem)
        (fun (input : Core.Strategy.ProblemInput graphProblem) =>
          graphTarget.Predicate input.object)
        (fun (input : Core.Strategy.ProblemInput graphProblem) => by
          change Decidable (input.object.vertices.card ≠ Nat.zero)
          infer_instance)
        graphMeasure]
  }

instance : NeZero graphDefinition.data.scans.length :=
  ⟨by simp [graphDefinition]⟩

instance : NeZero graphDefinition.data.dichotomies.length :=
  ⟨by simp [graphDefinition]⟩

instance : NeZero graphDefinition.data.homogeneousBottlenecks.length :=
  ⟨by simp [graphDefinition]⟩

/-- The Graph DAG places the homogeneous-bottleneck vertex first. -/
noncomputable def graphProgram : Program graphDefinition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.homogeneousBottleneck
      |>.orderedWitnessScan)

noncomputable def graphReduction : ReductionDeclaration :=
  reduceDag% graphDefinition graphProgram

/-- The bounded homogeneous-bottleneck output can reuse a sibling
continuation without any Graph-specific route data.  Exceptional and
structured remain independent live residuals. -/
noncomputable def graphSiblingProgram : Program graphDefinition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.dichotomy 0
        (left := Blueprint.root.homogeneousBottleneck
          (bounded := fun residual => residual.autoroute))
        (right := Blueprint.root.orderedWitnessScan))

noncomputable def graphSiblingReduction : ReductionDeclaration :=
  reduceDag% graphDefinition graphSiblingProgram

example : graphSiblingReduction.report.workBound = 4 := rfl

example : graphSiblingReduction.report.proofTrace.resolvedRoutes.map
    (fun route =>
      (route.sourceId, route.destinationId, route.scopeName,
        route.destinationWork)) =
    [(1, 2, "sibling", 1)] := rfl

/-! ## Represented PDE instantiation -/

private abbrev PDEField := Fin 4 → Int

private def pdeProblem : Core.Problem where
  Ambient := PDEField
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private def pdeMeasureObject (field : PDEField) : Nat :=
  Finset.univ.sum fun index => Int.natAbs (field index)

private def pdeMeasure
    (input : Core.Strategy.ProblemInput pdeProblem) : Nat :=
  pdeMeasureObject input.object

private def pdeTarget : Core.Target pdeProblem where
  Predicate := fun object => pdeMeasureObject object ≠ Nat.zero
  Statement := ∀ object, pdeMeasureObject object ≠ Nat.zero
  statement_to_target := fun statement object _ => statement object
  target_to_statement := fun proof object => proof object trivial

noncomputable def pdeDefinition : Core.ProblemDefinition where
  problem := pdeProblem
  target := pdeTarget
  initialState := fun _ => ()
  data := {
    targetDecidable :=
      fun (input : Core.Strategy.ProblemInput pdeProblem) => by
        change Decidable (pdeMeasureObject input.object ≠ Nat.zero)
        infer_instance
    scans := [scanData pdeProblem]
    homogeneousBottlenecks :=
      [registration
        (Residual := Core.Strategy.ProblemInput pdeProblem)
        (fun (input : Core.Strategy.ProblemInput pdeProblem) =>
          pdeTarget.Predicate input.object)
        (fun (input : Core.Strategy.ProblemInput pdeProblem) => by
          change Decidable (pdeMeasureObject input.object ≠ Nat.zero)
          infer_instance)
        pdeMeasure]
  }

instance : NeZero pdeDefinition.data.scans.length :=
  ⟨by simp [pdeDefinition]⟩

instance : NeZero pdeDefinition.data.homogeneousBottlenecks.length :=
  ⟨by simp [pdeDefinition]⟩

/-- The PDE DAG places the same Core Strategy after an unrelated scan. -/
noncomputable def pdeProgram : Program pdeDefinition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.orderedWitnessScan
      |>.homogeneousBottleneck)

noncomputable def pdeReduction : ReductionDeclaration :=
  reduceDag% pdeDefinition pdeProgram

end Hypostructure.Fixtures.HomogeneousBottleneck
