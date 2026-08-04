import Hypostructure.Core.Strategy.Dag

/-!
# Registered canonical accounting-composition fixtures

The same four Core registrations are instantiated over a graph-shaped
residual, a PDE-shaped residual, and a closed `StrategyData` family.  The two
blueprints deliberately use different orders, witnessing that the DAG adds
no hidden predecessor, successor, or control dependency between them.
-/

namespace Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.Dag

private def singleton : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

private def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

noncomputable def pairRegistration
    {Residual : Type} (scale : Residual → Nat) :
    Core.Strategy.CanonicalPairResponseAccounting.Registration Residual where
  Pair := fun _ => Unit
  pairSchedule := fun _ => singleton
  IntendedPair := fun _ _ => True
  pairSchedule_exact := by
    intro residual pair
    cases pair
    simp [singleton, Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  Dependent := fun _ _ => True
  AdmittedDependent := fun _ _ => True
  dependent_exact := by simp
  dependentDecidable := fun _ _ => isTrue trivial
  pairCharge := fun residual _ => scale residual
  pairCapacity := scale
  BlockerKind := fun _ => Unit
  completeBlockerKinds := fun _ => completeUnit
  CanonicalBlocker := fun _ _ _ => True
  blocker_exact := by simp
  roleOf := fun _ _ =>
    Core.Strategy.CanonicalPairResponseAccounting.Role.blocked ()
  role_freeAnchor_exact := by
    intro residual pair
    simp [Core.Strategy.CanonicalPairResponseAccounting.Role.blocked,
      Core.Strategy.CanonicalPairResponseAccounting.Role.freeAnchor]
  role_blocked_exact := by
    intro residual pair kind
    cases kind
    simp [Core.Strategy.CanonicalPairResponseAccounting.Role.blocked]
  roleCapacity := fun residual _ => scale residual

noncomputable def capacityRegistration
    {Residual : Type} (scale : Residual → Nat) :
    Core.Strategy.CanonicalCapacityTokenAccounting.Registration Residual where
  Demand := fun _ => Unit
  Token := fun _ => Unit
  Role := fun _ => Unit
  Label := fun _ => Unit
  demands := fun _ => singleton
  tokens := fun _ => singleton
  completeLabels := fun _ => completeUnit
  Eligible := fun _ _ _ => True
  eligibleDecidable := fun _ _ _ => isTrue trivial
  demandWeight := fun residual _ => scale residual
  tokenCapacity := fun residual _ => scale residual
  required := scale
  roleOf := fun _ _ => ()
  labelOf := fun _ _ _ => ()
  labelCapacity := fun residual _ => scale residual
  aggregateLabel := fun _ => Unit
  aggregateLabelDecidableEq := fun _ => inferInstance
  memberAggregateLabel := fun _ _ => ()

noncomputable def pressureRegistration
    {Residual : Type} (scale : Residual → Nat) :
    Core.Strategy.CoupledHomogeneousFibrePressure.Registration Residual where
  Item := fun _ => Unit
  Token := fun _ => Unit
  Role := fun _ => Unit
  Label := fun _ => Unit
  items := fun _ => singleton
  completeLabels := fun _ => completeUnit
  labelOf := fun _ _ => ()
  fibreCapacity := fun residual _ => scale residual
  Payer := fun _ => Unit
  Obstruction := fun _ => Unit
  Resource := fun _ => Unit
  payers := fun _ => singleton
  obstructions := fun _ =>
    { fallbackDefault := ()
      remaining := []
      nodup := by simp
      decEq := inferInstance }
  tierTwo := fun _ _ => singleton
  Eligible := fun _ _ => True
  obstructionCost := fun residual _ => scale residual
  payerResource := fun _ _ => ()
  charge := fun residual _ => scale residual
  demand := scale
  eligibleDecidable := fun _ _ => isTrue trivial
  resourceDecidableEq := fun _ => inferInstance
  Member := fun _ => Unit
  AggregateLabel := fun _ => Unit
  members := fun _ => singleton
  memberLowerMass := fun residual _ => scale residual
  memberCapacity := fun residual _ => some (scale residual)
  memberLabel := fun _ _ => some ()
  aggregateLabelDecidableEq := fun _ => inferInstance

noncomputable def bottleneckRegistration
    {Residual : Type} (scale : Residual → Nat) :
    Core.Strategy.FiniteBottleneckClassification.Registration Residual where
  PatternItem := fun _ => Unit
  CoarseCode := fun _ => Unit
  patternItems := fun _ => singleton
  completeCoarseCodes := fun _ => completeUnit
  coarseCodeOf := fun _ _ => ()
  PressureLabel := fun _ => Unit
  pressureCapacity := fun residual _ => some (scale residual)
  pressureLabel := fun _ _ => some ()
  pressureLabelDecidableEq := fun _ => inferInstance
  Datum := fun _ => Unit
  SemanticTag := fun _ => Unit
  Promotion := fun _ => Unit
  data := fun _ => singleton
  completeSemanticTags := fun _ => completeUnit
  classOf := fun _ _ => ()
  Direct := fun _ _ => True
  promote := fun _ _ => ()
  directDecidable := fun _ _ => isTrue trivial
  SeparatorIndex := fun _ => Unit
  SeparatorData := fun _ _ => Empty
  separatorOrder := fun _ => singleton
  SeparatorFailure := fun _ _ => False
  separatorFailureData := fun _ _ failure => failure.elim
  separatorFailureDecidable := fun _ _ => isFalse id
  separatorContribution := fun residual _ => scale residual

structure GraphResidual where
  vertexCount : Nat

structure PDEResidual where
  representedModeCount : Nat

abbrev GraphStage := Ledger GraphResidual
abbrev PDEStage := Ledger PDEResidual

noncomputable def graphPairProfile :
    Core.Strategy.CanonicalPairResponseAccounting.Profile
      GraphStage GraphResidual where
  registration := pairRegistration (·.vertexCount)

noncomputable def pdePairProfile :
    Core.Strategy.CanonicalPairResponseAccounting.Profile
      PDEStage PDEResidual where
  registration := pairRegistration (·.representedModeCount)

noncomputable def graphCapacityProfile :
    Core.Strategy.CanonicalCapacityTokenAccounting.Profile
      GraphStage GraphResidual where
  registration := capacityRegistration (·.vertexCount)

noncomputable def pdeCapacityProfile :
    Core.Strategy.CanonicalCapacityTokenAccounting.Profile
      PDEStage PDEResidual where
  registration := capacityRegistration (·.representedModeCount)

noncomputable def graphPressureProfile :
    Core.Strategy.CoupledHomogeneousFibrePressure.Profile
      GraphStage GraphResidual where
  registration := pressureRegistration (·.vertexCount)

noncomputable def pdePressureProfile :
    Core.Strategy.CoupledHomogeneousFibrePressure.Profile
      PDEStage PDEResidual where
  registration := pressureRegistration (·.representedModeCount)

noncomputable def graphBottleneckProfile :
    Core.Strategy.FiniteBottleneckClassification.Profile
      GraphStage GraphResidual where
  registration := bottleneckRegistration (·.vertexCount)

noncomputable def pdeBottleneckProfile :
    Core.Strategy.FiniteBottleneckClassification.Profile
      PDEStage PDEResidual where
  registration := bottleneckRegistration (·.representedModeCount)

example : graphPairProfile.execution.Terminal =
    pdePairProfile.execution.Terminal := rfl

example : graphCapacityProfile.execution.Terminal =
    pdeCapacityProfile.execution.Terminal := rfl

example : graphPressureProfile.execution.Terminal =
    pdePressureProfile.execution.Terminal := rfl

example : graphBottleneckProfile.execution.Terminal =
    pdeBottleneckProfile.execution.Terminal := rfl

private def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private def target : Core.Target problem where
  Predicate := fun object => object = Nat.zero
  Statement := ∀ object, object = Nat.zero
  statement_to_target := fun statement object _ => statement object
  target_to_statement := fun proof object => proof object trivial

noncomputable def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input => by
      change Decidable (input.object = Nat.zero)
      exact Nat.decEq input.object Nat.zero
    canonicalPairResponseAccountings :=
      [pairRegistration (fun input => input.object)]
    canonicalCapacityTokenAccountings :=
      [capacityRegistration (fun input => input.object)]
    coupledHomogeneousFibrePressures :=
      [pressureRegistration (fun input => input.object)]
    finiteBottleneckClassifications :=
      [{ fst := ⟨0, by simp⟩
         snd := bottleneckRegistration (fun input => input.object) }]
  }

instance : NeZero definition.data.canonicalPairResponseAccountings.length :=
  ⟨by simp [definition]⟩

instance :
    NeZero definition.data.canonicalCapacityTokenAccountings.length :=
  ⟨by simp [definition]⟩

instance :
    NeZero definition.data.coupledHomogeneousFibrePressures.length :=
  ⟨by simp [definition]⟩

instance :
    NeZero definition.data.finiteBottleneckClassifications.length :=
  ⟨by simp [definition]⟩

noncomputable def forwardProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.canonicalPairResponseAccounting
      |>.canonicalCapacityTokenAccounting
      |>.coupledHomogeneousFibrePressure
      |>.finiteBottleneckClassification)

noncomputable def sealedForwardReduction : ReductionDeclaration :=
  reduceDag% definition forwardProgram

end Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions
