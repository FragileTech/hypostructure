import Hypostructure.Core.Strategy.Dag
import Hypostructure.Graph.Strategy.FiniteStateCapacity
import Hypostructure.PDE.Strategy.FiniteStateCapacity

/-!
# Graph/PDE consumers of finite-state capacity

Both consumers register only primitive domain observations and invoke the
same sealed Core strategy chain.  The final two checks execute the existing
CT17 → CT14 profile on concrete domain states and verify that Core computes
the survivor and capacity terminals.
-/

namespace Hypostructure.Fixtures.FiniteStateCapacityDomains

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.Dag

universe uAmbient

namespace Neutral

universe uResidual
universe uJoint

def singleton : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

def zeroScale : Core.Finite.Enumeration Nat :=
  Core.Finite.Enumeration.singleton 0

def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

noncomputable def unitJointProfile :
    Core.DependentOwnerGlueCapacity.BaseProfile.{
      uJoint, uJoint, uJoint, uJoint, uJoint} where
  Base := ULift.{uJoint} Unit
  Owner := ULift.{uJoint} Unit
  Local := fun _ => ULift.{uJoint} Unit
  Global :=
    ULift.{uJoint} Unit ×
      (ULift.{uJoint} Unit → ULift.{uJoint} Unit)
  Code :=
    ULift.{uJoint} Unit ×
      (ULift.{uJoint} Unit → ULift.{uJoint} Unit)
  finiteBase := inferInstance
  finiteOwner := inferInstance
  finiteLocal := fun _ => inferInstance
  finiteCode := inferInstance
  glue := fun base choice => (base, choice)
  recoverBase := Prod.fst
  recoverLocal := Prod.snd
  recoverBase_glue := by simp
  recoverLocal_glue := by simp
  code := id
  codeInjectiveOnGlue := by
    intro _ _ _ _ equal
    exact equal

def supplySummary : Core.Strategy.LocalSupplyLowerBound.Summary :=
  { requiredMass := Fintype.card Unit
    observedSupply := Fintype.card Unit
    assignedSurplus := Fintype.card Empty
    subcubicAtomCard := Fintype.card Empty
    netDeficiency :=
      { scale := Fintype.card Unit
        coefficient := Fintype.card Empty
        deficiency := Fintype.card Unit
        remainder := Fintype.card Empty
        surplus := Fintype.card Unit
        scale_pos := by simp
        finiteCap := by simp }
    subcubicAtomPart := by simp
    assignedSurplusNonAtom := by
      intro positive
      simp only [Fintype.card_empty] at positive
      exact absurd positive (Nat.lt_irrefl 0)
    netDeficiencyCap := Nat.le_add_right _ _ }

noncomputable def packingSemantics {Residual : Type uResidual}
    (Target : Residual → Prop) :
    Core.Strategy.ObstructionPackingClosure.Semantics.{
      uResidual, uResidual} Residual Target where
  Occurrence := fun _ => ULift.{uResidual} Unit
  occurrences := fun _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  conflict := fun _ _ _ => True
  conflictDecidable := fun _ _ _ => isTrue trivial
  conflictSymmetric := fun _ _ _ _ => trivial
  freeForcesTarget := by
    intro residual empty
    change [ULift.up ()] = [] at empty
    simp at empty

noncomputable def normalizationRegistration {Residual : Type uResidual}
    (Target : Residual → Prop) :
    Core.Strategy.SupportComplementNormalization.Registration
  Residual Target (packingSemantics Target) where
  AmbientItem := fun _ => ULift.{uResidual} Unit
  ambientSupport := fun _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  cover := fun _ _ => [ULift.up ()]
  conflict_iff_shared_item := by
    intro residual left right
    simp [packingSemantics]
  cover_ne := by simp
  LocalPiece := fun _ _ => ULift.{uResidual} Unit
  localPieces := fun _ _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  FailureData := fun _ _ _ => ULift.{uResidual} Empty
  Failure := fun _ _ _ => False
  failureData := fun _ _ _ failure => failure.elim
  failureDecidable := fun _ _ _ => isFalse id
  contribution := fun _ complement _ => complement.card
  failureForcesTarget := fun _ _ _ failure => failure.elim

noncomputable def boundaryRegistration {Residual : Type uResidual} :
    Core.Strategy.BoundaryDemandAccounting.Registration Residual where
  Demand := fun _ => Unit
  Payer := fun _ => Unit
  demands := fun _ => singleton
  payers := fun _ => singleton
  Eligible := fun _ _ _ => True
  eligibleDecidable := fun _ _ _ => isTrue trivial
  demandWeight := fun _ _ => 1
  payerCapacity := fun _ _ => 1
  Member := fun _ => Unit
  Label := fun _ => Unit
  members := fun _ => singleton
  memberLowerMass := fun _ _ => 1
  memberCapacityRate := fun _ _ => 1
  memberLabel := fun _ _ => ()
  labelDecidableEq := fun _ => inferInstance

noncomputable def supplyRegistration {Residual : Type uResidual} :
    Core.Strategy.LocalSupplyLowerBound.Registration Residual
      (fun _ => Unit) where
  Member := fun _ => Unit
  Label := fun _ => Unit
  members := fun _ _ => singleton
  requiredMass := fun _ _ _ => 1
  observedSupply := fun _ _ _ => 1
  defectCorrection := fun _ _ _ => 0
  surplus := fun _ _ _ => 0
  label := fun _ _ _ => ()
  labelDecidableEq := fun _ => inferInstance
  pointwise := by simp

noncomputable def barrierRegistration {Residual : Type uResidual} :
    Core.Strategy.FiniteBarrierEnumeration.Registration Residual where
  Candidate := fun _ => Unit
  candidates := fun _ => completeUnit
  accepted := fun _ _ => True
  acceptedDecidable := fun _ _ => isTrue trivial
  labelCount := fun _ => 1
  profile := fun _ => {
    row := fun _ _ => BitVec.allOnes 1
  }
  leftLength := fun _ _ => 0
  rightLength := fun _ _ => 0
  flatCount_pos := by intro _ _; decide

noncomputable def rankRegistration {Residual : Type uResidual} :
    Core.Strategy.TargetRelativeRankDichotomy.Registration Residual
      (fun _ => Unit)
      (fun _ => Unit) where
  Response := fun _ => Unit
  response := fun _ => ()
  Datum := fun _ => Unit
  Class := fun _ => Unit
  Promotion := fun _ => Unit
  observationData := fun _ => singleton
  completeClasses := fun _ => completeUnit
  classOf := fun _ _ _ => ()
  Direct := fun _ _ _ => True
  promote := fun _ _ _ => ()
  directDecidable := fun _ _ _ => isTrue trivial
  coordinates := fun _ _ => singleton
  TargetDependent := fun _ _ _ => False
  targetDependentDecidable := fun _ _ _ => isFalse id
  charge := fun _ _ _ => 0
  capacitySlack := fun _ _ => 0

end Neutral

namespace Graph

private abbrev problem :=
  Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit)

private def target : Core.Target problem where
  Predicate := fun object : problem.Ambient =>
    Hypostructure.Graph.FiniteObject.vertexCount object = 0
  Statement := ∀ object : problem.Ambient,
    Hypostructure.Graph.FiniteObject.vertexCount object = 0
  statement_to_target := by
    intro statement object _
    exact statement object
  target_to_statement := by
    intro targetProof object
    exact targetProof object trivial

private abbrev Residual := Core.Strategy.ProblemInput problem

private def object : Hypostructure.Graph.FiniteObject where
  Vertex := PUnit
  graph := ⊥
  vertices := inferInstance
  decideAdj := inferInstance

private def input : Residual where
  object := object
  baseline := trivial
  branchState := ()

noncomputable def registration {AmbientItem : Residual → Type uAmbient} :
    Hypostructure.Graph.Strategy.FiniteStateCapacity.Registration.{
      0, 1, uAmbient, 1}
      Residual AmbientItem where
  object := fun residual => residual.object
  Target := fun _ _ => ULift.{1} Unit
  Offset := fun _ _ => ULift.{1} Unit
  Position := fun _ _ _ => ULift.{1} Unit
  Value := fun _ _ => ULift.{1} Nat
  targets := fun _ _ _ _ _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  offsets := fun _ _ _ _ _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  scales := fun _ _ _ _ _ => Neutral.zeroScale
  selectedScale := fun _ _ _ _ _ => 0
  selectedScale_mem := by
    intro
    simp [Neutral.zeroScale, Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  positions := fun _ _ _ _ _ _ =>
    Core.Finite.Enumeration.singleton (ULift.up ())
  finiteScaleLimit := fun _ object _ barrier supply =>
    object.vertexCount + barrier.rows.length + supply.observedSupply
  targetValue := fun _ object rank barrier supply _ =>
    ULift.up (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply + 1)
  blockValue := fun _ object rank barrier supply _ _ _ =>
    ULift.up (object.vertexCount + rank +
      barrier.rows.length + supply.observedSupply)
  orbitValue := fun _ object rank barrier supply _ _ =>
    ULift.up (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply)
  Compatible := fun _ _ _ _ => True
  compatibleDecidable := fun _ _ _ _ => isTrue trivial
  valueDecidableEq := fun _ _ => inferInstance
  Label := fun _ _ => ULift.{1} Unit
  memberLowerMass := fun _ object rank barrier supply _ =>
    object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply
  memberCapacity := fun _ object rank barrier supply _ =>
    some (object.vertexCount + rank + barrier.rows.length +
      supply.observedSupply)
  memberLabel := fun _ _ _ _ _ _ => some (ULift.up ())
  labelDecidableEq := fun _ _ => inferInstance
  RealizedState := fun _ _ _ _ _ _ => ULift.{1} Unit
  realizedStateFinite := fun _ _ _ _ _ _ => inferInstance
  realizedStateNonempty := fun _ _ _ _ _ _ => inferInstance
  ambientOrder := fun _ object _ _ _ _ => object.vertexCount
  remainderCard := fun _ object _ _ _ _ => object.vertexCount
  statePowerExponent := fun _ _ _ _ _ => 1
  statePowerExponent_pos := by intro; norm_num
  forcedBase := fun _ _ _ _ _ => 1
  flatBase := fun _ _ _ _ _ => 1
  flatBase_pos := by
    intro
    norm_num
  jointProfile := fun _ _ _ _ _ _ => Neutral.unitJointProfile
  jointBaseCard := by intro; simp [Neutral.unitJointProfile]
  jointExponent := fun _ _ _ _ _ => 1
  jointWeight := fun _ _ _ _ _ _ _ => 0
  jointLocalLower := by
    intro _ _ _ _ _ _ _
    change 2 ^ 0 ≤ Nat.card (ULift.{1} Unit) ^ 1
    simp
  jointPaidExponent := fun _ _ _ _ _ => 0
  jointPaidExponent_exact := by
    intro
    simp [Neutral.unitJointProfile,
      Core.DependentOwnerGlueCapacity.BaseProfile.weightSum]
  jointDesiredExponent := fun _ _ _ _ _ => 0
  jointErrorExponent := fun _ _ _ _ _ => 0
  jointCapacity := fun _ _ _ _ _ => 1
  jointCapacity_pos := by
    intro
    norm_num
  jointCodeCapacity := by intro; simp [Neutral.unitJointProfile]
  jointDesiredExponent_exact := by intro; simp

noncomputable def baseData : Core.StrategyData problem target where
  targetDecidable := fun residual =>
    Nat.decEq residual.object.vertexCount 0
  coldBranchAggregations := []
  obstructionPackingClosures :=
    [Neutral.packingSemantics
      (fun residual : Residual => residual.object.vertexCount = 0)]
  boundaryDemandAccountings := [⟨0, Neutral.boundaryRegistration⟩]
  localSupplyLowerBounds := [⟨0, Neutral.supplyRegistration⟩]
  finiteBarrierEnumerations := [Neutral.barrierRegistration]
  targetRelativeRankDichotomies :=
    [⟨(fun _ => Unit), ⟨0, Neutral.rankRegistration⟩⟩]
  finiteStateCapacities := [⟨0, registration.toCore⟩]

private def packingIndex :
    Fin baseData.obstructionPackingClosures.length :=
  ⟨0, by simp [baseData]⟩

private noncomputable def normalization :
    Sigma fun index : Fin baseData.obstructionPackingClosures.length =>
      Core.Strategy.SupportComplementNormalization.Registration
        Residual (fun residual => residual.object.vertexCount = 0)
        baseData.obstructionPackingClosures[index] := by
  refine ⟨packingIndex, ?_⟩
  simpa [baseData, packingIndex] using
    (Neutral.normalizationRegistration (Residual := Residual)
      (fun residual => residual.object.vertexCount = 0))

noncomputable def data : Core.StrategyData problem target :=
  { baseData with supportComplementNormalizations := [normalization] }

noncomputable def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := data

instance : NeZero definition.data.obstructionPackingClosures.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.supportComplementNormalizations.length :=
  ⟨by simp [definition, data]⟩

instance : NeZero definition.data.boundaryDemandAccountings.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.localSupplyLowerBounds.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.finiteBarrierEnumerations.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.targetRelativeRankDichotomies.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.finiteStateCapacities.length :=
  ⟨by simp [definition, data, baseData]⟩

noncomputable def program : Program definition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint definition.data .authoring)
      |>.obstructionPackingClosure
      |>.supportComplementNormalization
      |>.boundaryDemandAccounting
      |>.localSupplyLowerBound
      |>.finiteBarrierEnumeration
      |>.targetRelativeRankDichotomy
        (fullRank := fun branch => branch.finiteStateCapacity))

noncomputable def reduction : ReductionDeclaration :=
  reduceDag% definition program

theorem reduction_path : reduction.report.path =
    [.obstructionPackingClosure 0, .supportComplementNormalization 0,
      .boundaryDemandAccounting 0, .localSupplyLowerBound 0,
      .finiteBarrierEnumeration 0, .targetRelativeRankDichotomy 0,
      .finiteStateCapacity 0] :=
  rfl

theorem one_registration :
    definition.data.finiteStateCapacities.length = 1 := by
  simp [definition, data, baseData]

theorem toCore_reads_exact_graph (residual : Residual)
    (rank : Nat) (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary)
    (supply : Core.Strategy.LocalSupplyLowerBound.Summary) :
    (registration (AmbientItem := fun _ => Unit)).toCore.selectedScale
        residual rank barrier supply =
      (registration (AmbientItem := fun _ => Unit)).selectedScale
        residual residual.object rank barrier supply :=
  rfl

private def stage : Core.Strategy.InitStage problem :=
  Core.Residual.Ledger.initial input

private noncomputable def profile :
    Core.Strategy.FiniteStateCapacity.Profile
      (Core.Strategy.InitStage problem) Residual where
  AmbientItem := fun _ => Unit
  registration := registration.toCore
  complement := Query.ofFunction fun _ => Neutral.singleton
  independentRank := Query.ofFunction fun _ => 0
  finiteBarrierSummary :=
    Query.ofFunction fun _ =>
      Core.Strategy.FiniteBarrierEnumeration.Summary.ofRows [(0, 0)]
  localSupply := Query.ofFunction fun _ =>
    Neutral.supplySummary

theorem computes_survivor :
    (profile.execution.run stage).fst.terminal = .survivors := by
  rfl

theorem computes_capacity :
    (profile.execution.run stage).snd.terminal = .capacity := by
  rfl

end Graph

namespace PDE

private abbrev problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private abbrev atlas : Hypostructure.PDE.LocalAtlas problem where
  Point := Unit
  Window := Unit
  contains := fun _ _ => True
  nested := fun _ _ => True
  nested_refl := fun _ => trivial
  nested_trans := fun _ _ => trivial
  core := id
  core_nested := fun _ => trivial
  LocalObject := fun _ => Nat
  restrict := fun state _ => state
  restrictLocal := fun _ state => state
  restrict_refl := fun _ _ => rfl
  restrict_trans := fun _ _ _ => rfl
  restrict_global := by
    intro state source target nested
    rfl

private abbrev equation :
    Hypostructure.PDE.RepresentedEquation problem atlas where
  EquationData := fun _ _ => Unit
  satisfies := fun _ => True
  restrictEquation := fun _ _ data => data
  restrict_satisfies := fun _ _ _ valid => valid

private abbrev model : Hypostructure.PDE.LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

private def target : Core.Target problem where
  Predicate := fun state => state = 0
  Statement := ∀ state, state = 0
  statement_to_target := by
    intro statement state _
    exact statement state
  target_to_statement := by
    intro targetProof state
    exact targetProof state trivial

private abbrev Residual := Core.Strategy.ProblemInput problem

private def input : Residual where
  object := 3
  baseline := trivial
  branchState := ()

noncomputable def registration {AmbientItem : Residual → Type uAmbient} :
    Hypostructure.PDE.Strategy.FiniteStateCapacity.Registration
      model Residual AmbientItem where
  state := fun residual => residual.object
  Target := fun _ _ => Unit
  Offset := fun _ _ => Unit
  Position := fun _ _ _ => Unit
  Value := fun _ _ => Nat
  targets := fun _ _ _ _ _ => Neutral.singleton
  offsets := fun _ _ _ _ _ => Neutral.singleton
  scales := fun _ _ _ _ _ => Neutral.zeroScale
  selectedScale := fun _ _ _ _ _ => 0
  selectedScale_mem := by
    intro
    simp [Neutral.zeroScale, Core.Finite.Enumeration.singleton,
      Core.Finite.Enumeration.ofNodupList]
  positions := fun _ _ _ _ _ _ => Neutral.singleton
  finiteScaleLimit := fun _ state _ barrier supply =>
    state + barrier.rows.length + supply.observedSupply
  targetValue := fun _ state rank barrier supply _ =>
    state + rank + barrier.rows.length + supply.observedSupply + 1
  blockValue := fun _ state rank barrier supply _ _ _ =>
    state + rank + barrier.rows.length + supply.observedSupply
  orbitValue := fun _ state rank barrier supply _ _ =>
    state + rank + barrier.rows.length + supply.observedSupply
  Compatible := fun _ _ _ _ => True
  compatibleDecidable := fun _ _ _ _ => isTrue trivial
  valueDecidableEq := fun _ _ => inferInstance
  Label := fun _ _ => Unit
  memberLowerMass := fun _ state rank barrier supply _ =>
    state + rank + barrier.rows.length + supply.observedSupply
  memberCapacity := fun _ state rank barrier supply _ =>
    some (state + rank + barrier.rows.length + supply.observedSupply)
  memberLabel := fun _ _ _ _ _ _ => some ()
  labelDecidableEq := fun _ _ => inferInstance
  RealizedState := fun _ _ _ _ _ _ => Unit
  realizedStateFinite := fun _ _ _ _ _ _ => inferInstance
  realizedStateNonempty := fun _ _ _ _ _ _ => inferInstance
  ambientOrder := fun _ state _ _ _ _ => state
  remainderCard := fun _ state _ _ _ _ => state
  statePowerExponent := fun _ _ _ _ _ => 1
  statePowerExponent_pos := by intro; norm_num
  forcedBase := fun _ _ _ _ _ => 1
  flatBase := fun _ _ _ _ _ => 1
  flatBase_pos := by
    intro
    norm_num
  jointProfile := fun _ _ _ _ _ _ => Neutral.unitJointProfile
  jointBaseCard := by intro; simp [Neutral.unitJointProfile]
  jointExponent := fun _ _ _ _ _ => 1
  jointWeight := fun _ _ _ _ _ _ _ => 0
  jointLocalLower := by
    intro _ _ _ _ _ _ _
    change 2 ^ 0 ≤ Nat.card (ULift.{0} Unit) ^ 1
    simp
  jointPaidExponent := fun _ _ _ _ _ => 0
  jointPaidExponent_exact := by
    intro
    simp [Neutral.unitJointProfile,
      Core.DependentOwnerGlueCapacity.BaseProfile.weightSum]
  jointDesiredExponent := fun _ _ _ _ _ => 0
  jointErrorExponent := fun _ _ _ _ _ => 0
  jointCapacity := fun _ _ _ _ _ => 1
  jointCapacity_pos := by
    intro
    norm_num
  jointCodeCapacity := by intro; simp [Neutral.unitJointProfile]
  jointDesiredExponent_exact := by intro; simp

noncomputable def baseData : Core.StrategyData problem target where
  targetDecidable := fun residual =>
    Nat.decEq residual.object 0
  coldBranchAggregations := []
  obstructionPackingClosures :=
    [Neutral.packingSemantics
      (fun residual : Residual => residual.object = 0)]
  boundaryDemandAccountings := [⟨0, Neutral.boundaryRegistration⟩]
  localSupplyLowerBounds := [⟨0, Neutral.supplyRegistration⟩]
  finiteBarrierEnumerations := [Neutral.barrierRegistration]
  targetRelativeRankDichotomies :=
    [⟨(fun _ => Unit), ⟨0, Neutral.rankRegistration⟩⟩]
  finiteStateCapacities := [⟨0, registration.toCore⟩]

private def packingIndex :
    Fin baseData.obstructionPackingClosures.length :=
  ⟨0, by simp [baseData]⟩

private noncomputable def normalization :
    Sigma fun index : Fin baseData.obstructionPackingClosures.length =>
      Core.Strategy.SupportComplementNormalization.Registration
        Residual (fun residual => residual.object = 0)
        baseData.obstructionPackingClosures[index] := by
  refine ⟨packingIndex, ?_⟩
  simpa [baseData, packingIndex] using
    (Neutral.normalizationRegistration (Residual := Residual)
      (fun residual => residual.object = 0))

noncomputable def data : Core.StrategyData problem target :=
  { baseData with supportComplementNormalizations := [normalization] }

noncomputable def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := data

instance : NeZero definition.data.obstructionPackingClosures.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.supportComplementNormalizations.length :=
  ⟨by simp [definition, data]⟩

instance : NeZero definition.data.boundaryDemandAccountings.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.localSupplyLowerBounds.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.finiteBarrierEnumerations.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.targetRelativeRankDichotomies.length :=
  ⟨by simp [definition, data, baseData]⟩

instance : NeZero definition.data.finiteStateCapacities.length :=
  ⟨by simp [definition, data, baseData]⟩

noncomputable def program : Program definition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint definition.data .authoring)
      |>.obstructionPackingClosure
      |>.supportComplementNormalization
      |>.boundaryDemandAccounting
      |>.localSupplyLowerBound
      |>.finiteBarrierEnumeration
      |>.targetRelativeRankDichotomy
        (fullRank := fun branch => branch.finiteStateCapacity))

noncomputable def reduction : ReductionDeclaration :=
  reduceDag% definition program

theorem reduction_path : reduction.report.path =
    [.obstructionPackingClosure 0, .supportComplementNormalization 0,
      .boundaryDemandAccounting 0, .localSupplyLowerBound 0,
      .finiteBarrierEnumeration 0, .targetRelativeRankDichotomy 0,
      .finiteStateCapacity 0] :=
  rfl

theorem one_registration :
    definition.data.finiteStateCapacities.length = 1 := by
  simp [definition, data, baseData]

theorem toCore_reads_exact_state (residual : Residual)
    (rank : Nat) (barrier : Core.Strategy.FiniteBarrierEnumeration.Summary)
    (supply : Core.Strategy.LocalSupplyLowerBound.Summary) :
    (registration (AmbientItem := fun _ => Unit)).toCore.selectedScale
        residual rank barrier supply =
      (registration (AmbientItem := fun _ => Unit)).selectedScale
        residual residual.object rank barrier supply :=
  rfl

private def stage : Core.Strategy.InitStage problem :=
  Core.Residual.Ledger.initial input

private noncomputable def profile :
    Core.Strategy.FiniteStateCapacity.Profile
      (Core.Strategy.InitStage problem) Residual where
  AmbientItem := fun _ => Unit
  registration := registration.toCore
  complement := Query.ofFunction fun _ => Neutral.singleton
  independentRank := Query.ofFunction fun _ => 0
  finiteBarrierSummary :=
    Query.ofFunction fun _ =>
      Core.Strategy.FiniteBarrierEnumeration.Summary.ofRows [(0, 0)]
  localSupply := Query.ofFunction fun _ =>
    Neutral.supplySummary

theorem computes_survivor :
    (profile.execution.run stage).fst.terminal = .survivors := by
  rfl

theorem computes_capacity :
    (profile.execution.run stage).snd.terminal = .capacity := by
  rfl

end PDE

theorem graph_pde_use_same_strategy_path :
    Graph.reduction.report.path = PDE.reduction.report.path := by
  rw [Graph.reduction_path, PDE.reduction_path]

#print axioms Graph.toCore_reads_exact_graph
#print axioms Graph.reduction_path
#print axioms Graph.computes_survivor
#print axioms Graph.computes_capacity
#print axioms PDE.toCore_reads_exact_state
#print axioms PDE.reduction_path
#print axioms PDE.computes_survivor
#print axioms PDE.computes_capacity
#print axioms graph_pde_use_same_strategy_path

end Hypostructure.Fixtures.FiniteStateCapacityDomains
