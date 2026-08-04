import Hypostructure.Core.Strategy.Dag

/-!
# Finite-state capacity: missing-capability rejection (`FSC-043`)

A DAG invoking `finiteStateCapacity` without a preceding producer of
`independentRank`, `finiteBarrierSummary`, or `localSupplyLedger` must be
rejected by the sealed `ofDag%` frontend before the private compiler ever
runs.  This is the same generic `StrategyKey.requirementsMet` gate every
other capability-requiring key already exercises; no new rejection
mechanism is built here.
-/

namespace Hypostructure.Fixtures.FiniteStateCapacityRejection

open Hypostructure
open Hypostructure.Core.Strategy.Dag

private def singleton : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

private def natSingleton : Core.Finite.Enumeration Nat :=
  Core.Finite.Enumeration.singleton 0

private noncomputable def unitJointProfile :
    Core.DependentOwnerGlueCapacity.BaseProfile where
  Base := Unit
  Owner := Unit
  Local := fun _ => Unit
  Global := Unit × (Unit → Unit)
  Code := Unit × (Unit → Unit)
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

/-- One closed, all-`Unit` registration.  It supplies no query and no
capability; it exists only to populate `StrategyData.finiteStateCapacities`
so the blueprint below can name the key at all. -/
noncomputable def registration {Residual : Type}
    {AmbientItem : Residual → Type} :
    Core.Strategy.FiniteStateCapacity.Registration Residual AmbientItem where
  Target := fun _ => Unit
  Offset := fun _ => Unit
  Position := fun _ _ => Unit
  Value := fun _ => Unit
  targets := fun _ _ _ _ => singleton
  offsets := fun _ _ _ _ => singleton
  scales := fun _ _ _ _ => natSingleton
  selectedScale := fun _ _ _ _ => 0
  selectedScale_mem := fun _ _ _ _ => by simp [natSingleton,
    Core.Finite.Enumeration.singleton, Core.Finite.Enumeration.ofNodupList]
  positions := fun _ _ _ _ _ => singleton
  finiteScaleLimit := fun _ _ _ _ => 0
  targetValue := fun _ _ _ _ _ => ()
  blockValue := fun _ _ _ _ _ _ _ => ()
  orbitValue := fun _ _ _ _ _ _ => ()
  Compatible := fun _ _ _ => True
  compatibleDecidable := fun _ _ _ => isTrue trivial
  valueDecidableEq := fun _ => inferInstance
  Label := fun _ => Unit
  memberLowerMass := fun _ _ _ _ _ => 0
  memberCapacity := fun _ _ _ _ _ => some 0
  memberLabel := fun _ _ _ _ _ => some ()
  labelDecidableEq := fun _ => inferInstance
  RealizedState := fun _ _ _ _ _ => Unit
  realizedStateFinite := fun _ _ _ _ _ => inferInstance
  realizedStateNonempty := fun _ _ _ _ _ => inferInstance
  ambientOrder := fun _ _ _ _ _ => 1
  remainderCard := fun _ _ _ _ _ => 0
  statePowerExponent := fun _ _ _ _ => 1
  statePowerExponent_pos := by intro; norm_num
  forcedBase := fun _ _ _ _ => 1
  flatBase := fun _ _ _ _ => 1
  flatBase_pos := by
    intro
    norm_num
  jointProfile := fun _ _ _ _ _ => unitJointProfile
  jointBaseCard := by
    intro
    simp [unitJointProfile]
  jointExponent := fun _ _ _ _ => 1
  jointWeight := fun _ _ _ _ _ _ => 0
  jointLocalLower := by
    intro _ _ _ _ _ _
    simp [unitJointProfile]
  jointPaidExponent := fun _ _ _ _ => 0
  jointPaidExponent_exact := by
    intro
    simp [unitJointProfile,
      Core.DependentOwnerGlueCapacity.BaseProfile.weightSum]
  jointDesiredExponent := fun _ _ _ _ => 0
  jointErrorExponent := fun _ _ _ _ => 0
  jointCapacity := fun _ _ _ _ => 1
  jointCapacity_pos := by
    intro
    norm_num
  jointCodeCapacity := by
    intro
    simp [unitJointProfile]
  jointDesiredExponent_exact := by intro; simp

private def problem : Core.Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private def target : Core.Target problem where
  Predicate := fun object => object = Nat.zero
  Statement := ∀ object, object = Nat.zero
  statement_to_target := fun statement object _ => statement object
  target_to_statement := fun proof object => proof object trivial

private abbrev Residual := Core.Strategy.ProblemInput problem

private abbrev Avoids : Residual → Prop :=
  fun input => target.Predicate input.object

/-! The finite-state-capacity entry names its local-supply predecessor by
index, so the fixture data has to carry that predecessor chain even though no
vertex ever executes it.  All four registrations below are the same closed
all-`Unit` presentation as `registration` itself: they exist only so the
indices type-check, and none of them publishes a capability. -/

private noncomputable def packing :
    Core.Strategy.ObstructionPackingClosure.Semantics Residual Avoids where
  Occurrence := fun _ => Unit
  occurrences := fun _ => singleton
  conflict := fun _ _ _ => True
  conflictDecidable := fun _ _ _ => isTrue trivial
  conflictSymmetric := fun _ _ _ _ => trivial
  freeForcesTarget := by
    intro residual empty
    change [()] = [] at empty
    simp at empty

private noncomputable def normalization :
    Core.Strategy.SupportComplementNormalization.Registration
      Residual Avoids packing where
  AmbientItem := fun _ => Unit
  ambientSupport := fun _ => singleton
  cover := fun _ _ => [()]
  coverNodup := by simp
  coverSupported := by simp
  coverCard := fun _ => 1
  cover_card := by simp
  conflict_iff_shared_item := by
    intro residual left right
    simp [packing]
  cover_ne := by simp
  LocalPiece := fun _ _ => Unit
  localPieces := fun _ _ => singleton
  FailureData := fun _ _ _ => Empty
  Failure := fun _ _ _ => False
  failureData := fun _ _ _ failure => failure.elim
  failureDecidable := fun _ _ _ => isFalse id
  contribution := fun _ complement _ => complement.card
  failureForcesTarget := fun _ _ _ failure => failure.elim

private noncomputable def boundary :
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

private noncomputable def supply :
    Core.Strategy.LocalSupplyLowerBound.Registration
      Residual (fun _ => Unit) where
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

noncomputable def definition : Core.ProblemDefinition where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input => by
      change Decidable (input.object = Nat.zero)
      exact Nat.decEq input.object Nat.zero
    obstructionPackingClosures := [packing]
    supportComplementNormalizations := [⟨0, normalization⟩]
    boundaryDemandAccountings := [⟨0, boundary⟩]
    localSupplyLowerBounds := [⟨0, supply⟩]
    finiteStateCapacities := [⟨0, registration⟩]
  }

private local instance : NeZero definition.data.finiteStateCapacities.length :=
  ⟨by simp [definition]⟩

/-- No preceding vertex publishes any of the three capabilities
`finiteStateCapacity` requires.  Both branches close with `targetOrAvoid`,
the same closing step verified in isolation (against a plain `dichotomy` and
against the capability-free sibling key `finiteScheduleCapacity`) to expand
cleanly on its own — so the failure below is caused by the missing
capability, not by this closing shape. -/
noncomputable def program : Program definition.data :=
  Program.ofBlueprint (Blueprint.root.finiteStateCapacity
    (nonCapacity := fun branch => branch.targetOrAvoid)
    (capacity := fun branch => branch.targetOrAvoid))

/- `resolveBinary`'s hypothesis `strategy.key.requirementsMet data
strategy.resolved available = true` cannot be discharged when `available`
carries none of `independentRank`/`finiteBarrierSummary`/`localSupplyLedger`,
so the vertex cannot be constructed during `Program.expand` at all.  The
observable rejection is therefore the frontend's generic expansion failure
below, rather than the later, more specific "queried a ledger capability"
message a scalar (`Blueprint.step`) vertex would produce instead. -/
/--
error: ofDag% rejected this declaration: invalid autoroute program: Core could not derive a typed acyclic bridge from a targetless branch terminal to a compatible continuation.
-/
#guard_msgs (error) in
noncomputable def rejected : ProblemDeclaration :=
  ofDag% definition program

end Hypostructure.Fixtures.FiniteStateCapacityRejection
