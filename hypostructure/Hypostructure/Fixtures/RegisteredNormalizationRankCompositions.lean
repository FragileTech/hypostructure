import Hypostructure.Core.Strategy.Dag
import Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions

/-!
# Registered normalization/rank composition fixtures

The four registered CT compositions

```text
supportComplementNormalization : CT9 → CT14 → CT1 → CT6
boundaryDemandAccounting       : CT4 → CT14
localSupplyLowerBound          : CT14
targetRelativeRankDichotomy    : CT10 → CT15 → CT16
```

are instantiated over one closed `StrategyData` family and compiled twice.
The second blueprint interleaves an unrelated registered Strategy between
them and reorders the independent prefix, so the compiler's capability flow —
not a hardcoded Strategy order in the DAG — is what sequences these vertices.
-/

namespace Hypostructure.Fixtures.RegisteredNormalizationRankCompositions

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy.Dag
open Hypostructure.Fixtures.RegisteredCanonicalAccountingCompositions
  (pairRegistration)

private def singleton : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.singleton ()

private def completeUnit : Core.Finite.CompleteEnumeration Unit :=
  Core.Finite.CompleteEnumeration.ofFinEnum inferInstance

/-! ## Four inert registrations -/

noncomputable def normalizationRegistration
    {Residual : Type} (Target : Residual → Prop) :
    Core.Strategy.SupportComplementNormalization.Registration
      Residual Target where
  AmbientItem := fun _ => Unit
  ambientSupport := fun _ => singleton
  Occurrence := fun _ => Unit
  occurrences := fun _ => singleton
  cover := fun _ _ => [()]
  cover_ne := fun _ _ => by simp
  LocalPiece := fun _ => Unit
  localPieces := fun _ => singleton
  FailureData := fun _ _ => Empty
  Failure := fun _ _ => False
  failureData := fun _ _ failure => failure.elim
  failureDecidable := fun _ _ => isFalse id
  contribution := fun _ _ => 0
  failureForcesTarget := fun _ _ failure => failure.elim

noncomputable def accountingRegistration {Residual : Type} :
    Core.Strategy.BoundaryDemandAccounting.Registration Residual where
  Demand := fun _ => Unit
  Payer := fun _ => Unit
  demands := fun _ => singleton
  payers := fun _ => singleton
  Eligible := fun _ _ _ => True
  eligibleDecidable := fun _ _ _ => isTrue trivial
  demandWeight := fun _ _ => 0
  payerCapacity := fun _ _ => 0
  Member := fun _ => Unit
  Label := fun _ => Unit
  members := fun _ => singleton
  memberLowerMass := fun _ _ => 0
  memberCapacityRate := fun _ _ => 0
  memberLabel := fun _ _ => ()
  labelDecidableEq := fun _ => inferInstance

noncomputable def localSupplyRegistration {Residual : Type} :
    Core.Strategy.LocalSupplyLowerBound.Registration Residual
      (fun _ => Unit) where
  Member := fun _ => Unit
  Label := fun _ => Unit
  members := fun _ _ => singleton
  requiredMass := fun _ _ _ => 0
  observedSupply := fun _ _ _ => 0
  defectCorrection := fun _ _ _ => 0
  surplus := fun _ _ _ => 0
  label := fun _ _ _ => ()
  labelDecidableEq := fun _ => inferInstance
  pointwise := fun _ _ _ => Nat.zero_le _

noncomputable def rankRegistration {Residual : Type} :
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

/-! ## One closed registered problem -/

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
    supportComplementNormalizations :=
      [normalizationRegistration
        (Residual := Core.Strategy.ProblemInput problem)
        (fun input => input.object = Nat.zero)]
    boundaryDemandAccountings := [⟨0, accountingRegistration⟩]
    localSupplyLowerBounds := [⟨0, localSupplyRegistration⟩]
    targetRelativeRankDichotomies :=
      [⟨(fun _ => Unit), ⟨0, rankRegistration⟩⟩]
  }

instance : NeZero definition.data.canonicalPairResponseAccountings.length :=
  ⟨by simp [definition]⟩

instance : NeZero definition.data.supportComplementNormalizations.length :=
  ⟨by simp [definition]⟩

instance : NeZero definition.data.boundaryDemandAccountings.length :=
  ⟨by simp [definition]⟩

instance : NeZero definition.data.localSupplyLowerBounds.length :=
  ⟨by simp [definition]⟩

instance : NeZero definition.data.targetRelativeRankDichotomies.length :=
  ⟨by simp [definition]⟩

/-! ## Two admissible concatenations of the same registrations -/

/-- Direct concatenation of the four registered compositions. -/
noncomputable def forwardProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.canonicalPairResponseAccounting
      |>.supportComplementNormalization
      |>.boundaryDemandAccounting
      |>.localSupplyLowerBound
      |>.targetRelativeRankDichotomy)

/-- The same registrations with the independent Strategy moved between two
capability-linked vertices.  Nothing in the DAG assumes adjacency: the only
constraint the compiler enforces is that each consumer is reached after some
producer of the ledger value it declares. -/
noncomputable def interleavedProgram : Program definition.data :=
  Program.ofBlueprint (
    Blueprint.root
      |>.supportComplementNormalization
      |>.boundaryDemandAccounting
      |>.canonicalPairResponseAccounting
      |>.localSupplyLowerBound
      |>.targetRelativeRankDichotomy)

noncomputable def sealedForwardReduction : ReductionDeclaration :=
  reduceDag% definition forwardProgram

noncomputable def sealedInterleavedReduction : ReductionDeclaration :=
  reduceDag% definition interleavedProgram

end Hypostructure.Fixtures.RegisteredNormalizationRankCompositions
