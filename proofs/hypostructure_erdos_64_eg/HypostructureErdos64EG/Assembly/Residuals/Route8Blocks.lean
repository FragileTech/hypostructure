import HypostructureErdos64EG.Assembly.Basic

/-!
# Assembly: Residuals / Route8Blocks

The arm blocks of the route-`8` lane, shared by every residual returned from
`selectedRouteEightUnifiedResidual` (`Route8QuotientOutcome`,
`TypeBSublinearOutcome`, ...).  The paths into that return site form the
product `5 prefix × 4 entropy × 56 continuation`, with
`56 = 2·25 + 6` (Type A lane, Type B high-surplus lane; the B-chain has 6
fan/certificate arms).  The absorbed lane `[174]`--`[177]` is closed at
`[173]` against the private-carrier rate and contributes no path.
Each block is an explicit conjunction of EVERY key of its arm as a `Holds`
conjunct, with a `.ret` theorem that reads each key with one `get` from the
single ledger.  Keys common to all paths are not listed here: they belong to
the generic residual.  A block's keys are exactly the keys a path carries
because it took that arm (checked path by path against the elaborated
ledgers; no key is in two factors).
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u

-- Prefix: the five near-cubic routes into `selectedNetChargeContinuation`.
/-- Route-8 lane prefix arm: window package realized; cold route-8 rate below (`nearCubicRealized` → `nearCubicLargeBudgetColdRate`) (2 facts). -/
abbrev Route8LanePrefixBlock_realizedColdBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

/-- `Route8LanePrefixBlock_realizedColdBelow` from the one ledger: one `get` per key. -/
theorem Route8LanePrefixBlock_realizedColdBelow.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .windowPackageRealized) known] :
    Route8LanePrefixBlock_realizedColdBelow selected :=
  ⟨(history.get (K .coldRoute8Below)).down,
    (history.get (K .windowPackageRealized)).down⟩

/-- Route-8 lane prefix arm: window package realized; cold route-8 rate at or above, density cap (`nearCubicRealized` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`) (4 facts). -/
abbrev Route8LanePrefixBlock_realizedColdAtOrAbove (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

/-- `Route8LanePrefixBlock_realizedColdAtOrAbove` from the one ledger: one `get` per key. -/
theorem Route8LanePrefixBlock_realizedColdAtOrAbove.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .windowPackageRealized) known] :
    Route8LanePrefixBlock_realizedColdAtOrAbove selected :=
  ⟨(history.get (K .coldMassBounded)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .windowPackageRealized)).down⟩

/-- Route-8 lane prefix arm: window package unrealized; dense deficiency at or above; cold route-8 rate below (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetColdRate`) (3 facts). -/
abbrev Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

/-- `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow` from the one ledger: one `get` per key. -/
theorem Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldRoute8Below) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .windowPackageUnrealized) known] :
    Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow selected :=
  ⟨(history.get (K .coldRoute8Below)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- Route-8 lane prefix arm: window package unrealized; dense deficiency at or above; cold route-8 rate at or above, density cap (`nearCubicUnrealized` → `nearCubicDensePassAtOrAbove` → `nearCubicLargeBudgetDensityCap` → `nearCubicRouteEightEntry`) (5 facts). -/
abbrev Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

/-- `Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove` from the one ledger: one `get` per key. -/
theorem Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldMassBounded) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseDeficiencyAtOrAbove) known]
    [FactKeys.Has (K .densityCap) known]
    [FactKeys.Has (K .windowPackageUnrealized) known] :
    Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected :=
  ⟨(history.get (K .coldMassBounded)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .denseDeficiencyAtOrAbove)).down,
    (history.get (K .densityCap)).down,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- Route-8 lane prefix arm: window package unrealized; dense deficiency below (`nearCubicUnrealized` → `nearCubicLargeBudgetDenseRate`) (2 facts). -/
abbrev Route8LanePrefixBlock_unrealizedDenseBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

/-- `Route8LanePrefixBlock_unrealizedDenseBelow` from the one ledger: one `get` per key. -/
theorem Route8LanePrefixBlock_unrealizedDenseBelow.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .denseDeficiencyBelow) known]
    [FactKeys.Has (K .windowPackageUnrealized) known] :
    Route8LanePrefixBlock_unrealizedDenseBelow selected :=
  ⟨(history.get (K .denseDeficiencyBelow)).down,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- The prefix factor: exactly one of the five near-cubic routes. -/
abbrev Route8LanePrefix (selected : EGInput.{u}) : Prop :=
  Route8LanePrefixBlock_realizedColdBelow selected ∨
  Route8LanePrefixBlock_realizedColdAtOrAbove selected ∨
  Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdBelow selected ∨
  Route8LanePrefixBlock_unrealizedDenseAtOrAboveColdAtOrAbove selected ∨
  Route8LanePrefixBlock_unrealizedDenseBelow selected

-- Entropy: the four remainder-entropy / local-type arms.
/-- Entropy arm: remainder entropy high (3 facts). -/
abbrev EntropyArmBlock_high (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object

/-- `EntropyArmBlock_high` from the one ledger: one `get` per key. -/
theorem EntropyArmBlock_high.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .entropyCapBound) known]
    [FactKeys.Has (K .entropyPackageDemand) known]
    [FactKeys.Has (K .remainderEntropyHigh) known] :
    EntropyArmBlock_high selected :=
  ⟨(history.get (K .entropyCapBound)).down,
    (history.get (K .entropyPackageDemand)).down,
    (history.get (K .remainderEntropyHigh)).down⟩

/-- Entropy arm: remainder entropy low; local type coordinate non-repetitive (2 facts). -/
abbrev EntropyArmBlock_lowNonrepetitive (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object

/-- `EntropyArmBlock_lowNonrepetitive` from the one ledger: one `get` per key. -/
theorem EntropyArmBlock_lowNonrepetitive.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .localTypeCoordinateNonrepetitive) known]
    [FactKeys.Has (K .remainderEntropyLow) known] :
    EntropyArmBlock_lowNonrepetitive selected :=
  ⟨(history.get (K .localTypeCoordinateNonrepetitive)).down,
    (history.get (K .remainderEntropyLow)).down⟩

/-- Entropy arm: remainder entropy low; local type coordinate repetitive; dominant rooted type wedge-free (4 facts). -/
abbrev EntropyArmBlock_lowRepetitiveWedgeFree (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object

/-- `EntropyArmBlock_lowRepetitiveWedgeFree` from the one ledger: one `get` per key. -/
theorem EntropyArmBlock_lowRepetitiveWedgeFree.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedTypeWedgeFree) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .remainderEntropyLow) known] :
    EntropyArmBlock_lowRepetitiveWedgeFree selected :=
  ⟨(history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedTypeWedgeFree)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .remainderEntropyLow)).down⟩

/-- Entropy arm: remainder entropy low; local type coordinate repetitive; dominant rooted wedge type (5 facts). -/
abbrev EntropyArmBlock_lowRepetitiveWedge (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedWedgeType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .independentObstructionTranslates selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object

/-- `EntropyArmBlock_lowRepetitiveWedge` from the one ledger: one `get` per key. -/
theorem EntropyArmBlock_lowRepetitiveWedge.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .dominantRootedType) known]
    [FactKeys.Has (K .dominantRootedWedgeType) known]
    [FactKeys.Has (K .independentObstructionTranslates) known]
    [FactKeys.Has (K .localTypeCoordinateRepetitive) known]
    [FactKeys.Has (K .remainderEntropyLow) known] :
    EntropyArmBlock_lowRepetitiveWedge selected :=
  ⟨(history.get (K .dominantRootedType)).down,
    (history.get (K .dominantRootedWedgeType)).down,
    (history.get (K .independentObstructionTranslates)).down,
    (history.get (K .localTypeCoordinateRepetitive)).down,
    (history.get (K .remainderEntropyLow)).down⟩

/-- The entropy factor: exactly one of the four entropy arms. -/
abbrev EntropyArm (selected : EGInput.{u}) : Prop :=
  EntropyArmBlock_high selected ∨
  EntropyArmBlock_lowNonrepetitive selected ∨
  EntropyArmBlock_lowRepetitiveWedgeFree selected ∨
  EntropyArmBlock_lowRepetitiveWedge selected

-- B-chain: the Type B fan entry and the 6 fan/certificate arms.
/-- B-chain entry: the Type B route-8 entry and fan/certificate routing facts carried on every B-chain arm (7 facts). -/
abbrev BChainEntryBlock (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .compatiblePairFanClosure selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .compatiblePairTypeBRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanClosedPortTypeBRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBExclusionResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBRoute8Entry selected.object

/-- `BChainEntryBlock` from the one ledger: one `get` per key. -/
theorem BChainEntryBlock.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .compatiblePairFanClosure) known]
    [FactKeys.Has (K .compatiblePairTypeBRouting) known]
    [FactKeys.Has (K .fanCertificateCap) known]
    [FactKeys.Has (K .fanClosedPortTypeBRouting) known]
    [FactKeys.Has (K .typeBExclusionResidual) known]
    [FactKeys.Has (K .typeBFanEntry) known]
    [FactKeys.Has (K .typeBRoute8Entry) known] :
    BChainEntryBlock selected :=
  ⟨(history.get (K .compatiblePairFanClosure)).down,
    (history.get (K .compatiblePairTypeBRouting)).down,
    (history.get (K .fanCertificateCap)).down,
    (history.get (K .fanClosedPortTypeBRouting)).down,
    (history.get (K .typeBExclusionResidual)).down,
    (history.get (K .typeBFanEntry)).down,
    (history.get (K .typeBRoute8Entry)).down⟩

/-- B-chain fan arm: degree-four centres (2 facts). -/
abbrev BChainFanBlock_degreeFour (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanDegreeFourCentres selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanDegreeFourProfile selected.object

/-- `BChainFanBlock_degreeFour` from the one ledger: one `get` per key. -/
theorem BChainFanBlock_degreeFour.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeBFanDegreeFourCentres) known]
    [FactKeys.Has (K .typeBFanDegreeFourProfile) known] :
    BChainFanBlock_degreeFour selected :=
  ⟨(history.get (K .typeBFanDegreeFourCentres)).down,
    (history.get (K .typeBFanDegreeFourProfile)).down⟩

/-- B-chain fan arm: heavy centre (triangular fan core) (6 facts). -/
abbrev BChainFanBlock_heavyCentre (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularCrossShoulder selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularFanCore selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularFirstLanding selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .triangularPortTypeBRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanHeavyCentre selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBFanLocalDichotomy selected.object

/-- `BChainFanBlock_heavyCentre` from the one ledger: one `get` per key. -/
theorem BChainFanBlock_heavyCentre.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .triangularCrossShoulder) known]
    [FactKeys.Has (K .triangularFanCore) known]
    [FactKeys.Has (K .triangularFirstLanding) known]
    [FactKeys.Has (K .triangularPortTypeBRouting) known]
    [FactKeys.Has (K .typeBFanHeavyCentre) known]
    [FactKeys.Has (K .typeBFanLocalDichotomy) known] :
    BChainFanBlock_heavyCentre selected :=
  ⟨(history.get (K .triangularCrossShoulder)).down,
    (history.get (K .triangularFanCore)).down,
    (history.get (K .triangularFirstLanding)).down,
    (history.get (K .triangularPortTypeBRouting)).down,
    (history.get (K .typeBFanHeavyCentre)).down,
    (history.get (K .typeBFanLocalDichotomy)).down⟩

/-- B-chain certificate arm: residual (2 facts). -/
abbrev BChainCertificateBlock_residual (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateResidualMass selected.object

/-- `BChainCertificateBlock_residual` from the one ledger: one `get` per key. -/
theorem BChainCertificateBlock_residual.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateResidual) known]
    [FactKeys.Has (K .fanCertificateResidualMass) known] :
    BChainCertificateBlock_residual selected :=
  ⟨(history.get (K .fanCertificateResidual)).down,
    (history.get (K .fanCertificateResidualMass)).down⟩

/-- B-chain certificate arm: b2Choice (6 facts). -/
abbrev BChainCertificateBlock_b2Choice (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateMarked selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBB2Choice selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDirectCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDisjointLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBExcluded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHybridEntry selected.object

/-- `BChainCertificateBlock_b2Choice` from the one ledger: one `get` per key. -/
theorem BChainCertificateBlock_b2Choice.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    [FactKeys.Has (K .typeBB2Choice) known]
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    [FactKeys.Has (K .typeBDisjointLedger) known]
    [FactKeys.Has (K .typeBExcluded) known]
    [FactKeys.Has (K .typeBHybridEntry) known] :
    BChainCertificateBlock_b2Choice selected :=
  ⟨(history.get (K .fanCertificateMarked)).down,
    (history.get (K .typeBB2Choice)).down,
    (history.get (K .typeBDirectCycleFree)).down,
    (history.get (K .typeBDisjointLedger)).down,
    (history.get (K .typeBExcluded)).down,
    (history.get (K .typeBHybridEntry)).down⟩

/-- B-chain certificate arm: degreeFourClosed (5 facts). -/
abbrev BChainCertificateBlock_degreeFourClosed (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateMarked selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDegreeFourClosed selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDegreeFourLedger selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDirectCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHybridEntry selected.object

/-- `BChainCertificateBlock_degreeFourClosed` from the one ledger: one `get` per key. -/
theorem BChainCertificateBlock_degreeFourClosed.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    [FactKeys.Has (K .typeBDegreeFourClosed) known]
    [FactKeys.Has (K .typeBDegreeFourLedger) known]
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    [FactKeys.Has (K .typeBHybridEntry) known] :
    BChainCertificateBlock_degreeFourClosed selected :=
  ⟨(history.get (K .fanCertificateMarked)).down,
    (history.get (K .typeBDegreeFourClosed)).down,
    (history.get (K .typeBDegreeFourLedger)).down,
    (history.get (K .typeBDirectCycleFree)).down,
    (history.get (K .typeBHybridEntry)).down⟩

/-- B-chain certificate arm: degreeFourOverlap (6 facts). -/
abbrev BChainCertificateBlock_degreeFourOverlap (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateMarked selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDegreeFourOverlap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDirectCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBGlobalLocalBridge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHybridEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBOverlapObstructionMass selected.object

/-- `BChainCertificateBlock_degreeFourOverlap` from the one ledger: one `get` per key. -/
theorem BChainCertificateBlock_degreeFourOverlap.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    [FactKeys.Has (K .typeBDegreeFourOverlap) known]
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    [FactKeys.Has (K .typeBGlobalLocalBridge) known]
    [FactKeys.Has (K .typeBHybridEntry) known]
    [FactKeys.Has (K .typeBOverlapObstructionMass) known] :
    BChainCertificateBlock_degreeFourOverlap selected :=
  ⟨(history.get (K .fanCertificateMarked)).down,
    (history.get (K .typeBDegreeFourOverlap)).down,
    (history.get (K .typeBDirectCycleFree)).down,
    (history.get (K .typeBGlobalLocalBridge)).down,
    (history.get (K .typeBHybridEntry)).down,
    (history.get (K .typeBOverlapObstructionMass)).down⟩

/-- B-chain certificate arm: overlapObstruction (6 facts). -/
abbrev BChainCertificateBlock_overlapObstruction (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .fanCertificateMarked selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDirectCycleFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBGlobalLocalBridge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHybridEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBOverlapObstruction selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBOverlapObstructionMass selected.object

/-- `BChainCertificateBlock_overlapObstruction` from the one ledger: one `get` per key. -/
theorem BChainCertificateBlock_overlapObstruction.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .fanCertificateMarked) known]
    [FactKeys.Has (K .typeBDirectCycleFree) known]
    [FactKeys.Has (K .typeBGlobalLocalBridge) known]
    [FactKeys.Has (K .typeBHybridEntry) known]
    [FactKeys.Has (K .typeBOverlapObstruction) known]
    [FactKeys.Has (K .typeBOverlapObstructionMass) known] :
    BChainCertificateBlock_overlapObstruction selected :=
  ⟨(history.get (K .fanCertificateMarked)).down,
    (history.get (K .typeBDirectCycleFree)).down,
    (history.get (K .typeBGlobalLocalBridge)).down,
    (history.get (K .typeBHybridEntry)).down,
    (history.get (K .typeBOverlapObstruction)).down,
    (history.get (K .typeBOverlapObstructionMass)).down⟩

/-- The certificate arms reached after a heavy-centre fan (`[72]`: B2 holds
or the minimal overlap obstruction `[73]`; or the certificate residual). -/
abbrev BChainHeavyCertificate (selected : EGInput.{u}) : Prop :=
  BChainCertificateBlock_residual selected ∨
  BChainCertificateBlock_b2Choice selected ∨
  BChainCertificateBlock_overlapObstruction selected

/-- The certificate arms reached after a degree-four fan (`[81]`: `[82]` or
`[83]`; or the certificate residual). -/
abbrev BChainDegreeFourCertificate (selected : EGInput.{u}) : Prop :=
  BChainCertificateBlock_residual selected ∨
  BChainCertificateBlock_degreeFourClosed selected ∨
  BChainCertificateBlock_degreeFourOverlap selected

/-- The fan and certificate arms of the B-chain: each fan arm with the three
certificate arms its walk reaches (6 arms; the B2 test `[72]` runs only after a
heavy-centre fan and the `[81]` test only after a degree-four fan). -/
abbrev BChainFanCertificate (selected : EGInput.{u}) : Prop :=
  (BChainFanBlock_heavyCentre selected ∧ BChainHeavyCertificate selected) ∨
  (BChainFanBlock_degreeFour selected ∧ BChainDegreeFourCertificate selected)

/-- The B-chain: the entry block and one fan/certificate arm (6 arms). -/
abbrev BChain (selected : EGInput.{u}) : Prop :=
  BChainEntryBlock selected ∧ BChainFanCertificate selected

-- Net-charge continuation lanes.
/-- Net-charge lane: Type A low surplus (`selectedTypeALowSurplusContinuation`) (11 facts). -/
abbrev NetChargeLaneBlock_typeALowSurplus (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .negativeSupport selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeABoundedSupport selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourFiniteDescent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeALowSurplus selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPortReturn selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAReceiverRouting selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedExitEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedReceiver selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASupport selected.object

/-- `NetChargeLaneBlock_typeALowSurplus` from the one ledger: one `get` per key. -/
theorem NetChargeLaneBlock_typeALowSurplus.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .typeABoundedSupport) known]
    [FactKeys.Has (K .typeAExitFourFiniteDescent) known]
    [FactKeys.Has (K .typeALowSurplus) known]
    [FactKeys.Has (K .typeAPortReturn) known]
    [FactKeys.Has (K .typeAReceiverRouting) known]
    [FactKeys.Has (K .typeASaturatedExitEntry) known]
    [FactKeys.Has (K .typeASaturatedReceiver) known]
    [FactKeys.Has (K .typeASupport) known] :
    NetChargeLaneBlock_typeALowSurplus selected :=
  ⟨(history.get (K .negativeSupport)).down,
    (history.get (K .netChargeCap)).down,
    (history.get (K .netChargeNegative)).down,
    (history.get (K .typeABoundedSupport)).down,
    (history.get (K .typeAExitFourFiniteDescent)).down,
    (history.get (K .typeALowSurplus)).down,
    (history.get (K .typeAPortReturn)).down,
    (history.get (K .typeAReceiverRouting)).down,
    (history.get (K .typeASaturatedExitEntry)).down,
    (history.get (K .typeASaturatedReceiver)).down,
    (history.get (K .typeASupport)).down⟩

/-- Net-charge lane: Type B high surplus (`selectedTypeBHighSurplusContinuation`) (5 facts). -/
abbrev NetChargeLaneBlock_typeBHighSurplus (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .negativeSupport selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netChargeNegative selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAssignedSupport selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBHighSurplus selected.object

/-- `NetChargeLaneBlock_typeBHighSurplus` from the one ledger: one `get` per key. -/
theorem NetChargeLaneBlock_typeBHighSurplus.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .negativeSupport) known]
    [FactKeys.Has (K .netChargeCap) known]
    [FactKeys.Has (K .netChargeNegative) known]
    [FactKeys.Has (K .typeBAssignedSupport) known]
    [FactKeys.Has (K .typeBHighSurplus) known] :
    NetChargeLaneBlock_typeBHighSurplus selected :=
  ⟨(history.get (K .negativeSupport)).down,
    (history.get (K .netChargeCap)).down,
    (history.get (K .netChargeNegative)).down,
    (history.get (K .typeBAssignedSupport)).down,
    (history.get (K .typeBHighSurplus)).down⟩

/-- Type A entry arm: visible entry (`selectedTypeAVisibleExitChain`) (4 facts). -/
abbrev TypeAEntryBlock_visible (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitOneFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitThreeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitTwoFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAVisibleEntry selected.object

/-- `TypeAEntryBlock_visible` from the one ledger: one `get` per key. -/
theorem TypeAEntryBlock_visible.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitOneFree) known]
    [FactKeys.Has (K .typeAExitThreeFree) known]
    [FactKeys.Has (K .typeAExitTwoFree) known]
    [FactKeys.Has (K .typeAVisibleEntry) known] :
    TypeAEntryBlock_visible selected :=
  ⟨(history.get (K .typeAExitOneFree)).down,
    (history.get (K .typeAExitThreeFree)).down,
    (history.get (K .typeAExitTwoFree)).down,
    (history.get (K .typeAVisibleEntry)).down⟩

/-- Type A entry arm: no visible entry (2 facts). -/
abbrev TypeAEntryBlock_noVisible (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeANoVisibleEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAVisibleFirstExcess selected.object

/-- `TypeAEntryBlock_noVisible` from the one ledger: one `get` per key. -/
theorem TypeAEntryBlock_noVisible.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeANoVisibleEntry) known]
    [FactKeys.Has (K .typeAVisibleFirstExcess) known] :
    TypeAEntryBlock_noVisible selected :=
  ⟨(history.get (K .typeANoVisibleEntry)).down,
    (history.get (K .typeAVisibleFirstExcess)).down⟩

/-- The Type A entry factor. -/
abbrev TypeAEntry (selected : EGInput.{u}) : Prop :=
  TypeAEntryBlock_visible selected ∨
  TypeAEntryBlock_noVisible selected

/-- Type A continuation arm: decorated handoff (`selectedTypeADecoratedHandoff`) (6 facts). -/
abbrev TypeAArmBlock_decorated (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFiveFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitSevenEnvelope selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitSevenHandoff selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitSixFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedHandoffExitFourFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBDecoratedAssignedSupport selected.object

/-- `TypeAArmBlock_decorated` from the one ledger: one `get` per key. -/
theorem TypeAArmBlock_decorated.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFiveFree) known]
    [FactKeys.Has (K .typeAExitSevenEnvelope) known]
    [FactKeys.Has (K .typeAExitSevenHandoff) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known]
    [FactKeys.Has (K .typeBDecoratedAssignedSupport) known] :
    TypeAArmBlock_decorated selected :=
  ⟨(history.get (K .typeAExitFiveFree)).down,
    (history.get (K .typeAExitSevenEnvelope)).down,
    (history.get (K .typeAExitSevenHandoff)).down,
    (history.get (K .typeAExitSixFree)).down,
    (history.get (K .typeASaturatedHandoffExitFourFree)).down,
    (history.get (K .typeBDecoratedAssignedSupport)).down⟩

/-- Type A continuation arm: route-8 residual (`selectedRouteEightResidual`) (5 facts). -/
abbrev TypeAArmBlock_route8Residual (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8ResidualProfile selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFiveFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitSevenFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitSixFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedHandoffExitFourFree selected.object

/-- `TypeAArmBlock_route8Residual` from the one ledger: one `get` per key. -/
theorem TypeAArmBlock_route8Residual.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8ResidualProfile) known]
    [FactKeys.Has (K .typeAExitFiveFree) known]
    [FactKeys.Has (K .typeAExitSevenFree) known]
    [FactKeys.Has (K .typeAExitSixFree) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFourFree) known] :
    TypeAArmBlock_route8Residual selected :=
  ⟨(history.get (K .route8ResidualProfile)).down,
    (history.get (K .typeAExitFiveFree)).down,
    (history.get (K .typeAExitSevenFree)).down,
    (history.get (K .typeAExitSixFree)).down,
    (history.get (K .typeASaturatedHandoffExitFourFree)).down⟩

/-- Type A continuation arm: exit-four discharged retest (`selectedTypeAExitFourDischargedRetest`) (4 facts). -/
abbrev TypeAArmBlock_dischargedRetest (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourPeeled selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourReceiverDischarged selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledUnsaturatedDischarge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedHandoffExitFour selected.object

/-- `TypeAArmBlock_dischargedRetest` from the one ledger: one `get` per key. -/
theorem TypeAArmBlock_dischargedRetest.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    [FactKeys.Has (K .typeAExitFourReceiverDischarged) known]
    [FactKeys.Has (K .typeAPeeledUnsaturatedDischarge) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFour) known] :
    TypeAArmBlock_dischargedRetest selected :=
  ⟨(history.get (K .typeAExitFourPeeled)).down,
    (history.get (K .typeAExitFourReceiverDischarged)).down,
    (history.get (K .typeAPeeledUnsaturatedDischarge)).down,
    (history.get (K .typeASaturatedHandoffExitFour)).down⟩

/-- Type A exit-four arm: absent (1 fact). -/
abbrev TypeAExitFourBlock_absent (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourAbsent selected.object

/-- `TypeAExitFourBlock_absent` from the one ledger: one `get` per key. -/
theorem TypeAExitFourBlock_absent.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourAbsent) known] :
    TypeAExitFourBlock_absent selected :=
  (history.get (K .typeAExitFourAbsent)).down

/-- Type A exit-four arm: peeledVisible (7 facts). -/
abbrev TypeAExitFourBlock_peeledVisible (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourPeeled selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledExitOneFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledExitThreeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledExitTwoFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledSaturatedReceiver selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledVisibleEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedHandoffExitFour selected.object

/-- `TypeAExitFourBlock_peeledVisible` from the one ledger: one `get` per key. -/
theorem TypeAExitFourBlock_peeledVisible.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    [FactKeys.Has (K .typeAPeeledExitOneFree) known]
    [FactKeys.Has (K .typeAPeeledExitThreeFree) known]
    [FactKeys.Has (K .typeAPeeledExitTwoFree) known]
    [FactKeys.Has (K .typeAPeeledSaturatedReceiver) known]
    [FactKeys.Has (K .typeAPeeledVisibleEntry) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFour) known] :
    TypeAExitFourBlock_peeledVisible selected :=
  ⟨(history.get (K .typeAExitFourPeeled)).down,
    (history.get (K .typeAPeeledExitOneFree)).down,
    (history.get (K .typeAPeeledExitThreeFree)).down,
    (history.get (K .typeAPeeledExitTwoFree)).down,
    (history.get (K .typeAPeeledSaturatedReceiver)).down,
    (history.get (K .typeAPeeledVisibleEntry)).down,
    (history.get (K .typeASaturatedHandoffExitFour)).down⟩

/-- Type A exit-four arm: peeledNoVisible (5 facts). -/
abbrev TypeAExitFourBlock_peeledNoVisible (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAExitFourPeeled selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledNoVisibleEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledSaturatedReceiver selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeAPeeledSilentExcess selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeASaturatedHandoffExitFour selected.object

/-- `TypeAExitFourBlock_peeledNoVisible` from the one ledger: one `get` per key. -/
theorem TypeAExitFourBlock_peeledNoVisible.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .typeAExitFourPeeled) known]
    [FactKeys.Has (K .typeAPeeledNoVisibleEntry) known]
    [FactKeys.Has (K .typeAPeeledSaturatedReceiver) known]
    [FactKeys.Has (K .typeAPeeledSilentExcess) known]
    [FactKeys.Has (K .typeASaturatedHandoffExitFour) known] :
    TypeAExitFourBlock_peeledNoVisible selected :=
  ⟨(history.get (K .typeAExitFourPeeled)).down,
    (history.get (K .typeAPeeledNoVisibleEntry)).down,
    (history.get (K .typeAPeeledSaturatedReceiver)).down,
    (history.get (K .typeAPeeledSilentExcess)).down,
    (history.get (K .typeASaturatedHandoffExitFour)).down⟩

/-- The Type A exit-four factor. -/
abbrev TypeAExitFour (selected : EGInput.{u}) : Prop :=
  TypeAExitFourBlock_absent selected ∨
  TypeAExitFourBlock_peeledVisible selected ∨
  TypeAExitFourBlock_peeledNoVisible selected

/-- Route-8 large-budget deficit arm: the deficit holds (true residual) (5 facts). -/
abbrev Route8DeficitBlock_holds (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8CarrierCutParity selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8LargeBudgetDeficit selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8NoSmallCoreEntry selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8TrueResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8TwoCarrierEntry selected.object

/-- `Route8DeficitBlock_holds` from the one ledger: one `get` per key. -/
theorem Route8DeficitBlock_holds.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8CarrierCutParity) known]
    [FactKeys.Has (K .route8LargeBudgetDeficit) known]
    [FactKeys.Has (K .route8NoSmallCoreEntry) known]
    [FactKeys.Has (K .route8TrueResidual) known]
    [FactKeys.Has (K .route8TwoCarrierEntry) known] :
    Route8DeficitBlock_holds selected :=
  ⟨(history.get (K .route8CarrierCutParity)).down,
    (history.get (K .route8LargeBudgetDeficit)).down,
    (history.get (K .route8NoSmallCoreEntry)).down,
    (history.get (K .route8TrueResidual)).down,
    (history.get (K .route8TwoCarrierEntry)).down⟩

/-- Route-8 large-budget deficit arm: the deficit fails (1 fact). -/
abbrev Route8DeficitBlock_fails (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8LargeBudgetDeficitFails selected.object

/-- `Route8DeficitBlock_fails` from the one ledger: one `get` per key. -/
theorem Route8DeficitBlock_fails.ret
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .route8LargeBudgetDeficitFails) known] :
    Route8DeficitBlock_fails selected :=
  (history.get (K .route8LargeBudgetDeficitFails)).down

/-- The route-8 large-budget deficit factor. -/
abbrev Route8Deficit (selected : EGInput.{u}) : Prop :=
  Route8DeficitBlock_holds selected ∨
  Route8DeficitBlock_fails selected

/-- The 25 Type A continuation arms: decorated (3 exit-four blocks × B-chain),
route-8 residual (3 exit-four blocks × 2 deficit blocks), discharged retest. -/
abbrev TypeAArm (selected : EGInput.{u}) : Prop :=
  (TypeAArmBlock_decorated selected ∧ TypeAExitFour selected ∧ BChain selected) ∨
  (TypeAArmBlock_route8Residual selected ∧ TypeAExitFour selected ∧
    Route8Deficit selected) ∨
  TypeAArmBlock_dischargedRetest selected

/-- The Type A lane: 2 entry blocks × 37 continuation arms. -/
abbrev TypeALane (selected : EGInput.{u}) : Prop :=
  NetChargeLaneBlock_typeALowSurplus selected ∧ TypeAEntry selected ∧
    TypeAArm selected

/-- The Type B high-surplus lane: the B-chain. -/
abbrev TypeBHighSurplusLane (selected : EGInput.{u}) : Prop :=
  NetChargeLaneBlock_typeBHighSurplus selected ∧ BChain selected

/-- The continuation factor (56 arms = 2·25 + 6).  The absorbed lane
`[174]`--`[177]` is not a factor: the `[173]` no-arm is closed at the node
against `K .route8Rate` (`instIncompatibleExactCollisionFailsRoute8Rate`). -/
abbrev NetChargeContinuation (selected : EGInput.{u}) : Prop :=
  TypeALane selected ∨ TypeBHighSurplusLane selected

end HypostructureErdos64EG
