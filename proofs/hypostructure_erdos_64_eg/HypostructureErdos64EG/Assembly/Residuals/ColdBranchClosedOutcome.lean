import HypostructureErdos64EG.Assembly.Residuals.ArmBlocks

/-!
# Assembly: the `ColdBranchClosedOutcome` residual, split by fact set

`ColdBranchClosedOutcome` ([187], local cold-terminal exclusion) is reached
along 104 root paths, each with its own ledger fact set.  They split as:

* 100 paths through `selectedAbsorbedGermResidual`, which form an exact
  product 4 × 5 × 5 of arm blocks: the entropy-side arm (4 blocks), the
  window/test arm (5 blocks) and the absorbed-germ exit (5 blocks), over the
  generic 57 facts and 5 further facts common to all 100
  (`ColdBranchClosedAbsorbedCommon`).  Their residual is
  `ColdBranchClosedOutcome_product`.
* 4 paths on the [153] linear cold-mass arm, each its own subtype.

Every block lists every key of its arm as an explicit `Holds` conjunct, and
every return theorem reads each fact with one `ExactLedger.get`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Core.Residual
open Hypostructure.Core.Strategy
open Hypostructure.Graph.Strategy.Spine

universe u
/-- The 5 facts common to every absorbed-germ path of
`ColdBranchClosedOutcome` beyond the generic 57. -/
abbrev ColdBranchClosedAbsorbedCommon (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedConfigurationResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .exactCollisionFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .largeBudgetResidual selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .netDeficiencyCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8Rate selected.object

/-- One `get` per fact of `ColdBranchClosedAbsorbedCommon`. -/
theorem coldBranchClosedAbsorbedCommonReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    : ColdBranchClosedAbsorbedCommon selected :=
  ⟨(history.get (K .absorbedConfigurationResidual)).down,
    (history.get (K .exactCollisionFails)).down,
    (history.get (K .largeBudgetResidual)).down,
    (history.get (K .netDeficiencyCap)).down,
    (history.get (K .route8Rate)).down⟩
/-- Block `E1` (3 facts): [50] remainder entropy high, with the [53] entropy cap. -/
abbrev ColdBranchClosedEntropyHighCap (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyCapBound selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .entropyPackageDemand selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyHigh selected.object

/-- Block `E2` (2 facts): [50] remainder entropy low, local-type coordinate non-repetitive. -/
abbrev ColdBranchClosedEntropyLowNonrepetitive (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateNonrepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object

/-- Block `E3` (4 facts): [50] remainder entropy low, local-type coordinate repetitive, dominant rooted type wedge-free. -/
abbrev ColdBranchClosedEntropyLowWedgeFree (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedType selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .dominantRootedTypeWedgeFree selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .localTypeCoordinateRepetitive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .remainderEntropyLow selected.object

/-- Block `E4` (5 facts): [50] remainder entropy low, local-type coordinate repetitive, dominant rooted wedge type. -/
abbrev ColdBranchClosedEntropyLowWedgeType (selected : EGInput.{u}) : Prop :=
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

/-- Block `W1` (4 facts): [158] window package realized, [146] theta at or above 1/78 (with [153] bounded cold mass and its density cap). -/
abbrev ColdBranchClosedWindowRealizedThetaAtOrAbove (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassBounded selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .densityCap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

/-- Block `W2` (2 facts): [158] window package realized, [146] theta below 1/78. -/
abbrev ColdBranchClosedWindowRealizedThetaBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

/-- Block `W3` (5 facts): [158] window package unrealized, [160] tau at or above 1/4, [146] theta at or above 1/78 (with [153] bounded cold mass and its density cap). -/
abbrev ColdBranchClosedWindowUnrealizedTauAtOrAboveThetaAtOrAbove (selected : EGInput.{u}) : Prop :=
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

/-- Block `W4` (3 facts): [158] window package unrealized, [160] tau at or above 1/4, [146] theta below 1/78. -/
abbrev ColdBranchClosedWindowUnrealizedTauAtOrAboveThetaBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8Below selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

/-- Block `W5` (2 facts): [158] window package unrealized, [160] tau below 1/4. -/
abbrev ColdBranchClosedWindowUnrealizedTauBelow (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

/-- Block `X1` (4 facts): `Absorbed/Residual.lean` exit 1: [175] no positive germ, [175] read at [177] Type B absorbed half-edge, [177] counted core absent (F4 charge). -/
abbrev ColdBranchClosedExitNoGermCharged (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedF4Charge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedHandoffCoreAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldNoPositiveGerm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedHalfEdge selected.object

/-- Block `X2` (3 facts): `Absorbed/Residual.lean` exit 2: [175] no positive germ, [175] read at [177] no Type B absorbed half-edge (subcubic). -/
abbrev ColdBranchClosedExitNoGermSubcubic (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldNoPositiveGerm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldSelectedFamilyEmpty selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedHalfEdgeAbsent selected.object

/-- Block `X3` (4 facts): `Absorbed/Residual.lean` exit 3: [175] positive germ, [154] G1 none realizing, [154] G2 some distinguishing. -/
abbrev ColdBranchClosedExitGermDistinguished (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldPositiveGerm selected.object

/-- Block `X4` (11 facts): `Absorbed/Residual.lean` exit 4: [175] positive germ, [154] none realizing and none distinguishing, [163] canonical neutral configuration, [175] read at [177] Type B absorbed half-edge, [177] counted core absent (F4 charge). -/
abbrev ColdBranchClosedExitGermCanonicalCharged (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedF4Charge selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .absorbedHandoffCoreAbsent selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAbsorbedNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementTrivial selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldPositiveGerm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedHalfEdge selected.object

/-- Block `X5` (9 facts): `Absorbed/Residual.lean` exit 5: [175] positive germ, [154] none realizing and none distinguishing, [163] canonical neutral configuration, [175] read at [177] no Type B absorbed half-edge (subcubic). -/
abbrev ColdBranchClosedExitGermCanonicalSubcubic (selected : EGInput.{u}) : Prop :=
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldAbsorbedNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalNeutralConfiguration selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementSwap selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldCanonicalReplacementTrivial selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldPositiveGerm selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .typeBAbsorbedHalfEdgeAbsent selected.object

/-- the entropy-side arm ([50], [53]): one of its 4 blocks. -/
abbrev ColdBranchClosedEntropyArm (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedEntropyHighCap selected ∨
  ColdBranchClosedEntropyLowNonrepetitive selected ∨
  ColdBranchClosedEntropyLowWedgeFree selected ∨
  ColdBranchClosedEntropyLowWedgeType selected
/-- the window/test arm ([158], [160], [146], [153]): one of its 5 blocks. -/
abbrev ColdBranchClosedWindowArm (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedWindowRealizedThetaAtOrAbove selected ∨
  ColdBranchClosedWindowRealizedThetaBelow selected ∨
  ColdBranchClosedWindowUnrealizedTauAtOrAboveThetaAtOrAbove selected ∨
  ColdBranchClosedWindowUnrealizedTauAtOrAboveThetaBelow selected ∨
  ColdBranchClosedWindowUnrealizedTauBelow selected
/-- the absorbed-germ exit ([175], [154], [163], [177]): one of its 5 blocks. -/
abbrev ColdBranchClosedExitArm (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedExitNoGermCharged selected ∨
  ColdBranchClosedExitNoGermSubcubic selected ∨
  ColdBranchClosedExitGermDistinguished selected ∨
  ColdBranchClosedExitGermCanonicalCharged selected ∨
  ColdBranchClosedExitGermCanonicalSubcubic selected

/-- Builds the `X1` disjunct of `ColdBranchClosedExitArm`: one `get` per fact
of block `X1`. -/
theorem coldBranchClosedExitNoGermChargedReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedF4Charge) known]
    [FactKeys.Has (K .absorbedHandoffCoreAbsent) known]
    [FactKeys.Has (K .coldNoPositiveGerm) known]
    [FactKeys.Has (K .typeBAbsorbedHalfEdge) known]
    : ColdBranchClosedExitArm selected :=
  Or.inl ⟨(history.get (K .absorbedF4Charge)).down,
    (history.get (K .absorbedHandoffCoreAbsent)).down,
    (history.get (K .coldNoPositiveGerm)).down,
    (history.get (K .typeBAbsorbedHalfEdge)).down⟩
/-- Builds the `X2` disjunct of `ColdBranchClosedExitArm`: one `get` per fact
of block `X2`. -/
theorem coldBranchClosedExitNoGermSubcubicReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldNoPositiveGerm) known]
    [FactKeys.Has (K .coldSelectedFamilyEmpty) known]
    [FactKeys.Has (K .typeBAbsorbedHalfEdgeAbsent) known]
    : ColdBranchClosedExitArm selected :=
  Or.inr (Or.inl ⟨(history.get (K .coldNoPositiveGerm)).down,
    (history.get (K .coldSelectedFamilyEmpty)).down,
    (history.get (K .typeBAbsorbedHalfEdgeAbsent)).down⟩)
/-- Builds the `X3` disjunct of `ColdBranchClosedExitArm`: one `get` per fact
of block `X3`. -/
theorem coldBranchClosedExitGermDistinguishedReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldPositiveGerm) known]
    : ColdBranchClosedExitArm selected :=
  Or.inr (Or.inr (Or.inl ⟨(history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldPositiveGerm)).down⟩))
/-- Builds the `X4` disjunct of `ColdBranchClosedExitArm`: one `get` per fact
of block `X4`. -/
theorem coldBranchClosedExitGermCanonicalChargedReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedF4Charge) known]
    [FactKeys.Has (K .absorbedHandoffCoreAbsent) known]
    [FactKeys.Has (K .coldAbsorbedNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .coldCanonicalReplacementTrivial) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldPositiveGerm) known]
    [FactKeys.Has (K .typeBAbsorbedHalfEdge) known]
    : ColdBranchClosedExitArm selected :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨(history.get (K .absorbedF4Charge)).down,
    (history.get (K .absorbedHandoffCoreAbsent)).down,
    (history.get (K .coldAbsorbedNeutralConfiguration)).down,
    (history.get (K .coldCanonicalNeutralConfiguration)).down,
    (history.get (K .coldCanonicalReplacementSwap)).down,
    (history.get (K .coldCanonicalReplacementTrivial)).down,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldPositiveGerm)).down,
    (history.get (K .typeBAbsorbedHalfEdge)).down⟩)))
/-- Builds the `X5` disjunct of `ColdBranchClosedExitArm`: one `get` per fact
of block `X5`. -/
theorem coldBranchClosedExitGermCanonicalSubcubicReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .coldAbsorbedNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalNeutralConfiguration) known]
    [FactKeys.Has (K .coldCanonicalReplacementSwap) known]
    [FactKeys.Has (K .coldCanonicalReplacementTrivial) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldPositiveGerm) known]
    [FactKeys.Has (K .typeBAbsorbedHalfEdgeAbsent) known]
    : ColdBranchClosedExitArm selected :=
  Or.inr (Or.inr (Or.inr (Or.inr (⟨(history.get (K .coldAbsorbedNeutralConfiguration)).down,
    (history.get (K .coldCanonicalNeutralConfiguration)).down,
    (history.get (K .coldCanonicalReplacementSwap)).down,
    (history.get (K .coldCanonicalReplacementTrivial)).down,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldPositiveGerm)).down,
    (history.get (K .typeBAbsorbedHalfEdgeAbsent)).down⟩))))

/-- **`[187]` (local cold-terminal exclusion), absorbed-germ product.**  The
100 absorbed-germ paths: the generic 57 facts, the 5 absorbed-common
facts, and exactly one block of each arm family. -/
abbrev ColdBranchClosedOutcome_product (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧ ColdBranchClosedAbsorbedCommon selected ∧
  ColdBranchClosedEntropyArm selected ∧ ColdBranchClosedWindowArm selected ∧
  ColdBranchClosedExitArm selected

theorem ColdBranchClosedOutcome_product.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_product selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_product`, parameterised by the arm
of each family: the entropy and window arms are the path's `EntropyArm` and
`Route8LanePrefix` (read as `E1`--`E4` and `W1`--`W5`), each block built by
its `Route8Blocks` `.ret` where the arm's keys are in scope, and the exit arm
is `coldBranchClosed<Exit>Return history`.  With those, one `get` per fact. -/
theorem coldBranchClosedProductReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .absorbedConfigurationResidual) known]
    [FactKeys.Has (K .exactCollisionFails) known]
    [FactKeys.Has (K .largeBudgetResidual) known]
    [FactKeys.Has (K .netDeficiencyCap) known]
    [FactKeys.Has (K .route8Rate) known]
    (entropy : ColdBranchClosedEntropyArm selected)
    (window : ColdBranchClosedWindowArm selected)
    (exit : ColdBranchClosedExitArm selected) :
    ColdBranchClosedOutcome_product selected :=
  ⟨coldBranchClosedReturn history, coldBranchClosedAbsorbedCommonReturn history,
    entropy, window, exit⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearDenseAtOrAbove`**
(66 facts): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassAtOrAbove`: [158] unrealized, [160] tau at or above 1/4, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearDenseAtOrAbove (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyAtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

theorem ColdBranchClosedOutcome_linearDenseAtOrAbove.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseAtOrAbove selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearDenseAtOrAbove`: one `get` per
fact. The facts of the upstream arm are read from its block
(`DenseTauBlock_atOrAbove`), built by the block's `.ret` with one `get` per key
on the same ledger. -/
theorem coldBranchClosed_linearDenseAtOrAboveReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauBlock_atOrAbove selected)
    : ColdBranchClosedOutcome_linearDenseAtOrAbove selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldHeavyEntryTerminal)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .denseColdCorridorsTerminal)).down,
    tau,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearDenseRateFailed`**
(67 facts): [153] linear cold mass through `nearCubicDenseLinear` after `nearCubicDensePassRateFailed`: [158] unrealized, [160] tau below 1/4 and route-8 rate failing, [146] theta at or above, [162] heavy entry, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearDenseRateFailed (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldHeavyEntryTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseColdCorridorsTerminal selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .denseDeficiencyBelow selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .route8RateFails selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageUnrealized selected.object

theorem ColdBranchClosedOutcome_linearDenseRateFailed.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearDenseRateFailed selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearDenseRateFailed`: one `get` per
fact. The facts of the upstream arm are read from its block
(`DenseTauBlock_belowRateFails`), built by the block's `.ret` with one `get` per
key on the same ledger. -/
theorem coldBranchClosed_linearDenseRateFailedReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauBlock_belowRateFails selected)
    : ColdBranchClosedOutcome_linearDenseRateFailed selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldHeavyEntryTerminal)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .denseColdCorridorsTerminal)).down,
    tau.1,
    tau.2,
    (history.get (K .windowPackageUnrealized)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedDistinguished`**
(63 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / some distinguishing. -/
abbrev ColdBranchClosedOutcome_linearRealizedDistinguished (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermSomeDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

theorem ColdBranchClosedOutcome_linearRealizedDistinguished.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearRealizedDistinguished selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearRealizedDistinguished`: one `get` per fact. -/
theorem coldBranchClosed_linearRealizedDistinguishedReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    : ColdBranchClosedOutcome_linearRealizedDistinguished selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldGermSomeDistinguishing)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .windowPackageRealized)).down⟩

/-- **`[187]` (local cold-terminal exclusion), singleton `linearRealizedSilent`**
(63 facts): [153] linear cold mass in `nearCubicRealized`: [158] realized, [146] theta at or above, [154] none realizing / none distinguishing. -/
abbrev ColdBranchClosedOutcome_linearRealizedSilent (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome selected ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermFamilyPositive selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneDistinguishing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldGermNoneRealizing selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldMassLinear selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .coldRoute8AtOrAbove selected.object ∧
  Holds BranchState Graph.ReceiverLoad.LoadCapacityProfile
      erdosReceiverLoadProfile spineData .windowPackageRealized selected.object

theorem ColdBranchClosedOutcome_linearRealizedSilent.toGeneric {selected : EGInput.{u}}
    (h : ColdBranchClosedOutcome_linearRealizedSilent selected) :
    ColdBranchClosedOutcome selected :=
  h.1

/-- The return of `ColdBranchClosedOutcome_linearRealizedSilent`: one `get` per fact. -/
theorem coldBranchClosed_linearRealizedSilentReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneDistinguishing) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .windowPackageRealized) known]
    : ColdBranchClosedOutcome_linearRealizedSilent selected :=
  ⟨coldBranchClosedReturn history,
    (history.get (K .coldGermFamilyPositive)).down,
    (history.get (K .coldGermNoneDistinguishing)).down,
    (history.get (K .coldGermNoneRealizing)).down,
    (history.get (K .coldMassLinear)).down,
    (history.get (K .coldRoute8AtOrAbove)).down,
    (history.get (K .windowPackageRealized)).down⟩

/-- The near-cubic prefix block of a path, read as its window/test block
(`W1`--`W5` list the same keys as the five `Route8LanePrefix` blocks). -/
theorem Route8LanePrefix.toColdBranchClosedWindowArm {selected : EGInput.{u}}
    (lanePrefix : Route8LanePrefix selected) :
    ColdBranchClosedWindowArm selected := by
  rcases lanePrefix with p | p | p | p | p
  · exact Or.inr (Or.inl p)
  · exact Or.inl p
  · exact Or.inr (Or.inr (Or.inr (Or.inl p)))
  · exact Or.inr (Or.inr (Or.inl p))
  · exact Or.inr (Or.inr (Or.inr (Or.inr p)))

/-- The entropy arm of a path, read as its entropy-side block (`E1`--`E4` are
the four `EntropyArm` blocks, key for key). -/
theorem EntropyArm.toColdBranchClosedEntropyArm {selected : EGInput.{u}}
    (entropy : EntropyArm selected) : ColdBranchClosedEntropyArm selected :=
  entropy

/-- The four linear-arm singletons of the residual `[187]` (local
cold-terminal exclusion), returned on the `[153]` linear arm of the near-cubic
survivor. -/
abbrev ColdBranchClosedLinearSubtypes (selected : EGInput.{u}) : Prop :=
  ColdBranchClosedOutcome_linearDenseAtOrAbove selected ∨
  ColdBranchClosedOutcome_linearDenseRateFailed selected ∨
  ColdBranchClosedOutcome_linearRealizedDistinguished selected ∨
  ColdBranchClosedOutcome_linearRealizedSilent selected

/-- The return of the local cold-terminal exclusion on the `[153]` linear arm of the dense pass (`nearCubicDenseLinear`), on the `[160]` arm named by `tau`, through that singleton's return theorem. -/
theorem coldBranchClosedLinearDenseReturn
    {selected : EGInput.{u}} {known : FactKeys EGInput.{u}}
    (history : ExactLedger EGInput.{u} selected known)
    [FactKeys.Has (K .absorbedGermFanData) known]
    [FactKeys.Has (K .absorbedGermSplit) known]
    [FactKeys.Has (K .barrierCap) known]
    [FactKeys.Has (K .barrierEnumeration) known]
    [FactKeys.Has (K .boundaryDemand) known]
    [FactKeys.Has (K .bridgeless) known]
    [FactKeys.Has (K .coldAmbientCubic) known]
    [FactKeys.Has (K .coldAmbientCubicStubExcess) known]
    [FactKeys.Has (K .coldBranchClosed) known]
    [FactKeys.Has (K .coldCorridorState) known]
    [FactKeys.Has (K .coldCutStatesDistinct) known]
    [FactKeys.Has (K .coldExchangeBound) known]
    [FactKeys.Has (K .coldFailureCompression) known]
    [FactKeys.Has (K .coldFailureCycle) known]
    [FactKeys.Has (K .coldFailureDefectRoute) known]
    [FactKeys.Has (K .coldFailureRouting) known]
    [FactKeys.Has (K .coldFirstFailureOccurrence) known]
    [FactKeys.Has (K .coldGermCandidates) known]
    [FactKeys.Has (K .coldGermDistinguished) known]
    [FactKeys.Has (K .coldGermRealized) known]
    [FactKeys.Has (K .coldGermRouted) known]
    [FactKeys.Has (K .coldGermSilent) known]
    [FactKeys.Has (K .coldHandoffTransfer) known]
    [FactKeys.Has (K .coldHotEntropyCap) known]
    [FactKeys.Has (K .coldMass) known]
    [FactKeys.Has (K .coldReturnCorridors) known]
    [FactKeys.Has (K .coldSameInterfaceTable) known]
    [FactKeys.Has (K .coldSelectedBranchExcess) known]
    [FactKeys.Has (K .coldStubExcess) known]
    [FactKeys.Has (K .cubicBaseline) known]
    [FactKeys.Has (K .curvatureFullRank) known]
    [FactKeys.Has (K .curvatureTargetRank) known]
    [FactKeys.Has (K .cycleRankConstraint) known]
    [FactKeys.Has (K .degreeProfileFibres) known]
    [FactKeys.Has (K .exactResponseProfile) known]
    [FactKeys.Has (K .forcedCurvatureCost) known]
    [FactKeys.Has (K .hotColdPartition) known]
    [FactKeys.Has (K .localAlgebra) known]
    [FactKeys.Has (K .maximalPacking) known]
    [FactKeys.Has (K .netChargeLocalization) known]
    [FactKeys.Has (K .noProperBaseline) known]
    [FactKeys.Has (K .remainderNormalized) known]
    [FactKeys.Has (K .replacementExclusion) known]
    [FactKeys.Has (K .returnAvoidance) known]
    [FactKeys.Has (K .selection) known]
    [FactKeys.Has (K .skeletonDominates) known]
    [FactKeys.Has (K .slackIndependent) known]
    [FactKeys.Has (K .sparseSurplusSurvivor) known]
    [FactKeys.Has (K .stubSupply) known]
    [FactKeys.Has (K .surplusAtOrBelow) known]
    [FactKeys.Has (K .targetCompleteContextUniversality) known]
    [FactKeys.Has (K .targetRankCircuit) known]
    [FactKeys.Has (K .tightEndpoint) known]
    [FactKeys.Has (K .uncompressible) known]
    [FactKeys.Has (K .wedgeSupply) known]
    [FactKeys.Has (K .windowPackageSeparated) known]
    [FactKeys.Has (K .windowPresent) known]
    [FactKeys.Has (K .coldGermFamilyPositive) known]
    [FactKeys.Has (K .coldGermNoneRealizing) known]
    [FactKeys.Has (K .coldGermSomeDistinguishing) known]
    [FactKeys.Has (K .coldHeavyEntryTerminal) known]
    [FactKeys.Has (K .coldMassLinear) known]
    [FactKeys.Has (K .coldRoute8AtOrAbove) known]
    [FactKeys.Has (K .denseColdCorridorsTerminal) known]
    [FactKeys.Has (K .windowPackageUnrealized) known]
    (tau : DenseTauArm selected) :
    ColdBranchClosedLinearSubtypes selected := by
  rcases tau with t | t
  · exact Or.inl (coldBranchClosed_linearDenseAtOrAboveReturn history t)
  · exact Or.inr (Or.inl (coldBranchClosed_linearDenseRateFailedReturn history t))

end HypostructureErdos64EG
