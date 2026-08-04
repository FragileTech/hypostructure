import Hypostructure.Core.Budget.Resource
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Response.FiniteTable

/-!
# Residual-indexed homogeneous-bottleneck semantics

This file contains only the inert mathematical presentation consumed by the
domain-neutral `HomogeneousBottleneck` Strategy.  It contains no predecessor
stage, query, ledger, CT result, terminal, route, executor, selected witness,
or completed branch payload.
-/

namespace Hypostructure.Core.Strategy.HomogeneousBottleneck

universe uResidual uData

/-- Inert residual-owned presentation for the homogeneous-bottleneck pattern.

Every finite execution family is indexed by the received residual.  CT3's
response system and CT5's resource algebra are fixed because those are the
dependency shapes of the existing public CT interfaces; neither can carry an
execution result or choose a terminal. -/
structure Registration (Residual : Type uResidual) (Target : Residual → Prop) where
  Item : Residual → Type uData
  HomogeneityCode : Residual → Type uData
  items : (residual : Residual) →
    Core.Finite.Enumeration (Item residual)
  completeHomogeneityCodes : (residual : Residual) →
    Core.Finite.CompleteEnumeration (HomogeneityCode residual)
  homogeneityCodeOf : (residual : Residual) →
    Item residual → HomogeneityCode residual
  homogeneityCapacity : (residual : Residual) →
    HomogeneityCode residual → Nat

  CapacityLabel : Residual → Type uData
  codeCapacity : (residual : Residual) →
    HomogeneityCode residual → Option Nat
  codeLabel : (residual : Residual) →
    HomogeneityCode residual → Option (CapacityLabel residual)
  codeLabelDecidableEq : (residual : Residual) →
    DecidableEq (CapacityLabel residual)

  Datum : Residual → Type uData
  LocalClass : Residual → Type uData
  Promotion : Residual → Type uData
  data : (residual : Residual) →
    Core.Finite.Enumeration (Datum residual)
  completeLocalClasses : (residual : Residual) →
    Core.Finite.CompleteEnumeration (LocalClass residual)
  classOf : (residual : Residual) → Datum residual → LocalClass residual
  Direct : (residual : Residual) → LocalClass residual → Prop
  promote : (residual : Residual) → LocalClass residual → Promotion residual
  directDecidable : (residual : Residual) →
    (localClass : LocalClass residual) →
      Decidable (Direct residual localClass)

  LocalIndex : Residual → Type uData
  LocalFailureData : (residual : Residual) → LocalIndex residual → Type uData
  localOrder : (residual : Residual) →
    Core.Finite.Enumeration (LocalIndex residual)
  LocalFailure : (residual : Residual) → LocalIndex residual → Prop
  localFailureData : (residual : Residual) →
    (index : LocalIndex residual) →
    LocalFailure residual index → LocalFailureData residual index
  localFailureDecidable : (residual : Residual) →
    (index : LocalIndex residual) →
      Decidable (LocalFailure residual index)
  localContribution : (residual : Residual) → LocalIndex residual → Nat

  Representative : Type uData
  responseSystem :
    Core.Response.System.{uData, uData, uData, uData} Representative
  targetSemantics : Core.Response.TargetSemantics responseSystem
  ResponseCandidate : Type uData
  ResponseRow : Type uData
  candidatePiece : ResponseCandidate → Representative
  rowPiece : ResponseRow → Representative
  rowResponse : ResponseRow →
    responseSystem.Coordinate → responseSystem.Value
  responseSource : Residual → Representative
  responseCoordinates : Residual →
    Core.Finite.Enumeration responseSystem.Coordinate
  responseCandidates : Residual →
    Core.Finite.Enumeration ResponseCandidate
  responseRows : Residual → Core.Finite.Enumeration ResponseRow
  ResponseAdmissible : Residual →
    Representative → ResponseCandidate → Prop
  ResponseStrictlySmaller : Residual →
    Representative → ResponseCandidate → Prop
  responseValueDecEq : DecidableEq responseSystem.Value
  responseAdmissibleDecidable : (residual : Residual) →
    (source : Representative) → (candidate : ResponseCandidate) →
      Decidable (ResponseAdmissible residual source candidate)
  responseSmallerDecidable : (residual : Residual) →
    (source : Representative) → (candidate : ResponseCandidate) →
      Decidable (ResponseStrictlySmaller residual source candidate)
  responseCandidateCoverage : (residual : Residual) →
    (candidate : ResponseCandidate) →
    candidate ∈ (responseCandidates residual).values →
      Core.Response.FiniteTable.SymbolicCoverage responseSystem
        { source := responseSource residual
          replacement := candidatePiece candidate }
        (Core.Response.FiniteTable.ExactSchedule.ofList
          (responseCoordinates residual).values)
  responseRowCoverage : (residual : Residual) →
    (row : ResponseRow) →
    row ∈ (responseRows residual).values →
      Core.Response.FiniteTable.SymbolicCoverage responseSystem
        { source := responseSource residual
          replacement := rowPiece row }
        (Core.Response.FiniteTable.ExactSchedule.ofList
          (responseCoordinates residual).values)

  AdmissibilityField : Residual → Type uData
  AdmissibilityFailureData : (residual : Residual) →
    AdmissibilityField residual → Type uData
  admissibilityOrder : (residual : Residual) →
    Core.Finite.Enumeration (AdmissibilityField residual)
  AdmissibilityFailure : (residual : Residual) →
    AdmissibilityField residual → Prop
  admissibilityFailureData : (residual : Residual) →
    (field : AdmissibilityField residual) →
    AdmissibilityFailure residual field →
      AdmissibilityFailureData residual field
  admissibilityFailureDecidable : (residual : Residual) →
    (field : AdmissibilityField residual) →
      Decidable (AdmissibilityFailure residual field)
  admissibilityContribution : (residual : Residual) →
    AdmissibilityField residual → Nat

  TargetCandidate : Residual → Type uData
  ExceptionalCandidate : Residual → Type uData
  outcomeCandidates : (residual : Residual) →
    Core.Finite.Enumeration
      (Sum (TargetCandidate residual) (ExceptionalCandidate residual))
  RealizesTarget : (residual : Residual) → TargetCandidate residual → Prop
  RealizesException : (residual : Residual) →
    ExceptionalCandidate residual → Prop
  targetRealizationDecidable : (residual : Residual) →
    (candidate : TargetCandidate residual) →
      Decidable (RealizesTarget residual candidate)
  exceptionRealizationDecidable : (residual : Residual) →
    (candidate : ExceptionalCandidate residual) →
      Decidable (RealizesException residual candidate)
  targetOfRealization : ∀ (residual : Residual)
    (candidate : TargetCandidate residual),
      RealizesTarget residual candidate → Target residual

  supportBudget : Core.ResourceBudget.{uData}
  SupportSite : Residual → Type uData
  SupportWitness : (residual : Residual) → SupportSite residual → Type uData
  supportFamily : (residual : Residual) →
    Core.Finite.DependentEnumeration
      (SupportSite residual) (SupportWitness residual)
  SupportActive : (residual : Residual) → SupportSite residual → Prop
  SupportRelation : (residual : Residual) →
    (site : SupportSite residual) → SupportWitness residual site → Prop
  supportContribution : (residual : Residual) →
    (site : SupportSite residual) →
    SupportWitness residual site → supportBudget.Resource
  supportRequired : Residual → supportBudget.Resource
  supportCapacity : Residual → supportBudget.Resource
  supportActiveDecidable : (residual : Residual) →
    (site : SupportSite residual) →
      Decidable (SupportActive residual site)
  supportRelationDecidable : (residual : Residual) →
    (site : SupportSite residual) →
    (witness : SupportWitness residual site) →
      Decidable (SupportRelation residual site witness)
  supportResourceLEDecidable : (left right : supportBudget.Resource) →
    Decidable (left ≤ right)

  BoundedMember : Residual → Type uData
  BoundedLabel : Residual → Type uData
  boundedMembers : (residual : Residual) →
    Core.Finite.Enumeration (BoundedMember residual)
  boundedLowerMass : (residual : Residual) → BoundedMember residual → Nat
  boundedCapacity : (residual : Residual) →
    BoundedMember residual → Option Nat
  boundedLabel : (residual : Residual) →
    BoundedMember residual → Option (BoundedLabel residual)
  boundedLabelDecidableEq : (residual : Residual) →
    DecidableEq (BoundedLabel residual)

  /-- A first local failure is represented in the complete exceptional
  schedule scanned later by CT1. -/
  localFailureScheduled : ∀ (residual : Residual)
    (index : LocalIndex residual),
      index ∈ (localOrder residual).values →
      LocalFailure residual index →
      ∃ candidate : ExceptionalCandidate residual,
        Sum.inr candidate ∈ (outcomeCandidates residual).values ∧
          RealizesException residual candidate

  /-- A stored response-table defect is represented in the complete
  exceptional schedule scanned later by CT1. -/
  responseDefectScheduled : ∀ (residual : Residual)
    (row : ResponseRow) (coordinate : responseSystem.Coordinate),
      row ∈ (responseRows residual).values →
      coordinate ∈ (responseCoordinates residual).values →
      responseSystem.coordinateResponse (rowPiece row) coordinate ≠
        rowResponse row coordinate →
      ∃ candidate : ExceptionalCandidate residual,
        Sum.inr candidate ∈ (outcomeCandidates residual).values ∧
          RealizesException residual candidate

  /-- A failed admissibility field is represented in the complete
  exceptional schedule scanned later by CT1. -/
  admissibilityFailureScheduled : ∀ (residual : Residual)
    (field : AdmissibilityField residual),
      field ∈ (admissibilityOrder residual).values →
      AdmissibilityFailure residual field →
      ∃ candidate : ExceptionalCandidate residual,
        Sum.inr candidate ∈ (outcomeCandidates residual).values ∧
          RealizesException residual candidate

  /-- Every active support deficit is represented in the same complete CT1
  exceptional schedule. -/
  supportDeficitScheduled : ∀ (residual : Residual)
    (site : SupportSite residual),
      site ∈ (supportFamily residual).indices.values →
      SupportActive residual site →
      (∀ index : Fin ((supportFamily residual).fibres site).card,
        ¬ SupportRelation residual site
          (((supportFamily residual).fibres site).get index)) →
      ∃ candidate : ExceptionalCandidate residual,
        Sum.inr candidate ∈ (outcomeCandidates residual).values ∧
          RealizesException residual candidate

  /-- Failure of the registered support capacity comparison is represented in
  the same complete CT1 exceptional schedule. -/
  supportCapacityFailureScheduled : ∀ residual,
      ¬ supportRequired residual ≤ supportCapacity residual →
      ∃ candidate : ExceptionalCandidate residual,
        Sum.inr candidate ∈ (outcomeCandidates residual).values ∧
          RealizesException residual candidate

  /-- The final CT14 member schedule has total residual-owned capacity data. -/
  boundedCapacityTotal : ∀ (residual : Residual)
    (member : BoundedMember residual),
      member ∈ (boundedMembers residual).values →
      ∃ capacity, boundedCapacity residual member = some capacity

  /-- The final CT14 member schedule has total residual-owned label data. -/
  boundedLabelTotal : ∀ (residual : Residual)
    (member : BoundedMember residual),
      member ∈ (boundedMembers residual).values →
      ∃ label, boundedLabel residual member = some label

  /-- Optional registered closure of the exceptional output: the residual-owned
  fact that the exceptional candidate schedule has no inhabitant at all.

  This is not a routing decision and not an asserted terminal.  It is the
  mathematical content already carried by the five `…Scheduled` obligations
  above read in the contrapositive: when a registration discharges each of
  them from a standing hypothesis rather than by exhibiting a candidate, its
  `ExceptionalCandidate` family is empty, and CT1 can never select the
  exceptional route.  Supplying this field lets Core eliminate the exceptional
  output as vacuous instead of retaining it as an open branch endpoint.

  Registrations whose exceptional schedule is genuinely inhabited leave this
  `none`, and the exceptional output stays live exactly as before. -/
  exceptionalImpossible :
    Option (PLift (∀ residual : Residual,
      ExceptionalCandidate residual → False)) := none

end Hypostructure.Core.Strategy.HomogeneousBottleneck
