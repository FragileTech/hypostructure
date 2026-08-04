import Hypostructure.Core.Finite.Enumeration

/-!
# Finite bottleneck classification semantics

The registration contains only residual-indexed mathematical carriers,
complete schedules, primitive observations, and decision procedures.  The
strategy implementation delegates every scan, ledger extension, terminal,
and work bound to CT9, CT14, CT10, and CT6.
-/

namespace Hypostructure.Core.Strategy.FiniteBottleneckClassification

universe uResidual uPatternItem uCoarseCode uPressureLabel
  uDatum uSemanticTag uPromotion uSeparatorIndex uSeparatorData

structure Registration (Residual : Type uResidual) where
  PatternItem : Residual → Type uPatternItem
  CoarseCode : Residual → Type uCoarseCode
  patternItems : (residual : Residual) →
    Core.Finite.Enumeration (PatternItem residual)
  completeCoarseCodes : (residual : Residual) →
    Core.Finite.CompleteEnumeration (CoarseCode residual)
  coarseCodeOf : (residual : Residual) →
    PatternItem residual → CoarseCode residual
  PressureLabel : Residual → Type uPressureLabel
  pressureCapacity : (residual : Residual) →
    CoarseCode residual → Option Nat
  pressureLabel : (residual : Residual) →
    CoarseCode residual → Option (PressureLabel residual)
  pressureLabelDecidableEq : (residual : Residual) →
    DecidableEq (PressureLabel residual)
  Datum : Residual → Type uDatum
  SemanticTag : Residual → Type uSemanticTag
  Promotion : Residual → Type uPromotion
  data : (residual : Residual) →
    Core.Finite.Enumeration (Datum residual)
  completeSemanticTags : (residual : Residual) →
    Core.Finite.CompleteEnumeration (SemanticTag residual)
  classOf : (residual : Residual) →
    Datum residual → SemanticTag residual
  Direct : (residual : Residual) → SemanticTag residual → Prop
  promote : (residual : Residual) →
    SemanticTag residual → Promotion residual
  directDecidable : (residual : Residual) →
    (tag : SemanticTag residual) → Decidable (Direct residual tag)
  SeparatorIndex : Residual → Type uSeparatorIndex
  SeparatorData : (residual : Residual) →
    SeparatorIndex residual → Type uSeparatorData
  separatorOrder : (residual : Residual) →
    Core.Finite.Enumeration (SeparatorIndex residual)
  SeparatorFailure : (residual : Residual) →
    SeparatorIndex residual → Prop
  separatorFailureData : (residual : Residual) →
    (index : SeparatorIndex residual) →
    SeparatorFailure residual index → SeparatorData residual index
  separatorFailureDecidable : (residual : Residual) →
    (index : SeparatorIndex residual) →
    Decidable (SeparatorFailure residual index)
  separatorContribution : (residual : Residual) →
    SeparatorIndex residual → Nat

end Hypostructure.Core.Strategy.FiniteBottleneckClassification
