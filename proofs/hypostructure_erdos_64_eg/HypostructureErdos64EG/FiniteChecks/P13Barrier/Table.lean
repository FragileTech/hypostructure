import HypostructureErdos64EG.FiniteChecks.P13Barrier.CertificateAudit
import Hypostructure.Core.Finite.CertifiedTableBounds

/-!
# Certified P13 barrier table

This module is the sole public interface of the generated finite check.  Its
products and entropy rate are projections of `certifiedTable`; downstream
strategy code therefore has no numeric table parameters to fill.
-/

namespace HypostructureErdos64EG.FiniteChecks.P13Barrier

set_option maxRecDepth 10000

open Hypostructure.Core.FiniteBitRelationBarrier
open Hypostructure.Core.Finite.CertifiedTableAggregation
open Hypostructure.Core.Finite.CertifiedTableBounds

/-- The generated profile packaged with the carrier size appearing in the
certificate's type. -/
def semanticPresentation :
    Σ labelCount, Hypostructure.Core.FiniteBitRelationBarrier.Profile labelCount :=
  ⟨_, Certificate.profile⟩

abbrev labelCount : Nat := semanticPresentation.1

def semanticProfile :
    Hypostructure.Core.FiniteBitRelationBarrier.Profile labelCount :=
  semanticPresentation.2

/-- Exactly the positive connector-length pairs whose sum remains in range. -/
abbrev AcceptedPair :=
  {pair : Fin 15 × Fin 15 //
    0 < pair.1.1 ∧ 0 < pair.2.1 ∧ pair.1.1 + pair.2.1 ≤ 14}

def leftLength (index : AcceptedPair) : Nat := index.1.1.1

def rightLength (index : AcceptedPair) : Nat := index.1.2.1

def semanticCertificate :
    SemanticCertificate Certificate.profile (Fin 15) (fun length => length.1)
      (fun length => semanticRelation length.1) where
  row_semantic := p13MultiScaleRows_codeAudit

def countCertificate :
    CountCertificate Certificate.profile AcceptedPair where
  leftLength := leftLength
  rightLength := rightLength
  storedSafe := fun index =>
    Certificate.safeCount (leftLength index) (rightLength index)
  storedFlat := fun index =>
    Certificate.flatCount (leftLength index) (rightLength index)
  safeExact := by
    intro index
    simpa [leftLength, rightLength, index.2.1, index.2.2.1,
      index.2.2.2] using
      p13MultiScaleSafeCounts_audit index.1.1 index.1.2
  flatExact := by
    intro index
    simpa [leftLength, rightLength, index.2.1, index.2.2.1,
      index.2.2.2] using
      p13MultiScaleFlatCounts_audit index.1.1 index.1.2

/-- The complete current-Core certificate consumed by strategy machinery. -/
def certifiedTable :
    CertifiedTable Certificate.profile (Fin 15) (fun length => length.1)
      (fun length => semanticRelation length.1) AcceptedPair where
  semantic := semanticCertificate
  counts := countCertificate

def flatProduct : Nat :=
  Hypostructure.Core.Finite.CertifiedTableAggregation.flatProduct certifiedTable

def safeProduct : Nat :=
  Hypostructure.Core.Finite.CertifiedTableAggregation.safeProduct certifiedTable

/-- **The registered per-window barrier rate, derived.**

The manuscript's `c₁₃` is `log₂(safeProduct / flatProduct)`, the per-window
cost of the scale-free `91`-barrier package per dyadic scale.  This is that
rate as the natural number the spine compares against: the framework's
`binaryRateFloor` of this very table, which rounds *down*, so the demand it
states is no larger than the real one.

It is a projection of the audited counts, not a numeral: nothing downstream
has a table parameter to fill. -/
def windowRate : Nat :=
  Hypostructure.Core.Finite.CertifiedTableAggregation.binaryRateFloor
    certifiedTable

set_option maxHeartbeats 8000000 in
/-- The exact natural rate projected from the certified stored counts.  Native
evaluation is confined to this closed table projection; downstream arithmetic
rewrites this theorem and never unfolds the certificate rows. -/
lemma windowRate_eq : windowRate = 118 := by
  native_decide

end HypostructureErdos64EG.FiniteChecks.P13Barrier
