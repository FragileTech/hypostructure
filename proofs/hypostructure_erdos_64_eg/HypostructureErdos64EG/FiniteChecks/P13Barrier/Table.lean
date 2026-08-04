import HypostructureErdos64EG.FiniteChecks.P13Barrier.CertificateAudit
import Hypostructure.Core.Finite.CertifiedTableBounds
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraBitTable
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics

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

/-- **What the certificate's row indices name.**  The audit above says the
stored bits are the bits the source model computes; it fixes no interpretation
of the index.  This record supplies the interpretation, and every field is a
framework theorem about `WindowCurvature.windowLabel`: the index names a legal
attachment label of the induced window, distinct indices name distinct labels,
every legal label is named, and the audited relation is the manuscript's `C_s`
on the labels named.

Through `Core.Strategy.ExactFiniteLocalAlgebra.LabelDenotation.labels_card`
this is what turns the generated profile's `399` into `lem:labels`' count of
`WindowCurvature.Labels`: it is no longer a size a generator wrote into a
type. -/
def labelDenotation :
    Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra.LabelDenotation
      (size := 399) (fun length : Fin 15 => length.1)
      (fun length => semanticRelation length.1)
      (Hypostructure.Graph.WindowCurvature.Labels
        Hypostructure.Graph.WindowCurvature.windowOrder)
      (fun shift source target =>
        Hypostructure.Graph.WindowCurvature.Safe shift source target) where
  denote := Hypostructure.Graph.WindowCurvature.windowLabel
  denote_mem := Hypostructure.Graph.WindowCurvature.windowLabel_mem_Labels
  denote_injective := Hypostructure.Graph.WindowCurvature.windowLabel_injective
  denote_surjective := fun _ member =>
    Hypostructure.Graph.WindowCurvature.windowLabel_surjective member
  relation_denote := fun length source target =>
    Hypostructure.Graph.WindowCurvature.windowRelation_eq_safe length.1 source
      target

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

/-- Inert presentation consumed by Core's sealed finite-barrier Strategy.
Core derives the accepted schedule and every safe/flat count; no stored count
column or execution result is registered here.

This is the schedule of one *scale-free* window package: the `91` ordered
barriers `(a, b)` with `a, b ≥ 1` and `a + b ≤ 14` of `app:curv-code`, once
each.  Its derived rate `log₂(safeProduct / flatProduct)` is the manuscript's
`c₁₃`, the per-window cost **per dyadic scale**.  The number of separated
dyadic scales is a property of the residual object, not of this table, so the
problem declaration wraps this registration in
`Graph.Strategy.FiniteDensityBudget.multiScaleWindowPackage`, which repeats it
once per dyadic scale of the object.  Nothing here is repeated or restated
there: the label carrier, bit-relation profile and both leg lengths are read
straight off this registration. -/
def enumerationRegistration (Residual : Type*) :
    Hypostructure.Core.Strategy.FiniteBarrierEnumeration.Registration
      Residual where
  Candidate := fun _ => Fin 15 × Fin 15
  candidates := fun _ =>
    (Hypostructure.Core.Finite.CompleteEnumeration.ofFinEnum inferInstance).product
      (Hypostructure.Core.Finite.CompleteEnumeration.ofFinEnum inferInstance)
  accepted := fun _ pair =>
    0 < pair.1.1 ∧ 0 < pair.2.1 ∧ pair.1.1 + pair.2.1 ≤ 14
  acceptedDecidable := fun _ _ => inferInstance
  labelCount := fun _ => labelCount
  relationPosition := fun _ relation => relation
  leftLength := fun _ index => index.1.1
  rightLength := fun _ index => index.2.1

def flatProduct : Nat :=
  Hypostructure.Core.Finite.CertifiedTableAggregation.flatProduct certifiedTable

def safeProduct : Nat :=
  Hypostructure.Core.Finite.CertifiedTableAggregation.safeProduct certifiedTable

end HypostructureErdos64EG.FiniteChecks.P13Barrier
