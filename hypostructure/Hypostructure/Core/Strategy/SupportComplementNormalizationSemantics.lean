import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Strategy.ObstructionPackingSemantics

/-!
# Residual-indexed support-complement normalization semantics

This lower-layer record is inert mathematical presentation data for the
CT9 → CT14 → CT1 → CT6 composition implemented in
`SupportComplementNormalization.lean`.  It contains only finite carriers,
schedules, decision procedures, numeric observations, local mathematical
laws, and one target implication.

It deliberately contains no previous stage value, `Query`, ledger value, CT
result, terminal, route, contract, executor, or precomputed residual.  The
private strategy compiler is the only layer permitted to consume this record
operationally.
-/

namespace Hypostructure.Core.Strategy.SupportComplementNormalization

universe uResidual uItem uPacking uPiece uFailure

/-- Exact numeric ledger published by one completed normalization.  Every
field is computed by Core from the literal four-CT output; the record is the
typed capability consumed by later Strategies. -/
structure Summary where
  ambientCount : Nat
  packingCount : Nat
  coverCard : Nat
  selectedCount : Nat
  complementCount : Nat
  lowerMass : Nat
  activeTotal : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Residual-owned presentation of the ambient support, the selected packing,
the density cap, the obstruction family, and the local-core family.

The registration contributes carriers only.  Core selects the canonical
maximal packing from `occurrences` against the "share a covered item"
conflict, defines the selected part of the ambient support as the items that
packing covers, and *derives* both the maximality law that makes CT1's hit
terminal unreachable and the mass law that makes CT14's aggregate terminal
unreachable.  `failureForcesTarget` is the sole domain implication. -/
structure Registration (Residual : Type uResidual)
    (Target : Residual → Prop)
    (packing :
      ObstructionPackingClosure.Semantics.{uResidual, uPacking}
        Residual Target) where
  AmbientItem : Residual → Type uItem
  ambientSupport : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual)
  /-- The ambient items one occurrence uses.  Two occurrences conflict exactly
  when they share one, which is the conflict relation Core packs against. -/
  cover : (residual : Residual) → packing.Occurrence residual →
    List (AmbientItem residual)
  coverNodup : ∀ (residual : Residual)
    (occurrence : packing.Occurrence residual),
      (cover residual occurrence).Nodup
  coverSupported : ∀ (residual : Residual)
    (occurrence : packing.Occurrence residual),
      cover residual occurrence ⊆ (ambientSupport residual).values
  coverCard : Residual → Nat
  cover_card : ∀ (residual : Residual)
    (occurrence : packing.Occurrence residual),
      (cover residual occurrence).length = coverCard residual
  conflict_iff_shared_item : ∀ (residual : Residual)
    (left right : packing.Occurrence residual),
      packing.conflict residual left right ↔
        ∃ item, item ∈ cover residual left ∧ item ∈ cover residual right
  /-- Every occurrence uses at least one ambient item.  This is the only
  provision Core needs to derive packing maximality. -/
  cover_ne : ∀ (residual : Residual)
    (occurrence : packing.Occurrence residual),
    cover residual occurrence ≠ []
  /-- Canonical local pieces are indexed by CT9's literal complementary
  fibre.  The compiler supplies this enumeration from the composed output;
  registrations cannot supply, reconstruct, or ignore it. -/
  LocalPiece : (residual : Residual) →
    Core.Finite.Enumeration (AmbientItem residual) → Type uPiece
  localPieces : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
      Core.Finite.Enumeration (LocalPiece residual complement)
  FailureData : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
    LocalPiece residual complement → Type uFailure
  Failure : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
    LocalPiece residual complement → Prop
  failureData : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
    (piece : LocalPiece residual complement) →
    Failure residual complement piece →
      FailureData residual complement piece
  failureDecidable : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
    (piece : LocalPiece residual complement) →
      Decidable (Failure residual complement piece)
  contribution : (residual : Residual) →
    (complement : Core.Finite.Enumeration (AmbientItem residual)) →
    LocalPiece residual complement → Nat
  /-- The sole target implication combines a genuine failing local piece with
  literal CT1 avoidance for every registered occurrence supported by the same
  exact complement. -/
  failureForcesTarget : ∀ (residual : Residual)
    (complement : Core.Finite.Enumeration (AmbientItem residual))
    (piece : LocalPiece residual complement),
      Failure residual complement piece →
      (∀ occurrence : packing.Occurrence residual,
        (∀ item ∈ cover residual occurrence,
          item ∈ complement.values) →
        occurrence ∉ (packing.occurrences residual).values) →
      Target residual

end Hypostructure.Core.Strategy.SupportComplementNormalization
