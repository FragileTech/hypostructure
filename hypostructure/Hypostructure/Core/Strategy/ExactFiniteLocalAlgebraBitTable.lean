import Hypostructure.Core.FiniteBitRelationBarrier
import Hypostructure.Core.Strategy.ExactFiniteLocalAlgebraSemantics

/-!
# Exact finite local algebra derived from a certified bit-relation table

An application that has already audited a generated bit-relation table against
its executable source model owns a `FiniteBitRelationBarrier.SemanticCertificate`
and nothing else.  This module turns that single audited object into the inert
`ExactFiniteLocalAlgebra.Registration` Core's sealed Strategy consumes.

Every carrier size is projected from the certified profile: the label carrier
is `Fin size` for the profile's own `size`, and the relation index is the
certificate's own length carrier.  The generated code column is read straight
off the packed rows, and the obligation that it agrees with the semantic
schedules is discharged here by the certificate's audit -- an application
registers no numerical parameter and proves nothing.

A certificate audited against its own executable model fixes no
*interpretation*: it says the stored bits are the bits the model computes, and
says nothing about what the row indices name or how many of them there ought to
be.  `LabelDenotation` is that missing half.  It carries a finite carrier of
named objects, a bijection from the row indices onto it, and the identification
of the audited relation with a stated relation on those objects; from it, the
profile's own `size` becomes a *theorem* about the named carrier
(`LabelDenotation.labels_card`) rather than a number the generator wrote into a
type.  `ofDenotedBitRelationTable` is `ofBitRelationTable` with that record
demanded, so a registration built through it cannot leave the interpretation
open.
-/

namespace Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra

open Hypostructure.Core.FiniteBitRelationBarrier

universe uInput

/-- The exact finite local algebra of a certified bit-relation table. -/
def ofBitRelationTable
    {size : Nat} {profile : Profile size}
    {Length : Type} {lengthValue : Length → Nat}
    {relation : Length → Fin size → Fin size → Bool}
    [labelEnum : FinEnum (Fin size)] [lengthEnum : FinEnum Length]
    (certificate : SemanticCertificate profile Length lengthValue relation)
    (Input : Type uInput) :
    Registration.{uInput, 0, 0, 0} Input where
  Item := fun _ => Fin size
  items := fun _ =>
    (Core.Finite.CompleteEnumeration.ofFinEnum labelEnum).toEnumeration
  semantics := {
    Label := fun _ => Fin size
    labels := fun _ => Core.Finite.CompleteEnumeration.ofFinEnum labelEnum
    capacity := fun _ label =>
      (Core.Finite.CompleteEnumeration.ofFinEnum labelEnum).values.count label
    RelationIndex := fun _ => Length
    relationIndices := fun _ =>
      Core.Finite.CompleteEnumeration.ofFinEnum lengthEnum
    relation := fun _ length source destination =>
      relation length source destination
    targetCode := fun _ =>
      ((Core.Finite.CompleteEnumeration.ofFinEnum
          lengthEnum).toEnumeration.product
        ((Core.Finite.CompleteEnumeration.ofFinEnum labelEnum).toEnumeration.product
          (Core.Finite.CompleteEnumeration.ofFinEnum
            labelEnum).toEnumeration)).values.map fun coordinate =>
              (profile.row (lengthValue coordinate.1)
                coordinate.2.1).getLsb coordinate.2.2
    targetCode_exact := by
      intro _
      apply List.map_congr_left
      intro coordinate _
      exact certificate.row_semantic coordinate.1 coordinate.2.1 coordinate.2.2
  }
  label := fun _ item => item

universe uCarrier

/-- What a certified table's row indices *name*.

`labels` is the finite carrier of the named objects, `denote` names one for
each row index, and `Meaning` is the relation the application's mathematics
states on those objects.  The four proof fields say that naming is a bijection
onto `labels` and that the audited relation is exactly `Meaning` transported
along it. -/
structure LabelDenotation {size : Nat} {Length : Type}
    (lengthValue : Length → Nat)
    (relation : Length → Fin size → Fin size → Bool)
    {Carrier : Type uCarrier}
    (labels : Finset Carrier)
    (Meaning : Nat → Carrier → Carrier → Prop)
    [∀ shift source target, Decidable (Meaning shift source target)] where
  /-- The object a row index names. -/
  denote : Fin size → Carrier
  /-- Every row index names one of the carrier's objects. -/
  denote_mem : ∀ index, denote index ∈ labels
  /-- Distinct row indices name distinct objects. -/
  denote_injective : Function.Injective denote
  /-- Every object of the carrier is named by a row index. -/
  denote_surjective : ∀ label ∈ labels, ∃ index, denote index = label
  /-- The audited relation is the stated relation on the objects named. -/
  relation_denote : ∀ length source target,
    relation length source target =
      decide (Meaning (lengthValue length) (denote source) (denote target))

namespace LabelDenotation

variable {size : Nat} {Length : Type} {lengthValue : Length → Nat}
  {relation : Length → Fin size → Fin size → Bool}
  {Carrier : Type uCarrier} {labels : Finset Carrier}
  {Meaning : Nat → Carrier → Carrier → Prop}
  [∀ shift source target, Decidable (Meaning shift source target)]

/-- **The generated carrier size is the named carrier's cardinality.**  This is
the theorem a bare `SemanticCertificate` cannot state: it turns the `size` a
generator wrote into the profile's type into a count of the application's own
finite object. -/
theorem labels_card
    (denotation : LabelDenotation lengthValue relation labels Meaning) :
    labels.card = size := by
  classical
  have image : Finset.image denotation.denote Finset.univ = labels := by
    ext label
    rw [Finset.mem_image]
    constructor
    · rintro ⟨index, _, named⟩
      exact named ▸ denotation.denote_mem index
    · intro member
      obtain ⟨index, named⟩ := denotation.denote_surjective label member
      exact ⟨index, Finset.mem_univ index, named⟩
  rw [← image, Finset.card_image_of_injective _ denotation.denote_injective,
    Finset.card_univ, Fintype.card_fin]

end LabelDenotation

/-- The exact finite local algebra of a certified bit-relation table whose row
indices carry a proved interpretation.  The registration is the one
`ofBitRelationTable` builds; what this entry point adds is that it cannot be
built without the denotation, so no application registers an uninterpreted
carrier. -/
def ofDenotedBitRelationTable
    {size : Nat} {profile : Profile size}
    {Length : Type} {lengthValue : Length → Nat}
    {relation : Length → Fin size → Fin size → Bool}
    {Carrier : Type uCarrier} {labels : Finset Carrier}
    {Meaning : Nat → Carrier → Carrier → Prop}
    [∀ shift source target, Decidable (Meaning shift source target)]
    [labelEnum : FinEnum (Fin size)] [lengthEnum : FinEnum Length]
    (certificate : SemanticCertificate profile Length lengthValue relation)
    (_denotation : LabelDenotation lengthValue relation labels Meaning)
    (Input : Type uInput) :
    Registration.{uInput, 0, 0, 0} Input :=
  ofBitRelationTable certificate Input

/-- **The registered relation is the application's stated relation.**  Read at
the registration Core executes, not at the source model the certificate was
audited against. -/
theorem ofDenotedBitRelationTable_relation
    {size : Nat} {profile : Profile size}
    {Length : Type} {lengthValue : Length → Nat}
    {relation : Length → Fin size → Fin size → Bool}
    {Carrier : Type uCarrier} {labels : Finset Carrier}
    {Meaning : Nat → Carrier → Carrier → Prop}
    [∀ shift source target, Decidable (Meaning shift source target)]
    [FinEnum (Fin size)] [FinEnum Length]
    (certificate : SemanticCertificate profile Length lengthValue relation)
    (denotation : LabelDenotation lengthValue relation labels Meaning)
    (Input : Type uInput) (input : Input) (length : Length)
    (source target : Fin size) :
    (ofDenotedBitRelationTable certificate denotation Input).semantics.relation
        input length source target =
      decide (Meaning (lengthValue length) (denotation.denote source)
        (denotation.denote target)) :=
  denotation.relation_denote length source target

end Hypostructure.Core.Strategy.ExactFiniteLocalAlgebra
