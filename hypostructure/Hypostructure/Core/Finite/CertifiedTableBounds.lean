import Hypostructure.Core.Finite.CertifiedTableAggregation
import Hypostructure.Core.FiniteEntropy

/-!
# Numeric bounds derived from certified finite tables

Constructors in this module infer every numeric parameter from either a
certified table projection or the type of an already-proved inequality.
They are intentionally theorem-driven: there is no wildcard-filled structure
literal and no second copy of a computed product or exponent.
-/

namespace Hypostructure.Core.Finite.CertifiedTableBounds

open Hypostructure.Core.FiniteBitRelationBarrier
open Hypostructure.Core.Finite.CertifiedTableAggregation

/-- A power bound whose exponent and endpoints are indices of its proof.
Use `ofProof`; applications never fill this structure directly. -/
structure PowerBound (base lower upper : Nat) where
  exponent : Nat
  bound : base ^ exponent * lower < upper

namespace PowerBound

/-- Derive a power-bound value from a certified inequality.  All four numeric
parameters are inferred from the theorem's type. -/
def ofProof {base exponent lower upper : Nat}
    (bound : base ^ exponent * lower < upper) :
    PowerBound base lower upper where
  exponent := exponent
  bound := bound

@[simp] theorem ofProof_exponent {base exponent lower upper : Nat}
    (bound : base ^ exponent * lower < upper) :
    (ofProof bound).exponent = exponent := rfl

end PowerBound

section BarrierTable

variable {size : Nat} {profile : Profile size}
variable {Length : Type*} {lengthValue : Length -> Nat}
variable {relation : Length -> Fin size -> Fin size -> Bool}
variable {Index : Type*} [Fintype Index]

/-- A binary rate floor whose products are definitionally derived from one
certified table.  The exponent is inferred from the supplied theorem. -/
def binaryRateFloor
    (table : CertifiedTable profile Length lengthValue relation Index)
    {exponent : Nat}
    (flatPositive : 0 < flatProduct table)
    (bound : 2 ^ exponent * flatProduct table < safeProduct table) :
    Hypostructure.Core.FiniteEntropy.RateFloorCertificate :=
  .ofComputedRate flatPositive bound

@[simp] theorem binaryRateFloor_exponent
    (table : CertifiedTable profile Length lengthValue relation Index)
    {exponent : Nat}
    (flatPositive : 0 < flatProduct table)
    (bound : 2 ^ exponent * flatProduct table < safeProduct table) :
    (binaryRateFloor table flatPositive bound).k = exponent := rfl

@[simp] theorem binaryRateFloor_flat
    (table : CertifiedTable profile Length lengthValue relation Index)
    {exponent : Nat}
    (flatPositive : 0 < flatProduct table)
    (bound : 2 ^ exponent * flatProduct table < safeProduct table) :
    (binaryRateFloor table flatPositive bound).flat = flatProduct table := rfl

@[simp] theorem binaryRateFloor_safe
    (table : CertifiedTable profile Length lengthValue relation Index)
    {exponent : Nat}
    (flatPositive : 0 < flatProduct table)
    (bound : 2 ^ exponent * flatProduct table < safeProduct table) :
    (binaryRateFloor table flatPositive bound).safe = safeProduct table := rfl

end BarrierTable

end Hypostructure.Core.Finite.CertifiedTableBounds
