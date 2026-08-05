import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Hypostructure.Core.FiniteBitRelationBarrier

/-!
# Derived parameters of certified finite tables

This module provides generic, executable projections from a certified finite
table.  Applications name the table and an index family; Core computes all
cardinalities and multiplicative column totals.  Consequently no application
has to copy a table-derived numeral into a strategy declaration.
-/

namespace Hypostructure.Core.Finite.CertifiedTableAggregation

open scoped BigOperators

/-- Product of a finite column. -/
def product {ι : Type*} [Fintype ι] (column : ι -> Nat) : Nat :=
  ∏ i, column i

/-- Cardinality of the finite row/index family over which a table aggregate
is computed. -/
def rowCount (ι : Type*) [Fintype ι] : Nat :=
  Fintype.card ι

@[simp] theorem product_empty (column : Empty -> Nat) :
    product column = 1 := by
  simp [product]

@[simp] theorem rowCount_eq (ι : Type*) [Fintype ι] :
    rowCount ι = Fintype.card ι := rfl

section BarrierTable

open Hypostructure.Core.FiniteBitRelationBarrier

variable {size : Nat} {profile : Profile size}
variable {Length : Type*} {lengthValue : Length -> Nat}
variable {relation : Length -> Fin size -> Fin size -> Bool}
variable {Index : Type*} [Fintype Index]

/-- The product of the certified safe-count column. -/
def safeProduct
    (table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
  product table.counts.storedSafe

/-- The product of the certified flat-count column. -/
def flatProduct
    (table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
  product table.counts.storedFlat

/-- Number of labels, derived from the table's row carrier. -/
def labelCount
    (_table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
  size

/-- Number of certified count rows. -/
def countRowCount
    (_table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
  rowCount Index

theorem safeProduct_eq_computed
    (table : CertifiedTable profile Length lengthValue relation Index) :
    safeProduct table =
      ∏ index, profile.safeCount (table.counts.leftLength index)
        (table.counts.rightLength index) := by
  apply Finset.prod_congr rfl
  intro index _
  exact table.storedSafe_eq index

theorem flatProduct_eq_computed
    (table : CertifiedTable profile Length lengthValue relation Index) :
    flatProduct table =
      ∏ index, profile.flatCount (table.counts.leftLength index)
        (table.counts.rightLength index) := by
  apply Finset.prod_congr rfl
  intro index _
  exact table.storedFlat_eq index

/-- **The binary rate a certified table sustains, as a natural number.**

The table's two columns multiply out to a safe total `S` and a flat total `F`;
the rate the table can pay per unit is `log₂ (S / F)`, and this is that rate
rounded down to a natural number in a way that stays *below* the real one:
`⌊log₂ ((S - 1) / F)⌋`.

Taking `S - 1` before dividing is what makes the floor safe.  The result
underestimates the true rate, so an inequality that holds at this rate holds at
the real one; `two_pow_binaryRateFloor_mul_flatProduct_le` is that guarantee. -/
def binaryRateFloor
    (table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
  if flatProduct table = 0 then 0
  else Nat.log2 ((safeProduct table - 1) / flatProduct table)

/-- **The derived rate really is a rate.**  The table's safe column dominates
its flat column by at least `2 ^ binaryRateFloor`, so a consumer that needs
"the rate of this certified table" reads it here rather than restating it.

No numeral occurs: the exponent is computed from the table's own two columns. -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le
    (table : CertifiedTable profile Length lengthValue relation Index)
    (flatPositive : 0 < flatProduct table)
    (improves : flatProduct table ≤ safeProduct table) :
    2 ^ binaryRateFloor table * flatProduct table ≤ safeProduct table := by
  set flat := flatProduct table with flatDef
  set safe := safeProduct table with safeDef
  rw [binaryRateFloor, ← flatDef, ← safeDef, if_neg (Nat.ne_of_gt flatPositive)]
  rcases Nat.eq_zero_or_pos ((safe - 1) / flat) with quotientZero | quotientPos
  · rw [quotientZero]
    simpa using improves
  · calc 2 ^ Nat.log2 ((safe - 1) / flat) * flat
        ≤ ((safe - 1) / flat) * flat := by
          refine Nat.mul_le_mul_right _ ?_
          simpa [Nat.log2_eq_log_two] using
            Nat.pow_log_le_self 2 (Nat.ne_of_gt quotientPos)
      _ ≤ safe - 1 := Nat.div_mul_le_self _ _
      _ ≤ safe := Nat.sub_le _ _

/-- **The binary rate one certified row sustains.**

`binaryRateFloor` reads the whole table's two column products, which is the rate
a package of every certified row pays.  A consumer that needs the rate of a
*single* row -- one flatness cost per test at one connector-length pair -- reads
it here.  The floor is taken the same safe way, on that row's own two stored
counts, so the value again underestimates the real rate. -/
def binaryRowRateFloor
    (table : CertifiedTable profile Length lengthValue relation Index)
    (index : Index) : Nat :=
  if table.counts.storedFlat index = 0 then 0
  else Nat.log2 ((table.counts.storedSafe index - 1) /
    table.counts.storedFlat index)

/-- **The derived row rate really is a rate**, by the same argument as for the
whole-table rate: the row's safe count dominates its flat count by at least
`2 ^ binaryRowRateFloor`. -/
theorem two_pow_binaryRowRateFloor_mul_storedFlat_le
    (table : CertifiedTable profile Length lengthValue relation Index)
    (index : Index)
    (flatPositive : 0 < table.counts.storedFlat index)
    (improves : table.counts.storedFlat index ≤ table.counts.storedSafe index) :
    2 ^ binaryRowRateFloor table index * table.counts.storedFlat index ≤
      table.counts.storedSafe index := by
  set flat := table.counts.storedFlat index with flatDef
  set safe := table.counts.storedSafe index with safeDef
  rw [binaryRowRateFloor, ← flatDef, ← safeDef,
    if_neg (Nat.ne_of_gt flatPositive)]
  rcases Nat.eq_zero_or_pos ((safe - 1) / flat) with quotientZero | quotientPos
  · rw [quotientZero]
    simpa using improves
  · calc 2 ^ Nat.log2 ((safe - 1) / flat) * flat
        ≤ ((safe - 1) / flat) * flat := by
          refine Nat.mul_le_mul_right _ ?_
          simpa [Nat.log2_eq_log_two] using
            Nat.pow_log_le_self 2 (Nat.ne_of_gt quotientPos)
      _ ≤ safe - 1 := Nat.div_mul_le_self _ _
      _ ≤ safe := Nat.sub_le _ _

omit [Fintype Index] in
@[simp] theorem labelCount_eq
    (table : CertifiedTable profile Length lengthValue relation Index) :
    labelCount table = size := rfl

@[simp] theorem countRowCount_eq
    (table : CertifiedTable profile Length lengthValue relation Index) :
    countRowCount table = Fintype.card Index := rfl

end BarrierTable

end Hypostructure.Core.Finite.CertifiedTableAggregation
