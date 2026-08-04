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

omit [Fintype Index] in
@[simp] theorem labelCount_eq
    (table : CertifiedTable profile Length lengthValue relation Index) :
    labelCount table = size := rfl

@[simp] theorem countRowCount_eq
    (table : CertifiedTable profile Length lengthValue relation Index) :
    countRowCount table = Fintype.card Index := rfl

end BarrierTable

end Hypostructure.Core.Finite.CertifiedTableAggregation
