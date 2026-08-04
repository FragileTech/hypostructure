import Hypostructure.Core.FiniteBitRelationBarrier
import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Residual-indexed finite barrier presentation

Only irreducible finite semantics live here.  Terminals, work, and routing
are deliberately absent.  `Summary` is the one produced result type: it is a
plain record of `Nat`/`List (Nat × Nat)` fields with no dependence on `CT16`,
`Previous`, or `Residual`, so it lives here (not in the CT-heavy
`FiniteBarrierEnumeration.lean`) precisely so that residual-only consumers,
including other Strategies' `Registration` records, can name it without
pulling in CT machinery.
-/

namespace Hypostructure.Core.Strategy.FiniteBarrierEnumeration

universe uResidual uCandidate uStage uNew

structure Registration (Residual : Type uResidual) where
  Candidate : Residual → Type uCandidate
  candidates : (residual : Residual) →
    Core.Finite.CompleteEnumeration (Candidate residual)
  accepted : (residual : Residual) → Candidate residual → Prop
  acceptedDecidable : (residual : Residual) →
    (candidate : Candidate residual) → Decidable (accepted residual candidate)
  labelCount : Residual → Nat
  relationPosition : Residual → Nat → Nat
  leftLength : (residual : Residual) → Candidate residual → Nat
  rightLength : (residual : Residual) → Candidate residual → Nat

namespace Registration

variable {Residual : Type uResidual}

/-- Replicate one scale-free barrier schedule across a residual-derived
number of separated scales.

A registered barrier schedule lists the finite relation barriers carried by
*one* package instance.  A package that is declared at several separated
scales carries every one of those barriers once per scale, so its schedule is
the scale index paired with the scale-free schedule and its accepted subfamily
is the scale-free accepted subfamily at each scale.  Nothing else changes:
the label carrier, the bit-relation profile, and the two leg lengths of an
accepted barrier are read from the underlying registration, so the derived
safe/flat counts of a barrier are the same at every scale.

The scale count is a function of the residual, so the entropy demand this
schedule generates is residual-derived and not a fixed numeral.  With
`scaleCount` the number of separated dyadic scales available in an object of
order `n`, the derived products of `Summary.ofRows` are the scale-free
products raised to `scaleCount` (`rows_multiScale`,
`safeProduct_multiScale`, `flatProduct_multiScale` in
`FiniteBarrierEnumeration.lean`), i.e. the package demands
`scaleCount · log₂(safe/flat)` bits rather than `log₂(safe/flat)`. -/
def multiScale (registration : Registration.{uResidual, uCandidate} Residual)
    (scaleCount : Residual → Nat) :
    Registration.{uResidual, uCandidate} Residual where
  Candidate := fun residual =>
    Fin (scaleCount residual) × registration.Candidate residual
  candidates := fun residual =>
    (Core.Finite.CompleteEnumeration.ofFinEnum
        (inferInstance : FinEnum (Fin (scaleCount residual)))).product
      (registration.candidates residual)
  accepted := fun residual candidate =>
    registration.accepted residual candidate.2
  acceptedDecidable := fun residual candidate =>
    registration.acceptedDecidable residual candidate.2
  labelCount := registration.labelCount
  relationPosition := registration.relationPosition
  leftLength := fun residual index =>
    registration.leftLength residual index.2
  rightLength := fun residual index =>
    registration.rightLength residual index.2

@[simp] theorem multiScale_labelCount
    (registration : Registration.{uResidual, uCandidate} Residual)
    (scaleCount : Residual → Nat) (residual : Residual) :
    (registration.multiScale scaleCount).labelCount residual =
      registration.labelCount residual := rfl

end Registration

/-- Complete derived barrier summary.  Every field is computed by Core from
the generated rows; registrations cannot provide any of them. -/
structure Summary where
  rows : List (Nat × Nat)
  safeProduct : Nat
  flatProduct : Nat
  binaryRateFloor : Nat
  deriving DecidableEq, Repr

namespace Summary

inductive AggregationPhase
  | safeProduct
  | flatProduct
  | binaryRateFloor
  deriving DecidableEq, Fintype

/-- Core derives the aggregation cost from the closed phase type. -/
def aggregationChecksPerRow : Nat :=
  Fintype.card AggregationPhase

def ofRows (rows : List (Nat × Nat)) : Summary :=
  let safeProduct := (rows.map Prod.fst).prod
  let flatProduct := (rows.map Prod.snd).prod
  let binaryRateFloor :=
    if flatProduct = 0 then 0
    else Nat.log2 ((safeProduct - 1) / flatProduct)
  { rows, safeProduct, flatProduct, binaryRateFloor }

/-- Read one scheduled barrier row of an already-derived summary.

`rows` is the exact generated safe/flat column pair of the barrier schedule,
in schedule order, so `rowAt position` is the single-barrier granularity of
the same derived table whose full multiplicative totals are `safeProduct` and
`flatProduct`.  A consumer that needs the rate of one named barrier reads it
here instead of registering a second table.

A position past the end of the schedule reads the multiplicatively neutral
row `(1, 1)`: it is the unit of both aggregation columns, so an absent row
contributes nothing to any product or ratio taken over `rowAt`, exactly as an
absent row contributes nothing to `safeProduct`/`flatProduct`.  This keeps the
accessor total without a nonemptiness hypothesis. -/
def rowAt (summary : Summary) (position : Nat) : Nat × Nat :=
  summary.rows.getD position (1, 1)

/-- Safe count of one scheduled barrier row. -/
def safeAt (summary : Summary) (position : Nat) : Nat :=
  (summary.rowAt position).1

/-- Flat count of one scheduled barrier row. -/
def flatAt (summary : Summary) (position : Nat) : Nat :=
  (summary.rowAt position).2

/-- The composition-obstructed count of one retained barrier row.  It is
computed solely from the safe and flat entries CT16 appended to `rows`. -/
def obstructedAt (summary : Summary) (position : Nat) : Nat :=
  summary.safeAt position - summary.flatAt position

/-- The exact base-two cost of one retained barrier row.  This reads the
generated safe and flat columns from the CT16 summary; it never reconstructs
the schedule or accepts a caller-supplied count. -/
noncomputable def rowRate (summary : Summary) (position : Nat) : ℝ :=
  Real.logb 2 ((summary.safeAt position : ℝ) / (summary.flatAt position : ℝ))

/-- The exact finite-table rate in its schedule form: one logarithmic cost for
each generated barrier row, summed in the retained schedule order. -/
noncomputable def scheduleRate (summary : Summary) : ℝ :=
  (summary.rows.map fun row =>
    Real.logb 2 ((row.1 : ℝ) / (row.2 : ℝ))).sum

/-- The same finite-table rate read from the aggregate columns.  This form is
useful for multiplicative capacity comparisons; `scheduleRate` is the
per-barrier accounting form. -/
noncomputable def windowRate (summary : Summary) : ℝ :=
  Real.logb 2 ((summary.safeProduct : ℝ) / (summary.flatProduct : ℝ))

@[simp] theorem rowAt_of_lt (summary : Summary) {position : Nat}
    (inRange : position < summary.rows.length) :
    summary.rowAt position = summary.rows[position] := by
  simp [rowAt, List.getElem?_eq_getElem inRange]

@[simp] theorem ofRows_rows (rows : List (Nat × Nat)) :
    (ofRows rows).rows = rows := rfl

@[simp] theorem ofRows_rowAt (rows : List (Nat × Nat)) (position : Nat) :
    (ofRows rows).rowAt position = rows.getD position (1, 1) := rfl

@[simp] theorem ofRows_safeProduct (rows : List (Nat × Nat)) :
    (ofRows rows).safeProduct = (rows.map Prod.fst).prod := rfl

@[simp] theorem ofRows_flatProduct (rows : List (Nat × Nat)) :
    (ofRows rows).flatProduct = (rows.map Prod.snd).prod := rfl

@[simp] theorem ofRows_rowRate (rows : List (Nat × Nat)) (position : Nat) :
    (ofRows rows).rowRate position =
      Real.logb 2 (((rows.getD position (1, 1)).1 : ℝ) /
        ((rows.getD position (1, 1)).2 : ℝ)) :=
  rfl

@[simp] theorem ofRows_obstructedAt (rows : List (Nat × Nat)) (position : Nat) :
    (ofRows rows).obstructedAt position =
      (rows.getD position (1, 1)).1 - (rows.getD position (1, 1)).2 :=
  rfl

@[simp] theorem ofRows_scheduleRate (rows : List (Nat × Nat)) :
    (ofRows rows).scheduleRate =
      (rows.map fun row => Real.logb 2 ((row.1 : ℝ) / (row.2 : ℝ))).sum :=
  rfl

@[simp] theorem ofRows_windowRate (rows : List (Nat × Nat)) :
    (ofRows rows).windowRate =
      Real.logb 2 (((rows.map Prod.fst).prod : ℝ) /
        ((rows.map Prod.snd).prod : ℝ)) :=
  rfl

@[simp] theorem ofRows_binaryRateFloor (rows : List (Nat × Nat)) :
    (ofRows rows).binaryRateFloor =
      (if (ofRows rows).flatProduct = 0 then 0
        else Nat.log2 (((ofRows rows).safeProduct - 1) /
          (ofRows rows).flatProduct)) := rfl

/-- **The derived rate really is a rate.**  `binaryRateFloor` is computed by
Core from the two aggregation columns alone, and this is the inequality it
certifies: the derived table's own safe column dominates its flat column by at
least `2 ^ binaryRateFloor`.

No numeral occurs: the exponent is the summary's own field, itself a `log₂` of
the generated `safeProduct`/`flatProduct` pair, so a consumer that needs "the
rate of the registered barrier table" reads it from the ledger instead of
restating it. -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le
    (rows : List (Nat × Nat))
    (flatPositive : 0 < (ofRows rows).flatProduct)
    (improves : (ofRows rows).flatProduct ≤ (ofRows rows).safeProduct) :
    2 ^ (ofRows rows).binaryRateFloor * (ofRows rows).flatProduct ≤
      (ofRows rows).safeProduct := by
  set flat := (ofRows rows).flatProduct with flatDef
  set safe := (ofRows rows).safeProduct with safeDef
  rw [ofRows_binaryRateFloor, ← flatDef, ← safeDef,
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

/-! ### The rate algebra of a Core-derived summary

`Summary` is a plain record, so its three aggregation fields are unrelated to
one another *as data*.  They are related as soon as the record is the one Core
produced, because Core produces it by `ofRows` and nothing else.  `Derived` is
that provenance, stated without naming the rows a particular execution
generated, and every rate theorem below is proved from it. -/

/-- **A summary Core actually derived.**  Its aggregation columns are the
`ofRows` aggregation of its own retained row list, which is what makes
`binaryRateFloor` a `log₂` of `safeProduct`/`flatProduct` rather than a free
field.  Registrations cannot manufacture this: they supply no summary at
all. -/
def Derived (summary : Summary) : Prop :=
  summary = ofRows summary.rows

/-- Everything `ofRows` builds is derived, definitionally: `ofRows` retains its
argument in `rows`. -/
theorem derived_ofRows (rows : List (Nat × Nat)) : Derived (ofRows rows) := rfl

namespace Derived

variable {summary : Summary}

theorem safeProduct_eq (derived : Derived summary) :
    summary.safeProduct = (summary.rows.map Prod.fst).prod :=
  congrArg Summary.safeProduct derived

theorem flatProduct_eq (derived : Derived summary) :
    summary.flatProduct = (summary.rows.map Prod.snd).prod :=
  congrArg Summary.flatProduct derived

/-- The derived rate really is the `log₂` of the derived columns. -/
theorem binaryRateFloor_eq (derived : Derived summary) :
    summary.binaryRateFloor =
      if summary.flatProduct = 0 then 0
      else Nat.log2 ((summary.safeProduct - 1) / summary.flatProduct) := by
  conv_lhs => rw [derived, ofRows_binaryRateFloor]
  rw [← derived]

/-- **The rate floor of a derived summary.**  `Summary.two_pow_binaryRateFloor_mul_flatProduct_le`
stated on the retained record rather than on a literal `ofRows` application, so
a consumer that only ever sees the summary through a ledger query can use it. -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le
    (derived : Derived summary)
    (flatPositive : 0 < summary.flatProduct)
    (improves : summary.flatProduct ≤ summary.safeProduct) :
    2 ^ summary.binaryRateFloor * summary.flatProduct ≤ summary.safeProduct := by
  have base := Summary.two_pow_binaryRateFloor_mul_flatProduct_le summary.rows
    (by rw [ofRows_flatProduct, ← derived.flatProduct_eq]; exact flatPositive)
    (by
      rw [ofRows_flatProduct, ofRows_safeProduct, ← derived.flatProduct_eq,
        ← derived.safeProduct_eq]
      exact improves)
  rwa [← derived] at base

/-- A derived summary whose safe column never exceeds its flat column carries
no rate at all: the truncated quotient is zero, so is its `log₂`.

This is not a degenerate special case to be excluded by hypothesis -- it is
what `ofRows` computes, and stating it keeps `binaryRateFloor` a *total*
accessor whose meaning does not depend on an unstated nondegeneracy. -/
theorem binaryRateFloor_eq_zero_of_le
    (derived : Derived summary)
    (degenerate : summary.safeProduct ≤ summary.flatProduct) :
    summary.binaryRateFloor = 0 := by
  rw [derived.binaryRateFloor_eq]
  by_cases flatZero : summary.flatProduct = 0
  · rw [if_pos flatZero]
  · rw [if_neg flatZero]
    have quotientZero : (summary.safeProduct - 1) / summary.flatProduct = 0 :=
      Nat.div_eq_of_lt (by omega)
    rw [quotientZero]
    rfl

/-- **The rate floor, unconditionally.**  Either the derived rate is paid by the
derived columns, or the derived rate is zero.  No hypothesis at all: both
alternatives are computed by `ofRows`. -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero
    (derived : Derived summary) :
    2 ^ summary.binaryRateFloor * summary.flatProduct ≤ summary.safeProduct ∨
      summary.binaryRateFloor = 0 := by
  by_cases flatZero : summary.flatProduct = 0
  · exact Or.inr (by
      rw [derived.binaryRateFloor_eq, if_pos flatZero])
  · by_cases improves : summary.flatProduct ≤ summary.safeProduct
    · exact Or.inl (derived.two_pow_binaryRateFloor_mul_flatProduct_le
        (Nat.pos_of_ne_zero flatZero) improves)
    · exact Or.inr (derived.binaryRateFloor_eq_zero_of_le (by omega))

/-- **The rate ceiling.**  `binaryRateFloor` is a floor, so it under-reports the
true rate by strictly less than one bit:

  `safeProduct ≤ 2 ^ (binaryRateFloor + 1) · flatProduct`.

The successor is not slack that could be removed.  Floor and ceiling coincide
only when `safeProduct / flatProduct` is an exact power of two, so the two rates
must not be conflated: `two_pow_binaryRateFloor_mul_flatProduct_le`
is what a *demand* may be paid with, and this is what a *supply* may be charged
with. -/
theorem safeProduct_le_two_pow_succ_binaryRateFloor_mul_flatProduct
    (derived : Derived summary)
    (flatPositive : 0 < summary.flatProduct) :
    summary.safeProduct ≤
      2 ^ (summary.binaryRateFloor + 1) * summary.flatProduct := by
  rw [derived.binaryRateFloor_eq, if_neg (Nat.ne_of_gt flatPositive)]
  set flat := summary.flatProduct with flatDef
  set safe := summary.safeProduct with safeDef
  have quotientBound :
      (safe - 1) / flat < 2 ^ (Nat.log2 ((safe - 1) / flat) + 1) := by
    simpa [Nat.log2_eq_log_two] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((safe - 1) / flat)
  have expanded : safe - 1 <
      2 ^ (Nat.log2 ((safe - 1) / flat) + 1) * flat :=
    (Nat.div_lt_iff_lt_mul flatPositive).mp quotientBound
  omega

end Derived

end Summary

/-! ## The barrier node's rate ledger

`CapabilityKey.finiteBarrierSummary`'s payload is the bare `Summary` record.
That is enough to *read* the aggregation columns and nothing else: as data, a
`Summary` does not know that its `binaryRateFloor` was computed from its own
columns, nor that its flat column is nonzero.  Both facts are owned by the node
that produced it -- `Derived` because Core produced it by `ofRows`, flat
positivity because Core retains only rows passing its closed admissibility test -- so they travel in
a dedicated query-only ledger record, exactly as the surviving density cap
travels in `FiniteDensityBudget.CapLedger`.

Nothing is reconstructed and nothing is stored twice: `summary` is the very
query the density comparison is run on, and the other two fields are proofs
about that query's value. -/

/-- **Query-only view of the exact derived barrier table.** -/
structure RateLedger (Stage : Type uStage) where
  summary : Core.Residual.Query Stage (fun _ => Summary)
  sourceRows : Core.Residual.Query Stage (fun _ => List (Nat × Nat))
  exact : Core.Residual.Query Stage fun stage =>
    summary.read stage = Summary.ofRows (sourceRows.read stage)
  /-- The retained summary is the one Core derived from its own generated
  rows, so its `binaryRateFloor` is a genuine `log₂` of its own columns. -/
  derived : Core.Residual.Query Stage fun stage =>
    Summary.Derived (summary.read stage)
  /-- The registered accepted schedule's flat column is nonvanishing, so the
  flatness ratio `safeProduct / flatProduct` the manuscript takes `log₂` of is
  defined. -/
  flatPositive : Core.Residual.Query Stage fun stage =>
    0 < (summary.read stage).flatProduct

namespace RateLedger

open Core.Residual

def comap (ledger : RateLedger Stage) (project : NewStage → Stage) :
    RateLedger NewStage where
  summary := ledger.summary.comap project
  sourceRows := ledger.sourceRows.comap project
  exact := ledger.exact.comap project
  derived := ledger.derived.comap project
  flatPositive := ledger.flatPositive.comap project

def preserve {Added : Stage → Type uNew} (ledger : RateLedger Stage) :
    RateLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

def preserveProp {Added : Stage → Prop} (ledger : RateLedger Stage) :
    RateLedger (Ledger.Extension Stage Added) :=
  ledger.comap Ledger.Extension.previous

/-- Read the safe count of a retained barrier row from the CT16 ledger. -/
def safeAt (ledger : RateLedger Stage) (stage : Stage) (position : Nat) : Nat :=
  (ledger.summary.read stage).safeAt position

theorem summary_eq_ofRows (ledger : RateLedger Stage) (stage : Stage) :
    ledger.summary.read stage = Summary.ofRows (ledger.sourceRows.read stage) :=
  ledger.exact.read stage

/-- Read the flat count of a retained barrier row from the CT16 ledger. -/
def flatAt (ledger : RateLedger Stage) (stage : Stage) (position : Nat) : Nat :=
  (ledger.summary.read stage).flatAt position

/-- Read the composition-obstructed count of a retained barrier row from the
CT16 ledger. -/
def obstructedAt (ledger : RateLedger Stage) (stage : Stage)
    (position : Nat) : Nat :=
  (ledger.summary.read stage).obstructedAt position

/-- Read one exact barrier cost from the CT16-produced summary. -/
noncomputable def rowRate (ledger : RateLedger Stage) (stage : Stage)
    (position : Nat) : ℝ :=
  (ledger.summary.read stage).rowRate position

/-- Read the exact sum of all generated barrier costs from the CT16 ledger. -/
noncomputable def scheduleRate (ledger : RateLedger Stage) (stage : Stage) : ℝ :=
  (ledger.summary.read stage).scheduleRate

/-- Read the aggregate-product presentation of the same table rate from the
CT16 ledger. -/
noncomputable def windowRate (ledger : RateLedger Stage) (stage : Stage) : ℝ :=
  (ledger.summary.read stage).windowRate

/-- **The registered table's rate floor, read off the ledger.** -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le
    (ledger : RateLedger Stage) (stage : Stage)
    (improves : (ledger.summary.read stage).flatProduct ≤
      (ledger.summary.read stage).safeProduct) :
    2 ^ (ledger.summary.read stage).binaryRateFloor *
        (ledger.summary.read stage).flatProduct ≤
      (ledger.summary.read stage).safeProduct :=
  (ledger.derived.read stage).two_pow_binaryRateFloor_mul_flatProduct_le
    (ledger.flatPositive.read stage) improves

/-- **The registered table's rate ceiling, read off the ledger.**  The exponent
is `binaryRateFloor + 1`; the exact rate and its natural-number floor are kept
apart and never identified. -/
theorem safeProduct_le_two_pow_succ_binaryRateFloor_mul_flatProduct
    (ledger : RateLedger Stage) (stage : Stage) :
    (ledger.summary.read stage).safeProduct ≤
      2 ^ ((ledger.summary.read stage).binaryRateFloor + 1) *
        (ledger.summary.read stage).flatProduct :=
  (ledger.derived.read stage).safeProduct_le_two_pow_succ_binaryRateFloor_mul_flatProduct
    (ledger.flatPositive.read stage)

/-- The unconditional form of the rate floor, read off the ledger. -/
theorem two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero
    (ledger : RateLedger Stage) (stage : Stage) :
    2 ^ (ledger.summary.read stage).binaryRateFloor *
        (ledger.summary.read stage).flatProduct ≤
      (ledger.summary.read stage).safeProduct ∨
      (ledger.summary.read stage).binaryRateFloor = 0 :=
  (ledger.derived.read stage).two_pow_binaryRateFloor_mul_flatProduct_le_or_eq_zero

end RateLedger

end Hypostructure.Core.Strategy.FiniteBarrierEnumeration
