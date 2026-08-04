import Hypostructure.CTAdapters
import Hypostructure.Core.Strategy.FiniteBarrierEnumerationSemantics

/-!
# Finite barrier enumeration

A domain-neutral CT16 Strategy which filters a complete residual-owned
candidate schedule, computes every safe/flat barrier count from the semantic
bit-relation profile, and appends the computed table to the literal
predecessor ledger.  Registrations contain no stored count, product, rate,
terminal, route, or execution result.
-/

namespace Hypostructure.Core.Strategy.FiniteBarrierEnumeration

open Hypostructure
open Hypostructure.Core.Residual

universe uPrevious uResidual uCandidate

/-- Lift inert residual semantics to one exact accumulated ledger stage. -/
structure Profile (Previous : Type uPrevious) (Residual : Type uResidual)
    [HasResidual Previous Residual] where
  registration : Registration.{uResidual, uCandidate} Residual
  /-- The object whose curvature table is enumerated.  It defaults to the
  incoming residual; a compiler that has already rebased onto a selected
  minimal counterexample passes that query instead, so the accepted schedule
  and the derived barrier summary speak about the same object as the
  strategies that produced this node's inputs. -/
  current : Query Previous (fun _ => Residual) := Query.residual

namespace Profile

variable [HasResidual Previous Residual]
variable (profile : Profile.{uPrevious, uResidual, uCandidate}
  Previous Residual)

abbrev Candidate (previous : Previous) :=
  profile.registration.Candidate (profile.current.read previous)

abbrev Accepted (previous : Previous) :=
  {candidate : profile.Candidate previous //
    profile.registration.accepted (profile.current.read previous) candidate}

def acceptedSchedule (previous : Previous) :
    Core.Finite.CompleteEnumeration (profile.Accepted previous) :=
  (profile.registration.candidates (profile.current.read previous)).subtype
    (profile.registration.accepted (profile.current.read previous))
    (profile.registration.acceptedDecidable (profile.current.read previous))

def countRow (previous : Previous) (index : profile.Accepted previous) :
    Nat × Nat :=
  let residual := profile.current.read previous
  let table := profile.registration.profile residual
  (table.safeCount (profile.registration.leftLength residual index)
      (profile.registration.rightLength residual index),
    table.flatCount (profile.registration.leftLength residual index)
      (profile.registration.rightLength residual index))

def rows (previous : Previous) : List (Nat × Nat) :=
  (profile.acceptedSchedule previous).values.map (profile.countRow previous)

/-! ### Positivity of the generated flat column

The flatness cost the manuscript reads off this table is the *ratio*
`γ_{a,b} = log₂(W_{a,b} / F_{a,b})`, so `F` -- the generated flat column -- is a
denominator.  Consumers used to take its positivity as a bare hypothesis; it is
a fact about the registered presentation, and this is where the registration's
`flatCount_pos` obligation becomes the derived summary's positivity. -/

/-- **Every generated flat entry is positive.**  Read straight off the
registration's obligation at the exact accepted index the row was generated
from; no count is recomputed. -/
theorem countRow_snd_pos (previous : Previous)
    (index : profile.Accepted previous) :
    0 < (profile.countRow previous index).2 :=
  profile.registration.flatCount_pos (profile.current.read previous) index

/-- **`0 < flatProduct` of the derived summary.**

`flatProduct` is the product of the generated flat column over the accepted
schedule, and every factor is positive by the registration's `flatCount_pos`.
Nothing about the table is recomputed and no numeral appears: the schedule is
the one `acceptedSchedule` filtered and the entries are the ones `countRow`
generated. -/
theorem flatProduct_pos (previous : Previous) :
    0 < (Summary.ofRows (profile.rows previous)).flatProduct := by
  rw [Summary.ofRows_flatProduct, rows, List.map_map]
  refine List.prod_pos ?_
  intro entry member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact profile.countRow_snd_pos previous index

section ScheduleAlgebra

universe uValue uIndex uColumn

/-- Restricting a lexicographic product by a predicate that only inspects the
second component keeps, for each left member, the restriction of the right
schedule.  Stated on the mapped column so it is directly usable on generated
count rows. -/
theorem subtype_product_values_map
    {Index : Type uIndex} {Value : Type uValue} {Column : Type uColumn}
    (left : Core.Finite.Enumeration Index)
    (right : Core.Finite.Enumeration Value)
    (predicate : Value → Prop)
    (decidePredicate : (value : Value) → Decidable (predicate value))
    (column : {value : Index × Value // predicate value.2} → Column) :
    (((left.product right).subtype (fun value => predicate value.2)
        (fun value => decidePredicate value.2)).values.map column)
      = left.values.flatMap (fun index =>
          ((right.subtype predicate decidePredicate).values.map
            fun value => column ⟨(index, value.1), value.2⟩)) := by
  rw [Core.Finite.Enumeration.subtype_values,
    Core.Finite.Enumeration.subtype_values]
  show (List.map column
    (List.filterMap _ (left.values ×ˢ right.values))) = _
  rw [show left.values ×ˢ right.values
        = left.values.flatMap (fun index => right.values.map (Prod.mk index))
      from by simp [SProd.sprod, List.product]]
  rw [List.filterMap_flatMap]
  rw [List.flatMap_def, List.flatMap_def, List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro index _
  simp only [Function.comp, List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro value _
  by_cases holds : predicate value <;> simp [holds]

/-- Concatenating one fixed block once per index multiplies its product. -/
theorem prod_flatMap_const {Index : Type uIndex} {M : Type uColumn}
    [CommMonoid M] (indices : List Index) (block : List M) :
    (indices.flatMap (fun _ => block)).prod = block.prod ^ indices.length := by
  induction indices with
  | nil => simp
  | cons _ tail ih =>
      simp [List.flatMap_cons, List.prod_append, ih, pow_succ, mul_comm]

end ScheduleAlgebra

section MultiScale

variable (registration : Registration.{uResidual, uCandidate} Residual)
variable (scaleCount : Residual → Nat)
variable (current : Query Previous fun _ => Residual)

/-- The scale-free profile of a registration. -/
abbrev scaleFree : Profile.{uPrevious, uResidual, uCandidate} Previous Residual :=
  { registration := registration, current := current }

/-- The same registration declared at `scaleCount` separated scales. -/
abbrev multiScale : Profile.{uPrevious, uResidual, uCandidate} Previous Residual :=
  { registration := registration.multiScale scaleCount, current := current }

/-- The generated count rows of a multi-scale package are the scale-free
count rows repeated once per scale.  Every scale carries the same barriers on
the same label carrier, so the two leg lengths — and hence the derived safe
and flat counts — of a barrier do not vary with the scale. -/
theorem rows_multiScale (previous : Previous) :
    (multiScale (Previous := Previous) registration scaleCount
        current).rows previous
      = (Core.Finite.Enumeration.ofFinEnum
            (inferInstance : FinEnum (Fin (scaleCount (current.read previous))))
          ).values.flatMap
          (fun _ => (scaleFree (Previous := Previous) registration current).rows
            previous) := by
  simp only [rows, acceptedSchedule, Registration.multiScale,
    Core.Finite.CompleteEnumeration.product,
    Core.Finite.CompleteEnumeration.subtype,
    Core.Finite.CompleteEnumeration.ofFinEnum]
  refine Eq.trans (subtype_product_values_map
    (left := (Core.Finite.Enumeration.ofFinEnum
      (inferInstance : FinEnum (Fin (scaleCount (current.read previous))))))
    (right := (registration.candidates (current.read previous)).toEnumeration)
    (predicate := registration.accepted (current.read previous))
    (decidePredicate :=
      registration.acceptedDecidable (current.read previous))
    (column := (multiScale (Previous := Previous) registration
      scaleCount current).countRow previous)) ?_
  exact List.flatMap_congr fun _ _ => rfl

omit [HasResidual Previous Residual] in
/-- The exact number of scheduled scales. -/
theorem scaleSchedule_length (previous : Previous) :
    (Core.Finite.Enumeration.ofFinEnum
        (inferInstance : FinEnum (Fin (scaleCount (current.read previous))))
      ).values.length = scaleCount (current.read previous) := by
  simpa [Core.Finite.Enumeration.card] using
    Core.Finite.Enumeration.card_ofFinEnum
      (inferInstance : FinEnum (Fin (scaleCount (current.read previous))))

/-- **The multi-scale safe demand is the scale-free one raised to the scale
count.**  This is the residual-dependence of the barrier rate: with
`scaleCount` derived from the residual, the package's exact state demand is
`safe₀ ^ scaleCount`, i.e. `scaleCount · log₂ safe₀` bits, not a fixed
numeral. -/
theorem safeProduct_multiScale (previous : Previous) :
    (Summary.ofRows ((multiScale (Previous := Previous) registration
        scaleCount current).rows previous)).safeProduct
      = (Summary.ofRows ((scaleFree (Previous := Previous)
          registration current).rows previous)).safeProduct ^
        scaleCount (current.read previous) := by
  rw [Summary.ofRows_safeProduct, Summary.ofRows_safeProduct,
    rows_multiScale, List.map_flatMap, prod_flatMap_const,
    scaleSchedule_length]

/-- The multi-scale flat count is the scale-free one raised to the same scale
count, so the derived *ratio* — the entropy rate — is exactly `scaleCount`
times the scale-free rate. -/
theorem flatProduct_multiScale (previous : Previous) :
    (Summary.ofRows ((multiScale (Previous := Previous) registration
        scaleCount current).rows previous)).flatProduct
      = (Summary.ofRows ((scaleFree (Previous := Previous)
          registration current).rows previous)).flatProduct ^
        scaleCount (current.read previous) := by
  rw [Summary.ofRows_flatProduct, Summary.ofRows_flatProduct,
    rows_multiScale, List.map_flatMap, prod_flatMap_const,
    scaleSchedule_length]

/-- **The residual-derived barrier rate.**  Whatever rate the scale-free
schedule certifies, the multi-scale package certifies exactly `scaleCount`
times it.

Read with `scaleCount` the object's separated dyadic scale count, this is the
manuscript's per-window package rate: the scale-free rate is `c₁₃`, the number
of scales is `log₂ n`, and the package's exact multiplicative state demand is
`safe₀ ^ scaleCount` against `flat₀ ^ scaleCount` — `c₁₃ · log₂ n` bits, i.e.
`n ^ c₁₃` states.  Both factors are read: `rate` from the generated
`Summary` of the registered table, `scaleCount` from the residual.  No numeral
enters. -/
theorem two_pow_rate_mul_scaleCount_mul_flatProduct_le_safeProduct
    (previous : Previous) {rate : Nat}
    (scaleFreeRate :
      2 ^ rate * (Summary.ofRows ((scaleFree (Previous := Previous)
          registration current).rows previous)).flatProduct ≤
        (Summary.ofRows ((scaleFree (Previous := Previous)
          registration current).rows previous)).safeProduct) :
    2 ^ (rate * scaleCount (current.read previous)) *
        (Summary.ofRows ((multiScale (Previous := Previous) registration
          scaleCount current).rows previous)).flatProduct ≤
      (Summary.ofRows ((multiScale (Previous := Previous) registration
        scaleCount current).rows previous)).safeProduct := by
  rw [safeProduct_multiScale, flatProduct_multiScale, pow_mul, ← mul_pow]
  exact Nat.pow_le_pow_left scaleFreeRate _

end MultiScale

inductive RelationCountPhase
  | safe
  | flat
  deriving DecidableEq, Fintype

inductive LabelNestingLevel
  | source
  | target
  deriving DecidableEq, Fintype

inductive WorkNestingLevel
  | candidate
  | sourceLabel
  | targetLabel
  deriving DecidableEq, Fintype

def relationCountPhaseEquiv : RelationCountPhase ≃ Bool where
  toFun
    | .safe => false
    | .flat => true
  invFun
    | false => .safe
    | true => .flat
  left_inv := by intro phase; cases phase <;> rfl
  right_inv := by intro value; cases value <;> rfl

def labelNestingLevelEquiv : LabelNestingLevel ≃ Bool where
  toFun
    | .source => false
    | .target => true
  invFun
    | false => .source
    | true => .target
  left_inv := by intro level; cases level <;> rfl
  right_inv := by intro value; cases value <;> rfl

def workNestingLevelEquiv : WorkNestingLevel ≃ Option Bool where
  toFun
    | .candidate => none
    | .sourceLabel => some false
    | .targetLabel => some true
  invFun
    | none => .candidate
    | some false => .sourceLabel
    | some true => .targetLabel
  left_inv := by intro level; cases level <;> rfl
  right_inv := by
    intro value
    cases value with
    | none => rfl
    | some value => cases value <;> rfl

def aggregationPhaseEquiv :
    Summary.AggregationPhase ≃ WorkNestingLevel where
  toFun
    | .safeProduct => .candidate
    | .flatProduct => .sourceLabel
    | .binaryRateFloor => .targetLabel
  invFun
    | .candidate => .safeProduct
    | .sourceLabel => .flatProduct
    | .targetLabel => .binaryRateFloor
  left_inv := by intro phase; cases phase <;> rfl
  right_inv := by intro level; cases level <;> rfl

/-- The polynomial coefficient is derived from the closed relation-count and
summary-aggregation phase types. -/
def workCoefficient : Nat :=
  Fintype.card RelationCountPhase + Summary.aggregationChecksPerRow

/-- Maximum nesting of the label carrier in one relation-count phase. -/
def relationNestingDepth : Nat :=
  Fintype.card LabelNestingLevel

/-- The polynomial degree is the number of nested finite carriers inspected
by the closed evaluator. -/
def workDegree : Nat :=
  Fintype.card WorkNestingLevel

def primitiveChecks (previous : Previous) : Nat :=
  (profile.acceptedSchedule previous).card *
    let size :=
      profile.registration.labelCount (profile.current.read previous)
    (size + size ^ relationNestingDepth +
      Summary.aggregationChecksPerRow)

def inputSize (previous : Previous) : Nat :=
  (profile.acceptedSchedule previous).card +
    profile.registration.labelCount (profile.current.read previous)

def spec : CT16.Spec Previous where
  Coordinate := profile.Accepted
  InSupport := fun _ _ => True
  ClosedCode := fun _ => Summary
  closedCode := fun previous => Summary.ofRows (profile.rows previous)
  targetCode := fun previous => Summary.ofRows (profile.rows previous)

def computation : CT16.ClosedCodeComputation profile.spec where
  run := fun previous =>
    ⟨Summary.ofRows (profile.rows previous), profile.primitiveChecks previous⟩
  correct := fun _ => rfl
  budget := {
    size := profile.inputSize
    checks := profile.primitiveChecks
    coefficient := workCoefficient
    degree := workDegree
    bounded := by
      intro previous
      simp only [primitiveChecks, inputSize]
      let rows := (profile.acceptedSchedule previous).card
      let labels :=
        profile.registration.labelCount (profile.current.read previous)
      change rows * (labels + labels ^ relationNestingDepth +
          Summary.aggregationChecksPerRow) ≤
        workCoefficient * (rows + labels + 1) ^ workDegree
      let total := rows + labels + 1
      have rows_le : rows ≤ total := by
        omega
      have labels_le : labels ≤ total := by
        omega
      have nested_le :
          labels ^ relationNestingDepth ≤
            total ^ relationNestingDepth :=
        Nat.pow_le_pow_left labels_le relationNestingDepth
      calc
        rows * (labels + labels ^ relationNestingDepth +
            Summary.aggregationChecksPerRow) ≤
            total * (total + total ^ relationNestingDepth +
              Summary.aggregationChecksPerRow) :=
          Nat.mul_le_mul rows_le
            (Nat.add_le_add (Nat.add_le_add labels_le nested_le)
              (le_refl Summary.aggregationChecksPerRow))
        _ ≤ workCoefficient * total ^ workDegree := by
          have total_pos : 0 < total := by simp [total]
          have relationCard :
              Fintype.card RelationCountPhase = Fintype.card Bool :=
            Fintype.card_congr relationCountPhaseEquiv
          have labelCard :
              Fintype.card LabelNestingLevel = Fintype.card Bool :=
            Fintype.card_congr labelNestingLevelEquiv
          have workCard :
              Fintype.card WorkNestingLevel = Fintype.card (Option Bool) :=
            Fintype.card_congr workNestingLevelEquiv
          have aggregationCard :
              Fintype.card Summary.AggregationPhase =
                Fintype.card WorkNestingLevel :=
            Fintype.card_congr aggregationPhaseEquiv
          rw [workCoefficient, Summary.aggregationChecksPerRow,
            relationNestingDepth, workDegree, relationCard, labelCard,
            aggregationCard, workCard]
          norm_num
          nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt total_pos)]
  }
  checks_eq := fun _ => rfl

def equalityDecision : CT16.CodeEqualityDecision profile.spec :=
  CT16.CodeEqualityDecision.unitCost profile.inputSize
    (fun _ => inferInstanceAs (DecidableEq Summary))

def capability : CT16.Capability profile.spec where
  coordinates :=
    Query.ofFunction fun previous =>
      (profile.acceptedSchedule previous).toEnumeration
  inSupportDecidable := fun _ _ => .isTrue trivial
  codeComputation := profile.computation
  equalityDecision := profile.equalityDecision

/-- The sealed Strategy is exactly one canonical CT16 execution. -/
noncomputable def execution : Core.Strategy.CTExecution Previous :=
  CTAdapters.ct16 profile.capability

/-- Recover the literal summary stored in one generated CT16 ledger entry. -/
private def summaryOfGenerated (previous : Previous)
    (generated : CT16.Generated profile.spec profile.capability previous) :
    Summary :=
  match generated.terminal, generated.outcome with
  | .properSupport, .properSupport residual =>
      False.elim (residual.absent trivial)
  | .exactCode, .exactCode certificate =>
      certificate.state.code
  | .mismatch, .mismatch residual =>
      False.elim (residual.notEqual residual.state.exact)

/-- Recover the literal summary stored by CT16.  The finite-barrier profile
has total support and definitionally identical closed and target codes, so
the proper-support and mismatch constructors are impossible.  This projection
does not rerun the table computation: it reads `ClosedCodeState.code` from
the retained execution result. -/
def summaryOfExecution
    (result : CT16.ExecutionResult profile.spec profile.capability) :
    Summary :=
  profile.summaryOfGenerated result.stage.previous result.stage.added

/-- **The retained summary is the one Core derived.**

`summaryOfExecution` reads `ClosedCodeState.code` off the retained CT16 result,
and that field carries its own semantic equality with `Spec.closedCode`
(`ClosedCodeState.exact`), which for this profile is literally
`Summary.ofRows (rows previous)`.  The projection therefore does not merely
*happen* to agree with the aggregation of the generated rows: it is that
aggregation, proved, with the two impossible terminals eliminated exactly as in
`summaryOfGenerated`. -/
theorem summaryOfGenerated_eq (previous : Previous)
    (generated : CT16.Generated profile.spec profile.capability previous) :
    profile.summaryOfGenerated previous generated =
      Summary.ofRows (profile.rows previous) := by
  unfold summaryOfGenerated
  match generated.terminal, generated.outcome with
  | .properSupport, .properSupport residual =>
      exact False.elim (residual.absent trivial)
  | .exactCode, .exactCode certificate =>
      exact certificate.state.exact
  | .mismatch, .mismatch residual =>
      exact False.elim (residual.notEqual residual.state.exact)

theorem summaryOfExecution_eq
    (result : CT16.ExecutionResult profile.spec profile.capability) :
    profile.summaryOfExecution result =
      Summary.ofRows (profile.rows result.stage.previous) :=
  profile.summaryOfGenerated_eq result.stage.previous result.stage.added

/-- **The retained summary is `Derived`.**  The one fact a downstream consumer
needs in order to read `binaryRateFloor` as a genuine `log₂` of the retained
aggregation columns, and it is a theorem about the execution, not a field a
registration could supply. -/
theorem summaryOfExecution_derived
    (result : CT16.ExecutionResult profile.spec profile.capability) :
    Summary.Derived (profile.summaryOfExecution result) := by
  rw [profile.summaryOfExecution_eq result]
  exact Summary.derived_ofRows _

/-- **The retained summary's flat column is positive.**  `flatProduct_pos`
transported along `summaryOfExecution_eq`, so the density comparison's
denominator is nonvanishing on the retained ledger entry rather than by
hypothesis. -/
theorem summaryOfExecution_flatProduct_pos
    (result : CT16.ExecutionResult profile.spec profile.capability) :
    0 < (profile.summaryOfExecution result).flatProduct := by
  rw [profile.summaryOfExecution_eq result]
  exact profile.flatProduct_pos result.stage.previous

end Profile

end Hypostructure.Core.Strategy.FiniteBarrierEnumeration
