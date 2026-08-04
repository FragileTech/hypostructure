import Hypostructure.Graph.WindowCurvatureEnumeration

/-!
# Label codes: the certificate's index *is* a legal label

A generated finite-check certificate stores its safety relations as packed bit
rows indexed by a *label code*, and its audit relates the stored bits to an
executable relation on those codes.  That leaves one half of the dictionary
open: whether the code-indexed relation is the manuscript's `C_s` on actual
labels.  This file proves that half, in the framework and generically in the
path order.

* `labelOfCode` reads a packed code as a label, and is a bijection onto the
  labels of the order (`labelOfCode_injective`, `labelOfCode_surjective`).
* `codeCompatible` is the bitwise safety test -- `source &&& (target >>> d)`
  for every *derived* forbidden difference `d`, and its mirror -- and
  `codeCompatible_eq_true_iff` says it is exactly `Safe`, i.e. exactly `C_s`.
* `codeLegal` is the bitwise legality test and `codeLegal_eq_true_iff` says it
  is exactly `Legal`.
* `legalCodeList` is the ascending enumeration of legal codes, `labelAtIndex`
  is the resulting index, and `labelAtIndex_mem_Labels`,
  `labelAtIndex_injective`, `labelAtIndex_surjective` say the index is a
  bijection onto `Labels`.  Its length is `(Labels order).card`, hence `399` at
  the registered window order.
* `codeRelation_eq_safe` is the conclusion: the code-indexed relation *is* the
  manuscript's `C_s` on the labels those codes name.

The last section presents the same algebra in the form a generated certificate
is actually audited against -- schedules and enumeration computed once,
lookups by array index -- and identifies every piece of that presentation with
the object above that it presents: `windowLabel` is a bijection onto `Labels`
(`windowLabel_image`), `windowRelation` is `C_s` on the labels its indices name
(`windowRelation_eq_safe`), and `windowCurvatureTwo` is the manuscript's `Ω₂`
built from the audited rows themselves (`windowCurvatureTwo_eq_curvatureTwo`).
An application therefore defines no label carrier, no difference schedule, and
no relation: it audits its packed table against these.

No difference schedule is written down anywhere below: every shift is tested
against `forbiddenGaps`, which asks the registered dyadic target.

## What is retrieved

* the packed-row reading -- `Core.FiniteBitRelationBarrier.semanticRow_getLsb`
  at `Core/FiniteBitRelationBarrier.lean:83` and `Profile.flatCount` at `:34`;
* the certificate shape whose open half this closes --
  `Core.Strategy.ExactFiniteLocalAlgebra.ofBitRelationTable` at
  `Core/Strategy/ExactFiniteLocalAlgebraBitTable.lean:27` and
  `Core.FiniteBitRelationBarrier.SemanticCertificate.row_semantic` at
  `Core/FiniteBitRelationBarrier.lean:93`;
* `Safe`, `Legal`, `Labels` and `labels_card` from this namespace.
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Core.DyadicLength

/-! ## Reading a packed code as a label -/

/-- The label a packed bit code names: coordinate `i` belongs to it exactly
when bit `i` is set.

*Provenance.* Follows `Core.FiniteBitRelationBarrier.semanticRow_getLsb` at
`Core/FiniteBitRelationBarrier.lean:83`, which is how the framework already
reads a relation off a packed `BitVec` row.
-/
def labelOfCode {order : Nat} (code : BitVec order) : Label order :=
  Finset.univ.filter fun index => code.getLsbD index.1 = true

/-- *Provenance.* Follows `Core.FiniteBitRelationBarrier.semanticRow_getLsb` at
`Core/FiniteBitRelationBarrier.lean:83`. -/
@[simp] theorem mem_labelOfCode {order : Nat} {code : BitVec order}
    {index : Fin order} :
    index ∈ labelOfCode code ↔ code.getLsbD index.1 = true := by
  simp [labelOfCode]

/-- *Provenance.* Follows `Core.FiniteBitRelationBarrier.semanticRow_getLsb`
at `Core/FiniteBitRelationBarrier.lean:83`. -/
theorem labelOfCode_injective {order : Nat} :
    Function.Injective (labelOfCode (order := order)) := by
  intro source target equal
  refine BitVec.eq_of_getLsbD_eq fun index below => ?_
  have pointwise := Finset.ext_iff.mp equal ⟨index, below⟩
  rw [mem_labelOfCode, mem_labelOfCode] at pointwise
  cases sourceBit : source.getLsbD index <;>
    cases targetBit : target.getLsbD index <;>
      simp [sourceBit, targetBit] at pointwise ⊢

/-- The ascending enumeration of all packed codes of the order.

*Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`.
-/
def codeList (order : Nat) : List (BitVec order) :=
  (List.range (2 ^ order)).map (BitVec.ofNat order)

/-- *Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`. -/
theorem codeList_length (order : Nat) : (codeList order).length = 2 ^ order := by
  simp [codeList]

/-- *Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`. -/
theorem mem_codeList {order : Nat} (code : BitVec order) :
    code ∈ codeList order := by
  refine List.mem_map.mpr ⟨code.toNat, List.mem_range.mpr code.isLt, ?_⟩
  simp

/-- *Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`. -/
theorem codeList_nodup (order : Nat) : (codeList order).Nodup := by
  refine List.Nodup.map_on ?_ (List.nodup_range)
  intro left memLeft right memRight equal
  rw [List.mem_range] at memLeft memRight
  have := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt memLeft,
    Nat.mod_eq_of_lt memRight] at this
  exact this

/-- *Provenance.* Consumes `codeList_nodup` and `labelOfCode_injective` above.
-/
theorem labelOfCode_surjective {order : Nat} :
    Function.Surjective (labelOfCode (order := order)) := by
  classical
  have nodup : ((codeList order).map labelOfCode).Nodup :=
    (codeList_nodup order).map labelOfCode_injective
  have cardinality : ((codeList order).map labelOfCode).toFinset.card = 2 ^ order := by
    rw [List.toFinset_card_of_nodup nodup, List.length_map, codeList_length]
  have complete : ((codeList order).map labelOfCode).toFinset = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [cardinality, Fintype.card_finset, Fintype.card_fin]
  intro label
  have member : label ∈ ((codeList order).map labelOfCode).toFinset := by
    rw [complete]; exact Finset.mem_univ label
  rw [List.mem_toFinset, List.mem_map] at member
  obtain ⟨code, _, equal⟩ := member
  exact ⟨code, equal⟩

/-- *Provenance.* Follows `Core.FiniteBitRelationBarrier.semanticRow_getLsb`
at `Core/FiniteBitRelationBarrier.lean:83`. -/
theorem nonempty_labelOfCode_iff {order : Nat} (code : BitVec order) :
    (labelOfCode code).Nonempty ↔ code ≠ 0#order := by
  constructor
  · rintro ⟨index, member⟩ zero
    rw [zero, mem_labelOfCode, BitVec.getLsbD_zero] at member
    exact absurd member (by decide)
  · intro nonzero
    by_contra empty
    refine nonzero (BitVec.zero_iff_eq_false.mpr fun index => ?_)
    by_cases below : index < order
    · by_contra bit
      refine empty ⟨⟨index, below⟩, mem_labelOfCode.mpr ?_⟩
      simpa using bit
    · exact BitVec.getLsbD_of_ge code index (by omega)

/-! ## The bitwise safety test -/

/-- The bitwise form of the manuscript's `C_s`: no coordinate of `source` and
coordinate of `target` may sit at a difference whose closing cycle the target
accepts.  The differences tested are `forbiddenGaps`, i.e. they are derived, not
scheduled.

*Provenance.* Follows `Core.FiniteBitRelationBarrier.Profile.flatCount` at
`Core/FiniteBitRelationBarrier.lean:34`, the framework's own bitwise `&&&`
composition test on packed rows.
-/
def codeCompatible (order shift : Nat) (source target : BitVec order) : Bool :=
  decide (∀ gap ∈ forbiddenGaps order shift,
    source &&& (target >>> gap) = 0#order ∧
      target &&& (source >>> gap) = 0#order)

/-- *Provenance.* Follows `Core.FiniteBitRelationBarrier.semanticRow_getLsb`
at `Core/FiniteBitRelationBarrier.lean:83`. -/
theorem getLsbD_lt {order : Nat} {code : BitVec order} {index : Nat}
    (bit : code.getLsbD index = true) : index < order := by
  by_contra notBelow
  rw [BitVec.getLsbD_of_ge code index (by omega)] at bit
  exact absurd bit (by decide)

/-- **The code relation is the manuscript's `C_s`.**  The bitwise test on two
packed codes holds exactly when the labels those codes name are safe at that
outside length.

*Provenance.* Consumes `WindowCurvature.safe_iff_notMem_forbiddenGaps`.
-/
theorem codeCompatible_eq_true_iff (order shift : Nat)
    (source target : BitVec order) :
    codeCompatible order shift source target = true ↔
      Safe shift (labelOfCode source) (labelOfCode target) := by
  rw [codeCompatible, decide_eq_true_eq, safe_iff_notMem_forbiddenGaps]
  constructor
  · intro bitwise left memLeft right memRight member
    rw [mem_labelOfCode] at memLeft memRight
    obtain ⟨ascending, descending⟩ := bitwise _ member
    rcases Nat.le_total left.1 right.1 with le | le
    · have collapse : Nat.dist left.1 right.1 + left.1 = right.1 := by
        unfold Nat.dist; omega
      have zero := congrArg (fun word : BitVec order => word.getLsbD left.1) ascending
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_zero, collapse] at zero
      rw [memLeft, memRight] at zero
      exact absurd zero (by decide)
    · have collapse : Nat.dist left.1 right.1 + right.1 = left.1 := by
        unfold Nat.dist; omega
      have zero := congrArg (fun word : BitVec order => word.getLsbD right.1) descending
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_zero, collapse] at zero
      rw [memLeft, memRight] at zero
      exact absurd zero (by decide)
  · intro safe gap member
    constructor
    · refine BitVec.zero_iff_eq_false.mpr fun index => ?_
      by_contra bit
      simp only [Bool.not_eq_false, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        Bool.and_eq_true] at bit
      obtain ⟨sourceBit, targetBit⟩ := bit
      have belowIndex : index < order := getLsbD_lt sourceBit
      have belowShifted : gap + index < order := getLsbD_lt targetBit
      refine safe ⟨index, belowIndex⟩ (mem_labelOfCode.mpr sourceBit)
        ⟨gap + index, belowShifted⟩ (mem_labelOfCode.mpr targetBit) ?_
      have collapse : Nat.dist index (gap + index) = gap := by
        unfold Nat.dist; omega
      simpa [collapse] using member
    · refine BitVec.zero_iff_eq_false.mpr fun index => ?_
      by_contra bit
      simp only [Bool.not_eq_false, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
        Bool.and_eq_true] at bit
      obtain ⟨targetBit, sourceBit⟩ := bit
      have belowIndex : index < order := getLsbD_lt targetBit
      have belowShifted : gap + index < order := getLsbD_lt sourceBit
      refine safe ⟨gap + index, belowShifted⟩ (mem_labelOfCode.mpr sourceBit)
        ⟨index, belowIndex⟩ (mem_labelOfCode.mpr targetBit) ?_
      have collapse : Nat.dist (gap + index) index = gap := by
        unfold Nat.dist; omega
      simpa [collapse] using member

/-! ## The bitwise legality test -/

/-- The bitwise form of the manuscript's legality: a nonzero code no two of
whose set bits sit at a forbidden difference.

*Provenance.* Follows `Core.FiniteBitRelationBarrier.Profile.flatCount` at
`Core/FiniteBitRelationBarrier.lean:34`.
-/
def codeLegal (order : Nat) (code : BitVec order) : Bool :=
  !(code == 0#order) && codeCompatible order 0 code code

/-- **The code legality test is the manuscript's legality.**

*Provenance.* Consumes `codeCompatible_eq_true_iff` above.
-/
theorem codeLegal_eq_true_iff (order : Nat) (code : BitVec order) :
    codeLegal order code = true ↔ Legal (labelOfCode code) := by
  rw [codeLegal, Legal, Bool.and_eq_true, codeCompatible_eq_true_iff,
    nonempty_labelOfCode_iff]
  simp

/-! ## The label index -/

/-- The legal codes of the order, in ascending numeric order.  This is the
enumeration a generated certificate indexes its rows by.

*Provenance.* Follows `codeList` above.
-/
def legalCodeList (order : Nat) : List (BitVec order) :=
  (codeList order).filter (codeLegal order)

/-- *Provenance.* Consumes `codeLegal_eq_true_iff` above. -/
theorem mem_legalCodeList {order : Nat} (code : BitVec order) :
    code ∈ legalCodeList order ↔ Legal (labelOfCode code) := by
  rw [legalCodeList, List.mem_filter, codeLegal_eq_true_iff]
  simp [mem_codeList]

/-- *Provenance.* Consumes `codeList_nodup` above. -/
theorem legalCodeList_nodup (order : Nat) : (legalCodeList order).Nodup :=
  (codeList_nodup order).filter _

/-- The labels named by the legal codes are exactly `Labels`.

*Provenance.* Consumes `labelOfCode_surjective` and `mem_legalCodeList` above.
-/
theorem legalCodeList_toFinset (order : Nat) :
    ((legalCodeList order).map labelOfCode).toFinset = Labels order := by
  classical
  ext label
  rw [List.mem_toFinset, List.mem_map, mem_Labels]
  constructor
  · rintro ⟨code, member, equal⟩
    exact equal ▸ (mem_legalCodeList code).mp member
  · intro legal
    obtain ⟨code, equal⟩ := labelOfCode_surjective label
    exact ⟨code, (mem_legalCodeList code).mpr (equal ▸ legal), equal⟩

/-- **The certificate's label count is `|Labels|`.**

*Provenance.* Consumes `legalCodeList_toFinset` above.
-/
theorem legalCodeList_length (order : Nat) :
    (legalCodeList order).length = (Labels order).card := by
  classical
  have nodup : ((legalCodeList order).map labelOfCode).Nodup :=
    (legalCodeList_nodup order).map labelOfCode_injective
  have := List.toFinset_card_of_nodup nodup
  rw [legalCodeList_toFinset, List.length_map] at this
  exact this.symm

/-- **At the registered window order the certificate's label carrier is
`Fin 399`,** because `lem:labels` counted `Labels`.

*Provenance.* Consumes `WindowCurvature.labels_card` (`lem:labels`) and
`legalCodeList_length` above.
-/
theorem legalCodeList_length_windowOrder :
    (legalCodeList windowOrder).length = 399 := by
  rw [legalCodeList_length, labels_card]

/-- The label a certificate row index names.

*Provenance.* Follows the `Fin size` label carrier of
`Core.Strategy.ExactFiniteLocalAlgebra.ofBitRelationTable` at
`Core/Strategy/ExactFiniteLocalAlgebraBitTable.lean:35`.
-/
def labelAtIndex (order : Nat) (index : Fin (legalCodeList order).length) :
    Label order :=
  labelOfCode ((legalCodeList order).get index)

/-- *Provenance.* Consumes `mem_legalCodeList` above. -/
theorem labelAtIndex_mem_Labels (order : Nat)
    (index : Fin (legalCodeList order).length) :
    labelAtIndex order index ∈ Labels order :=
  mem_Labels.mpr ((mem_legalCodeList _).mp (List.get_mem _ _))

/-- *Provenance.* Consumes `legalCodeList_nodup` and `labelOfCode_injective`
above. -/
theorem labelAtIndex_injective (order : Nat) :
    Function.Injective (labelAtIndex order) := by
  intro left right equal
  have codes : (legalCodeList order).get left = (legalCodeList order).get right :=
    labelOfCode_injective equal
  exact (List.nodup_iff_injective_get.mp (legalCodeList_nodup order)) codes

/-- *Provenance.* Consumes `labelOfCode_surjective` and `mem_legalCodeList`
above. -/
theorem labelAtIndex_surjective (order : Nat) {label : Label order}
    (member : label ∈ Labels order) :
    ∃ index, labelAtIndex order index = label := by
  obtain ⟨code, equal⟩ := labelOfCode_surjective label
  have inList : code ∈ legalCodeList order :=
    (mem_legalCodeList code).mpr (equal ▸ mem_Labels.mp member)
  obtain ⟨index, get⟩ := List.mem_iff_get.mp inList
  exact ⟨index, by rw [labelAtIndex, get, equal]⟩

/-! ## The conclusion -/

/-- The code-indexed safety relation of a certificate row.

*Provenance.* Follows
`Core.FiniteBitRelationBarrier.SemanticCertificate.row_semantic` at
`Core/FiniteBitRelationBarrier.lean:93`, the code-indexed relation a generated
table is audited against.
-/
def codeRelation (order shift : Nat)
    (source target : Fin (legalCodeList order).length) : Bool :=
  codeCompatible order shift ((legalCodeList order).get source)
    ((legalCodeList order).get target)

/-- **The missing half of the certificate dictionary.**  The code-indexed
relation a generated bit table is audited against *is* the manuscript's `C_s`
on the labels its indices name.

*Provenance.* Consumes `codeCompatible_eq_true_iff` above; this is the half of
the dictionary that `Core.Strategy.ExactFiniteLocalAlgebra.ofBitRelationTable`
at `Core/Strategy/ExactFiniteLocalAlgebraBitTable.lean:27` leaves open.
-/
theorem codeRelation_eq_safe (order shift : Nat)
    (source target : Fin (legalCodeList order).length) :
    codeRelation order shift source target =
      decide (Safe shift (labelAtIndex order source) (labelAtIndex order target)) := by
  rw [codeRelation, labelAtIndex, labelAtIndex]
  by_cases safe : Safe shift (labelOfCode ((legalCodeList order).get source))
      (labelOfCode ((legalCodeList order).get target))
  · rw [(codeCompatible_eq_true_iff order shift _ _).mpr safe, decide_eq_true safe]
  · rw [decide_eq_false safe, Bool.eq_false_iff]
    exact fun contradiction =>
      safe ((codeCompatible_eq_true_iff order shift _ _).mp contradiction)

set_option maxRecDepth 100000

/-! ## The same algebra, presented for execution

Everything above is phrased with `Finset` and `List.get`, which is what makes
it provable.  A generated certificate is audited against a *presentation* of
the same relation: the difference schedules and the legal-code enumeration are
computed once as top-level constants, and every lookup is an array index.  The
declarations below are that presentation, together with the theorem
identifying each one with the object above that it presents.  An application
audits its table against these and defines none of them.
-/

/-- The forbidden differences at one outside length, as a list.  The same
derived condition as `forbiddenGaps`, in the form an executable test folds
over.

*Provenance.* Follows `WindowCurvature.forbiddenGaps` at
`Graph/WindowCurvatureAlgebra.lean:111`.
-/
def gapSchedule (order shift : Nat) : List Nat :=
  (List.range order).filter fun difference => decide (ForbiddenGap shift difference)

/-- *Provenance.* Consumes `WindowCurvature.mem_forbiddenGaps` at
`Graph/WindowCurvatureAlgebra.lean:116`. -/
theorem mem_gapSchedule {order shift difference : Nat} :
    difference ∈ gapSchedule order shift ↔ difference ∈ forbiddenGaps order shift := by
  simp [gapSchedule, mem_forbiddenGaps, List.mem_filter, List.mem_range]

/-- The bitwise safety test folded over an explicitly scheduled difference
list.  This is `codeCompatible` with its quantifier replaced by a fold; the
schedule it is run at is supplied, so a caller can compute it once.

*Provenance.* Follows `codeCompatible` above.
-/
def codeCompatibleWith {order : Nat} (gaps : List Nat)
    (source target : BitVec order) : Bool :=
  gaps.all fun gap =>
    (source &&& (target >>> gap) == 0#order) &&
      (target &&& (source >>> gap) == 0#order)

/-- **The executable test is the quantified one.**

*Provenance.* Consumes `mem_gapSchedule` above.
-/
theorem codeCompatibleWith_gapSchedule (order shift : Nat)
    (source target : BitVec order) :
    codeCompatibleWith (gapSchedule order shift) source target =
      codeCompatible order shift source target := by
  rw [Bool.eq_iff_iff, codeCompatible, decide_eq_true_eq, codeCompatibleWith,
    List.all_eq_true]
  constructor
  · intro folded gap member
    have := folded gap (mem_gapSchedule.mpr member)
    simpa using this
  · intro quantified gap member
    have := quantified gap (mem_gapSchedule.mp member)
    simpa using this

/-! ### At the registered window order -/

/-- The outside lengths the manuscript's multi-relation curvature package runs
through: every length whose closing cycle can still reach the first dyadic
length strictly above the window, i.e. `0, …, order + 1`.

*Provenance.* Follows `closingLength` at
`Graph/WindowCurvatureAlgebra.lean:86` and `windowOrder`.
-/
abbrev windowRelationLengths : Nat := windowOrder + 2

/-- The difference schedules of every outside length of the package, computed
once.  A zero-argument definition, so it is evaluated at initialization and
every relation test is an array index into it.

*Provenance.* Follows `gapSchedule` above.
-/
def windowGapTable : Array (List Nat) :=
  ((List.range windowRelationLengths).map (gapSchedule windowOrder)).toArray

/-- The schedule of one outside length, read off the table when the length is
one the package carries and derived directly otherwise.  Total, and equal to
`gapSchedule` either way.

*Provenance.* Follows `windowGapTable` above.
-/
def windowGapSchedule (shift : Nat) : List Nat :=
  match windowGapTable[shift]? with
  | some gaps => gaps
  | none => gapSchedule windowOrder shift

/-- *Provenance.* Consumes `windowGapTable` above. -/
theorem windowGapSchedule_eq (shift : Nat) :
    windowGapSchedule shift = gapSchedule windowOrder shift := by
  rw [windowGapSchedule]
  cases entry : windowGapTable[shift]? with
  | none => rfl
  | some gaps =>
      rw [windowGapTable, List.getElem?_toArray, List.getElem?_map] at entry
      cases scheduled : (List.range windowRelationLengths)[shift]? with
      | none => rw [scheduled] at entry; exact absurd entry (by simp)
      | some length =>
          rw [scheduled] at entry
          obtain ⟨_, value⟩ := List.getElem?_eq_some_iff.mp scheduled
          have : length = shift := by simpa using value.symm
          simp only [Option.map_some] at entry
          rw [← Option.some_inj.mp entry, this]

/-- The legal codes of the registered order, computed once.

*Provenance.* Follows `legalCodeList` above.
-/
def windowLegalCodes : Array (BitVec windowOrder) :=
  (legalCodeList windowOrder).toArray

/-- **The certificate's carrier size, on the executable presentation.**

*Provenance.* Consumes `legalCodeList_length_windowOrder` above.
-/
theorem windowLegalCodes_size : windowLegalCodes.size = 399 := by
  rw [windowLegalCodes, List.size_toArray, legalCodeList_length_windowOrder]

/-- The code a certificate row index names.  There is no default value: the
index is in range because the carrier size is `windowLegalCodes_size`.

*Provenance.* Follows `labelAtIndex` above.
-/
def windowLabelCode (index : Fin 399) : BitVec windowOrder :=
  windowLegalCodes[index.1]'(by rw [windowLegalCodes_size]; exact index.isLt)

/-- A row index is an index of the enumeration.

*Provenance.* Consumes `legalCodeList_length_windowOrder` above. -/
theorem windowLabelCode_lt (index : Fin 399) :
    index.1 < (legalCodeList windowOrder).length := by
  rw [legalCodeList_length_windowOrder]
  exact index.isLt

/-- The array lookup is the enumeration's own entry.

*Provenance.* Consumes `windowLegalCodes` above. -/
theorem windowLabelCode_eq_getElem (index : Fin 399) :
    windowLabelCode index =
      (legalCodeList windowOrder)[index.1]'(windowLabelCode_lt index) :=
  rfl

/-- *Provenance.* Consumes `windowLabelCode_eq_getElem` above. -/
theorem windowLabelCode_mem (index : Fin 399) :
    windowLabelCode index ∈ legalCodeList windowOrder := by
  rw [windowLabelCode_eq_getElem]
  exact List.getElem_mem _

/-- *Provenance.* Consumes `legalCodeList_nodup` above. -/
theorem windowLabelCode_injective : Function.Injective windowLabelCode := by
  intro left right equal
  rw [windowLabelCode_eq_getElem, windowLabelCode_eq_getElem] at equal
  have := (List.nodup_iff_injective_get.mp (legalCodeList_nodup windowOrder))
    (a₁ := ⟨left.1, windowLabelCode_lt left⟩)
    (a₂ := ⟨right.1, windowLabelCode_lt right⟩)
    (by simpa [List.get_eq_getElem] using equal)
  have value : left.1 = right.1 := Fin.mk_eq_mk.mp this
  exact Fin.ext value

/-- **The label a certificate row index names.**  `Fin 399` is not a stipulated
carrier: `windowLabel` is a bijection onto the manuscript's `Labels`.

*Provenance.* Follows `labelAtIndex` above.
-/
def windowLabel (index : Fin 399) : Label windowOrder :=
  labelOfCode (windowLabelCode index)

/-- *Provenance.* Consumes `mem_legalCodeList` and `windowLabelCode_mem`. -/
theorem windowLabel_mem_Labels (index : Fin 399) :
    windowLabel index ∈ Labels windowOrder :=
  mem_Labels.mpr ((mem_legalCodeList _).mp (windowLabelCode_mem index))

/-- *Provenance.* Consumes `labelOfCode_injective` and
`windowLabelCode_injective`. -/
theorem windowLabel_injective : Function.Injective windowLabel :=
  labelOfCode_injective.comp windowLabelCode_injective

/-- *Provenance.* Consumes `labelOfCode_surjective` and `mem_legalCodeList`. -/
theorem windowLabel_surjective {label : Label windowOrder}
    (member : label ∈ Labels windowOrder) :
    ∃ index, windowLabel index = label := by
  obtain ⟨code, equal⟩ := labelOfCode_surjective label
  have inList : code ∈ legalCodeList windowOrder :=
    (mem_legalCodeList code).mpr (equal ▸ mem_Labels.mp member)
  obtain ⟨position, below, get⟩ := List.getElem_of_mem inList
  refine ⟨⟨position, by rw [← legalCodeList_length_windowOrder]; exact below⟩, ?_⟩
  rw [windowLabel, windowLabelCode_eq_getElem, get, equal]

/-- **The row indices are exactly the legal labels.**  The image of the
certificate's carrier is `Labels`, so its size is `lem:labels`' count.

*Provenance.* Consumes `windowLabel_mem_Labels` and `windowLabel_surjective`. -/
theorem windowLabel_image :
    Finset.image windowLabel Finset.univ = Labels windowOrder := by
  ext label
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, _, equal⟩
    exact equal ▸ windowLabel_mem_Labels index
  · intro member
    obtain ⟨index, equal⟩ := windowLabel_surjective member
    exact ⟨index, Finset.mem_univ index, equal⟩

/-- **The relation a generated certificate is audited against.**  Every lookup
is an array index; the schedules are the derived ones.

*Provenance.* Follows `codeRelation` above.
-/
def windowRelation (shift : Nat) (source target : Fin 399) : Bool :=
  codeCompatibleWith (windowGapSchedule shift)
    (windowLabelCode source) (windowLabelCode target)

/-- **The audited relation is the manuscript's `C_s` on the labels its indices
name.**  This is `codeRelation_eq_safe` on the executable presentation.

*Provenance.* Consumes `windowGapSchedule_eq`, `codeCompatibleWith_gapSchedule`
and `codeCompatible_eq_true_iff`.
-/
theorem windowRelation_eq_safe (shift : Nat) (source target : Fin 399) :
    windowRelation shift source target =
      decide (Safe shift (windowLabel source) (windowLabel target)) := by
  rw [windowRelation, windowGapSchedule_eq, codeCompatibleWith_gapSchedule,
    Bool.eq_iff_iff, codeCompatible_eq_true_iff, decide_eq_true_eq, windowLabel,
    windowLabel]

/-- The legality test on the executable presentation: a code is legal exactly
when it is one of the enumerated ones.

*Provenance.* Consumes `mem_legalCodeList` and `codeLegal_eq_true_iff`. -/
theorem windowLegalCodes_mem (code : BitVec windowOrder) :
    code ∈ windowLegalCodes ↔ Legal (labelOfCode code) := by
  rw [windowLegalCodes, List.mem_toArray, mem_legalCodeList]

/-! ### The response of a label, and invariant 25

The manuscript attaches to `lem:labels` the statement that *the zero-defect
quotient through path-lengths `1, 2, 3` is the identity*: a legal label is
determined by which coordinates an outside path of length `1`, `2` or `3` can
safely reach from it.  That is a statement about the relation family this file
presents, so it is settled here.
-/

/-- The singleton label at one path coordinate, as a packed code.

*Provenance.* Follows `labelOfCode` above. -/
def coordinateCode {order : Nat} (coordinate : Fin order) : BitVec order :=
  BitVec.twoPow order coordinate.1

/-- *Provenance.* Consumes `mem_labelOfCode` above. -/
@[simp] theorem labelOfCode_coordinateCode {order : Nat} (coordinate : Fin order) :
    labelOfCode (coordinateCode coordinate) = {coordinate} := by
  ext index
  rw [mem_labelOfCode, coordinateCode, BitVec.getLsbD_twoPow, Finset.mem_singleton]
  simp [coordinate.isLt, eq_comm, Fin.ext_iff]

/-- **The response of a label at one outside length**: the coordinates a length
`shift` outside path leaving a vertex with this label can safely land on.

*Provenance.* Follows `windowRelation` above. -/
def windowResponse (shift : Nat) (index : Fin 399) : Label windowOrder :=
  Finset.univ.filter fun coordinate =>
    codeCompatibleWith (windowGapSchedule shift) (windowLabelCode index)
      (coordinateCode coordinate) = true

/-- The response is the manuscript's own safety statement against singleton
labels.

*Provenance.* Consumes `windowGapSchedule_eq`, `codeCompatibleWith_gapSchedule`
and `codeCompatible_eq_true_iff`. -/
theorem mem_windowResponse (shift : Nat) (index : Fin 399)
    (coordinate : Fin windowOrder) :
    coordinate ∈ windowResponse shift index ↔
      Safe shift (windowLabel index) {coordinate} := by
  rw [windowResponse, Finset.mem_filter]
  rw [windowGapSchedule_eq, codeCompatibleWith_gapSchedule,
    codeCompatible_eq_true_iff, labelOfCode_coordinateCode]
  exact ⟨fun holds => holds.2, fun holds => ⟨Finset.mem_univ _, holds⟩⟩

/-- **Invariant 25, on the executable presentation.**  Two row indices whose
responses agree at outside lengths `1`, `2` and `3` are the same index.

*Provenance.* Follows `Graph.TypeBMarkedFan.packingCap_eq_eight` at
`Graph/TypeBMarkedFan.lean:294`, a finite verdict on this algebra; evaluated
over the presentation of this section. -/
theorem windowResponse_separates : ∀ source target : Fin 399,
    (∀ shift ∈ [1, 2, 3], windowResponse shift source = windowResponse shift target) →
      source = target := by
  native_decide

/-- **Invariant 25.**  The zero-defect quotient through path-lengths `1, 2, 3`
is the identity: two legal labels with the same safety response at those three
lengths are equal.

*Provenance.* Consumes `windowResponse_separates` and `mem_windowResponse`
above, and `windowLabel_surjective` for the passage from `Labels` to the
carrier. -/
theorem labels_separated {source target : Label windowOrder}
    (memSource : source ∈ Labels windowOrder)
    (memTarget : target ∈ Labels windowOrder)
    (agree : ∀ shift ∈ [1, 2, 3], ∀ probe : Label windowOrder,
      (Safe shift source probe ↔ Safe shift target probe)) :
    source = target := by
  obtain ⟨sourceIndex, sourceEq⟩ := windowLabel_surjective memSource
  obtain ⟨targetIndex, targetEq⟩ := windowLabel_surjective memTarget
  refine sourceEq ▸ targetEq ▸ congrArg windowLabel
    (windowResponse_separates sourceIndex targetIndex fun shift member => ?_)
  ext coordinate
  rw [mem_windowResponse, mem_windowResponse, sourceEq, targetEq]
  exact agree shift member {coordinate}

/-! ### The two-step curvature tensor at the certificate's carrier -/

/-- `Ω₂` on the certificate's own row indices: two individually safe outside
edges of the *registered relation family* composing into an unsafe outside path
of length two.  The manuscript's `C₁(S,A) C₁(A,T) (1 - C₂(S,T))`, with each
factor a relation the audited table carries.

*Provenance.* Follows `WindowCurvature.curvatureTwo` at
`Graph/WindowCurvatureAlgebra.lean:218`.
-/
def windowCurvatureTwo (source middle target : Fin 399) : Bool :=
  windowRelation 1 source middle && windowRelation 1 middle target &&
    !windowRelation 2 source target

/-- **The tensor built from the audited rows is the manuscript's `Ω₂`.**

*Provenance.* Consumes `windowRelation_eq_safe` above. -/
theorem windowCurvatureTwo_eq_curvatureTwo (source middle target : Fin 399) :
    windowCurvatureTwo source middle target =
      curvatureTwo (windowLabel source) (windowLabel middle)
        (windowLabel target) := by
  rw [windowCurvatureTwo, curvatureTwo, windowRelation_eq_safe,
    windowRelation_eq_safe, windowRelation_eq_safe]

/-- **`Ω₂ = 1` at the carrier.**

*Provenance.* Consumes `curvatureTwo_eq_true_iff` at
`Graph/WindowCurvatureAlgebra.lean:224`. -/
theorem windowCurvatureTwo_eq_true_iff (source middle target : Fin 399) :
    windowCurvatureTwo source middle target = true ↔
      Safe 1 (windowLabel source) (windowLabel middle) ∧
        Safe 1 (windowLabel middle) (windowLabel target) ∧
          ¬ Safe 2 (windowLabel source) (windowLabel target) := by
  rw [windowCurvatureTwo_eq_curvatureTwo, curvatureTwo_eq_true_iff]

end Hypostructure.Graph.WindowCurvature
