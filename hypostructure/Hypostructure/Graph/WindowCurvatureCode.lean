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

end Hypostructure.Graph.WindowCurvature
