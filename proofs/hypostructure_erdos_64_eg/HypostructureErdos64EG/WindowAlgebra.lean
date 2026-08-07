import Hypostructure.Graph.WindowCurvatureCode
import Hypostructure.Graph.FanCertificate
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Target

/-!
# The registered window order, and this problem's curvature algebra

Everything in this file is specific to Erdős problem 64 and is therefore
declared *here*, in the proof, rather than in the framework.  The framework's
`Graph.WindowCurvature` algebra is order-generic; below it is applied at this
problem's own registered order, and the manuscript's own numbers -- `13`, the
forbidden differences `{2, 6}`, and `lem:labels`' count `399` -- appear as
conclusions of kernel computations at that order.

The file also declares the one external input this problem consumes: the
Hegde--Sandeep--Shashank theorem.  It is an input to *this* problem, not a
framework law, so the framework never names it; the spine reads it through the
`freeForcesTarget` field of the problem's registered `Spine.Data`.
-/

namespace HypostructureErdos64EG

open Hypostructure
open Hypostructure.Graph

universe u

/-! ## The external theorem

`P₁₃`-free graphs of minimum degree at least three contain a power-of-two
cycle.  This is the sole external input of the proof and the sole axiom the
development declares. -/

/-- Induced-path order of the registered external theorem: the manuscript's
`P₁₃`. -/
def inducedPathOrder : Nat := 13

/-- Minimum-degree threshold of the registered external theorem. -/
def externalMinimumDegree : Nat := 3

/-- **Hegde--Sandeep--Shashank.**  Every finite induced-`P₁₃`-free graph of
minimum degree at least three contains a cycle whose length is a power of
two. -/
axiom p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    [Fintype object.Vertex] [DecidableRel object.graph.Adj]
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object

/-- Finite-object form of the external theorem, using exactly the object's
packed finite instances. -/
theorem finiteObject_p13Free_hasPowerOfTwoCycle
    (object : FiniteObject.{u})
    (minimumDegreeThree : 3 ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength (fun length =>
      ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent)
      object := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  apply p13Free_hasPowerOfTwoCycle object
  · simpa only [FiniteObject.minDegree] using minimumDegreeThree
  · exact p13Free

/-- The external theorem read through this problem's executable cycle-length
predicate and registered baseline threshold. -/
theorem externalHasCycleWithLength
    {LengthOK : Nat → Prop}
    (lengthBridge : ∀ length,
      (∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) →
        LengthOK length)
    {threshold : Nat} (thresholdOK : externalMinimumDegree ≤ threshold)
    (object : FiniteObject.{u})
    (baseline : threshold ≤ object.minDegree)
    (p13Free : InducedPathFree object inducedPathOrder) :
    HasCycleWithLength LengthOK object := by
  rcases finiteObject_p13Free_hasPowerOfTwoCycle object
      (Nat.le_trans thresholdOK baseline) p13Free with ⟨certificate⟩
  exact ⟨{
    vertex := certificate.vertex
    walk := certificate.walk
    isCycle := certificate.isCycle
    length_ok := lengthBridge certificate.walk.length certificate.length_ok }⟩

/-! ## The curvature algebra at the registered order

The declarations below are the framework's order-generic algebra applied at
`windowOrder`.  They stay in *this* namespace -- the framework's
`WindowCurvature` namespace is never extended from here -- and reach the
generic lemmas through `open`. -/

namespace WindowAlgebra

open Hypostructure.Graph.WindowCurvature

set_option maxRecDepth 100000

/-- The order of the induced windows this proof packs: the induced-path order
of the registered external theorem. -/
abbrev windowOrder : Nat := HypostructureErdos64EG.inducedPathOrder

/-- **The manuscript's own forbidden differences, derived.**  At outside length
zero and the registered window order, the differences whose closing cycle is
accepted are exactly `2` and `6` -- `(j - i) + 2 ∈ {4, 8}` -- which is the
sentence the manuscript proves before it defines `Labels`.  Nothing here is
listed in a definition; the numerals appear only in this conclusion.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25` and `windowOrder`; the same two numerals appear as
`Graph.TypeBMarkedFan.isDyadic_attachmentCycleLength_iff` at
`Graph/TypeBMarkedFan.lean:127`, which this derives rather than repeats.
-/
set_option maxHeartbeats 8000000 in
theorem forbiddenGaps_zero : forbiddenGaps windowOrder 0 = {2, 6} := by
  decide

/-- The forbidden differences at outside length one: `(j - i) + 3 ∈ {4, 8}`.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25` and `windowOrder`.
-/
theorem forbiddenGaps_one : forbiddenGaps windowOrder 1 = {1, 5} := by
  decide

/-- The forbidden differences at outside length two, i.e. the wedge gaps
`{0, 4, 12}` of `Graph.TypeBMarkedFan.isDyadic_wedgeCycle_iff`.

*Provenance.* Consumes `Core.DyadicLength.powerOfTwoLengthDecidable` at
`Core/DyadicLength.lean:25`; the same three numerals appear as
`Graph.TypeBMarkedFan.isDyadic_wedgeCycle_iff` at
`Graph/TypeBMarkedFan.lean:185`.
-/
theorem forbiddenGaps_two : forbiddenGaps windowOrder 2 = {0, 4, 12} := by
  decide

/-- Legality in the manuscript's stated form: `|i - j| ∉ {2, 6}`.

*Provenance.* Consumes `forbiddenGaps_zero` above; follows
`Graph.TypeBMarkedFan.isLegal_iff_attachment_not_dyadic` at
`Graph/TypeBMarkedFan.lean:137`.
-/
theorem legal_iff_dist {label : Label windowOrder} :
    Legal label ↔ label.Nonempty ∧
      ∀ i ∈ label, ∀ j ∈ label,
        Nat.dist i.1 j.1 ≠ 2 ∧ Nat.dist i.1 j.1 ≠ 6 := by
  rw [Legal, safe_iff_notMem_forbiddenGaps, forbiddenGaps_zero]
  constructor
  · rintro ⟨nonempty, safe⟩
    refine ⟨nonempty, fun i memI j memJ => ⟨fun equal => ?_, fun equal => ?_⟩⟩
    · exact safe i memI j memJ (by simp [equal])
    · exact safe i memI j memJ (by simp [equal])
  · rintro ⟨nonempty, distinct⟩
    refine ⟨nonempty, fun i memI j memJ member => ?_⟩
    obtain ⟨left, right⟩ := distinct i memI j memJ
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    exact member.elim left right

/-- **`lem:labels`, kernel-checked.**  Both halves of the manuscript's lemma
in one traversal of the powerset of the registered window order.

*Provenance.* Follows `Graph.TypeBMarkedFan.packingCap_eq_eight` at
`Graph/TypeBMarkedFan.lean:294`, the framework's precedent for a
kernel-`decide`d finite count on this algebra; consumes
`WindowCurvature.Labels` and `windowOrder`.
-/
theorem labels_enumeration :
    (Labels windowOrder).card = 399 ∧
      sizeDistribution windowOrder = [13, 60, 122, 122, 63, 17, 2, 0, 0, 0, 0, 0, 0] := by
  decide

/-- **The legal label count.**  `|Labels| = 399`.

*Provenance.* Consumes `labels_enumeration` above.
-/
theorem labels_card : (Labels windowOrder).card = 399 :=
  labels_enumeration.1

/-- **The size distribution.**  `13, 60, 122, 122, 63, 17, 2` for sizes
`1, …, 7`, and no legal label is larger.

*Provenance.* Consumes `labels_enumeration` above.
-/
theorem labels_sizeDistribution :
    sizeDistribution windowOrder =
      [13, 60, 122, 122, 63, 17, 2, 0, 0, 0, 0, 0, 0] :=
  labels_enumeration.2

/-- **At the registered window order the certificate's label carrier is
`Fin 399`,** because `lem:labels` counted `Labels`.

*Provenance.* Consumes `WindowCurvature.labels_card` (`lem:labels`) and
`legalCodeList_length` above.
-/
theorem legalCodeList_length_windowOrder :
    (legalCodeList windowOrder).length = 399 := by
  rw [legalCodeList_length, labels_card]

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


/-! ## The marked-fan packing cap at this order

`lem:fan-certificate`'s `α(D) = 2 + 2 + 2 + 2 = 8` is a kernel computation at the
registered order, exactly like `lem:labels`' `399` above: the framework's
`fanPackingCap` is order-generic, and the manuscript's `8` is its value here.

The local Type B fan ledger of node `[74]`/`[82]` spends this value once, through
the registered `Spine.Data.fanCapSlack`, as the slack `(11 − k)/4 ≥ 3/4` that lets
the hybrid half-credits pay the closed-neighbour deficit.  What the ledger needs is
only `α(D) + 1 ≤ 4 · 3`, so that is what is stated: the comparison is decided on
the registered numbers, and no node writes `8`.

The decision enumerates the fan-independent subsets of the thirteen window
coordinates, so it is deliberately isolated in this one declaration rather than
inlined at the registration site. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem fanPackingCap_succ_le :
    Hypostructure.Graph.WindowCurvature.fanPackingCap inducedPathOrder + 1 ≤
      4 * 3 := by
  unfold inducedPathOrder
  decide

end WindowAlgebra

end HypostructureErdos64EG
