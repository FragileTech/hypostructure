import Hypostructure.Graph.Statements.RouteEight

/-!
# Canonical objects of G: route 8

Proof-agnostic canonical objects of the selected counterexample `G` on the
route-8 residual (Part IX of the manuscript).  Each object is the witness that
the pre-refactor argument (d2ded0e) read from one upstream ledger key and split
on, made a function of `G` so that a published statement can name it (ledger
values are data-free, `FactSystem.value_subsingleton`).

**Design.**  A guarded object is `Option`-valued:

    if h : ∃ x, Spec data G x then some (Classical.choose h) else none

(or `Classical.choice` of the upstream `Nonempty` record).  Each comes with
`_spec` (existence ⇒ the object is `some x` with `Spec x`), `_spec_of_eq_some`
and `_eq_none_iff`.  Downstream statements pin with
`∃ x, obj = some x ∧ Q x`: when the upstream fact is absent this is *false*,
never vacuously true, and when it is present `x` is the unique canonical value,
so no witness is re-chosen.  Objects that depend on an earlier canonical object
(absorption at the ledger, blocker at the absorption) take that object as an
argument and are instantiated at its canonical value.

`Classical.choose` is a fixed choice of G, the same at every key that names it;
where the paper fixes the lexicographically first object (the ledger `P₀`, tex
15537; the descent's two-support entry, tex 6419) the choice is the minimum of
an explicit lexicographic key.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

noncomputable section

section Route8Canonical

variable (data : Parameters) (object : Graph.FiniteObject.{u})

attribute [local instance] Graph.Route8.vertexDecEq
attribute [local instance 10] Classical.propDecidable

/-! ## `P₀`: the committed maximal demand ledger (node `[181]`) -/

/-- The code of a carrier edge `{a, b}`: its two vertex codes, smaller first. -/
def route8CarrierKey (edge : Sym2 object.Vertex) : Lex (ℕ × ℕ) :=
  letI : FinEnum object.Vertex := object.vertices
  Sym2.lift ⟨fun a b =>
      toLex (min ((FinEnum.equiv a : Fin _) : ℕ) ((FinEnum.equiv b : Fin _) : ℕ),
        max ((FinEnum.equiv a : Fin _) : ℕ) ((FinEnum.equiv b : Fin _) : ℕ)),
    fun a b => by simp only [min_comm, max_comm]⟩ edge

/-- **The lexicographic key of a 2/3-demand ledger** (tex 15537, 6419): its
classes `Ξ₃`, `Ξ₂`, `Ξ_res` as sorted lists of entry keys (`route8IndexKey`),
then its assignment `A(ξ)` on `Ξ₃ ∪ Ξ₂`, entry by entry in key order, each as
the sorted list of its carrier-edge codes. -/
def route8LedgerKey (ledger : Route8DemandLedgerRecord data object) :
    Lex (List (Lex (List ℕ × Lex (ℕ × ℕ))) ×
      Lex (List (Lex (List ℕ × Lex (ℕ × ℕ))) ×
        Lex (List (Lex (List ℕ × Lex (ℕ × ℕ))) ×
          List (Lex (Lex (List ℕ × Lex (ℕ × ℕ)) × List (Lex (ℕ × ℕ))))))) :=
  let P := ledger.partition
  toLex ((P.three.image (route8IndexKey object)).sort (· ≤ ·),
    toLex ((P.two.image (route8IndexKey object)).sort (· ≤ ·),
      toLex ((P.residual.image (route8IndexKey object)).sort (· ≤ ·),
        ((P.three ∪ P.two).image fun index =>
          toLex (route8IndexKey object index,
            ((P.assigned index).image (route8CarrierKey object)).sort
              (· ≤ ·))).sort (· ≤ ·))))

/-- A ledger record is determined by its four data fields; the record type is
finite. -/
instance route8DemandLedgerRecord_finite :
    Finite (Route8DemandLedgerRecord data object) := by
  letI : FinEnum object.Vertex := object.vertices
  refine Finite.of_injective
    (fun ledger : Route8DemandLedgerRecord data object =>
      (ledger.partition.three, ledger.partition.two, ledger.partition.residual,
        ledger.partition.assigned)) ?_
  rintro ⟨⟨t, w, r, _, _, _, _, a, _, _, _, _⟩, _, _, _, _, _⟩
    ⟨⟨t', w', r', _, _, _, _, a', _, _, _, _⟩, _, _, _, _, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- **`P₀`, the committed 2/3-demand ledger** of `def:typeA-pressure-ledger`
(tex 15537: "choose once and for all the lexicographically first ledger
maximizing first `|Ξ₃|`, then `|Ξ₂|`"): among the node-`[349]` records
(`Route8DemandLedgerStatement`, the maximizing ledgers), the one whose
`route8LedgerKey` is least. -/
def canonicalRoute8DemandRecord : Option (Route8DemandLedgerRecord data object) :=
  if h : Route8DemandLedgerStatement data object then
    some (Classical.choose (Set.exists_min_image Set.univ
      (route8LedgerKey data object) Set.finite_univ
      ⟨Classical.choice h, Set.mem_univ _⟩))
  else none

/-- `P₀` is the lexicographically first maximizing ledger. -/
theorem canonicalRoute8DemandRecord_lexFirst
    {ledger : Route8DemandLedgerRecord data object}
    (h : canonicalRoute8DemandRecord data object = some ledger) :
    ∀ other : Route8DemandLedgerRecord data object,
      route8LedgerKey data object ledger ≤ route8LedgerKey data object other := by
  unfold canonicalRoute8DemandRecord at h
  split_ifs at h with present
  cases h
  exact fun other => (Classical.choose_spec (Set.exists_min_image Set.univ
    (route8LedgerKey data object) Set.finite_univ
    ⟨Classical.choice present, Set.mem_univ _⟩)).2 other (Set.mem_univ _)

theorem canonicalRoute8DemandRecord_spec
    (h : Route8DemandLedgerStatement data object) :
    ∃ ledger, canonicalRoute8DemandRecord data object = some ledger := by
  exact ⟨_, dif_pos h⟩

theorem canonicalRoute8DemandRecord_eq_none_iff :
    canonicalRoute8DemandRecord data object = none ↔
      ¬ Route8DemandLedgerStatement data object := by
  unfold canonicalRoute8DemandRecord
  split <;> simp_all

/-- The partition `P₀` of the committed ledger. -/
def canonicalRoute8Partition :
    Option (Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :=
  (canonicalRoute8DemandRecord data object).map Route8DemandLedgerRecord.partition

theorem canonicalRoute8Partition_spec_of_eq_some
    {P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)}
    (h : canonicalRoute8Partition data object = some P) :
    Route8MaximalDemandPartition data object P := by
  unfold canonicalRoute8Partition at h
  obtain ⟨ledger, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ledger.pinned, ledger.maximal⟩

/-! ## `A₀`: the maximal same-support absorption at `P₀` (node `[351]`) -/

/-- The displayed properties of an absorption `(A, dep)` at a ledger partition
`P`: the `∃ A dep`-body of `Route8DemandAbsorptionStatement`
(`def:typeA-pressure-absorbers`, tex 15769--15789), at `P`. -/
def Route8AbsorptionSpec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat)) : Prop :=
  let packing := canonicalWindowPacking data object
  A.absorbed ⊆ P.demandUnits ∧
    (∀ υ ∈ A.absorbed, A.absorber υ ∈ Graph.Route8Census.supply object packing) ∧
    (∀ υ ∈ A.absorbed, A.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) ∧
    dep ⊆ P.demandUnits ∧
    Disjoint A.absorbed dep ∧
    dep = ∅ ∧
    (∀ B : Graph.DemandPartition.Absorption P
        (Graph.Route8Census.Index object × Nat),
      B.absorbed ⊆ P.demandUnits →
      (∀ υ ∈ B.absorbed, B.absorber υ ∈ Graph.Route8Census.supply object packing) →
      (∀ υ ∈ B.absorbed, B.absorber υ ∈ Graph.Route8.cutEdges object υ.1.1) →
      Disjoint B.absorbed dep →
      B.absorbed.card ≤ A.absorbed.card) ∧
    3 * (route8UnifiedEntries data object).card ≤
      object.boundaryIncidence (object.remainderSupport packing) +
        dep.card + (P.demandUnits \ (A.absorbed ∪ dep)).card

/-- **`A₀`, the canonical absorption at a ledger** (tex 15789: "the fixed
maximal absorption").  Instantiated at `P₀ = canonicalRoute8Partition` it is
the witness of node `[351]` `route8DemandAbsorption`: the d2ded0e row
`SpineRows/Route8DemandAbsorption.lean` obtained `⟨A, …⟩` from exactly this
`∃ A dep` body at the `[349]` ledger it required. -/
def canonicalRoute8Absorption
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    Option (Graph.DemandPartition.Absorption P
        (Graph.Route8Census.Index object × Nat) ×
      Finset (Graph.Route8Census.Index object × Nat)) :=
  if h : ∃ x : Graph.DemandPartition.Absorption P
        (Graph.Route8Census.Index object × Nat) ×
      Finset (Graph.Route8Census.Index object × Nat),
      Route8AbsorptionSpec data object P x.1 x.2 then
    some (Classical.choose h)
  else none

theorem canonicalRoute8Absorption_spec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (h : ∃ x : Graph.DemandPartition.Absorption P
        (Graph.Route8Census.Index object × Nat) ×
      Finset (Graph.Route8Census.Index object × Nat),
      Route8AbsorptionSpec data object P x.1 x.2) :
    ∃ x, canonicalRoute8Absorption data object P = some x ∧
      Route8AbsorptionSpec data object P x.1 x.2 :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8Absorption_spec_of_eq_some
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    {x} (h : canonicalRoute8Absorption data object P = some x) :
    Route8AbsorptionSpec data object P x.1 x.2 := by
  unfold canonicalRoute8Absorption at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8Absorption_eq_none_iff
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    canonicalRoute8Absorption data object P = none ↔
      ¬ ∃ x : Graph.DemandPartition.Absorption P
          (Graph.Route8Census.Index object × Nat) ×
        Finset (Graph.Route8Census.Index object × Nat),
        Route8AbsorptionSpec data object P x.1 x.2 := by
  unfold canonicalRoute8Absorption
  split <;> simp_all

/-! ## The canonical open-window blockers at `(P₀, A₀)` (node `[352]`) -/

/-- The blocker clauses of `def:typeA-open-window-blocker` with
`lem:typeA-open-window-blocker-count` (tex 15911--15925) at a ledger `P` and
absorption `(A, dep)`: the `∃ carrier blocker`-body of
`Route8WindowBlockersStatement`. -/
def Route8WindowBlockerSpec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat))
    (carrier : Graph.Route8Census.Index object × Nat → Sym2 object.Vertex)
    (blocker : Graph.Route8Census.Index object × Nat → Finset object.Vertex) :
    Prop :=
  let packing := canonicalWindowPacking data object
  (∀ υ ∈ P.demandUnits \ (A.absorbed ∪ dep),
    carrier υ ∈ route8DemandCore data object υ.1 ∧
      ∃ inside ∈ carrier υ, ∃ outside ∈ carrier υ,
        inside ∈ object.remainderSupport packing ∧
          outside ∉ object.remainderSupport packing ∧
          outside ∈ blocker υ ∧ blocker υ ∈ packing) ∧
    (P.demandUnits \ (A.absorbed ∪ dep)).card =
      ∑ window ∈ packing,
        ((P.demandUnits \ (A.absorbed ∪ dep)).filter
          fun υ => blocker υ = window).card

/-- **The canonical window blocker `b₀(υ)`** (tex 15925: "the canonical
blocker"), with its carrier edge, at a ledger `P` and absorption `(A, dep)`;
instantiated at `(P₀, A₀)`.  It is the witness of node `[352]`
`route8WindowBlockers`: the d2ded0e row `SpineRows/Route8WindowBlockers.lean`
read `[349]` and `[351]` and produced exactly this `∃ carrier blocker`. -/
def canonicalRoute8WindowBlocker
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat)) :
    Option ((Graph.Route8Census.Index object × Nat → Sym2 object.Vertex) ×
      (Graph.Route8Census.Index object × Nat → Finset object.Vertex)) :=
  if h : ∃ x : (Graph.Route8Census.Index object × Nat → Sym2 object.Vertex) ×
      (Graph.Route8Census.Index object × Nat → Finset object.Vertex),
      Route8WindowBlockerSpec data object P A dep x.1 x.2 then
    some (Classical.choose h)
  else none

theorem canonicalRoute8WindowBlocker_spec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat))
    (h : ∃ x : (Graph.Route8Census.Index object × Nat → Sym2 object.Vertex) ×
      (Graph.Route8Census.Index object × Nat → Finset object.Vertex),
      Route8WindowBlockerSpec data object P A dep x.1 x.2) :
    ∃ x, canonicalRoute8WindowBlocker data object P A dep = some x ∧
      Route8WindowBlockerSpec data object P A dep x.1 x.2 :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8WindowBlocker_spec_of_eq_some
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat))
    {x} (h : canonicalRoute8WindowBlocker data object P A dep = some x) :
    Route8WindowBlockerSpec data object P A dep x.1 x.2 := by
  unfold canonicalRoute8WindowBlocker at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8WindowBlocker_eq_none_iff
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (A : Graph.DemandPartition.Absorption P
      (Graph.Route8Census.Index object × Nat))
    (dep : Finset (Graph.Route8Census.Index object × Nat)) :
    canonicalRoute8WindowBlocker data object P A dep = none ↔
      ¬ ∃ x : (Graph.Route8Census.Index object × Nat → Sym2 object.Vertex) ×
        (Graph.Route8Census.Index object × Nat → Finset object.Vertex),
        Route8WindowBlockerSpec data object P A dep x.1 x.2 := by
  unfold canonicalRoute8WindowBlocker
  split <;> simp_all

/-! ## `ξ*`: the unpaid witness-free entry of `P₀` (node `[181]`, yes) -/

/-- An unpaid entry of the ledger partition `P` with no exit-`(4)` witness:
the `∃ index`-body of `Route8UnpaidWitnessFreeStatement` at `P`
(`thm:typeA-unpaid-exit4-reduction` (i), tex 17142--17160). -/
def Route8UnpaidWitnessFreeSpec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (index : Graph.Route8Census.Index object) : Prop :=
  index ∈ P.two ∪ P.residual ∧
    ¬ ∃ witness : Graph.ExitFour.Witness
        (Graph.HasCycleWithLength data.LengthOK) index.1 data.threshold
        data.dischargeScale index.2.1 ∅,
      witness.load = index.2.2

/-- **`ξ*`**, instantiated at `P₀`: the unpaid witness-free entry that the
d2ded0e decision `route8UnpaidExitFourDichotomy` obtained
(`obtain ⟨index, unpaid, noExitFour⟩ := noWitness`) at the ledger partition it
had just opened, and republished as `[334]` `route8UnifiedTrueTwoCarrierEntry`. -/
def canonicalRoute8UnpaidEntry
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    Option (Graph.Route8Census.Index object) :=
  if h : ∃ index, Route8UnpaidWitnessFreeSpec data object P index then
    some (Classical.choose h)
  else none

theorem canonicalRoute8UnpaidEntry_spec
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    (h : ∃ index, Route8UnpaidWitnessFreeSpec data object P index) :
    ∃ index, canonicalRoute8UnpaidEntry data object P = some index ∧
      Route8UnpaidWitnessFreeSpec data object P index :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8UnpaidEntry_spec_of_eq_some
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object))
    {index} (h : canonicalRoute8UnpaidEntry data object P = some index) :
    Route8UnpaidWitnessFreeSpec data object P index := by
  unfold canonicalRoute8UnpaidEntry at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8UnpaidEntry_eq_none_iff
    (P : Graph.DemandPartition.Partition
      (route8UnifiedEntries data object) (route8DemandCore data object)) :
    canonicalRoute8UnpaidEntry data object P = none ↔
      ¬ ∃ index, Route8UnpaidWitnessFreeSpec data object P index := by
  unfold canonicalRoute8UnpaidEntry
  split <;> simp_all

/-! ## `ξ†`: the true entry of the terminal descent stage (node `[123]`, yes) -/

/-- A true two-support entry of the terminal stage `route8DescentChain`
(`thm:large-budget-route8-only`, tex 17085): the `∃ index`-body of the
rate-passing arm of `Route8PeelingDescentStatement`. -/
def Route8StageTrueEntrySpec (index : Graph.Route8Census.Index object) : Prop :=
  Graph.Route8Pressure.TrueEntryAt object (canonicalWindowPacking data object)
    (route8UnifiedEntries data object) data.threshold data.dischargeScale
    data.LengthOK (route8DescentChain data object).toFinset index

/-- **`ξ†`**: the true entry that node `[123]`-yes (`route8StageTrueEntry`,
reading `[282]` `route8PeelingDescent` and `[1402]` `route8StageRate`) takes
from the terminal stage of the fixed descent chain. -/
def canonicalRoute8StageTrueEntry : Option (Graph.Route8Census.Index object) :=
  if h : ∃ index, Route8StageTrueEntrySpec data object index then
    some (Classical.choose h)
  else none

theorem canonicalRoute8StageTrueEntry_spec
    (h : ∃ index, Route8StageTrueEntrySpec data object index) :
    ∃ index, canonicalRoute8StageTrueEntry data object = some index ∧
      Route8StageTrueEntrySpec data object index :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8StageTrueEntry_spec_of_eq_some
    {index} (h : canonicalRoute8StageTrueEntry data object = some index) :
    Route8StageTrueEntrySpec data object index := by
  unfold canonicalRoute8StageTrueEntry at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8StageTrueEntry_eq_none_iff :
    canonicalRoute8StageTrueEntry data object = none ↔
      ¬ ∃ index, Route8StageTrueEntrySpec data object index := by
  unfold canonicalRoute8StageTrueEntry
  split <;> simp_all

/-- **The terminal true entry of node `[334]`**: on the `[123]` rate arm the
true entry of the terminal stage of `route8DescentChain` (`ξ†`), and on the
rate-failed arm the witness-free unpaid entry `ξ*` of the committed ledger
`P₀` (node `[181]`).  The arm is decided by `Route8StageRateStatement` itself,
not by whether `ξ†` exists: a stage true entry can exist on the rate-failed
arm, and it is not the entry the `[181]` branch continues with. -/
def canonicalRoute8TerminalEntry : Option (Graph.Route8Census.Index object) :=
  if Route8StageRateStatement data object then
    canonicalRoute8StageTrueEntry data object
  else
    (canonicalRoute8Partition data object).bind
      (canonicalRoute8UnpaidEntry data object)

theorem canonicalRoute8TerminalEntry_eq_of_rate
    (rate : Route8StageRateStatement data object) :
    canonicalRoute8TerminalEntry data object =
      canonicalRoute8StageTrueEntry data object := by
  unfold canonicalRoute8TerminalEntry
  rw [if_pos rate]

theorem canonicalRoute8TerminalEntry_eq_of_rateFailed
    (failed : ¬ Route8StageRateStatement data object) :
    canonicalRoute8TerminalEntry data object =
      (canonicalRoute8Partition data object).bind
        (canonicalRoute8UnpaidEntry data object) := by
  unfold canonicalRoute8TerminalEntry
  rw [if_neg failed]

/-! ## `ι₂`: the terminal two-carrier entry of `𝒳_A` (nodes `[117]`/`[118]`) -/

/-- A two-support entry of the census of `𝒳_A = route8SurvivorComponents`:
the `∃ index`-body of `Route8TwoCarrierEntryStatement`
(`prop:typeA-route8-carrier-reduction`, tex 12509). -/
def Route8TwoCarrierEntrySpec (index : Graph.Route8Census.Index object) : Prop :=
  let packing := canonicalWindowPacking data object
  index ∈ Graph.Route8Census.entriesOfComponents object packing
      (route8SurvivorComponents data object) data.threshold data.dischargeScale ∧
    Graph.Route8Census.CollectionTwoCarrierEntry object packing
      (route8SurvivorComponents data object) data.threshold data.dischargeScale
      data.LengthOK index

/-- **`ι₂`**, the entry `ξ` of `def:typeA-terminal-two-carrier` (T1)--(T5)
(tex 12636).  It is the witness of node `[261]` `route8TwoCarrierEntry` that
the d2ded0e rows `Route8TrueTwoCarrierEntry` and
`Route8CarrierDeletionWitnesses` each obtained
(`obtain ⟨index, indexMem, two⟩ := selected.down`) from that key. -/
def canonicalRoute8TwoCarrierIndex : Option (Graph.Route8Census.Index object) :=
  if h : ∃ index, Route8TwoCarrierEntrySpec data object index then
    some (Classical.choose h)
  else none

theorem canonicalRoute8TwoCarrierIndex_spec
    (h : ∃ index, Route8TwoCarrierEntrySpec data object index) :
    ∃ index, canonicalRoute8TwoCarrierIndex data object = some index ∧
      Route8TwoCarrierEntrySpec data object index :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8TwoCarrierIndex_spec_of_eq_some
    {index} (h : canonicalRoute8TwoCarrierIndex data object = some index) :
    Route8TwoCarrierEntrySpec data object index := by
  unfold canonicalRoute8TwoCarrierIndex at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8TwoCarrierIndex_eq_none_iff :
    canonicalRoute8TwoCarrierIndex data object = none ↔
      ¬ ∃ index, Route8TwoCarrierEntrySpec data object index := by
  unfold canonicalRoute8TwoCarrierIndex
  split <;> simp_all

/-- `Route8TwoCarrierEntryStatement` ([261]) is literally the existence the
canonical index chooses from. -/
theorem route8TwoCarrierEntry_iff_exists_spec :
    Route8TwoCarrierEntryStatement data object ↔
      ∃ index, Route8TwoCarrierEntrySpec data object index := by
  simp only [Route8TwoCarrierEntryStatement, Route8TwoCarrierEntrySpec,
    route8SurvivorComponents]

/-! ## `ι₁`: the small-core entry of `𝒳_A` (nodes `[115]`/`[116]`) -/

/-- A small-core entry `(X, w, u)` of `𝒳_A`: the `∃ component receiver load`
body of `Route8SmallCoreEntry` (`lem:typeA-one-terminal-collapse`,
tex 12459): an entry of the census whose canonical essential incidence core
has cardinality at most one. -/
def Route8SmallCoreEntrySpec
    (entry : Graph.SupportComponents.Connected.Component object
        (object.remainderSupport (canonicalWindowPacking data object)) ×
      object.Vertex × object.Vertex) : Prop :=
  let support := object.remainderSupport (canonicalWindowPacking data object)
  let piece := object.pieceSupport support entry.1
  entry.1 ∈ route8SurvivorComponents data object ∧
    entry.2.1 ∈ Graph.VisibleEntry.saturatedReceivers object piece
      data.threshold data.dischargeScale ∧
    entry.2.2 ∈ Graph.VisibleEntry.silentExcess object piece data.threshold
      data.dischargeScale entry.2.1 ∧
    ((Graph.Route8Census.presented object data.threshold data.LengthOK
        (piece, entry.2.1, entry.2.2)).toEntry
      (Graph.HasCycleWithLength data.LengthOK)).alpha ≤ 1

/-- **`ι₁`**: the small-core entry of node `[330]` `route8SmallCoreEntry`
(the `[115]`-yes arm), the one `[116]` `route8SmallCoreCollapse` classifies.
At d2ded0e the `[115]` decision (`SpineRows/Route8SmallCoreCollapse.lean`)
split on exactly this `∃ component receiver load` body. -/
def canonicalRoute8SmallCoreEntry :
    Option (Graph.SupportComponents.Connected.Component object
        (object.remainderSupport (canonicalWindowPacking data object)) ×
      object.Vertex × object.Vertex) :=
  if h : ∃ entry, Route8SmallCoreEntrySpec data object entry then
    some (Classical.choose h)
  else none

theorem canonicalRoute8SmallCoreEntry_spec
    (h : ∃ entry, Route8SmallCoreEntrySpec data object entry) :
    ∃ entry, canonicalRoute8SmallCoreEntry data object = some entry ∧
      Route8SmallCoreEntrySpec data object entry :=
  ⟨Classical.choose h, dif_pos h, Classical.choose_spec h⟩

theorem canonicalRoute8SmallCoreEntry_spec_of_eq_some
    {entry} (h : canonicalRoute8SmallCoreEntry data object = some entry) :
    Route8SmallCoreEntrySpec data object entry := by
  unfold canonicalRoute8SmallCoreEntry at h
  split at h
  · next hx => cases h; exact Classical.choose_spec hx
  · cases h

theorem canonicalRoute8SmallCoreEntry_eq_none_iff :
    canonicalRoute8SmallCoreEntry data object = none ↔
      ¬ ∃ entry, Route8SmallCoreEntrySpec data object entry := by
  unfold canonicalRoute8SmallCoreEntry
  split <;> simp_all

/-- `Route8SmallCoreEntry` ([330]) is literally the existence the canonical
small-core entry chooses from. -/
theorem route8SmallCoreEntry_iff_exists_spec :
    Route8SmallCoreEntry data object ↔
      ∃ entry, Route8SmallCoreEntrySpec data object entry := by
  simp only [Route8SmallCoreEntry, Route8SmallCoreEntrySpec,
    route8SurvivorComponents]
  constructor
  · rintro ⟨component, mem, receiver, receiverMem, load, loadMem, small⟩
    exact ⟨(component, receiver, load), mem, receiverMem, loadMem, small⟩
  · rintro ⟨⟨component, receiver, load⟩, mem, receiverMem, loadMem, small⟩
    exact ⟨component, mem, receiver, receiverMem, load, loadMem, small⟩

end Route8Canonical

end

end Hypostructure.Graph.Strategy.Spine
