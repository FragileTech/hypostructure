import Hypostructure.Graph.SupportComponents
import Hypostructure.Graph.InducedPath
import Hypostructure.Graph.Replacement
import Hypostructure.Graph.TypeBOverlapObstruction

/-!
# Post-ledger Type A core hygiene

This file is `lem:typeB-postledger-core-hygiene` of `original_erdos_64_proof.tex`
(manuscript node `[73]`/`[75]`), the lemma that *decomposes* the post-ledger core
of a Type B support into admissible Type A components:

> Let `X` be a Type B support or a grouped decorated Type B envelope support.
> Remove from its counted core the vertices and incidence carriers used by the
> certificate-closed fan entries, the local B1 fan entries, and the grouped
> decorated envelope entries.  Each connected component `Z` of the remaining
> non-window core is an admissible Type A support after its inherited boundary
> profile is recorded.  In particular `Z` is `P₁₃`-free, contextually
> dyadic-safe, hereditarily target-uncompressible, and has supplied deficiency
> charged to the unused ordinary deficiency reserve and the window-stub reserve.

## Nothing is redefined

Both a Type B support and a grouped decorated Type B envelope support are one and
the same carrier: `TypeBBridgeResidual.Residual`, a counted core `Y_X` together
with its recorded high-degree centres (`def:decorated-typeB-envelope-support`
supplies `Y_𝔠^*` and `H_𝔠` in exactly that shape, which is why
`TypeBFanMass` treats its clause (iii) as the same per-centre calculation).

* the counted core is `Residual.core`;
* the declared family of ledger carriers removed from it is
  `demands.biUnion Residual.envelopeBlock`, the vertex support of every
  certificate-closed entry (`TypeBOverlapObstruction.certificateClosedEntry`),
  every local B1 hybrid entry (`TypeBOverlapObstruction.hybridEntry`) and every
  grouped decorated envelope entry, by
  `CandidateEntry.vertexCarriers_subset_envelopeBlock`; that the deletion really
  removes all of them -- vertex carriers and the owners of the incidence
  carriers -- is `vertexCarriers_subset_deletedCarriers`;
* the remaining non-window core is `TypeBOverlapObstruction.remainingCore`,
  which at the full demand family `H_X` is literally `Residual.residualCore`,
  the post-ledger core whose charge `Residual.residualCoreCharge` is the
  quantity `lem:typeB-bridge-deficit-bound` and `TypeBExclusion.typeBExclusion`
  leave undischarged;
* the components of that core are the *induced* connected components
  `SupportComponents.Connected.Component` of the existing core, and each one is
  carried by the *same* `Residual` type: `componentResidual` records the
  component as a counted core with no assigned centre.  There is no second
  residual, core, boundary or carrier type anywhere in this file;
* the incidence carriers are `TypeBFanClosedPorts.Profile.IsWindowIncidence` and
  `IsNonWindowIncidence`, the two kinds of `def:typeB-ledger-carriers` (c), (d).

## The manuscript proof, clause by clause

* *`P₁₃`-freeness and contextual dyadic safety by heredity.*  The remaining
  non-window core is an induced subgraph of the original remainder core after
  deleting a declared family of ledger carriers, so `inducedPathFree_of_subset`
  transports `P₁₃`-freeness along the induced restriction
  (`FiniteObject.induce`), and `componentDyadicSafety` reads dyadic safety off
  `ctx.avoids` exactly as `TypeBOverlapObstruction.contextualDyadicSafety` does.
  Neither is assumed: the first is *proved* from the induced-subgraph structure,
  the second is a field of the minimal-counterexample context.
* *Target-uncompressibility, hereditary by `cor:uncompressible`.*  A
  target-complete compression of `Z` is an `AtomReplacementCertificate` at the
  proper boundaried atom presenting `Z`; gluing it back with the recorded
  boundary profile `atom.decomposition.outside` extends it to a compression of
  the original support, which `AtomReplacementCertificate.impossible` refutes
  from `ctx.avoids` and `ctx.target_of_smaller`.
* *Supplied deficiency.*  Deleting ledger carriers can create new deficient
  boundary vertices in `Z`, and `coreDegree_eq_add_card_deletedCarriersAt` shows
  each such deficit is caused by exactly one removed carrier incidence: inside
  the counted core the neighbours of a vertex of `Z` split, without remainder,
  into the neighbours inside `Z` and the deleted ledger carriers.
  `deletedCarrierAt_classified` routes each removed carrier to one of the three
  reserves of the manuscript -- an already-paid fan entry (the assigned centre
  carrier of `def:typeB-ledger-carriers` (b)), an ordinary deficiency-reserve
  unit (carrier (a)), or a packed-window incidence charged by
  `cor:stub-boundary-supply` (carrier (c)).  Components are handled separately,
  so no connectivity assumption crosses a deleted carrier.

## Where the Type A boundary falls

Everything above is Type B bookkeeping and is proved here.  What this lemma
delivers to the Type A side is `sum_componentNetCharge_sub_reserve_le`:

`Σ_Z (No(Z) - reserve(Z)) ≤ Ch(post-ledger core)`,

so the single remaining input is the *per-component* discharge
`reserve(Z) ≤ No(Z)` supplied by `lem:typeA-unsaturated-discharge` and
`lem:typeA-saturated-handoff`.  Both lemmas are now formalised, in
`Hypostructure.Graph.TypeAReceiverClosure`: the discharge is
`unsaturated_discharge_core` (`|V(X)| ≤ loadMultiplier · def⁺(X)`, with its
ledger reading `remainder_le_multiplier_mul_requiredMass`), and the saturated
handoff is `saturated_handoff`, whose exit-(4) descent closes Figure 8's
`[102] → [89]` back-edge.  They are read here one component at a time,
at the component's own stage, by `componentCharge_nonneg_of_discharged`, which is
indexed exactly like `postLedgerCoreHygiene`; the statements that need the whole
post-ledger core read instead the single ledger quantity
`0 ≤ Σ_Z (No(Z) - reserve(Z))`, the extracted Type A deficit that
`netCharge_ge_componentDeficit_sub_eight_surplus` already hands to node `[77]`.
No statement in this file re-collects the components into a global hypothesis.

All rational quantities are over `ℚ`, consistent with
`TypeBBridgeResidual.Residual.netCharge`.
-/

namespace Hypostructure.Graph.TypeBPostLedgerCore

open Hypostructure.Graph
open Hypostructure.Graph.TypeBOpenPorts
open Hypostructure.Graph.TypeBMarkedFan
open Hypostructure.Graph.TypeBFanClosedPorts
open Hypostructure.Graph.TypeBBridgeResidual
open Hypostructure.Graph.TypeBExclusion
open Hypostructure.Graph.TypeBOverlapObstruction
open Hypostructure.Graph.SupportComponents
open Hypostructure.Graph.ReceiverLoad (LoadCapacityProfile)

universe u v w

variable {object : FiniteObject.{u}}

/-! ## Heredity along an induced restriction

The manuscript's first sentence -- "the remaining non-window core is an induced
subgraph of the original remainder core after deleting a declared family of
ledger carriers" -- is `FiniteObject.induce` on a smaller support.  The two
hereditary clauses below are *proved* from that induced-subgraph structure. -/

/-- The canonical induced embedding of a smaller support into a larger one.
Both sides are `FiniteObject.induce` of the *same* ambient object, so adjacency
on either side is ambient adjacency of the underlying vertices and the embedding
reflects it on the nose. -/
def inducedSubsetEmbedding (object : FiniteObject.{u})
    {small large : Finset object.Vertex} (subset : small ⊆ large) :
    (object.induce small).graph ↪g (object.induce large).graph :=
  ⟨⟨fun vertex => ⟨vertex.1, subset vertex.2⟩, by
      intro left right equal
      refine Subtype.ext ?_
      exact congrArg (fun v : {x : object.Vertex // x ∈ large} => v.1) equal⟩,
    Iff.rfl⟩

/-- **Heredity of induced-obstruction freeness.**  An induced copy of a pattern
inside the smaller support is an induced copy inside the larger one, so freeness
descends.  Nothing is assumed: this is the composition of two induced
embeddings. -/
theorem inducedObstructionFree_of_subset {PatternVertex : Type w}
    (pattern : SimpleGraph PatternVertex) {small large : Finset object.Vertex}
    (subset : small ⊆ large)
    (free : InducedObstructionFree pattern (object.induce large)) :
    InducedObstructionFree pattern (object.induce small) := by
  intro copy
  exact free (copy.trans ⟨inducedSubsetEmbedding object subset⟩)

/-- **`P₁₃`-freeness is hereditary** (manuscript invariant 22).  The `P₁₃` case
is `order = 13`. -/
theorem inducedPathFree_of_subset {small large : Finset object.Vertex}
    (order : Nat) (subset : small ⊆ large)
    (free : InducedPathFree (object.induce large) order) :
    InducedPathFree (object.induce small) order :=
  inducedObstructionFree_of_subset _ subset free

/-! ## The connected components of a counted support

`SupportComponents.Connected` already owns the connected components of an
induced support and their disjoint coverage law; the only thing added here is
that a weight sums over the support blockwise. -/

/-- A weight on a counted support is the sum of its blockwise weights over the
connected components of the induced restriction.  This is
`SupportComponents.Connected.mem_support_iff_mem_component_with_vertices`
together with `disjoint_vertices`; components are treated separately, exactly as
the manuscript demands. -/
theorem sum_eq_sum_components (object : FiniteObject.{u})
    (support : Finset object.Vertex) (weight : object.Vertex → ℚ) :
    ∑ y ∈ support, weight y
      = ((Connected.order object support).map fun component =>
          ∑ y ∈ Connected.vertices object support component, weight y).sum := by
  classical
  rw [← List.sum_toFinset _ (Connected.order_nodup object support)]
  have disjoint : Set.PairwiseDisjoint
      ((Connected.order object support).toFinset :
        Set (Connected.Component object support))
      (Connected.vertices object support) := by
    intro a _ b _ different
    exact Connected.disjoint_vertices object support different
  rw [← Finset.sum_biUnion (f := weight) disjoint]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext y
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  exact Connected.mem_support_iff_mem_component_with_vertices object support y

/-! ## `lem:typeB-postledger-core-hygiene`: the component as a Type A support

The component is recorded on the *existing* support carrier: a `Residual` of the
same object whose counted core is the component and which records no assigned
high-degree centre.  That last fact is the maximality clause (d) of
`def:typeB-candidate-ledger`, and it is a construction here, never a
hypothesis. -/

/-- The connected component `Z` of the remaining non-window core, recorded as a
Type A support: a `Residual` of the same object whose counted core is the
component's vertex set and whose recorded centre set is empty. -/
noncomputable def componentResidual (residual : Residual object)
    (demands : Finset object.Vertex)
    (component : Connected.Component object (remainingCore residual demands)) :
    Residual object where
  core := Connected.vertices object (remainingCore residual demands) component
  recordedCentres := ∅

variable (residual : Residual object) (demands : Finset object.Vertex)

@[simp] theorem componentResidual_core
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).core
      = Connected.vertices object (remainingCore residual demands) component := rfl

/-- `Z` carries no assigned surplus: it records no high-degree centre. -/
@[simp] theorem componentResidual_centers
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).centers = ∅ := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  show (∅ : Finset object.Vertex) ∩ _ = ∅
  exact Finset.empty_inter _

@[simp] theorem componentResidual_surplus
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).surplus = 0 := by
  unfold Residual.surplus
  rw [componentResidual_centers, Finset.sum_empty]

theorem mem_remainingCore_of_mem_componentResidual
    {component : Connected.Component object (remainingCore residual demands)}
    {y : object.Vertex}
    (member : y ∈ (componentResidual residual demands component).core) :
    y ∈ remainingCore residual demands :=
  ((Connected.mem_vertices_iff object (remainingCore residual demands) component y).1
    member).1

theorem remainingCore_subset_core :
    remainingCore residual demands ⊆ residual.core := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro y member
  exact (Finset.mem_sdiff.1 member).1

/-- The component is a sub-support of the counted core `Y_X`. -/
theorem componentResidual_core_subset_core
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).core ⊆ residual.core := fun _ member =>
  remainingCore_subset_core residual demands
    (mem_remainingCore_of_mem_componentResidual residual demands member)

/-- **The maximality clause of `def:typeB-candidate-ledger`, discharged.**  At
the full demand family `H_X` no assigned high-degree centre survives into the
post-ledger core, because every centre lies in its own fan envelope block.  This
is a theorem, not a hypothesis. -/
theorem isMaximal_centers : IsMaximal residual residual.centers := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  intro h member
  rw [remainingCore, Finset.mem_sdiff]
  rintro ⟨-, notCovered⟩
  refine notCovered (Finset.mem_biUnion.2 ⟨h, member, ?_⟩)
  rw [Residual.envelopeBlock]
  exact Finset.mem_insert_self _ _

/-- No assigned high-degree centre of `X` lies in a component of the remaining
core, once the ledger is maximal.  With `demands = H_X` the maximality input is
`isMaximal_centers`, so nothing is assumed there either. -/
theorem centre_notMem_componentResidual (maximal : IsMaximal residual demands)
    (component : Connected.Component object (remainingCore residual demands))
    {h : object.Vertex} (centre : h ∈ residual.centers) :
    h ∉ (componentResidual residual demands component).core := fun member =>
  maximal h centre (mem_remainingCore_of_mem_componentResidual residual demands member)

/-! ## The declared family of deleted ledger carriers -/

/-- The vertices deleted from the counted core by the chosen ledger entries: the
counted core minus the remaining core.  This is not a new carrier -- it is
exactly the vertex support `demands.biUnion Residual.envelopeBlock` of the
certificate-closed, local B1 and grouped decorated envelope entries, intersected
with the counted core (`mem_deletedCarriers_iff`). -/
noncomputable def deletedCarriers : Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  residual.core \ remainingCore residual demands

/-- The deleted ledger carriers incident to a vertex: the removed carrier
incidences at `y` of the manuscript's deficiency bookkeeping. -/
noncomputable def deletedCarriersAt (y : object.Vertex) : Finset object.Vertex :=
  (deletedCarriers residual demands).filter fun w => object.graph.Adj y w

variable {residual demands}

theorem mem_deletedCarriers_iff {w : object.Vertex} :
    w ∈ deletedCarriers residual demands ↔
      w ∈ residual.core ∧ ∃ h ∈ demands, w ∈ residual.envelopeBlock h := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  rw [deletedCarriers, Finset.mem_sdiff, remainingCore, Finset.mem_sdiff]
  constructor
  · rintro ⟨inCore, notRemaining⟩
    refine ⟨inCore, ?_⟩
    by_contra notCovered
    exact notRemaining ⟨inCore, fun covered =>
      notCovered (Finset.mem_biUnion.1 covered)⟩
  · rintro ⟨inCore, covered⟩
    refine ⟨inCore, ?_⟩
    rintro ⟨-, notCovered⟩
    exact notCovered (Finset.mem_biUnion.2 covered)

theorem mem_deletedCarriersAt_iff {y w : object.Vertex} :
    w ∈ deletedCarriersAt residual demands y ↔
      w ∈ deletedCarriers residual demands ∧ object.graph.Adj y w := by
  rw [deletedCarriersAt, Finset.mem_filter]

/-- **The deleted family really is the family the manuscript removes.**  Every
vertex carrier of every candidate Type B ledger entry -- the certificate-closed
fan entry of `def:typeB-candidate-ledger` (a)
(`TypeBOverlapObstruction.certificateClosedEntry`), the local B1 fan entry of
clause (b) (`TypeBOverlapObstruction.hybridEntry`), and the grouped decorated
envelope entry, which is the same construction on the grouped counted core -- is
deleted, and so is the owner of every one of its incidence carriers.  This is
`CandidateEntry.vertexCarriers_subset_envelopeBlock`; no second carrier notion is
introduced. -/
theorem vertexCarriers_subset_deletedCarriers (residual : Residual object)
    {ledger : LoadCapacityProfile}
    {hub : object.Vertex} (member : hub ∈ residual.centers)
    (entry : CandidateEntry residual ledger hub) :
    entry.vertexCarriers ⊆ deletedCarriers residual residual.centers ∧
      ∀ incidence ∈ entry.chosen,
        incidence.1 ∈ deletedCarriers residual residual.centers := by
  have blockSubset : entry.vertexCarriers ⊆ deletedCarriers residual residual.centers := by
    intro v inCarriers
    have blockMember : v ∈ residual.envelopeBlock hub :=
      entry.vertexCarriers_subset_envelopeBlock inCarriers
    exact mem_deletedCarriers_iff.2
      ⟨residual.envelopeBlock_subset_core (Residual.centers_subset_core member) blockMember,
        hub, member, blockMember⟩
  refine ⟨blockSubset, fun incidence owned => ?_⟩
  exact blockSubset
    (entry.assigned_subset_vertexCarriers (entry.chosen_owned incidence owned).1)

/-- **Each removed carrier is one of the three reserve units of the manuscript
proof.**  A deleted ledger carrier `w` incident to a vertex of the remaining
core lies in the vertex support of one of the chosen entries, and is

* an **already-paid fan entry** carrier -- the assigned high-degree centre of
  `def:typeB-ledger-carriers` (b), whose augmented charge the entry pays; or
* a **packed-window incidence** charged by `cor:stub-boundary-supply` --
  `(y, w)` is then literally a window incidence of `def:typeB-ledger-carriers`
  (c), for every fan-window profile carrying the packed-window union `W`; or
* an **ordinary deficiency-reserve unit** of `def:typeB-ledger-carriers` (a) --
  a non-centre vertex of the counted core lying on some fan rim, off the
  packed-window union, carrying the unrefined charge `ch_X(w)`. -/
theorem deletedCarrierAt_classified (window : Finset object.Vertex)
    {y w : object.Vertex} (member : w ∈ deletedCarriersAt residual demands y) :
    (∃ h ∈ demands, w ∈ residual.envelopeBlock h) ∧
      (w ∈ demands ∨
        (w ∈ window ∧ ∀ profile : Profile object, profile.window = window →
          y ∉ window → profile.IsWindowIncidence y w) ∨
        (w ∉ window ∧ w ∈ residual.core ∧
          ∃ h ∈ demands, w ∈ neighbourRim object h)) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨deleted, adjacency⟩ := mem_deletedCarriersAt_iff.1 member
  obtain ⟨inCore, h, hMember, blockMember⟩ := mem_deletedCarriers_iff.1 deleted
  refine ⟨⟨h, hMember, blockMember⟩, ?_⟩
  by_cases inWindow : w ∈ window
  · refine Or.inr (Or.inl ⟨inWindow, ?_⟩)
    intro profile windowEq outside
    refine ⟨?_, adjacency, ?_⟩
    · rw [windowEq]
      exact outside
    · rw [windowEq]
      exact inWindow
  · by_cases isDemand : w ∈ demands
    · exact Or.inl isDemand
    · refine Or.inr (Or.inr ⟨inWindow, inCore, h, hMember, ?_⟩)
      rw [Residual.envelopeBlock, Finset.mem_insert] at blockMember
      rcases blockMember with rfl | rimMember
      · exact absurd hMember isDemand
      · exact (Finset.mem_inter.1 rimMember).1

/-! ## The supplied-deficiency transfer

"Each such deficit is caused by one of the removed carrier incidences": inside
the counted core the neighbours of a vertex of `Z` split, with no remainder, into
its neighbours inside `Z` and the deleted ledger carriers.  The first half of
that split is the connectivity law of `SupportComponents.Connected`, so no
connectivity assumption is inherited across a deleted carrier. -/

/-- The exact incidence split at a vertex of a component: every counted-core
neighbour is either a neighbour inside the component or a deleted ledger
carrier, and never both. -/
theorem coreDegree_eq_add_card_deletedCarriersAt
    {component : Connected.Component object (remainingCore residual demands)}
    {y : object.Vertex}
    (member : y ∈ (componentResidual residual demands component).core) :
    residual.coreDegree y
      = (componentResidual residual demands component).coreDegree y
        + (deletedCarriersAt residual demands y).card := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have split :
      residual.core.filter (fun w => object.graph.Adj y w)
        = ((componentResidual residual demands component).core.filter
            fun w => object.graph.Adj y w)
          ∪ deletedCarriersAt residual demands y := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter, mem_deletedCarriersAt_iff,
      mem_deletedCarriers_iff, componentResidual_core]
    constructor
    · rintro ⟨inCore, adjacency⟩
      by_cases remaining : w ∈ remainingCore residual demands
      · refine Or.inl ⟨?_, adjacency⟩
        exact Connected.neighbor_mem_vertices object (remainingCore residual demands)
          component member remaining adjacency
      · refine Or.inr ⟨⟨inCore, ?_⟩, adjacency⟩
        rw [remainingCore, Finset.mem_sdiff] at remaining
        by_contra notCovered
        exact remaining ⟨inCore, fun covered =>
          notCovered (Finset.mem_biUnion.1 covered)⟩
    · rintro (⟨componentMember, adjacency⟩ | ⟨⟨inCore, -⟩, adjacency⟩)
      · exact ⟨componentResidual_core_subset_core residual demands component
          componentMember, adjacency⟩
      · exact ⟨inCore, adjacency⟩
  have disjoint :
      Disjoint ((componentResidual residual demands component).core.filter
          fun w => object.graph.Adj y w)
        (deletedCarriersAt residual demands y) := by
    rw [Finset.disjoint_left]
    intro w componentMember deletedMember
    have remaining : w ∈ remainingCore residual demands :=
      mem_remainingCore_of_mem_componentResidual residual demands
        (Finset.mem_filter.1 componentMember).1
    have deleted := (mem_deletedCarriersAt_iff.1 deletedMember).1
    rw [deletedCarriers, Finset.mem_sdiff] at deleted
    exact deleted.2 remaining
  show (residual.core.filter fun w => object.graph.Adj y w).card = _ + _
  rw [split, Finset.card_union_of_disjoint disjoint]
  rfl

/-- **The supplied-deficiency clause.**  Deleting ledger carriers can create new
deficient boundary vertices in `Z`, and every unit of the new deficit is charged
to one removed carrier incidence: the component's own deficiency exceeds the
ambient one by at most the number of deleted ledger carriers at that vertex. -/
theorem componentResidual_deficiency_le
    {component : Connected.Component object (remainingCore residual demands)}
    {y : object.Vertex}
    (member : y ∈ (componentResidual residual demands component).core) :
    (componentResidual residual demands component).deficiency y
      ≤ residual.deficiency y + ((deletedCarriersAt residual demands y).card : ℚ) := by
  have identity := coreDegree_eq_add_card_deletedCarriersAt member
  have cast : (residual.coreDegree y : ℚ)
      = ((componentResidual residual demands component).coreDegree y : ℚ)
        + ((deletedCarriersAt residual demands y).card : ℚ) := by
    exact_mod_cast congrArg (fun n : Nat => (n : ℚ)) identity
  have ambient : (3 : ℚ) - (residual.coreDegree y : ℚ) ≤ residual.deficiency y :=
    le_max_right _ _
  have ambientNonneg : 0 ≤ residual.deficiency y := le_max_left _ _
  have cardNonneg : (0 : ℚ) ≤ ((deletedCarriersAt residual demands y).card : ℚ) := by
    positivity
  have expand : (componentResidual residual demands component).deficiency y
      = max 0 (3 - ((componentResidual residual demands component).coreDegree y : ℚ)) :=
    rfl
  rw [expand]
  exact max_le (by linarith) (by linarith)

/-- The same statement on the ordinary vertex charge `ch(y) = δ⁺(y) - α`, with
the discharge rate `α` read from the registered presentation.  The rate cancels:
both charges subtract the same `α`. -/
theorem componentResidual_vertexCharge_le (ledger : LoadCapacityProfile)
    {component : Connected.Component object (remainingCore residual demands)}
    {y : object.Vertex}
    (member : y ∈ (componentResidual residual demands component).core) :
    (componentResidual residual demands component).vertexCharge ledger y
      ≤ residual.vertexCharge ledger y
        + ((deletedCarriersAt residual demands y).card : ℚ) := by
  have bound := componentResidual_deficiency_le member
  unfold Residual.vertexCharge
  linarith

/-! ## The recorded boundary profile of a component -/

variable (residual demands)

/-- The reserve charged to the component by its inherited boundary profile: one
unit per deleted ledger carrier incident to the component.  By
`deletedCarrierAt_classified` every unit is an already-paid fan entry carrier, an
ordinary deficiency-reserve unit of `def:typeB-ledger-carriers`, or a
packed-window incidence charged by `cor:stub-boundary-supply`. -/
noncomputable def componentReserve
    (component : Connected.Component object (remainingCore residual demands)) : ℚ :=
  ∑ y ∈ (componentResidual residual demands component).core,
    ((deletedCarriersAt residual demands y).card : ℚ)

theorem componentReserve_nonneg
    (component : Connected.Component object (remainingCore residual demands)) :
    0 ≤ componentReserve residual demands component :=
  Finset.sum_nonneg fun _ _ => by positivity

variable {residual demands}

/-- The net charge of the component as a Type A support: it carries no assigned
surplus, so `No(Z)` is exactly the sum of its own vertex charges. -/
theorem componentResidual_netCharge_eq (ledger : LoadCapacityProfile)
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).netCharge ledger
      = ∑ y ∈ (componentResidual residual demands component).core,
          (componentResidual residual demands component).vertexCharge ledger y := by
  rw [(componentResidual residual demands component).netCharge_eq_sum_vertexCharge_sub_surplus
      ledger,
    componentResidual_surplus]
  ring

/-- **The component's Type A net charge, minus the reserve its recorded boundary
profile charges, is bounded by the ambient charge the post-ledger core carries on
it.**  This is the quantitative form of "the supplied-deficiency hypothesis in
`def:admissible` transfers to each component". -/
theorem componentResidual_netCharge_sub_reserve_le (ledger : LoadCapacityProfile)
    (component : Connected.Component object (remainingCore residual demands)) :
    (componentResidual residual demands component).netCharge ledger
        - componentReserve residual demands component
      ≤ ∑ y ∈ (componentResidual residual demands component).core,
          residual.vertexCharge ledger y := by
  have blockwise :
      ∑ y ∈ (componentResidual residual demands component).core,
          (componentResidual residual demands component).vertexCharge ledger y
        ≤ ∑ y ∈ (componentResidual residual demands component).core,
            (residual.vertexCharge ledger y
              + ((deletedCarriersAt residual demands y).card : ℚ)) :=
    Finset.sum_le_sum fun _ member =>
      componentResidual_vertexCharge_le ledger member
  rw [Finset.sum_add_distrib] at blockwise
  rw [componentResidual_netCharge_eq ledger]
  unfold componentReserve
  linarith

/-! ## The three hereditary clauses of `def:admissible` -/

/-- **`P₁₃`-freeness of the component, by heredity.**  The component is an
induced subgraph of the counted core, so `def:admissible`'s `P₁₃`-free clause for
`X` transports to `Z`.  The transport is proved, not assumed. -/
theorem componentInducedPathFree (order : Nat)
    (component : Connected.Component object (remainingCore residual demands))
    (free : InducedPathFree (object.induce residual.core) order) :
    InducedPathFree
      (object.induce (componentResidual residual demands component).core) order :=
  inducedPathFree_of_subset order
    (componentResidual_core_subset_core residual demands component) free

/-- **Contextual dyadic safety of the component** (`def:dyadic-safe`).  No cycle
of `G` meeting `V(Z)` has an accepted (power-of-two) length.

The absence of the cycle is **not** a hypothesis: it is `ctx.avoids`, the target
avoidance the minimal-counterexample node already carries, read exactly as
`TypeBOverlapObstruction.contextualDyadicSafety` reads it.  Because
`Z ⊆ Y_X ⊆ G`, a power-of-two cycle meeting `V(Z)` would be a power-of-two cycle
of `G`. -/
theorem componentDyadicSafety
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    {residual : Residual ctx.G} {demands : Finset ctx.G.Vertex}
    (component : Connected.Component ctx.G (remainingCore residual demands))
    {base : ctx.G.Vertex} (cycle : ctx.G.graph.Walk base base)
    (isCycle : cycle.IsCycle) :
    ∀ vertex ∈ (componentResidual residual demands component).core,
      vertex ∈ cycle.support → ¬ LengthOK cycle.length := by
  intro _ _ _ accepted
  exact ctx.avoids ⟨⟨base, cycle, isCycle, accepted⟩⟩

/-- **Hereditary target-uncompressibility of the component** (`cor:uncompressible`,
manuscript invariant 8).  A target-complete compression of `Z` is a same-interface
replacement certificate at the proper boundaried atom presenting `Z`; gluing it
back with the recorded boundary profile `atom.decomposition.outside` extends it to
a compression of the original support, and
`AtomReplacementCertificate.impossible` refutes that from `ctx.avoids` and
`ctx.target_of_smaller`.

The presentation hypothesis only says *which* atom carries `Z`; the refutation
itself is uniform, so no absence is assumed. -/
theorem componentUncompressible
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    {residual : Residual ctx.G} {demands : Finset ctx.G.Vertex}
    (component : Connected.Component ctx.G (remainingCore residual demands))
    (atom : ProperBoundariedAtom ctx.G)
    (_presents : Set.range atom.decomposition.pieceIntoAmbient
      = ((componentResidual residual demands component).core : Set ctx.G.Vertex))
    (replacement : BoundaryPiece atom.decomposition.interface) :
    ¬ Nonempty (AtomReplacementCertificate ctx atom replacement) := by
  rintro ⟨certificate⟩
  exact certificate.impossible (cycleTargetInterface LengthOK).isomorphismInvariant

/-! ## `lem:typeB-postledger-core-hygiene` -/

/-- **`lem:typeB-postledger-core-hygiene`**, manuscript node `[73]`/`[75]`.

Let `X` be a Type B support or a grouped decorated Type B envelope support --
both are `TypeBBridgeResidual.Residual` -- inside the minimal counterexample.
Remove from its counted core `Y_X` the vertices and incidence carriers used by
the certificate-closed fan entries, the local B1 fan entries and the grouped
decorated envelope entries, i.e. the declared family
`H_X.biUnion Residual.envelopeBlock` of `def:typeB-ledger-carriers`; the
remaining non-window core is `Residual.residualCore`.  Then every connected
component `Z` of that core is an admissible Type A support once its inherited
boundary profile is recorded:

* `Z` is a connected sub-support of `Y_X` carrying no assigned high-degree
  centre and no assigned surplus, so it is a *Type A* support;
* `Z` is `P₁₃`-free, by heredity along the induced restriction;
* `Z` is contextually dyadic-safe, from `ctx.avoids`;
* `Z` is hereditarily target-uncompressible, by `cor:uncompressible`;
* the supplied deficiency of `Z` is charged: every deficit created by deleting
  ledger carriers is caused by exactly one removed carrier incidence, and each
  removed carrier is an already-paid fan entry, an ordinary deficiency-reserve
  unit of `def:typeB-ledger-carriers`, or a packed-window incidence charged by
  `cor:stub-boundary-supply`.

There is no hypothesis of the form "configuration `C` does not occur": the
`P₁₃`-free clause is an implication *transporting* the inherited constraint of
`def:admissible` along an induced subgraph, and the other three clauses are
produced.

This is the object-level half -- clauses (0), (1) and the supplied-deficiency
bookkeeping, none of which needs the ambient minimal-counterexample context.  The
two contextual clauses are added by `postLedgerCoreHygieneInContext`. -/
theorem postLedgerCoreHygiene (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (window : Finset object.Vertex) (order : Nat)
    (component :
      Connected.Component object (remainingCore residual residual.centers))
    (memberOrder :
      component ∈ Connected.order object (remainingCore residual residual.centers)) :
    -- (0) `Z` is a connected Type A sub-support of the counted core.
    ((componentResidual residual residual.centers component).core ⊆ residual.core ∧
      Connected.ConnectedOn object
        (componentResidual residual residual.centers component).core ∧
      (componentResidual residual residual.centers component).centers = ∅ ∧
      (componentResidual residual residual.centers component).surplus = 0 ∧
      ∀ h ∈ residual.centers,
        h ∉ (componentResidual residual residual.centers component).core) ∧
    -- (1) `P₁₃`-freeness, by heredity along the induced restriction.
    (InducedPathFree (object.induce residual.core) order →
      InducedPathFree
        (object.induce (componentResidual residual residual.centers component).core)
        order) ∧
    -- (4) supplied deficiency charged to the reserves.
    (∀ y ∈ (componentResidual residual residual.centers component).core,
      residual.coreDegree y
          = (componentResidual residual residual.centers component).coreDegree y
            + (deletedCarriersAt residual residual.centers y).card ∧
        (componentResidual residual residual.centers component).deficiency y
          ≤ residual.deficiency y
            + ((deletedCarriersAt residual residual.centers y).card : ℚ) ∧
        ∀ w ∈ deletedCarriersAt residual residual.centers y,
          (∃ h ∈ residual.centers, w ∈ residual.envelopeBlock h) ∧
            (w ∈ residual.centers ∨
              (w ∈ window ∧ ∀ profile : Profile object, profile.window = window →
                y ∉ window → profile.IsWindowIncidence y w) ∨
              (w ∉ window ∧ w ∈ residual.core ∧
                ∃ h ∈ residual.centers, w ∈ neighbourRim object h))) ∧
    -- and the charge the component carries is bounded by the Type A net charge
    -- minus that reserve.
    ((componentResidual residual residual.centers component).netCharge ledger
        - componentReserve residual residual.centers component
      ≤ ∑ y ∈ (componentResidual residual residual.centers component).core,
          residual.vertexCharge ledger y) := by
  refine ⟨⟨componentResidual_core_subset_core residual residual.centers component,
      Connected.connectedOn_of_mem_order object _ memberOrder,
      componentResidual_centers residual residual.centers component,
      componentResidual_surplus residual residual.centers component,
      fun h centre =>
        centre_notMem_componentResidual residual residual.centers
          (isMaximal_centers residual) component centre⟩,
    fun free => componentInducedPathFree order component free,
    ?_, componentResidual_netCharge_sub_reserve_le ledger component⟩
  intro y member
  exact ⟨coreDegree_eq_add_card_deletedCarriersAt member,
    componentResidual_deficiency_le member,
    fun w carrier => deletedCarrierAt_classified window carrier⟩

/-- **`lem:typeB-postledger-core-hygiene`, contextual form.**  Inside the minimal
counterexample the two remaining clauses of `def:admissible` are produced as
well: the component is contextually dyadic-safe (`def:dyadic-safe`, from
`ctx.avoids`) and hereditarily target-uncompressible (`cor:uncompressible`, from
`AtomReplacementCertificate.impossible`).  Together with
`postLedgerCoreHygiene` this is the whole "in particular" list of the
manuscript. -/
theorem postLedgerCoreHygieneInContext
    {Baseline : FiniteObject.{u} → Prop}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}
    (residual : Residual ctx.G)
    (component :
      Connected.Component ctx.G (remainingCore residual residual.centers)) :
    -- (2) contextual dyadic safety, from `ctx.avoids`.
    (∀ base : ctx.G.Vertex, ∀ cycle : ctx.G.graph.Walk base base, cycle.IsCycle →
      ∀ vertex ∈ (componentResidual residual residual.centers component).core,
        vertex ∈ cycle.support → ¬ LengthOK cycle.length) ∧
    -- (3) hereditary target-uncompressibility, by `cor:uncompressible`.
    (∀ atom : ProperBoundariedAtom ctx.G,
      Set.range atom.decomposition.pieceIntoAmbient
          = ((componentResidual residual residual.centers component).core
              : Set ctx.G.Vertex) →
        ∀ replacement : BoundaryPiece atom.decomposition.interface,
          ¬ Nonempty (AtomReplacementCertificate ctx atom replacement)) :=
  ⟨fun _ cycle isCycle => componentDyadicSafety component cycle isCycle,
    fun atom presents replacement =>
      componentUncompressible component atom presents replacement⟩

/-! ## The decomposition of the post-ledger core charge

`lem:typeB-bridge-deficit-bound` and `TypeBExclusion.typeBExclusion` both leave
`Residual.residualCoreCharge` undischarged.  The hygiene lemma decomposes it into
the Type A components, and the *only* remaining input is the per-component
discharge of `lem:typeA-unsaturated-discharge` and
`lem:typeA-saturated-handoff`. -/

/-- The post-ledger core charge is the sum of the charges its components
carry. -/
theorem residualCoreCharge_eq_sum_components (residual : Residual object)
    (ledger : LoadCapacityProfile) :
    residual.residualCoreCharge ledger
      = ((Connected.order object (remainingCore residual residual.centers)).map
          fun component =>
            ∑ y ∈ (componentResidual residual residual.centers component).core,
              residual.vertexCharge ledger y).sum := by
  rw [Residual.residualCoreCharge, ← remainingCore_centers residual]
  exact sum_eq_sum_components object (remainingCore residual residual.centers)
    (residual.vertexCharge ledger)

/-- **The decomposition delivered to the Type A side.**  The Type A net charge of
every post-ledger component, minus the reserve its recorded boundary profile
charges, sums to at most the post-ledger core charge. -/
theorem sum_componentNetCharge_sub_reserve_le (residual : Residual object)
    (ledger : LoadCapacityProfile) :
    ((Connected.order object (remainingCore residual residual.centers)).map
        fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum
      ≤ residual.residualCoreCharge ledger := by
  rw [residualCoreCharge_eq_sum_components residual ledger]
  exact list_sum_map_le fun component _ =>
    componentResidual_netCharge_sub_reserve_le ledger component

/-! ### The route-8 core extraction, manuscript nodes `[76]`/`[85]`

`lem:typeB-bridge-with-route8-core` and `lem:decorated-envelope-with-route8-core`
are the two lemmas node `[76]` applies before handing on to `[77]`
("route-8 cores continue in Part IX").  Both state the *same* inequality

`No(X) ≥ -D_A(𝒜_X) - 8 Σ_{h ∈ H_X}(d_G(h) - 3)`,

the first for an ordinary connected assigned Type B bridge residual and the
second for a grouped decorated Type B envelope support.  Here they are one
theorem, because both supports are one carrier: `TypeBBridgeResidual.Residual`
(`def:decorated-typeB-envelope-support` supplies `Y_𝔠^*` and `H_𝔠` in exactly
that shape, as the header of this file records).

The manuscript's `𝒜_X` -- "the canonical collection of Type A route-8 residual
supports contained in the remaining non-window core" -- is not a chosen
subcollection here.  `residualCoreCharge_eq_sum_components` already decomposes
the post-ledger core over *all* its components, and the manuscript's own proof
discards the others by `lem:typeA-exclusion` ("every other component has no
route-8 residual profile and no decorated Type B handoff, so
`lem:typeA-exclusion` gives nonnegative net charge on it").  Summing over every
component is therefore the sharper statement: it needs no selection and no
appeal to `lem:typeA-exclusion`, and it specialises to the manuscript's by
dropping the nonnegative terms.

The manuscript's `-D_A(𝒜_X) = Σ_{Y ∈ 𝒜_X} No(Y)` uses `σ(Y) = 0` on a route-8
piece; the corresponding Lean term is `componentResidual_netCharge_eq` together
with `componentResidual_surplus`, which is `σ(Z) = 0` by construction rather
than by hypothesis.  The extra `- componentReserve` is the reserve the
component's own recorded boundary profile charges, classified into the
manuscript's three reserves by `deletedCarrierAt_classified`. -/

/-- **`lem:typeB-bridge-with-route8-core`, and with it
`lem:decorated-envelope-with-route8-core`.**  The net charge of an assigned
Type B bridge residual -- equivalently of a grouped decorated Type B envelope
support -- is bounded below by the Type A deficit its post-ledger components
carry, minus eight times its assigned surplus:

`No(X) ≥ Σ_Z (No(Z) - reserve(Z)) - 8 Σ_{h ∈ H_X}(d_G(h) - 3)`.

Nothing is assumed about the absence of a route-8 core.  The route-8 part is the
explicit first term, exactly as the manuscript carries `-D_A(𝒜_X)` in its
conclusion; `lem:typeB-bridge-deficit-bound` is the special case where that term
is nonnegative (`residualCoreCharge_nonneg_of_componentDeficit_nonneg`).

This is what manuscript node `[76]` hands to node `[77]`: the route-8 non-window
cores leave the Type B ledger as the summands of the first term and continue in
Part IX as entries of the Type A deficit ledger `D_A`, while the Type B side
retains only `8 Σ_{h}(d_G(h) - 3)`, which `prop:typeB-bridge-sublinear`
(`TypeBBridgeResidual.typeBBridgeSublinear_globalSurplus`) charges to
`16 σ(G)`. -/
theorem netCharge_ge_componentDeficit_sub_eight_surplus (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h) :
    ((Connected.order object (remainingCore residual residual.centers)).map
        fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum
        - 8 * residual.surplus
      ≤ residual.netCharge ledger := by
  have core := sum_componentNetCharge_sub_reserve_le residual ledger
  have bound :=
    residual.residualCoreCharge_sub_eight_surplus_le_netCharge ledger normal
  linarith

/-- **The collection form of the extraction.**  The undischarged remainder
`TypeBBridgeResidual.undischargedMass` that `prop:typeB-bridge-sublinear` carries
as an explicit term is bounded by the route-8 core deficit of the same
collection, member by member.  Combined with
`TypeBBridgeResidual.typeBBridgeSublinear_globalSurplus` this is the manuscript's

`M_B(𝒳_B) ≤ 16 σ(G) + D_A`,

the `[76]`/`[85]` statement "Type B cannot carry the linear deficit outside
two-carrier route 8": the only term that is not `O(σ(G)) = o(|R|)` on the
near-cubic spine is the extracted Type A route-8 deficit, which is precisely
what node `[77]` continues in Part IX. -/
theorem undischargedMass_le_componentDeficit (object : FiniteObject.{u})
    (ledger : LoadCapacityProfile) :
    undischargedMass object ledger
      ≤ ((bridgeResiduals object).map fun member =>
          max 0
            (-((Connected.order object
                (remainingCore member member.centers)).map fun component =>
                  (componentResidual member member.centers component).netCharge ledger
                    - componentReserve member member.centers component).sum)).sum := by
  unfold undischargedMass
  refine list_sum_map_le ?_
  intro member _
  have core := sum_componentNetCharge_sub_reserve_le member ledger
  exact max_le_max le_rfl (by linarith)

/-- **The Type A boundary, read at one component.**  Follows
`postLedgerCoreHygiene` at `Graph/TypeBPostLedgerCore.lean:624`: the statement is
indexed by a single component of the stored component order, with its
`memberOrder` witness, and says nothing about the other components.

Consumes `componentResidual_netCharge_sub_reserve_le` at
`Graph/TypeBPostLedgerCore.lean:508`.  Given the component's own Type A discharge
`reserve(Z) ≤ No(Z)`, the charge the post-ledger core carries on that component
-- the summand `residualCoreCharge_eq_sum_components` assembles -- is
nonnegative. -/
theorem componentCharge_nonneg_of_discharged (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (component :
      Connected.Component object (remainingCore residual residual.centers))
    (_memberOrder :
      component ∈ Connected.order object (remainingCore residual residual.centers))
    (discharged : componentReserve residual residual.centers component
      ≤ (componentResidual residual residual.centers component).netCharge ledger) :
    0 ≤ ∑ y ∈ (componentResidual residual residual.centers component).core,
        residual.vertexCharge ledger y := by
  have bound := componentResidual_netCharge_sub_reserve_le ledger component
  linarith

/-- **The Type A boundary, stated exactly.**  `lem:typeB-postledger-core-hygiene`
hands each post-ledger component to the Type A analysis as an admissible Type A
support.  The only input this file does not supply is the Type A deficit
`-D_A(𝒜_X)` that those components carry, i.e. the sign of the extracted quantity
`netCharge_ge_componentDeficit_sub_eight_surplus` already hands to node `[77]`.

Follows `TypeBExclusion.netCharge_nonneg_of_certificateClosed` at
`Graph/TypeBExclusion.lean:526`, whose post-ledger input is likewise a single
scalar read of the ledger quantity (`0 ≤ Residual.residualCoreCharge`) and not a
re-collected family.  Consumes `sum_componentNetCharge_sub_reserve_le` at
`Graph/TypeBPostLedgerCore.lean:735`, which owns the aggregation over the stored
component order; the summand-level fact is
`componentCharge_nonneg_of_discharged`.

Given it, the post-ledger core charge is nonnegative -- the alternative
`Residual.residualCoreCharge < 0` that `TypeBExclusion.typeBExclusion` retains is
closed by `not_lt.2` of this statement. -/
theorem residualCoreCharge_nonneg_of_componentDeficit_nonneg (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (deficit : 0 ≤ ((Connected.order object
        (remainingCore residual residual.centers)).map fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum) :
    0 ≤ residual.residualCoreCharge ledger :=
  le_trans deficit (sum_componentNetCharge_sub_reserve_le residual ledger)

/-- The third alternative of `TypeBExclusion.typeBExclusion` -- the retained
route-8 / Type A residual core with `residualCoreCharge < 0` -- is closed exactly
when the extracted Type A deficit of the post-ledger components is nonnegative.

Consumes `residualCoreCharge_nonneg_of_componentDeficit_nonneg` above; the
premise is the same single ledger read, so nothing is re-collected here. -/
theorem not_residualCoreCharge_neg_of_componentDeficit_nonneg (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (deficit : 0 ≤ ((Connected.order object
        (remainingCore residual residual.centers)).map fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum) :
    ¬ residual.residualCoreCharge ledger < 0 :=
  not_lt.2
    (residualCoreCharge_nonneg_of_componentDeficit_nonneg residual ledger deficit)

/-! ### The two prose citations of `lem:typeB-postledger-core-hygiene`

`TypeBBridgeResidual` cites this lemma twice, in prose only:

* the docstring of `Residual.residualCoreCharge` -- "the quantity the manuscript
  discharges through the Type A components of `lem:typeB-postledger-core-hygiene`"
  -- which is now `residualCoreCharge_eq_sum_components` (the decomposition into
  Type A components) together with
  `residualCoreCharge_nonneg_of_componentDeficit_nonneg` (the discharge);
* the docstring of `Residual.negativePart_le_eight_surplus` -- "the manuscript
  obtains this from `lem:typeB-postledger-core-hygiene` together with the Type A
  saturated handoff and unsaturated discharge" -- which is the theorem below.

Both prose sentences are now consequences of named results, so the citations are
citations of an actual Lean statement. -/

/-- **`lem:typeB-bridge-deficit-bound` in its sharp form.**  The manuscript
obtains `No_-(X) ≤ 8 Σ_{h ∈ H_X}(d_G(h) - 3)` from
`lem:typeB-postledger-core-hygiene` together with the Type A saturated handoff
and unsaturated discharge; here the hygiene decomposition is supplied by
`residualCoreCharge_nonneg_of_componentDeficit_nonneg` and the Type A input
enters only as the sign of the extracted deficit, so the remainder term
`max{0, -Ch(post-ledger core)}` of
`TypeBBridgeResidual.Residual.negativePart_le_eight_surplus` disappears.

Consumes `TypeBBridgeResidual.Residual.negativePart_le_eight_surplus` at
`Graph/TypeBBridgeResidual.lean:751` and
`residualCoreCharge_nonneg_of_componentDeficit_nonneg` above. -/
theorem negativePart_le_eight_surplus_of_componentDeficit_nonneg
    (residual : Residual object) (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (deficit : 0 ≤ ((Connected.order object
        (remainingCore residual residual.centers)).map fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum) :
    residual.negativePart ledger ≤ 8 * residual.surplus := by
  have bound := residual.negativePart_le_eight_surplus ledger normal
  have nonneg :=
    residualCoreCharge_nonneg_of_componentDeficit_nonneg residual ledger deficit
  have vanishes : max 0 (-residual.residualCoreCharge ledger) = 0 :=
    max_eq_left (by linarith)
  rw [vanishes, add_zero] at bound
  exact bound

/-- **The retained route-8 alternative of `lem:typeB-exclusion` is closed by the
hygiene decomposition.**  `TypeBExclusion.typeBExclusion` keeps
`residualCoreCharge < 0` as an explicit alternative because discharging it needs
the Type A analysis of the post-ledger core.  This lemma performs the Type B half
of that discharge -- the decomposition of the post-ledger core into admissible
Type A components -- so the only input left is the sign of the extracted Type A
deficit.

Consumes `TypeBExclusion.netCharge_nonneg_of_certificateClosed` at
`Graph/TypeBExclusion.lean:526` and
`residualCoreCharge_nonneg_of_componentDeficit_nonneg` above; it converts the
component-deficit read into that theorem's post-ledger input. -/
theorem netCharge_nonneg_of_componentDeficit_nonneg (residual : Residual object)
    (ledger : LoadCapacityProfile)
    (normal : ∀ h ∈ residual.centers, NormalForm object h)
    (fanInCore : ∀ h ∈ residual.centers, neighbourRim object h ⊆ residual.core)
    (b2 : DisjointCarriers residual)
    (closed : ∀ h ∈ residual.centers, IsCertificateClosed residual ledger h)
    (deficit : 0 ≤ ((Connected.order object
        (remainingCore residual residual.centers)).map fun component =>
          (componentResidual residual residual.centers component).netCharge ledger
            - componentReserve residual residual.centers component).sum) :
    0 ≤ residual.netCharge ledger :=
  netCharge_nonneg_of_certificateClosed residual ledger normal fanInCore b2 closed
    (residualCoreCharge_nonneg_of_componentDeficit_nonneg residual ledger deficit)

/-! ## Non-vacuity

The lemma is realised on the explicit finite graph already used by
`TypeBFanClosedPorts`, `TypeBBridgeResidual`, `TypeBExclusion` and
`TypeBOverlapObstruction`: a degree-four centre with four cubic neighbours
carrying private shoulder pairs, on the assigned support the object's own
enumeration produces.  There the fan envelope block deletes the centre and its
four neighbours, the post-ledger core is the eight shoulders, and it really does
split into components: the shoulder `5` lies in one of them, so the hygiene lemma
is applied to a *nonempty* component and none of its five conclusions is reached
vacuously. -/

namespace Witness

open Hypostructure.Graph.TypeBFanClosedPorts.Witness
open Hypostructure.Graph.TypeBBridgeResidual.Witness

local instance vertexDecEq : DecidableEq fanObject.Vertex :=
  inferInstanceAs (DecidableEq (Fin 13))

local instance vertexFintype : Fintype fanObject.Vertex :=
  inferInstanceAs (Fintype (Fin 13))

local instance adjDecidable : DecidableRel fanObject.graph.Adj := fanObject.decideAdj

/-- A shoulder of the witness fan: it survives the ledger deletion, so the
post-ledger core is nonempty. -/
def shoulder : fanObject.Vertex := (5 : Fin 13)

theorem shoulder_mem_remainingCore :
    shoulder ∈ remainingCore bridgeResidual bridgeResidual.centers := by
  rw [remainingCore_centers]
  decide

/-- The post-ledger core of the witness support is nonempty: the ledger entry at
the centre deletes the centre and its four fan neighbours, and the eight
shoulders remain. -/
theorem remainingCore_nonempty :
    (remainingCore bridgeResidual bridgeResidual.centers).Nonempty :=
  ⟨shoulder, shoulder_mem_remainingCore⟩

/-- **The hygiene lemma fires on a concrete graph, at a nonempty component.**
The shoulder `5` lies in a genuine connected component of the post-ledger core of
the witness support, so `postLedgerCoreHygiene` applies to a component that is
*not* empty and delivers it as an admissible Type A support: a connected
sub-support of the counted core with no assigned centre and no assigned surplus,
`P₁₃`-free by heredity, with its supplied deficiency charged to the recorded
reserves.  None of the five conclusions is reached vacuously. -/
theorem hygiene_fires (ledger : LoadCapacityProfile) (order : Nat) :
    ∃ component ∈
        Connected.order fanObject (remainingCore bridgeResidual bridgeResidual.centers),
      shoulder ∈
          (componentResidual bridgeResidual bridgeResidual.centers component).core ∧
        (componentResidual bridgeResidual bridgeResidual.centers component).core.Nonempty ∧
        (((componentResidual bridgeResidual bridgeResidual.centers component).core
              ⊆ bridgeResidual.core ∧
            Connected.ConnectedOn fanObject
              (componentResidual bridgeResidual bridgeResidual.centers component).core ∧
            (componentResidual bridgeResidual bridgeResidual.centers component).centers
              = ∅ ∧
            (componentResidual bridgeResidual bridgeResidual.centers component).surplus
              = 0 ∧
            ∀ h ∈ bridgeResidual.centers,
              h ∉ (componentResidual bridgeResidual bridgeResidual.centers
                component).core) ∧
          (InducedPathFree (fanObject.induce bridgeResidual.core) order →
            InducedPathFree (fanObject.induce
              (componentResidual bridgeResidual bridgeResidual.centers component).core)
              order) ∧
          (∀ y ∈ (componentResidual bridgeResidual bridgeResidual.centers component).core,
            bridgeResidual.coreDegree y
                = (componentResidual bridgeResidual bridgeResidual.centers
                    component).coreDegree y
                  + (deletedCarriersAt bridgeResidual bridgeResidual.centers y).card ∧
              (componentResidual bridgeResidual bridgeResidual.centers
                  component).deficiency y
                ≤ bridgeResidual.deficiency y
                  + ((deletedCarriersAt bridgeResidual bridgeResidual.centers y).card
                      : ℚ) ∧
              ∀ w ∈ deletedCarriersAt bridgeResidual bridgeResidual.centers y,
                (∃ h ∈ bridgeResidual.centers, w ∈ bridgeResidual.envelopeBlock h) ∧
                  (w ∈ bridgeResidual.centers ∨
                    (w ∈ hybridWindow ∧ ∀ profile : Profile fanObject,
                      profile.window = hybridWindow → y ∉ hybridWindow →
                        profile.IsWindowIncidence y w) ∨
                    (w ∉ hybridWindow ∧ w ∈ bridgeResidual.core ∧
                      ∃ h ∈ bridgeResidual.centers, w ∈ neighbourRim fanObject h))) ∧
          ((componentResidual bridgeResidual bridgeResidual.centers
                  component).netCharge ledger
              - componentReserve bridgeResidual bridgeResidual.centers component
            ≤ ∑ y ∈ (componentResidual bridgeResidual bridgeResidual.centers
                component).core, bridgeResidual.vertexCharge ledger y)) := by
  obtain ⟨component, memberOrder, shoulderMember⟩ :=
    (Connected.mem_support_iff_mem_component_with_vertices fanObject
      (remainingCore bridgeResidual bridgeResidual.centers) shoulder).1
      shoulder_mem_remainingCore
  exact ⟨component, memberOrder, shoulderMember, ⟨shoulder, shoulderMember⟩,
    postLedgerCoreHygiene bridgeResidual ledger hybridWindow order component
      memberOrder⟩

end Witness

end Hypostructure.Graph.TypeBPostLedgerCore
