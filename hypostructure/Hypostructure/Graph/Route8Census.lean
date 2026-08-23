import Hypostructure.Graph.Route8Residual
import Hypostructure.Graph.Route8Supply
import Hypostructure.Graph.Route8CarrierCore
import Hypostructure.Graph.VisibleReceiverEntry
import Hypostructure.Graph.WindowRemainder

/-!
# The route-8 census at one object: nodes `[111]`--`[113]`, `[117]`--`[122]`

`def:typeA-route8-carriers` indexes the route-8 entries `(u, B_u)` of the
extracted Type A collection `𝒳_A`; `prop:typeA-route8-carrier-reduction`
counts their private essential carriers against the boundary-incidence supply
`def⁺(R)` and the deficit `|R| ≤ N_basin + s·def⁺(R)` (`lem:typeA-route8-burden`
substituted into `def:typeA-large-budget-deficit`), and closes the
no-two-carrier branch by the registered rate `τ < 3/13`.

This module states that census *at the object*: the entries are the
`(piece, receiver, silent-excess load)` triples of the Type A pieces of the
canonical decomposition of the remainder, each with its selected trace basin
(`Route8.TraceBasin.select?`) and its graph-owned presented entry
(`Route8.PresentedEntry.ofTraceBasin`); an entry's core is the canonical
essential carrier core of that entry; the supply is the cut of the remainder.
The two carrier lemmas of `Graph/Route8CarrierCore` then apply verbatim.  No
abstract index type, no census package, no numeral.
-/

namespace Hypostructure.Graph.Route8Census

open Hypostructure
open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u})

attribute [local instance] Route8.vertexDecEq

/-- The index of a route-8 basin entry: its Type A piece, its receiver `w`,
and its silent-excess load `u`. -/
abbrev Index : Type u := Finset object.Vertex × object.Vertex × object.Vertex

instance : DecidableEq (Index object) := by
  classical
  exact inferInstance

/-- The negative zero-surplus pieces of the canonical decomposition of the
remainder `R`. -/
noncomputable def typeAPieces (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) : Finset (Finset object.Vertex) := by
  classical
  exact ((object.canonicalPieces (object.remainderSupport packing)).image
    (object.pieceSupport (object.remainderSupport packing))).filter fun piece =>
      object.NegativeNetCharge piece threshold discharge ∧
        object.ambientSurplus piece threshold = 0

/-- Every silent-excess load of every receiver of every negative zero-surplus
canonical piece. -/
noncomputable def entries (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) : Finset (Index object) := by
  classical
  exact (typeAPieces object packing threshold discharge).biUnion fun piece =>
    (object.receivers piece threshold).biUnion fun receiver =>
      (VisibleEntry.silentExcess object piece threshold discharge receiver).image
        fun load => (piece, receiver, load)

theorem mem_entries {packing : Finset (Finset object.Vertex)}
    {threshold discharge : Nat} {index : Index object} :
    index ∈ entries object packing threshold discharge ↔
      index.1 ∈ typeAPieces object packing threshold discharge ∧
        index.2.1 ∈ object.receivers index.1 threshold ∧
        index.2.2 ∈ VisibleEntry.silentExcess object index.1 threshold discharge
          index.2.1 := by
  classical
  obtain ⟨piece, receiver, load⟩ := index
  simp only [entries, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨piece', pieceMem, receiver', receiverMem, load', loadMem, rfl, rfl, rfl⟩
    exact ⟨pieceMem, receiverMem, loadMem⟩
  · rintro ⟨pieceMem, receiverMem, loadMem⟩
    exact ⟨piece, pieceMem, receiver, receiverMem, load, loadMem, rfl, rfl, rfl⟩

/-- **The exact route-`8` entry family `Ξ(𝒳)`.**

The caller supplies the canonical component subcollection `𝒳` selected by
`def:typeA-route8-carriers`.  Each index is exactly a saturated receiver and an
unpaid silent-excess load of one component of that collection.  The component
is not stored in the index: its canonical piece support is the manuscript's
`X` in the tuple `(X,w,u,B_u)`. -/
noncomputable def entriesOfComponents
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge : Nat) : Finset (Index object) := by
  classical
  exact components.biUnion fun component =>
    let piece := object.pieceSupport (object.remainderSupport packing) component
    (VisibleEntry.saturatedReceivers object piece threshold discharge).biUnion
      fun receiver =>
        (VisibleEntry.silentExcess object piece threshold discharge receiver).image
          fun load => (piece, receiver, load)

/-- `B_u`: the trace basin selected for the entry (`def:typeA-trace-basin`). -/
noncomputable def basin (threshold : Nat) (index : Index object) :
    Finset object.Vertex :=
  (Route8.TraceBasin.select? object index.1 threshold index.2.1 index.2.2).getD ∅

/-- The graph-owned presented entry of the index (`def:typeA-route8-carriers`). -/
noncomputable def presented (threshold : Nat) (LengthOK : Nat → Prop)
    (index : Index object) : Route8.PresentedEntry object :=
  Route8.PresentedEntry.ofTraceBasin object index.1 (basin object threshold index)
    threshold LengthOK index.2.1 index.2.2

/-- `𝓒_ess(ξ)`: the canonical essential carrier core of the entry. -/
noncomputable def core (threshold : Nat) (LengthOK : Nat → Prop)
    (index : Index object) : Finset (Sym2 object.Vertex) :=
  ((presented object threshold LengthOK index).toEntry
    (HasCycleWithLength LengthOK)).essentialCore

/-- The boundary-incidence supply: the cut of the remainder `R`. -/
noncomputable def supply (packing : Finset (Finset object.Vertex)) :
    Finset (Sym2 object.Vertex) :=
  Route8.cutEdges object (object.remainderSupport packing)

/-- A core lies in the cut of its own piece. -/
theorem core_subset_cutEdges (threshold : Nat) (LengthOK : Nat → Prop)
    (index : Index object) :
    core object threshold LengthOK index ⊆ Route8.cutEdges object index.1 := by
  intro carrier member
  have := ((presented object threshold LengthOK index).toEntry
    (HasCycleWithLength LengthOK)).essentialCore_subset_carriers member
  have supportEq : (presented object threshold LengthOK index).support = index.1 := rfl
  simpa [Route8.PresentedEntry.toEntry, Route8.cutSchedule_toFinset, supportEq] using this

/-- The cut of a piece of the remainder lies in the cut of the remainder: a
component of `R` has no edge to the rest of `R`. -/
theorem cutEdges_piece_subset (packing : Finset (Finset object.Vertex))
    (component : SupportComponents.Connected.Component object
      (object.remainderSupport packing)) :
    Route8.cutEdges object
        (object.pieceSupport (object.remainderSupport packing) component) ⊆
      Route8.cutEdges object (object.remainderSupport packing) := by
  intro edge member
  rw [Route8.mem_cutEdges] at member ⊢
  obtain ⟨edgeMem, inside, insideMem, outside, outsideMem, insidePiece, outsidePiece⟩ :=
    member
  refine ⟨edgeMem, inside, insideMem, outside, outsideMem, ?_, ?_⟩
  · exact object.pieceSupport_subset _ component insidePiece
  · intro outsideRemainder
    apply outsidePiece
    have adjacent : object.graph.Adj inside outside := by
      have edgeAdj : edge ∈ object.graph.edgeSet := by simpa using edgeMem
      have distinct : inside ≠ outside := by
        intro same
        exact outsidePiece (same ▸ insidePiece)
      induction edge using Sym2.inductionOn with
      | hf left right =>
        simp only [Sym2.mem_iff] at insideMem outsideMem
        rcases insideMem with rfl | rfl <;> rcases outsideMem with rfl | rfl
        · exact absurd rfl distinct
        · exact edgeAdj
        · exact edgeAdj.symm
        · exact absurd rfl distinct
    exact SupportComponents.Connected.neighbor_mem_vertices object _ component
      insidePiece outsideRemainder adjacent

/-- Every entry's core lies in the supply. -/
theorem core_subset_supply (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) :
    ∀ index ∈ entries object packing threshold discharge,
      core object threshold LengthOK index ⊆ supply object packing := by
  intro index member
  have pieceMem := (mem_entries object).1 member |>.1
  classical
  simp only [typeAPieces, Finset.mem_filter, Finset.mem_image] at pieceMem
  obtain ⟨⟨component, _, pieceEq⟩, _⟩ := pieceMem
  refine (core_subset_cutEdges object threshold LengthOK index).trans ?_
  rw [← pieceEq]
  exact cutEdges_piece_subset object packing component

/-! ## The census readings and the two-carrier decision

The two readings carry the manuscript's `o(|R|)` explicitly as `slack`: the
deficit `|R| ≤ N_basin + s·|∂R| + slack` is `def:typeA-large-budget-deficit`
with `lem:typeA-route8-burden` substituted and the Type B bridge mass
(`prop:typeB-bridge-sublinear`) charged to `slack`; the rate is
`rem:route8-carrier-margin`'s `τ < 3/13` with the same slack on the ambient
side.  The supply `|∂R|` is `e(R,W)` (`Route8.card_cutEdges_eq_boundaryIncidence`). -/

/-- **`def:typeA-large-budget-deficit` with `lem:typeA-route8-burden`
substituted** (node `[113]`): `|R| ≤ N_basin + s·|∂R| + slack`. -/
def Deficit (packing : Finset (Finset object.Vertex)) (threshold discharge slack : Nat) :
    Prop :=
  (object.remainderSupport packing).card ≤
    (entries object packing threshold discharge).card +
      discharge * (supply object packing).card + slack

/-- The same cleared deficit reading on the exact route-`8` collection
`Ξ(𝒳)`, rather than on the broader unified Type A ledger. -/
def CollectionDeficit
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge slack : Nat) : Prop :=
  (object.remainderSupport packing).card ≤
    (entriesOfComponents object packing components threshold discharge).card +
      discharge * (supply object packing).card + slack

/-- **The private-carrier rate** (nodes `[120]`--`[122]`, `rem:route8-carrier-margin`):
`(δ·s + 1)·|∂R| + δ·slack < δ·|R|`, i.e. `τ < δ/(δs+1)` with the `o(|R|)`
allowance; at the manuscript's `δ = 3`, `s = 4` this is `13·τ|R| < 3|R| − o(|R|)`,
i.e. `τ < 3/13`. -/
def Rate (packing : Finset (Finset object.Vertex)) (threshold discharge slack : Nat) :
    Prop :=
  (threshold * discharge + 1) * (supply object packing).card + threshold * slack <
    threshold * (object.remainderSupport packing).card

/-- The supply is the boundary incidence `e(R,W)` of the remainder. -/
theorem card_supply (packing : Finset (Finset object.Vertex)) :
    (supply object packing).card =
      object.boundaryIncidence (object.remainderSupport packing) :=
  Route8.card_cutEdges_eq_boundaryIncidence _

/-- **The two-carrier condition of node `[117]`** at an entry
(`def:typeA-terminal-two-carrier`): at most `δ − 1` private essential carriers
— the manuscript's "at most two private essential carriers" at `δ = 3`; the
no-two-carrier bound is therefore `δ` private carriers per entry. -/
def TwoCarrierEntry (packing : Finset (Finset object.Vertex))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (index : Index object) :
    Prop :=
  Route8.IndexedTwoCarrierCore (entries object packing threshold discharge)
    (core object threshold LengthOK) (threshold - 1) index

/-- The paper's two-support condition `π_𝒳(ξ) ≤ 2`, with privacy measured
inside the exact selected route-`8` collection `Ξ(𝒳)`. -/
def CollectionTwoCarrierEntry
    (packing : Finset (Finset object.Vertex))
    (components : Finset (SupportComponents.Connected.Component object
      (object.remainderSupport packing)))
    (threshold discharge : Nat) (LengthOK : Nat → Prop) (index : Index object) :
    Prop :=
  Route8.IndexedTwoCarrierCore
    (entriesOfComponents object packing components threshold discharge)
    (core object threshold LengthOK) (threshold - 1) index

/-- The two slack readings, transported to the slack-free ambient
`|R| − slack` the carrier lemmas of `Graph/Route8CarrierCore` are stated on. -/
theorem ambient_of_readings {ambient supplyCard entriesCard threshold discharge slack : Nat}
    (thresholdPos : 1 ≤ threshold)
    (deficit : ambient ≤ entriesCard + discharge * supplyCard + slack)
    (rate : (threshold * discharge + 1) * supplyCard + threshold * slack <
      threshold * ambient) :
    ambient - slack ≤ entriesCard + discharge * supplyCard ∧
      ((threshold - 1 + 1) * discharge + 1) * supplyCard <
        (threshold - 1 + 1) * (ambient - slack) := by
  rw [Nat.sub_add_cancel thresholdPos]
  have slackLt : slack < ambient := by
    by_contra notLt
    have le : ambient ≤ slack := Nat.le_of_not_lt notLt
    have := Nat.mul_le_mul_left threshold le
    omega
  refine ⟨by omega, ?_⟩
  rw [Nat.mul_sub]
  have := Nat.mul_le_mul_left threshold (Nat.le_of_lt slackLt)
  omega

/-- **`prop:typeA-route8-carrier-reduction`** at the object: the census gives a
two-carrier entry. -/
theorem exists_twoCarrierEntry (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (deficit : Deficit object packing threshold discharge slack)
    (rate : Rate object packing threshold discharge slack) :
    ∃ index ∈ entries object packing threshold discharge,
      TwoCarrierEntry object packing threshold discharge LengthOK index := by
  obtain ⟨deficit', rate'⟩ := ambient_of_readings thresholdPos deficit rate
  exact Route8.exists_indexedTwoCarrierCore (entries object packing threshold discharge)
    (core object threshold LengthOK) (supply object packing)
    (core_subset_supply object packing threshold discharge LengthOK) deficit' rate'

/-- **Nodes `[119]`--`[122]`**: the no-two-carrier branch contradicts the census. -/
theorem false_of_noTwoCarrier (packing : Finset (Finset object.Vertex))
    (threshold discharge slack : Nat) (LengthOK : Nat → Prop)
    (thresholdPos : 1 ≤ threshold)
    (deficit : Deficit object packing threshold discharge slack)
    (rate : Rate object packing threshold discharge slack)
    (noTwo : ∀ index ∈ entries object packing threshold discharge,
      ¬ TwoCarrierEntry object packing threshold discharge LengthOK index) : False := by
  obtain ⟨deficit', rate'⟩ := ambient_of_readings thresholdPos deficit rate
  exact Route8.noTwoCarrier_contradiction (entries object packing threshold discharge)
    (core object threshold LengthOK) (supply object packing)
    (core_subset_supply object packing threshold discharge LengthOK) deficit' rate' noTwo

end Hypostructure.Graph.Route8Census
