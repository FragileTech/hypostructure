import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.TypeBHybridIncidence

/-!
# Canonical Type B component carriers

The canonical support decomposition retains a component of the packed-window
remainder, rather than an arbitrary connected subset.  At that granularity an
incidence missing from the component has a unique explanation: its far endpoint
lies in the packed-window union.  This module records that equality before any
Type B candidate or ledger is formed.
-/

namespace Hypostructure.Graph.TypeBCanonicalCarrier

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.TypeBHybridIncidence

universe u

variable {object : FiniteObject.{u}}

noncomputable section

local instance objectVertexFinEnum : FinEnum object.Vertex := object.vertices
local instance objectVertexDecidableEq : DecidableEq object.Vertex :=
  object.vertices.decEq
local instance objectAdjDecidable : DecidableRel object.graph.Adj :=
  object.decideAdj

/-- An actual member of the canonical component decomposition of the fixed
packed-window remainder. -/
abbrev PieceIndex (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex)) :=
  { component : SupportComponents.Connected.Component object
      (object.remainderSupport packing) //
    component ∈ object.canonicalPieces (object.remainderSupport packing) }

/-- `Y_X`, the literal vertex support of a retained canonical component. -/
noncomputable def support (object : FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)}
    (piece : PieceIndex object packing) : Finset object.Vertex :=
  object.pieceSupport (object.remainderSupport packing) piece.1

theorem support_subset_remainder (object : FiniteObject.{u})
    {packing : Finset (Finset object.Vertex)}
    (piece : PieceIndex object packing) :
    support object piece ⊆ object.remainderSupport packing :=
  object.pieceSupport_subset (object.remainderSupport packing) piece.1

/-- The non-hub shoulders of `u` whose far endpoint lies in the packed-window
union. -/
noncomputable def windowShoulders (object : FiniteObject.{u})
    (packing : Finset (Finset object.Vertex))
    (hub owner : object.Vertex) : Finset object.Vertex :=
  nonHubIncidences object hub owner ∩ object.windowSupport packing

/-- In a canonical remainder component, the literal neighbours of `u` missing
from the component are exactly its window shoulders.  Equality, rather than
only equality of cardinalities, retains ownership of every incidence. -/
theorem missingNeighbours_eq_windowShoulders
    {packing : Finset (Finset object.Vertex)}
    (piece : PieceIndex object packing) {hub owner : object.Vertex}
    (hubMem : hub ∈ support object piece)
    (ownerMem : owner ∈ support object piece) :
    object.graph.neighborFinset owner \ support object piece =
      windowShoulders object packing hub owner := by
  classical
  ext other
  rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
    windowShoulders, Finset.mem_inter, mem_nonHubIncidences_iff]
  constructor
  · rintro ⟨adjacent, outside⟩
    have notHub : other ≠ hub := by
      intro equal
      exact outside (equal ▸ hubMem)
    refine ⟨⟨notHub, adjacent⟩, ?_⟩
    by_contra notWindow
    have inRemainder : other ∈ object.remainderSupport packing := by
      simp [FiniteObject.remainderSupport, notWindow]
    have inPiece := SupportComponents.Connected.neighbor_mem_vertices object
      (object.remainderSupport packing) piece.1 ownerMem inRemainder adjacent
    exact outside inPiece
  · rintro ⟨⟨_notHub, adjacent⟩, inWindow⟩
    refine ⟨adjacent, ?_⟩
    intro inPiece
    exact (FiniteObject.notMem_windowSupport_of_mem_remainderSupport
      (support_subset_remainder object piece inPiece)) inWindow

/-- The missing internal-degree units of a baseline fan neighbour are exactly
its window shoulders. -/
theorem missingInternalDegree_eq_card_windowShoulders
    {packing : Finset (Finset object.Vertex)}
    (piece : PieceIndex object packing) {threshold : Nat}
    {hub owner : object.Vertex}
    (hubMem : hub ∈ support object piece)
    (ownerMem : owner ∈ support object piece)
    (baseline : object.degree owner = threshold) :
    threshold - object.internalDegree (support object piece) owner =
      (windowShoulders object packing hub owner).card := by
  classical
  have split := Finset.card_sdiff_add_card_inter
    (s := object.graph.neighborFinset owner) (t := support object piece)
  have missing := congrArg Finset.card
    (missingNeighbours_eq_windowShoulders piece hubMem ownerMem)
  have degreeCard : (object.graph.neighborFinset owner).card =
      object.degree owner := by
    simpa [FiniteObject.degree] using
      (SimpleGraph.card_neighborFinset_eq_degree object.graph owner)
  have internalCard :
      (object.graph.neighborFinset owner ∩ support object piece).card =
        object.internalDegree (support object piece) owner := by
    rfl
  rw [missing, degreeCard, internalCard, baseline] at split
  omega

/-- At the common scale `2s`, a canonical cubic fan neighbour's core charge is
exactly its two copies of window-shoulder capacity minus the two unit debits.
No incidence credit is added on top of this charge: this identity is the
carrier refinement. -/
theorem twice_scaledCoreCharge_eq_windowShoulders
    {packing : Finset (Finset object.Vertex)}
    (piece : PieceIndex object packing) {threshold dischargeScale : Nat}
    {hub owner : object.Vertex}
    (hubMem : hub ∈ support object piece)
    (ownerMem : owner ∈ support object piece)
    (baseline : object.degree owner = threshold) :
    2 * (((dischargeScale *
          (threshold - object.internalDegree (support object piece) owner) : Nat) :
        Int) - 1) =
      -2 +
        (dischargeScale : Int) *
          (windowShoulders object packing hub owner).card +
        (dischargeScale : Int) *
          (windowShoulders object packing hub owner).card := by
  rw [missingInternalDegree_eq_card_windowShoulders piece hubMem ownerMem baseline]
  push_cast
  ring

end

end Hypostructure.Graph.TypeBCanonicalCarrier
