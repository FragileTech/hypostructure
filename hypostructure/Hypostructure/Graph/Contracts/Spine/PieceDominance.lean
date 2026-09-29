import Hypostructure.Graph.Statements.PieceDominance

/-!
# Contracts: CT3, dominance irreducibility of G's pieces

Each statement of `Statements.PieceDominance` from the facts it consumes: the
target avoidance of G (node `[1]`), node `[13]`'s exclusion of replacement
supports, and (for the canonical pieces of `R`) node `[15]`'s maximal packing,
which makes every piece of `R` a proper support.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **CT3 at G.**  From target avoidance and `lem:replacement` (node `[13]`):
a dominated gadget glued into `G − Z` is target-free
(`DominatedReplacement.not_target_glue_of_dominated`), so a smaller,
profile-preserving, baseline-keeping dominated gadget would be a replacement
support. -/
theorem pieceDominanceIrreducible (data : Parameters) (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (exclusion : ReplacementExclusionStatement data object) :
    PieceDominanceIrreducibleStatement data object :=
  fun _support connected proper gadget smaller profile baseline =>
    DominatedReplacement.not_dominated_of_exclusion avoids exclusion connected proper
      gadget smaller profile baseline

/-- **CT3 at G, terminal-pair form.** -/
theorem twoExitNewLength (data : Parameters) (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (exclusion : ReplacementExclusionStatement data object) :
    TwoExitNewLengthStatement data object :=
  fun _support connected proper _first _second distinct two gadget smaller profile baseline
      noCycle =>
    DominatedReplacement.exists_new_length_of_exclusion avoids exclusion connected proper
      distinct two gadget smaller profile baseline noCycle

/-- A vertex of a packed window of `P₀` lies outside `R`: `P₀` is nonempty and
its windows are nonempty (node `[15]`). -/
theorem exists_not_mem_remainder (data : Parameters) (object : FiniteObject.{u})
    (maximal : MaximalPackingStatement data object) :
    ∃ vertex, vertex ∉ object.remainderSupport (canonicalWindowPacking data object) := by
  obtain ⟨pos, valid, card, -⟩ := maximal
  have nonempty : (canonicalWindowPacking data object).Nonempty :=
    Finset.card_pos.mp (card ▸ pos)
  obtain ⟨window, present⟩ := nonempty
  obtain ⟨vertex, inside⟩ :=
    object.nonempty_of_inducesWindow data.windowOrder_pos (valid.1 window present)
  exact ⟨vertex, fun inRemainder =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport inRemainder
      (FiniteObject.mem_windowSupport present inside)⟩

/-- A canonical piece of `R` is a proper connected support of G. -/
theorem canonicalPiece_connected_proper (data : Parameters) (object : FiniteObject.{u})
    (maximal : MaximalPackingStatement data object)
    {piece : SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (present : piece ∈ object.canonicalPieces
      (object.remainderSupport (canonicalWindowPacking data object))) :
    SupportComponents.Connected.ConnectedOn object
        (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object))
          piece) ∧
      ∃ vertex, vertex ∉ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) piece := by
  refine ⟨SupportComponents.Connected.connectedOn_of_mem_order object _
    ((object.mem_canonicalPieces _).mp present), ?_⟩
  obtain ⟨vertex, outside⟩ := exists_not_mem_remainder data object maximal
  exact ⟨vertex, fun inside => outside (object.pieceSupport_subset _ piece inside)⟩

/-- **CT3 at the canonical pieces of `R`.** -/
theorem canonicalPieceDominance (data : Parameters) (object : FiniteObject.{u})
    (irreducible : PieceDominanceIrreducibleStatement data object)
    (maximal : MaximalPackingStatement data object) :
    CanonicalPieceDominanceStatement data object := by
  intro piece present
  obtain ⟨connected, proper⟩ := canonicalPiece_connected_proper data object maximal present
  exact irreducible _ connected proper

/-- **CT3, terminal-pair form, at the canonical pieces of `R`.** -/
theorem canonicalTwoExitNewLength (data : Parameters) (object : FiniteObject.{u})
    (twoExit : TwoExitNewLengthStatement data object)
    (maximal : MaximalPackingStatement data object) :
    CanonicalTwoExitNewLengthStatement data object := by
  intro piece present
  obtain ⟨connected, proper⟩ := canonicalPiece_connected_proper data object maximal present
  exact twoExit _ connected proper

/-- **Two-exit size monotonicity at G**: from target avoidance, the baseline and
node `[13]`, through the copy of `G[Z']` onto `{u, v}`
(`DominatedReplacement.internalVertexCount_le_of_twoExit`). -/
theorem twoExitSizeMonotone (data : Parameters) (object : FiniteObject.{u})
    (avoids : ¬ HasCycleWithLength data.LengthOK object)
    (base : MinimumDegreeAtLeast data.threshold object)
    (exclusion : ReplacementExclusionStatement data object) :
    TwoExitSizeMonotoneStatement data object :=
  fun _support _other connected proper _first _second distinct two _first' _second'
      distinct' two' degFirst degSecond lengths =>
    DominatedReplacement.internalVertexCount_le_of_twoExit avoids exclusion base connected
      proper distinct two distinct' two' degFirst degSecond lengths

/-- **Two-exit size monotonicity between the canonical pieces of `R`.** -/
theorem canonicalTwoExitSizeMonotone (data : Parameters) (object : FiniteObject.{u})
    (monotone : TwoExitSizeMonotoneStatement data object)
    (maximal : MaximalPackingStatement data object) :
    CanonicalTwoExitSizeMonotoneStatement data object := by
  intro piece present piece' _present'
  obtain ⟨connected, proper⟩ := canonicalPiece_connected_proper data object maximal present
  exact monotone _ _ connected proper

end Hypostructure.Graph.Contracts.Spine
