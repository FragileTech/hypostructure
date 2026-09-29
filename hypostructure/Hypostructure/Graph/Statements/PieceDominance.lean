import Hypostructure.Graph.Statements.Spine
import Hypostructure.Graph.DominatedReplacement

/-!
# Statements: CT3, dominance irreducibility of G's pieces

External-type compression at G (`Graph.DominatedReplacement`).  A gadget `Y` on
the cut boundary `∂Z` of a support `Z` of G is *dominated* by `G[Z]` when every
linkage system of `Y` (vertex-disjoint terminal-to-terminal paths) is realized
in `G[Z]` with the same terminal pairing and length vector, interiors in
`int(Z)`, and `Y` has no power-of-two cycle of its own.  A dominated gadget
glued into `G − Z` closes no power-of-two cycle, so node `[13]`
(`lem:replacement`) forbids it as soon as it is strictly smaller and keeps the
baseline and the boundary-degree profile.

* `PieceDominanceIrreducibleStatement` (key `pieceDominanceIrreducible`): every
  proper connected support of G is dominance-irreducible.
* `CanonicalPieceDominanceStatement` (key `canonicalPieceDominance`): the same
  at every canonical piece of `R = G − W` (`W` the support of the canonical
  packing `P₀`).
* `TwoExitNewLengthStatement` (key `twoExitNewLength`): the terminal-pair form
  at every two-exit support: a smaller degree-valid gadget without a
  power-of-two cycle has a `u`–`v` path whose length is not a `u`–`v` path
  length of G inside `Z`.
* `CanonicalTwoExitNewLengthStatement` (key `canonicalTwoExitNewLength`): the
  terminal-pair form at every two-exit canonical piece of `R`.
* `TwoExitSizeMonotoneStatement` (key `twoExitSizeMonotone`): the explicit
  quantitative consequence, through the copy of one two-exit support of G onto
  the terminals of another (`DominatedReplacement.copyPiece`, constructed from
  G): for a proper connected two-exit support `Z` and a two-exit support `Z'`
  with matching terminal inner degrees, `L_{Z'}(u', v') ⊆ L_Z(u, v)` forces
  `|int Z| ≤ |int Z'|`.
* `CanonicalTwoExitSizeMonotoneStatement` (key `canonicalTwoExitSizeMonotone`):
  the same between any two two-exit canonical pieces of `R`.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

/-- **Dominance irreducibility of G's pieces** (CT3).  For every proper
connected support `Z` of G, no gadget `Y` on `∂Z` with fewer interior vertices
than `G[Z]`, the boundary-degree profile of `G[Z]` and minimum degree at least
the threshold in `glue Y (G − Z)` is dominated by `G[Z]`. -/
noncomputable abbrev PieceDominanceIrreducibleStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ support : Finset object.Vertex,
    Graph.SupportComponents.Connected.ConnectedOn object support →
    (∃ vertex, vertex ∉ support) →
    ∀ gadget : Graph.BoundaryPiece (SupportAtom.boundary object support),
      gadget.internalVertexCount < (SupportAtom.piece object support).internalVertexCount →
      gadget.boundaryDegreeProfile =
          (SupportAtom.piece object support).boundaryDegreeProfile →
      Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue gadget (SupportAtom.outside object support)) →
      ¬ Graph.DominatedReplacement.Dominated data.LengthOK gadget

/-- **Every canonical piece of `R` is dominance-irreducible** (CT3 at the
canonical pieces of the remainder of `P₀`). -/
noncomputable abbrev CanonicalPieceDominanceStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ∀ piece ∈ object.canonicalPieces remainder,
    ∀ gadget : Graph.BoundaryPiece
        (SupportAtom.boundary object (object.pieceSupport remainder piece)),
      gadget.internalVertexCount <
          (SupportAtom.piece object (object.pieceSupport remainder piece)).internalVertexCount →
      gadget.boundaryDegreeProfile =
          (SupportAtom.piece object (object.pieceSupport remainder piece)).boundaryDegreeProfile →
      Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue gadget
            (SupportAtom.outside object (object.pieceSupport remainder piece))) →
      ¬ Graph.DominatedReplacement.Dominated data.LengthOK gadget

/-- **Two-exit irreducibility** (CT3, terminal-pair form).  For every proper
connected support `Z` of G whose cut boundary is exactly two vertices `u ≠ v`,
every gadget `Y` on `{u, v}` with fewer interior vertices than `G[Z]`, the
boundary-degree profile of `G[Z]`, minimum degree at least the threshold in
`glue Y (G − Z)` and no power-of-two cycle of its own has a `u`–`v` path whose
length is not in `L_Z(u, v)`, the set of lengths of the `u`–`v` paths of G
inside `Z`. -/
noncomputable abbrev TwoExitNewLengthStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ support : Finset object.Vertex,
    Graph.SupportComponents.Connected.ConnectedOn object support →
    (∃ vertex, vertex ∉ support) →
    ∀ first second : (SupportAtom.boundary object support).Vertex, first ≠ second →
    (∀ label, label = first ∨ label = second) →
    ∀ gadget : Graph.BoundaryPiece (SupportAtom.boundary object support),
      gadget.internalVertexCount < (SupportAtom.piece object support).internalVertexCount →
      gadget.boundaryDegreeProfile =
          (SupportAtom.piece object support).boundaryDegreeProfile →
      Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue gadget (SupportAtom.outside object support)) →
      ¬ Graph.HasCycleWithLength data.LengthOK gadget.pack →
      ∃ path : gadget.graph.Walk (.inl first) (.inl second), path.IsPath ∧
        path.length ∉ Graph.DominatedReplacement.pathLengths object support first.1 second.1

/-- **Two-exit irreducibility at the canonical pieces of `R`.** -/
noncomputable abbrev CanonicalTwoExitNewLengthStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ∀ piece ∈ object.canonicalPieces remainder,
    ∀ first second :
        (SupportAtom.boundary object (object.pieceSupport remainder piece)).Vertex,
      first ≠ second → (∀ label, label = first ∨ label = second) →
    ∀ gadget : Graph.BoundaryPiece
        (SupportAtom.boundary object (object.pieceSupport remainder piece)),
      gadget.internalVertexCount <
          (SupportAtom.piece object (object.pieceSupport remainder piece)).internalVertexCount →
      gadget.boundaryDegreeProfile =
          (SupportAtom.piece object (object.pieceSupport remainder piece)).boundaryDegreeProfile →
      Graph.MinimumDegreeAtLeast data.threshold
          (Graph.glue gadget
            (SupportAtom.outside object (object.pieceSupport remainder piece))) →
      ¬ Graph.HasCycleWithLength data.LengthOK gadget.pack →
      ∃ path : gadget.graph.Walk (.inl first) (.inl second), path.IsPath ∧
        path.length ∉ Graph.DominatedReplacement.pathLengths object
          (object.pieceSupport remainder piece) first.1 second.1

/-- **Two-exit size monotonicity** (CT3, explicit form).  For a proper
connected support `Z` of G with cut boundary `{u, v}` and a support `Z'` with
cut boundary `{u', v'}` such that `u'`, `v'` have as many neighbours in `Z'` as
`u`, `v` have in `Z`: if every `u'`–`v'` path length inside `Z'` is a `u`–`v`
path length inside `Z`, then `Z` has at most as many interior vertices as
`Z'`. -/
noncomputable abbrev TwoExitSizeMonotoneStatement (_data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∀ support other : Finset object.Vertex,
    Graph.SupportComponents.Connected.ConnectedOn object support →
    (∃ vertex, vertex ∉ support) →
    ∀ first second : (SupportAtom.boundary object support).Vertex, first ≠ second →
    (∀ label, label = first ∨ label = second) →
    ∀ first' second' : (SupportAtom.boundary object other).Vertex, first' ≠ second' →
    (∀ label, label = first' ∨ label = second') →
    (Graph.DominatedReplacement.innerNeighbours object other first'.1).ncard =
        (Graph.DominatedReplacement.innerNeighbours object support first.1).ncard →
    (Graph.DominatedReplacement.innerNeighbours object other second'.1).ncard =
        (Graph.DominatedReplacement.innerNeighbours object support second.1).ncard →
    Graph.DominatedReplacement.pathLengths object other first'.1 second'.1 ⊆
        Graph.DominatedReplacement.pathLengths object support first.1 second.1 →
    (SupportAtom.piece object support).internalVertexCount ≤
      (SupportAtom.piece object other).internalVertexCount

/-- **Two-exit size monotonicity between the canonical pieces of `R`.** -/
noncomputable abbrev CanonicalTwoExitSizeMonotoneStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  let remainder := object.remainderSupport (canonicalWindowPacking data object)
  ∀ piece ∈ object.canonicalPieces remainder, ∀ piece' ∈ object.canonicalPieces remainder,
    ∀ first second :
        (SupportAtom.boundary object (object.pieceSupport remainder piece)).Vertex,
      first ≠ second → (∀ label, label = first ∨ label = second) →
    ∀ first' second' :
        (SupportAtom.boundary object (object.pieceSupport remainder piece')).Vertex,
      first' ≠ second' → (∀ label, label = first' ∨ label = second') →
    (Graph.DominatedReplacement.innerNeighbours object
        (object.pieceSupport remainder piece') first'.1).ncard =
      (Graph.DominatedReplacement.innerNeighbours object
        (object.pieceSupport remainder piece) first.1).ncard →
    (Graph.DominatedReplacement.innerNeighbours object
        (object.pieceSupport remainder piece') second'.1).ncard =
      (Graph.DominatedReplacement.innerNeighbours object
        (object.pieceSupport remainder piece) second.1).ncard →
    Graph.DominatedReplacement.pathLengths object (object.pieceSupport remainder piece')
        first'.1 second'.1 ⊆
      Graph.DominatedReplacement.pathLengths object (object.pieceSupport remainder piece)
        first.1 second.1 →
    (SupportAtom.piece object (object.pieceSupport remainder piece)).internalVertexCount ≤
      (SupportAtom.piece object (object.pieceSupport remainder piece')).internalVertexCount

end Hypostructure.Graph.Strategy.Spine
