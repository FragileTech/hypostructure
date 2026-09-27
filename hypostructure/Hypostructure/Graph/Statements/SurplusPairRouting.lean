import Hypostructure.Graph.Statements.CanonicalSameToken

/-!
# Statements: node `[144]`, `lem:same-token-bottleneck-routing`, at G

The routing statements of node `[144]` pinned to the canonical routing objects
of G (`Statements/CanonicalSameToken.lean`): the handoff is the canonical
envelope of the canonical first separator of the canonical maximal routes to
the canonical equal-label demands of the canonical homogeneous pattern; the
unresolved residual of the paper error at `[144]` is about the response
coordinates of exactly those two pattern edges.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- The response coordinate `r_π` of a scheduled pair of G at the
presentation's activation (`def:sparse-pair-response`). -/
noncomputable abbrev sameTokenPairCoordinate {data : Parameters}
    {object : Graph.FiniteObject.{u}} (capacity : SurplusCapacity data object)
    (pair : Finset (object.Vertex × object.Vertex)) : object.PairCoordinate :=
  Graph.FiniteObject.DemandActivation.pairCoordinate pair
    ((capacity.activation.pairSupport pair).getD ∅)

/-- **Node `[144]`, the same-token Type B handoff of G**
(`lem:same-token-bottleneck-routing`, separator case, tex 5596-5620): the
canonical first separator of G's canonical routes is a high-degree,
non-absorbing handoff centre, and its envelope escapes physically.  The
support `(Y, H)` is `canonicalSameTokenSupport`. -/
noncomputable def SameTokenTypeBHandoffStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ core centres, SameTokenHandoffAt data object core centres

/-- Node `[144]`, the exact complement of the same-token handoff of G. -/
noncomputable abbrev TypeBHandoffFailsStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  ¬ SameTokenTypeBHandoffStatement data object

/-- **Node `[144a]`, the residual of the paper error at `[144]`**
(`lem:same-token-bottleneck-routing`, parallel and cubic-first-separator cases,
tex 5585-5620; see `lean-vs-paper-discrepancies.md#paper-errors`).  The
response coordinates `r_p ≠ r_q` of the two equal-label pattern edges of G's
canonical routing, read on G's piece at the canonical support `Z` of their
supports: the readings lie in different boundary-degree fibres, or they are
context-equivalent (target-complete).  The paper claims both cases are sparse
exits (tex 5589, 5594); neither is established, and the pair is carried by the
open leaf `[144a]`. -/
noncomputable abbrev SameTokenPatternPairUnresolvedStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    let first := sameTokenPairCoordinate routing.capacity routing.demands.first
    let second := sameTokenPairCoordinate routing.capacity routing.demands.second
    first ≠ second ∧
      ∃ support : Finset object.Vertex,
        Graph.CanonicalSupport.select? object
            (Graph.DeclaredSignature.Coordinate.support first ∪
              Graph.DeclaredSignature.Coordinate.support second) = some support ∧
        ((Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
              support (Graph.DeclaredSignature.Coordinate.support first)).boundaryDegreeProfile ≠
            (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
              support (Graph.DeclaredSignature.Coordinate.support second)).boundaryDegreeProfile ∨
          Graph.Response.ContextEquivalent (Graph.HasCycleWithLength data.LengthOK)
            (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
              support (Graph.DeclaredSignature.Coordinate.support first))
            (Graph.Strategy.InterfaceReplacement.SupportAtom.retainedPiece object
              support (Graph.DeclaredSignature.Coordinate.support second)))

/-- **Node `[144]`, `lem:same-token-bottleneck-routing` at G**: the canonical
homogeneous pattern of G's overloading token routes to a sparse surplus exit of
G's declared family, to G's same-token Type B handoff, or to the unresolved
pattern pair of the paper error at `[144]`. -/
noncomputable abbrev BottleneckRoutingStatement
    (data : Parameters)
    (object : Graph.FiniteObject.{u}) :
    Prop :=
  HomogeneousBottleneckPatternSchema data object ∧
    (DeclaredSparseSurplusExit data object ∨
      SameTokenTypeBHandoffStatement data object ∨
      SameTokenPatternPairUnresolvedStatement data object)

end Hypostructure.Graph.Strategy.Spine
