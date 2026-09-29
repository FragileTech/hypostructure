import Hypostructure.Graph.Statements.SameTokenSwap
import Hypostructure.Graph.WalkHubEscape

/-!
# Statements: hubs escape to `Y` along the canonical port walks; the triangular sub-arm is
empty (`[144a]` exchange attack, Lean improvement)

Facts about G at G's canonical routing, for both pair seeds, for EVERY walk witness of the
seed (`SeedWalkWitness`: `seed = T ∪ supp w₁ ∪ supp w₂`, `|T| ≤ 2δ`, canonical port walks), so
every ingredient is read at one and the same witness.  `Y = V ∖ (W₁ ∪ W₂)` (`Yset`),
`H = {deg ≠ 3}`, `H_Y` the hubs with a neighbour in `Y` (`hubsY`).

* 9852 `SameTokenW0EscapeStatement`: with both ports triangular, the W0 escape and the stub
  rule on both walks (`WalkHubEscape.W0Escape`);
* 9853 `SameTokenCrossingCountStatement`: with both ports triangular and `EndEdgesFree`, a
  crossing hub leaves `W₂` at its next position, every bubble carries an exceptional position,
  and the crossing hubs are at most `25|Y| + 17`;
* 9854 `SameTokenHubCountStatement`: with both ports triangular and `EndEdgesFree`,
  `|H| ≤ 37|Y| + 21`, `|H_Y| ≤ 3|Y|`, `σ ≤ |H| + |H_Y|·|Y|`;
* 9855 `SameTokenTriArmEmptyStatement`: at the pinned `X_p`, `X_q`, `Z`, the configuration
  W ∧ Tri(k) ∧ EndEdgesFree is empty.
-/

namespace Hypostructure.Graph.Strategy.Spine

open Hypostructure

universe u

/-- **A walk witness of a pair seed**: `seed = T ∪ supp w₁ ∪ supp w₂` for two canonical port
walks, `|T| ≤ 2δ`. -/
def SeedWalkWitness (data : Parameters) (object : Graph.FiniteObject.{u})
    (seed T : Finset object.Vertex) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact T.card ≤ 2 * data.threshold ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w1 ∧
    Graph.PortPathCover.PortWalk object data.LengthOK w2 ∧
    seed = T ∪ w1.support.toFinset ∪ w2.support.toFinset

/-- **The crossing facts at two walks.**  A crossing hub leaves `W₂` at its next position;
every bubble (consecutive common positions `t + 2 ≤ t'`) carries a position exceptional for
`H ∪ Y ∪ {a₂, b₂}`; the crossing hubs are at most `25|Y| + 17`. -/
def CrossingFacts (object : Graph.FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop :=
  (∀ t p, 0 < t → t < w1.length → 0 < p → p < w2.length → w1.getVert t = w2.getVert p →
    4 ≤ object.degree (w1.getVert t) →
    (∀ y, object.graph.Adj (w1.getVert t) y → y ∈ w1.support ∨ y ∈ w2.support) →
    w1.getVert (t + 1) ∉ w2.support) ∧
  (∀ t t' p p', t + 2 ≤ t' → t' ≤ w1.length → p ≤ w2.length → p' ≤ w2.length →
    w1.getVert t = w2.getVert p → w1.getVert t' = w2.getVert p' →
    (∀ s, t < s → s < t' → w1.getVert s ∉ w2.support) →
    ∃ s, t < s ∧ s < t' ∧ Graph.TwoGeodesics.ExcS (fun v => object.degree v = 3) w1
      (Graph.WalkHubEscape.escapeSet object w1 w2) s) ∧
  (Graph.WalkHubEscape.crossings object w1 w2).card ≤
    25 * (Graph.WalkHubEscape.Yset w1 w2).card + 17

/-- **The hub count at two walks.** -/
def HubCountFacts (object : Graph.FiniteObject.{u}) {a1 b1 a2 b2 : object.Vertex}
    (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2) : Prop :=
  (Graph.JointObject.hubs object).card ≤ 37 * (Graph.WalkHubEscape.Yset w1 w2).card + 21 ∧
  (Graph.WalkHubEscape.hubsY object w1 w2).card ≤ 3 * (Graph.WalkHubEscape.Yset w1 w2).card ∧
  object.degreeSurplus 3 ≤ (Graph.JointObject.hubs object).card +
    (Graph.WalkHubEscape.hubsY object w1 w2).card * (Graph.WalkHubEscape.Yset w1 w2).card

/-- **Node `[144a]` (Lean improvement): the W0 escape at the canonical port walks (9852).**  At
G's canonical routing, for both pair seeds: the seed has a walk witness, and at every walk
witness with both ports triangular, on both walks, a hub `h = w₁(i)` off `W₂`, not an end, with
no neighbour in `Y` has `W₂`-neighbours `w₂(j)`, `w₂(j + 1)`; `w₁(i ± 1)` are off `W₂`; their
`W₂`-neighbours sit at `j − 2` or `j + 3` only; and one of them has a neighbour in `Y`. -/
noncomputable def SameTokenW0EscapeStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∀ pair, (pair = routing.demands.first ∨ pair = routing.demands.second) →
      (∃ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
          (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
        SeedWalkWitness data object (routing.capacity.activation.pairSeed pair) T w1 w2) ∧
      ∀ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
          (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
        SeedWalkWitness data object (routing.capacity.activation.pairSeed pair) T w1 w2 →
        object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
        Graph.WalkHubEscape.W0Escape object w1 w2 ∧ Graph.WalkHubEscape.W0Escape object w2 w1

/-- **Node `[144a]` (Lean improvement): the crossings of the canonical port walks (9853).**  At
G's canonical routing, for both pair seeds, at every walk witness with both ports triangular
and neither walk using the other's end edge: `CrossingFacts` in both orders. -/
noncomputable def SameTokenCrossingCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∀ pair, (pair = routing.demands.first ∨ pair = routing.demands.second) →
      ∀ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
          (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
        SeedWalkWitness data object (routing.capacity.activation.pairSeed pair) T w1 w2 →
        object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
        Graph.LadderG.EndEdgesFree object w1 w2 →
        CrossingFacts object w1 w2 ∧ CrossingFacts object w2 w1

/-- **Node `[144a]` (Lean improvement): the hub count in `|Y|` (9854).**  At G's canonical
routing, for both pair seeds, at every walk witness with both ports triangular and
`EndEdgesFree`: `|H| ≤ 37|Y| + 21`, `|H_Y| ≤ 3|Y|`, `σ ≤ |H| + |H_Y|·|Y|`. -/
noncomputable def SameTokenHubCountStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∀ pair, (pair = routing.demands.first ∨ pair = routing.demands.second) →
      ∀ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
          (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
        SeedWalkWitness data object (routing.capacity.activation.pairSeed pair) T w1 w2 →
        object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
        Graph.LadderG.EndEdgesFree object w1 w2 →
        HubCountFacts object w1 w2

/-- **The configuration W ∧ Tri ∧ EndEdgesFree at one pair seed is empty.**  For every walk
witness of the seed: the boundary-free configuration (the antecedent of
`SameTokenU2FreeWholeStatement`), both ports triangular and `EndEdgesFree` do not hold
together. -/
def TriArmEmpty (data : Parameters) (object : Graph.FiniteObject.{u})
    (Xp Xq Z seed : Finset object.Vertex) : Prop := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact ∀ (T : Finset object.Vertex) (a1 b1 a2 b2 : object.Vertex)
      (w1 : object.graph.Walk a1 b1) (w2 : object.graph.Walk a2 b2),
    SeedWalkWitness data object seed T w1 w2 →
    (∀ w ∈ Xp, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
    (∀ w ∈ Xq, w ∉ Graph.Strategy.InterfaceReplacement.SupportAtom.cutBoundary object Z) →
    Graph.MinimumDegreeAtLeast data.threshold
      (Graph.glue (Graph.Transplant.transplant object Z Xq)
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
    Graph.MinimumDegreeAtLeast data.threshold
      (Graph.glue (Graph.Transplant.transplant object Z Xp)
        (Graph.Strategy.InterfaceReplacement.SupportAtom.outside object Z)) →
    object.graph.Adj b1 a1 → object.graph.Adj b2 a2 →
    Graph.LadderG.EndEdgesFree object w1 w2 → False

/-- **Node `[144a]` (Lean improvement: the triangular sub-arm is empty at G) (9855).**  At G's
canonical routing and pinned supports `X_p`, `X_q`, `Z`, for both pair seeds and every walk
witness: the boundary-free configuration with both ports triangular and neither walk using the
other's end edge is impossible (`|Y| ≤ 4|T| ≤ 24` from the separated-configuration count, so
`σ ≤ 37·24 + 21 + 72·24 = 2637`, against `σ > C_sp⌈√n⌉ ≥ 102·103`). -/
noncomputable def SameTokenTriArmEmptyStatement (data : Parameters)
    (object : Graph.FiniteObject.{u}) : Prop :=
  ∃ routing, canonicalSameTokenRouting data object = some routing ∧
    ∃ Xp Xq Z : Finset object.Vertex, SameTokenPinnedAt data object routing Xp Xq Z ∧
      TriArmEmpty data object Xp Xq Z
        (routing.capacity.activation.pairSeed routing.demands.first) ∧
      TriArmEmpty data object Xp Xq Z
        (routing.capacity.activation.pairSeed routing.demands.second)

end Hypostructure.Graph.Strategy.Spine
