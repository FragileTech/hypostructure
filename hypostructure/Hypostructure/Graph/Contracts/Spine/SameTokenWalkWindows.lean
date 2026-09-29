import Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover
import Hypostructure.Graph.Statements.SameTokenWalkWindows

/-!
# Contracts: induced windows along the canonical port walks; exchange at `P₀`
(`[144a]` exchange attack, Lean improvement)

Proof-agnostic contract lemmas for `SameTokenWalkWindowsStatement` and
`SameTokenWalkExchangeStatement` (`Statements/SameTokenWalkWindows.lean`).  The mathematics is
the vocabulary-free `Graph/WalkWindows.lean`:

* a triangular port walk (`b ~ a`) is a shortest `a`–`b` path of `G − ab`
  (`PortWalk`, first kind: `GeodesicDetours s(a, b)`), so its `L`-segments other than the whole
  walk induce windows (`WalkWindows.seg_window`), its blocks form a packing
  (`WalkWindows.length_div_le`, `WalkWindows.two_length_div_le`), and every window meets the
  maximum packing `P₀` (`canonicalWindowPacking_spec`);
* the exchange at the maximum packing `P₀` (`WalkWindows.exchange_card_le`,
  `WalkWindows.exchange_single`).

The walk witness is the one `pairSeedWalks` gives at each pair seed (as for key 9990).

This module imports no strategy, row, or vocabulary module.
-/

set_option linter.unusedSectionVars false

namespace Hypostructure.Graph.Contracts.Spine.SameTokenWalkWindows

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.PortPathCover
open Hypostructure.Graph.Contracts.Spine.SameTokenSeedCover

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- A triangular port walk is a path, shortest among the paths avoiding its port edge. -/
theorem det_of {LengthOK : ℕ → Prop} {a b : object.Vertex} {w : object.graph.Walk a b}
    (h : PortWalk object LengthOK w) (t : object.graph.Adj b a) :
    w.IsPath ∧ PathChords.GeodesicDetours s(a, b) w := by
  refine ⟨h.1, ?_⟩
  rcases h.2.2.2.2.2 with ⟨-, -, det, -⟩ | ⟨x, -, -, -, nab, -⟩
  · exact det
  · exact absurd t.symm nab

/-- A window segment of a triangular port walk induces a window. -/
theorem triSegment_window {LengthOK : ℕ → Prop} {L : ℕ} {a b : object.Vertex}
    {w : object.graph.Walk a b} (h : PortWalk object LengthOK w) {q : Finset object.Vertex}
    (hq : TriSegment object L w q) : object.InducesWindow L q := by
  obtain ⟨t, s, hs, hend, rfl⟩ := hq
  obtain ⟨hp, det⟩ := det_of h t
  exact WalkWindows.seg_window hp det hs hend

/-- **The windows and the exchange of the two port walks at one pair seed.** -/
theorem pairWalkWindows_of
    (routing : SameTokenRouting data object)
    (routingEq : canonicalSameTokenRouting data object = some routing)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3)
    {pair : Finset (object.Vertex × object.Vertex)}
    (pairMem : pair = routing.demands.first ∨ pair = routing.demands.second) :
    PairWalkWindows data object (routing.capacity.activation.pairSeed pair) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP⟩ :=
    pairSeedWalks routing routingEq avoids family threshold pairMem
  have spec := canonicalWindowPacking_spec data object
  have win : ∀ q, TriSegment object data.windowOrder w1 q ∨
      TriSegment object data.windowOrder w2 q → object.InducesWindow data.windowOrder q := by
    rintro q (h | h)
    · exact triSegment_window hw1 h
    · exact triSegment_window hw2 h
  refine ⟨T, a1, b1, a2, b2, w1, w2, hT, hw1, hw2, eP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact ⟨win q hq, spec.2.2 q (win q hq)⟩
  · intro t
    obtain ⟨hp, det⟩ := det_of hw1 t
    exact WalkWindows.length_div_le hp det data.windowOrder_pos
  · intro t
    obtain ⟨hp, det⟩ := det_of hw2 t
    exact WalkWindows.length_div_le hp det data.windowOrder_pos
  · intro t1 t2 disj
    obtain ⟨hp1, det1⟩ := det_of hw1 t1
    obtain ⟨hp2, det2⟩ := det_of hw2 t2
    exact WalkWindows.two_length_div_le hp1 det1 hp2 det2 disj data.windowOrder_pos
  · intro S hS Q hQ hdisj havoid
    exact WalkWindows.exchange_card_le data.windowOrder_pos spec.1 spec.2.1 hS
      ⟨fun q hq => win q (hQ q hq), hdisj⟩ havoid
  · rintro X hX q1 q2 h1 h2 d ⟨a1', a2'⟩
    exact WalkWindows.exchange_single data.windowOrder_pos spec.1 spec.2.1 hX (win q1 h1)
      (win q2 h2) d a1' a2'

/-- **Node `[144a]`: induced windows along the canonical port walks.** -/
theorem sameTokenWalkWindows_holds
    (supports : SameTokenPatternSupportsStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (family : ActiveSurplusFamilyStatement data object)
    (threshold : data.threshold = 3) :
    SameTokenWalkWindowsStatement data object := by
  obtain ⟨routing, routingEq, -⟩ := supports
  exact ⟨routing, routingEq,
    pairWalkWindows_of routing routingEq avoids family threshold (Or.inl rfl),
    pairWalkWindows_of routing routingEq avoids family threshold (Or.inr rfl)⟩

/-- **Node `[144a]`: the exchange at G's canonical packing `P₀`.** -/
theorem sameTokenWalkExchange_holds : SameTokenWalkExchangeStatement data object := by
  have spec := canonicalWindowPacking_spec data object
  refine ⟨?_, ?_⟩
  · intro S hS Q hQ havoid
    exact WalkWindows.exchange_card_le data.windowOrder_pos spec.1 spec.2.1 hS hQ havoid
  · rintro X hX q1 q2 h1 h2 d ⟨a1', a2'⟩
    exact WalkWindows.exchange_single data.windowOrder_pos spec.1 spec.2.1 hX h1 h2 d a1' a2'

end Hypostructure.Graph.Contracts.Spine.SameTokenWalkWindows
