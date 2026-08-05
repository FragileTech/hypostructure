import Hypostructure.Graph.Target

/-!
# The high-neighbourhood normal form

`lem:heavy-neighbourhood-normal-form` of the manuscript, stated for an arbitrary
minimum-degree cycle problem.  Nothing here knows a baseline value, a target, or
a manuscript: the centre is high relative to a supplied `threshold`, and the two
laws the normal form runs on are supplied as ordinary hypotheses:

* every edge has an endpoint exactly at the threshold -- the tight-endpoint law
  of edge-deletion criticality;
* the object carries no accepted cycle, and the quadrilateral is an accepted
  length.

Both are facts the caller already holds.  The second is where the manuscript's
"`G` contains no power-of-two cycle" enters, at its own interface: the only
thing the normal form needs of the accepted set is that it contains `4`.

The three conclusions are the manuscript's (a), (b) and (c):

* every neighbour of a high centre sits exactly at the threshold;
* the graph induced on `N_G(h)` is a matching;
* two nonadjacent neighbours of `h` have no common neighbour outside `{h}`.

(b) and (c) are one argument -- a quadrilateral through `h` -- and are proved
from the single `not_quadrilateral` below.
-/

namespace Hypostructure.Graph

universe u

/-! ## The quadrilateral law -/

/-- **Four pairwise-compatible adjacencies would be an accepted quadrilateral.**

`a — b — c — d — a` with `a ≠ c` and `b ≠ d` is a simple cycle of length `4`, so
an object that avoids the accepted lengths carries no such configuration once
`4` is accepted.

This is the whole graph-theoretic content of parts (b) and (c) of
`lem:heavy-neighbourhood-normal-form`; the manuscript writes it twice, as
`hxyzh` and as `hxzyh`. -/
theorem not_quadrilateral {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (quadrilateralAccepted : LengthOK 4)
    {a b c d : object.Vertex}
    (ab : object.graph.Adj a b) (bc : object.graph.Adj b c)
    (cd : object.graph.Adj c d) (da : object.graph.Adj d a)
    (ac : a ≠ c) (bd : b ≠ d) : False := by
  have isCycle :
      (SimpleGraph.Walk.cons ab
        (SimpleGraph.Walk.cons bc
          (SimpleGraph.Walk.cons cd
            (SimpleGraph.Walk.cons da .nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.Walk.isPath_def]
      simp [ab.ne', bc.ne, cd.ne, da.ne, ac.symm, bd]
    · simp [ab.ne, ab.ne', bc.ne, da.ne', ac, bd]
  exact avoids ⟨⟨a, _, isCycle, by simpa using quadrilateralAccepted⟩⟩

/-! ## The normal form -/

/-- A vertex is a **high centre** when its degree is strictly above the
registered baseline.  For the manuscript's `δ = 3` this is `d_G(h) ≥ 4`, the
`def:heavy-center-triangular-port` notion of a high center. -/
def IsHighCentre (object : FiniteObject.{u}) (threshold : Nat)
    (centre : object.Vertex) : Prop :=
  threshold < object.degree centre

/-- **`lem:heavy-neighbourhood-normal-form` at one high centre.**

The three fields are the manuscript's (a), (b) and (c) verbatim.  (b) is stated
as "no neighbour of `h` has two distinct neighbours inside `N_G(h)`", which is
what "`G[N_G(h)]` is a matching" says about a graph whose every vertex has
degree at most one there. -/
structure NormalForm (object : FiniteObject.{u}) (threshold : Nat)
    (centre : object.Vertex) : Prop where
  /-- (a) Every vertex of `N_G(h)` sits exactly at the baseline. -/
  neighbourTight : ∀ ⦃x : object.Vertex⦄, object.graph.Adj centre x →
    object.degree x = threshold
  /-- (b) `G[N_G(h)]` is a matching: no two adjacent edges inside `N_G(h)`. -/
  inducedMatching : ∀ ⦃x y z : object.Vertex⦄,
    object.graph.Adj centre x → object.graph.Adj centre y →
    object.graph.Adj centre z → x ≠ z →
    object.graph.Adj x y → object.graph.Adj y z → False
  /-- (c) Two nonadjacent neighbours of `h` have no common neighbour outside
  `{h}`. -/
  noCommonNeighbourOutside : ∀ ⦃x y z : object.Vertex⦄,
    object.graph.Adj centre x → object.graph.Adj centre y → x ≠ y →
    ¬ object.graph.Adj x y → z ≠ centre →
    object.graph.Adj x z → object.graph.Adj y z → False

/-- **`lem:heavy-neighbourhood-normal-form`.**

(a) is the tight-endpoint law read at the edge `hx`: one endpoint sits exactly
at the baseline, and it is not `h`, whose degree is strictly above it.  (b) and
(c) are the manuscript's two quadrilaterals `hxyzh` and `hxzyh`. -/
theorem normalForm {object : FiniteObject.{u}} {LengthOK : Nat → Prop}
    {threshold : Nat} {centre : object.Vertex}
    (tight : ∀ dart : object.graph.Dart,
      object.degree dart.fst = threshold ∨ object.degree dart.snd = threshold)
    (avoids : ¬ HasCycleWithLength LengthOK object)
    (quadrilateralAccepted : LengthOK 4)
    (high : IsHighCentre object threshold centre) :
    NormalForm object threshold centre where
  neighbourTight := by
    intro x adjacent
    rcases tight ⟨(centre, x), adjacent⟩ with centreTight | endpointTight
    · exact absurd centreTight (Nat.ne_of_gt high)
    · exact endpointTight
  inducedMatching := by
    intro x y z centreX centreY centreZ distinct xy yz
    -- `h — x — y — z — h`.
    exact not_quadrilateral avoids quadrilateralAccepted centreX xy yz
      centreZ.symm centreY.ne distinct
  noCommonNeighbourOutside := by
    -- The manuscript states (c) for *nonadjacent* `x` and `y`.  The
    -- quadrilateral `hxzyh` does not use that hypothesis, so it is carried as
    -- stated rather than dropped: the lemma consumed downstream is the
    -- manuscript's.
    intro x y z centreX centreY distinct _nonadjacent outside xz yz
    -- `h — x — z — y — h`.
    exact not_quadrilateral avoids quadrilateralAccepted centreX xz yz.symm
      centreY.symm (Ne.symm outside) distinct

end Hypostructure.Graph
