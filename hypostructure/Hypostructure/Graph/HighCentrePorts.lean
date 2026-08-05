import Hypostructure.Graph.HighCentreNormalForm

/-!
# Surplus ports at a high centre, and the local dichotomy

The port layer of `def:surplus-ports` and `def:heavy-center-triangular-port`,
and the local alternative `cor:heavy-center-local-dichotomy` proved on it.
Everything is stated for an arbitrary minimum-degree cycle problem: the centre
is high relative to a supplied `threshold`, and the only structural input is the
`NormalForm` of `HighCentreNormalForm.lean`.

A *port* at a centre `h` is an ordered edge `(h, x)`.  The manuscript's shoulder
pair `s(p)` is the neighbourhood of `x` with `h` removed; when `x` is cubic --
which the normal form supplies at a high centre -- it is the two-element pair
`{a_p, b_p}`, and the shoulder chord `e_p^* = a_p b_p`.  A port is *triangular*
when its shoulder chord lies in the graph and *open* when it does not.

Nothing below fixes a numeral, and no port is ever selected: the manuscript's
excess selector chooses `d_G(h) − 3` of the incident ports, but every statement
here is about *all* ports at `h`, which is what the local dichotomy argues
about.
-/

namespace Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

/-! ## Ports and their shoulders -/

/-- **`s(p)`, membership form.**  `z` is a shoulder of the port `(centre,
endpoint)` when it is a neighbour of the endpoint other than the centre. -/
def IsShoulder (object : FiniteObject.{u}) (centre endpoint z : object.Vertex) :
    Prop :=
  object.graph.Adj endpoint z ∧ z ≠ centre

/-- **`def:heavy-center-triangular-port`, triangular.**  The shoulder chord
`e_p^* = a_p b_p` lies in `G`.  Adjacency is irreflexive, so two adjacent
shoulders are automatically distinct and this is exactly the manuscript's
condition once the endpoint is cubic. -/
def IsTriangularPort (object : FiniteObject.{u})
    (centre endpoint : object.Vertex) : Prop :=
  ∃ left right : object.Vertex, IsShoulder object centre endpoint left ∧
    IsShoulder object centre endpoint right ∧ object.graph.Adj left right

/-- **`def:heavy-center-triangular-port`, open.**  The shoulder chord is absent.
The word records only that absence; no suppressed graph is associated to the
port. -/
def IsOpenPort (object : FiniteObject.{u}) (centre endpoint : object.Vertex) :
    Prop :=
  ¬ IsTriangularPort object centre endpoint

/-! ## `def:fan-compatible-open-ports` -/

/-- **`def:fan-compatible-open-ports`.**  Two distinct open ports `p = (h, x)`
and `q = (h, y)` at the same centre are fan-compatible when
`x ∉ s(q)`, `y ∉ s(p)` and `s(p) ∩ s(q) = ∅`.

The two openness clauses are part of the definition's hypotheses and are carried
as fields, so an inhabitant is exactly the manuscript's object. -/
structure FanCompatible (object : FiniteObject.{u})
    (centre left right : object.Vertex) : Prop where
  /-- `p = (h, x)` is open. -/
  leftOpen : IsOpenPort object centre left
  /-- `q = (h, y)` is open. -/
  rightOpen : IsOpenPort object centre right
  /-- The two ports are distinct. -/
  endpointsNe : left ≠ right
  /-- `x ∉ s(q)`. -/
  leftNotShoulder : ¬ IsShoulder object centre right left
  /-- `y ∉ s(p)`. -/
  rightNotShoulder : ¬ IsShoulder object centre left right
  /-- `s(p) ∩ s(q) = ∅`. -/
  shouldersDisjoint : ∀ z : object.Vertex, IsShoulder object centre left z →
    IsShoulder object centre right z → False

/-- **`lem:same-center-open-port-compatibility`.**  Distinct open ports at the
same high centre whose endpoints are nonadjacent are fan-compatible.

`x ∉ s(q)` and `y ∉ s(p)` are immediate from `xy ∉ E(G)`, since a shoulder of a
port is a neighbour of its endpoint.  Disjointness is part (c) of the normal
form: a common shoulder would be a common neighbour of the nonadjacent
`x, y ∈ N_G(h)` outside `{h}`. -/
theorem fanCompatible_of_endpoints_nonadjacent {threshold : Nat}
    {centre left right : object.Vertex}
    (normal : NormalForm object threshold centre)
    (centreLeft : object.graph.Adj centre left)
    (centreRight : object.graph.Adj centre right)
    (distinct : left ≠ right)
    (nonadjacent : ¬ object.graph.Adj left right)
    (leftOpen : IsOpenPort object centre left)
    (rightOpen : IsOpenPort object centre right) :
    FanCompatible object centre left right where
  leftOpen := leftOpen
  rightOpen := rightOpen
  endpointsNe := distinct
  leftNotShoulder := fun shoulder => nonadjacent shoulder.1.symm
  rightNotShoulder := fun shoulder => nonadjacent shoulder.1
  shouldersDisjoint := fun _z leftShoulder rightShoulder =>
    normal.noCommonNeighbourOutside centreLeft centreRight distinct nonadjacent
      leftShoulder.2 leftShoulder.1 rightShoulder.1

/-! ## The endpoint split at a centre -/

open scoped Classical in
/-- The endpoints at `centre` whose port is open. -/
noncomputable def openEndpoints (object : FiniteObject.{u})
    (centre : object.Vertex) : Finset object.Vertex :=
  (object.orderedNeighbors centre).toFinset.filter
    (fun endpoint => IsOpenPort object centre endpoint)

open scoped Classical in
/-- The endpoints at `centre` whose port is triangular. -/
noncomputable def triangularEndpoints (object : FiniteObject.{u})
    (centre : object.Vertex) : Finset object.Vertex :=
  (object.orderedNeighbors centre).toFinset.filter
    (fun endpoint => IsTriangularPort object centre endpoint)

theorem mem_openEndpoints_iff {centre endpoint : object.Vertex} :
    endpoint ∈ openEndpoints object centre ↔
      object.graph.Adj centre endpoint ∧
        IsOpenPort object centre endpoint := by
  classical
  simp [openEndpoints, object.mem_orderedNeighbors_iff]

theorem mem_triangularEndpoints_iff {centre endpoint : object.Vertex} :
    endpoint ∈ triangularEndpoints object centre ↔
      object.graph.Adj centre endpoint ∧
        IsTriangularPort object centre endpoint := by
  classical
  simp [triangularEndpoints, object.mem_orderedNeighbors_iff]

/-- **Every port at a centre is open or triangular, and none is both.**  The two
endpoint sets partition `N_G(h)`, so their sizes add up to `d_G(h)`. -/
theorem openEndpoints_card_add_triangularEndpoints_card
    (object : FiniteObject.{u}) (centre : object.Vertex) :
    (openEndpoints object centre).card +
        (triangularEndpoints object centre).card =
      object.degree centre := by
  classical
  have partition :
      (openEndpoints object centre).card +
          (triangularEndpoints object centre).card =
        (object.orderedNeighbors centre).toFinset.card := by
    rw [openEndpoints, triangularEndpoints, Nat.add_comm]
    simp only [IsOpenPort]
    convert Finset.card_filter_add_card_filter_not
      (s := (object.orderedNeighbors centre).toFinset)
      (p := fun endpoint => IsTriangularPort object centre endpoint) using 3
  rw [partition,
    List.toFinset_card_of_nodup (object.orderedNeighbors_nodup centre),
    object.orderedNeighbors_length centre]

/-! ## `lem:heavy-center-triangular-alternative` -/

/-- **A matching carries no clique of size three.**

Part (b) of the normal form says `G[N_G(h)]` is a matching.  If three distinct
neighbours of `h` were pairwise adjacent, two of the induced edges would meet,
so at most two neighbours of `h` are pairwise adjacent. -/
theorem card_le_two_of_pairwise_adj {threshold : Nat} {centre : object.Vertex}
    (normal : NormalForm object threshold centre)
    (endpoints : Finset object.Vertex)
    (inside : ∀ endpoint ∈ endpoints, object.graph.Adj centre endpoint)
    (clique : ∀ first ∈ endpoints, ∀ second ∈ endpoints, first ≠ second →
      object.graph.Adj first second) :
    endpoints.card ≤ 2 := by
  by_contra big
  obtain ⟨first, second, third, firstMem, secondMem, thirdMem, firstSecond,
    firstThird, secondThird⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_le big)
  -- `first — second — third` are two meeting edges inside `N_G(h)`.
  exact normal.inducedMatching (inside first firstMem) (inside second secondMem)
    (inside third thirdMem) firstThird
    (clique first firstMem second secondMem firstSecond)
    (clique second secondMem third thirdMem secondThird)

/-- **`lem:heavy-center-triangular-alternative`.**

If no two open ports at a high centre `h` form a fan-compatible open pair, then
at least `d_G(h) − 2` ports at `h` are triangular.

The manuscript's argument exactly: the open endpoints are pairwise adjacent,
because a nonadjacent pair would be fan-compatible by
`lem:same-center-open-port-compatibility`; a matching has no clique of size
three, so there are at most two of them; and every remaining port is
triangular. -/
theorem triangularEndpoints_card_of_no_compatible_pair {threshold : Nat}
    {centre : object.Vertex} (normal : NormalForm object threshold centre)
    (noCompatible : ∀ left right : object.Vertex,
      ¬ FanCompatible object centre left right) :
    object.degree centre - 2 ≤ (triangularEndpoints object centre).card := by
  classical
  have clique : ∀ first ∈ openEndpoints object centre,
      ∀ second ∈ openEndpoints object centre, first ≠ second →
      object.graph.Adj first second := by
    intro first firstMem second secondMem distinct
    obtain ⟨centreFirst, firstOpen⟩ := mem_openEndpoints_iff.mp firstMem
    obtain ⟨centreSecond, secondOpen⟩ := mem_openEndpoints_iff.mp secondMem
    by_contra nonadjacent
    exact noCompatible first second
      (fanCompatible_of_endpoints_nonadjacent normal centreFirst centreSecond
        distinct nonadjacent firstOpen secondOpen)
  have small : (openEndpoints object centre).card ≤ 2 :=
    card_le_two_of_pairwise_adj normal _
      (fun _endpoint member => (mem_openEndpoints_iff.mp member).1) clique
  have total := openEndpoints_card_add_triangularEndpoints_card object centre
  omega

/-- **`cor:heavy-center-local-dichotomy`.**

At a high centre `h`, either two open ports at `h` are fan-compatible, or at
least `d_G(h) − 2` ports at `h` are triangular.

The manuscript states it for a *heavy* centre, `d_G(h) ≥ 5`, and adds "in
particular `h` has three triangular ports"; that consequence is
`three_le_triangularEndpoints_card` below, which is where the heaviness is
spent.  The dichotomy itself needs only the normal form. -/
theorem heavyCentreLocalDichotomy {threshold : Nat} {centre : object.Vertex}
    (normal : NormalForm object threshold centre) :
    (∃ left right : object.Vertex, FanCompatible object centre left right) ∨
      object.degree centre - 2 ≤ (triangularEndpoints object centre).card := by
  classical
  by_cases compatible :
      ∃ left right : object.Vertex, FanCompatible object centre left right
  · exact Or.inl compatible
  · refine Or.inr (triangularEndpoints_card_of_no_compatible_pair normal ?_)
    intro left right pair
    exact compatible ⟨left, right, pair⟩

/-- **"In particular, `h` has three triangular ports."**

The second alternative at a *heavy* centre -- one whose degree is at least two
above the baseline, `d_G(h) ≥ 5` at the manuscript's `δ = 3`.  This is the only
place the heaviness of the centre is used, and it is used exactly as the
manuscript uses it: `k − 2 ≥ 3`. -/
theorem three_le_triangularEndpoints_card {threshold : Nat}
    {centre : object.Vertex} (baseline : 3 ≤ threshold)
    (heavy : threshold + 1 < object.degree centre)
    (alternative :
      object.degree centre - 2 ≤ (triangularEndpoints object centre).card) :
    3 ≤ (triangularEndpoints object centre).card := by
  omega

end Hypostructure.Graph
