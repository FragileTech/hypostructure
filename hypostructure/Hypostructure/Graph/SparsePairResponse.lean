import Hypostructure.Graph.CanonicalSupportSelection
import Hypostructure.Graph.DeclaredCoordinateSignature
import Hypostructure.Graph.SurplusBlockers
import Hypostructure.Graph.Strategy.InterfaceReplacement

/-!
# `def:sparse-pair-response`: the pair support `X_π`, its boundary and `r_π`

> Let `𝒜₀` be a finite family of active surplus demands.  For an unordered pair
> `π = {p,q} ⊆ 𝒜₀`, let `X_π` be the lexicographically first connected subgraph
> of `G` with the minimum possible number of vertices that contains
> `T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)`.  Let
> `∂X_π = {v ∈ V(X_π) : v is incident with an edge of G − X_π}`.
> The *sparse pair-response coordinate* `r_π` is the declared coordinate of
> `ρ^ex_{∂X_π}(X_π)` whose label is `π`, whose support is `X_π`, and whose value
> is the exact target-response data of the two labelled demands `p` and `q`
> inside `X_π`.  This coordinate is part of the declared signature by clauses
> (D2), (D7), and (D8) of `def:declared-coordinate-signature`.
>
> For a set `Π ⊆ C(𝒜₀,2)`, let `X_Π` be the lexicographically first connected
> subgraph of `G` with the minimum possible number of vertices that contains
> every `X_π` with `π ∈ Π`.  Each `r_π` is then viewed as a labelled coordinate
> of `ρ^ex_{∂X_Π}(X_Π)` by restriction to its declared support.

Every clause is built here from an object the framework already owns.

* The seed `T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)` is the union of the two demands'
  `DemandActivation.declaredSupport`, which is the same data clause (a) of
  `def:surplus-blockers` intersects — so `X_π` and the blocker list read one
  support, not two.
* "The lexicographically first connected subgraph with the minimum possible
  number of vertices containing …" is `CanonicalSupport.select?`, the
  framework's single implementation of that phrase.
* `∂X_π` is `SupportAtom.cutBoundary`, the literal cut boundary of a retained
  support, which is also the boundary an admissible quotient's realizations are
  boundaried over.
* `r_π` is a base coordinate of `def:declared-coordinate-signature` at kind
  `sparseSurplus`, which is clause (D7)'s own name for *"sparse surplus-pair
  response coordinates"*, with label `π` and support `X_π`.  Its value is not a
  field: `def:exact-response-profile` reads a value off a realization, and the
  rank calculus of `Core.TargetRank` is where that reading happens.
* The manuscript's closing sentence — each `r_π` viewed inside
  `ρ^ex_{∂X_Π}(X_Π)` by restriction — is `support_restrict_pairCoordinate`
  below, a proved equation between the declared support of the (D7) coordinate
  and that of the (D8) restriction of the family coordinate, not a convention.

The pair family `ℛ_Π = {r_π : π ∈ Π}` has exactly `|Π|` members, because the
label of `r_π` is `π`; that is `card_pairFamily`, and it is what turns the
entropy sandwich's coordinate count into a pair count.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

namespace FiniteObject

variable {object : FiniteObject.{u}}

/-- The declared coordinate alphabet the sparse branch presents: a coordinate of
`def:declared-coordinate-signature` over the object's vertices, labelled by a
pair of the schedule. -/
abbrev PairCoordinate (object : FiniteObject.{u}) :=
  DeclaredSignature.Coordinate object.Vertex
    (Finset (object.Vertex × object.Vertex))

namespace DemandActivation

variable {Coordinate Chord : Type v}

/-! ## `X_π` and `∂X_π` -/

/-- **`T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)`**: the seed `X_π` is the minimum connected
superset of.  It is the union of the pair's own declared demand supports, the
same data clause (a) of `def:surplus-blockers` intersects. -/
noncomputable def pairSeed (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) : Finset object.Vertex := by
  classical
  exact pair.biUnion activation.declaredSupport

/-- Each demand's declared support lies in the pair's seed. -/
theorem declaredSupport_subset_pairSeed
    (activation : DemandActivation object Coordinate Chord)
    {pair : Finset (object.Vertex × object.Vertex)}
    {demand : object.Vertex × object.Vertex} (member : demand ∈ pair) :
    activation.declaredSupport demand ⊆ activation.pairSeed pair := by
  classical
  intro vertex inSupport
  exact Finset.mem_biUnion.2 ⟨demand, member, inSupport⟩

/-- **`X_π`**: the lexicographically first connected subgraph of `G` with the
minimum possible number of vertices containing `T(p) ∪ Γ(p) ∪ T(q) ∪ Γ(q)`.

`none` exactly when no connected set contains the seed, which cannot happen on
a connected object; `pairSupport_isSome_of_connected` records that. -/
noncomputable def pairSupport (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex)) :
    Option (Finset object.Vertex) :=
  CanonicalSupport.select? object (activation.pairSeed pair)

/-- `X_π` contains the seed and is connected. -/
theorem pairSupport_mem_candidates
    {activation : DemandActivation object Coordinate Chord}
    {pair : Finset (object.Vertex × object.Vertex)}
    {support : Finset object.Vertex}
    (selected : activation.pairSupport pair = some support) :
    activation.pairSeed pair ⊆ support ∧
      SupportComponents.Connected.ConnectedOn object support :=
  CanonicalSupport.mem_candidates_iff.1
    (CanonicalSupport.select?_mem_candidates selected)

/-- `X_π` has the minimum possible number of vertices among the connected
supersets of the seed. -/
theorem pairSupport_card_le
    {activation : DemandActivation object Coordinate Chord}
    {pair : Finset (object.Vertex × object.Vertex)}
    {support other : Finset object.Vertex}
    (selected : activation.pairSupport pair = some support)
    (contains : activation.pairSeed pair ⊆ other)
    (connected : SupportComponents.Connected.ConnectedOn object other) :
    support.card ≤ other.card :=
  CanonicalSupport.select?_card_le selected
    (CanonicalSupport.mem_candidates_iff.2 ⟨contains, connected⟩)

/-- On a connected object `X_π` always exists. -/
theorem pairSupport_isSome_of_connected
    (activation : DemandActivation object Coordinate Chord)
    (pair : Finset (object.Vertex × object.Vertex))
    (connected :
      SupportComponents.Connected.ConnectedOn object object.vertexFinset) :
    (activation.pairSupport pair).isSome :=
  CanonicalSupport.select?_isSome_of_connected connected

/-- **`∂X_π = {v ∈ V(X_π) : v is incident with an edge of G − X_π}`**: the
literal cut boundary of the pair support, which is also the boundary an
admissible quotient's realizations are boundaried over. -/
noncomputable def pairBoundary (object : FiniteObject.{u})
    (support : Finset object.Vertex) : Finset object.Vertex :=
  SupportAtom.cutBoundary object support

@[simp] theorem mem_pairBoundary_iff (object : FiniteObject.{u})
    (support : Finset object.Vertex) (vertex : object.Vertex) :
    vertex ∈ pairBoundary object support ↔
      vertex ∈ support ∧
        ∃ neighbor, object.graph.Adj vertex neighbor ∧ neighbor ∉ support :=
  SupportAtom.mem_cutBoundary_iff object support vertex

/-! ## `r_π` -/

/-- **`r_π`**: the declared coordinate of `ρ^ex_{∂X_π}(X_π)` whose label is `π`
and whose support is `X_π`.

Its kind is clause (D7), which is `def:declared-coordinate-signature`'s own name
for *"sparse surplus-pair response coordinates"*.  The value `val_X(r)` is
read from a realization by `def:exact-response-profile` through
`Core.TargetRank.RankQuotient.value`; it is retained in the exact-profile fact
on the incoming ledger, not duplicated on the coordinate or routed separately. -/
def pairCoordinate (label : Finset (object.Vertex × object.Vertex))
    (support : Finset object.Vertex) : PairCoordinate object :=
  .base .sparseSurplus label support

section DeclaredSupport

variable [DecidableEq object.Vertex]

@[simp] theorem pairCoordinate_support
    (label : Finset (object.Vertex × object.Vertex))
    (support : Finset object.Vertex) :
    (pairCoordinate label support).support = support := rfl

end DeclaredSupport

/-- Distinct pairs give distinct coordinates: the label of `r_π` is `π`. -/
theorem pairCoordinate_injective (support : Finset object.Vertex) :
    Function.Injective fun label : Finset (object.Vertex × object.Vertex) =>
      pairCoordinate label support := by
  intro left right equal
  injection equal

/-! ## `X_Π` and the pair family `ℛ_Π` -/

/-- **`X_Π`**: the minimum connected subgraph containing every `X_π`, `π ∈ Π`.

The seed is the union of the selected pair supports; a pair whose support does
not exist contributes nothing, which is the same convention `pairSupport`
already fixes. -/
noncomputable def familySupport (activation : DemandActivation object Coordinate Chord)
    (family : Finset (Finset (object.Vertex × object.Vertex))) :
    Option (Finset object.Vertex) := by
  classical
  exact CanonicalSupport.select? object
    (family.biUnion fun pair => (activation.pairSupport pair).getD ∅)

/-- Each `X_π` lies inside `X_Π`. -/
theorem pairSupport_subset_familySupport
    {activation : DemandActivation object Coordinate Chord}
    {family : Finset (Finset (object.Vertex × object.Vertex))}
    {pair : Finset (object.Vertex × object.Vertex)}
    {support ambient : Finset object.Vertex}
    (member : pair ∈ family)
    (selected : activation.pairSupport pair = some support)
    (ambientSelected : activation.familySupport family = some ambient) :
    support ⊆ ambient := by
  classical
  have seed :
      (family.biUnion fun other => (activation.pairSupport other).getD ∅) ⊆
        ambient :=
    (CanonicalSupport.mem_candidates_iff.1
      (CanonicalSupport.select?_mem_candidates ambientSelected)).1
  intro vertex inSupport
  refine seed (Finset.mem_biUnion.2 ⟨pair, member, ?_⟩)
  rw [selected]
  exact inSupport

/-- **The manuscript's closing sentence, as a theorem.**

> Each `r_π` is then viewed as a labelled coordinate of `ρ^ex_{∂X_Π}(X_Π)` by
> restriction to its declared support.

The ambient profile's `π`-labelled coordinate, restricted by clause (D8) to
`X_π`, has support exactly `X_π` — because `X_π ⊆ X_Π`.  So the view of `r_π`
inside `ρ^ex_{∂X_Π}(X_Π)` carries the same declared support as `r_π` itself, and
the manuscript's two readings agree on the datum every later definition reads
off a declared coordinate. -/
theorem support_restrict_pairCoordinate [DecidableEq object.Vertex]
    {label : Finset (object.Vertex × object.Vertex)}
    {support ambient : Finset object.Vertex} (inside : support ⊆ ambient) :
    (DeclaredSignature.Coordinate.restrict
        (pairCoordinate label ambient : PairCoordinate object) support).support =
      (pairCoordinate label support : PairCoordinate object).support :=
  Finset.inter_eq_right.2 inside

/-- **`ℛ_Π = {r_π : π ∈ Π}`**: the sparse pair-response coordinate family.

Each pair contributes the coordinate at its own `X_π`, so the family is the one
the dependence lemmas and the entropy sandwich quantify over. -/
noncomputable def pairFamily (activation : DemandActivation object Coordinate Chord)
    (family : Finset (Finset (object.Vertex × object.Vertex))) :
    Finset (PairCoordinate object) := by
  classical
  exact family.image fun pair =>
    pairCoordinate pair ((activation.pairSupport pair).getD ∅)

/-- **`|ℛ_Π| = |Π|`**: the pair family carries one coordinate per pair, because
the label of `r_π` is `π`.  This is what turns the entropy sandwich's coordinate
count into a pair count. -/
theorem card_pairFamily (activation : DemandActivation object Coordinate Chord)
    (family : Finset (Finset (object.Vertex × object.Vertex))) :
    (activation.pairFamily family).card = family.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro left _ right _ equal
  simp only [pairCoordinate, DeclaredSignature.Coordinate.base.injEq] at equal
  exact equal.2.1

end DemandActivation

end FiniteObject

end Hypostructure.Graph
