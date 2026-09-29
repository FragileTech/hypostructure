import Hypostructure.Graph.Transplant
import Hypostructure.Graph.ReadingProfiles

/-!
# The boundary-free configuration with full transplants is the whole graph (`[144a]`)

Vocabulary-free (G audit S144a).  Let `Z = select?(X_p ∪ X_q)` with both
supports connected and avoiding `∂Z`.  If every interior vertex of `Z` lies in
`X_p` and in `X_q` (which is what a baseline-valid transplant of each support
gives, `Transplant.transplant_fills_of_baseline`), then `X_p = X_q = Z`,
`∂Z = ∅`, and `Z` is every vertex of `G`.  The steps: `X_p` is then a connected
superset of the seed `X_p ∪ X_q`, so Steiner minimality of `select?`
(`ReadingProfiles.select_no_smaller`) forces `X_p = Z`; `∂Z ⊆ Z = X_p` is
disjoint from `X_p`; a set without cut boundary is closed under adjacency, and
`G` is connected.
-/

namespace Hypostructure.Graph.U2FreeWhole

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.ReadingProfiles

universe u

variable {object : FiniteObject.{u}}

/-- A nonempty vertex set closed under adjacency in a connected graph is everything. -/
theorem closed_univ (connected : object.graph.Connected) {Z : Finset object.Vertex}
    (nonempty : ∃ v, v ∈ Z)
    (closed : ∀ v n, v ∈ Z → object.graph.Adj v n → n ∈ Z) : ∀ u, u ∈ Z := by
  obtain ⟨v, hv⟩ := nonempty
  intro u
  obtain ⟨walk⟩ := connected.preconnected v u
  have key : ∀ (a b : object.Vertex) (w : object.graph.Walk a b), a ∈ Z → b ∈ Z := by
    intro a b w
    induction w with
    | nil => exact id
    | cons h p ih => exact fun ha => ih (closed _ _ ha h)
  exact key v u walk hv

/-- **Both supports fill the interior of `Z`, avoid `∂Z`, and are connected**:
then they are `Z`, `∂Z` is empty and `Z` is all of `G`. -/
theorem whole [DecidableEq object.Vertex] {Xp Xq Z : Finset object.Vertex}
    (connected : object.graph.Connected)
    (selected : CanonicalSupport.select? object (Xp ∪ Xq) = some Z)
    (pZ : Xp ⊆ Z) (qZ : Xq ⊆ Z)
    (connP : SupportComponents.Connected.ConnectedOn object Xp)
    (freeP : ∀ w ∈ Xp, w ∉ SupportAtom.cutBoundary object Z)
    (freeQ : ∀ w ∈ Xq, w ∉ SupportAtom.cutBoundary object Z)
    (fillP : ∀ v ∈ Z, v ∉ SupportAtom.cutBoundary object Z → v ∈ Xp)
    (fillQ : ∀ v ∈ Z, v ∉ SupportAtom.cutBoundary object Z → v ∈ Xq)
    (nonempty : ∃ y, y ∈ Xp) :
    Xp = Z ∧ Xq = Z ∧ (∀ v, v ∉ SupportAtom.cutBoundary object Z) ∧ ∀ v, v ∈ Z := by
  have qp : Xq ⊆ Xp := fun v hv => fillP v (qZ hv) (freeQ v hv)
  have eqP : Xp = Z := by
    by_contra ne
    exact select_no_smaller selected pZ ne
      (fun v hv => (Finset.mem_union.1 hv).elim id fun h => qp h) connP
  have noCut : ∀ v, v ∉ SupportAtom.cutBoundary object Z := by
    intro v hv
    have vZ := ((SupportAtom.mem_cutBoundary_iff object Z v).1 hv).1
    exact freeP v (eqP ▸ vZ) hv
  have eqQ : Xq = Z := by
    apply Finset.Subset.antisymm qZ
    intro v hv
    exact fillQ v hv (noCut v)
  have closed : ∀ v n, v ∈ Z → object.graph.Adj v n → n ∈ Z := by
    intro v n hv adj
    by_contra nZ
    exact noCut v ((SupportAtom.mem_cutBoundary_iff object Z v).2 ⟨hv, n, adj, nZ⟩)
  refine ⟨eqP, eqQ, noCut, closed_univ connected ?_ closed⟩
  obtain ⟨y, hy⟩ := nonempty
  exact ⟨y, pZ hy⟩

end Hypostructure.Graph.U2FreeWhole
