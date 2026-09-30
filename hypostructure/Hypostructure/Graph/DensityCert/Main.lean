import Hypostructure.Graph.DensityCert.Cert
import Hypostructure.Graph.DensityCert.DP
import Hypostructure.Graph.DensityCert.Ear

/-!
# The density theorem

*Every connected, subcubic finite graph with no cycle of length 4, 8, 16 or 32
and no induced path on 13 vertices satisfies `8 e ≤ 11 n`, unless it is
isomorphic to the 15-vertex graph `X15`.*

Relative form: for a finset `W` of the vertices of any finite simple graph `G`
with `G[W]` connected and admissible, `dIn G W = 8 e(G[W]) − 11 |W| ≤ 0`, or
`G[W]` is a copy of `X15`.

Proof: the block of any root is 2-connected or trivial (P1); P13-freeness
constrains the hanging pieces through their longest induced paths (P2); every
2-connected admissible graph is a copy of a member of the certified list
`Lcert` (ear closure P3 and the closure certificate); the tree DP over the
certified block profiles bounds `8e − 11n` (DP certificate).
-/

namespace Hypostructure.Graph.DensityCert

/-- **The density theorem** (relative form). -/
theorem density_le_of_admissible_in {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (hc : ConnIn G W) (ha : AdmIn G W) :
    dIn G W ≤ 0 ∨ EmbOnto CG.x15.graph G W :=
  density_le_in G Lcert (closure_of_cert G Lcert K2_mem_Lcert closure_cert) dp_cert W hc ha

/-- **The density theorem** (a whole finite graph): a connected graph `G` with
`G` admissible (subcubic, no cycle of length 4, 8, 16, 32, no induced path on 13
vertices) has `8 e(G) ≤ 11 |V|`, or `G ≅ X15`. -/
theorem density_le_of_admissible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (ha : AdmIn G Finset.univ) :
    8 * G.edgeFinset.card ≤ 11 * Fintype.card V ∨ Nonempty (G ≃g CG.x15.graph) := by
  classical
  have hconn : ConnIn G Finset.univ := by
    refine ⟨Finset.univ_nonempty_iff.2 hc.nonempty, fun u _ v _ => ?_⟩
    obtain ⟨p⟩ := hc.preconnected u v
    exact walk_reachIn (fun _ _ h => h) p (fun x _ => Finset.mem_univ x)
  have hdeg : ∀ v, degIn G Finset.univ v = G.degree v := by
    intro v
    unfold degIn
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp
  have hd : dIn G Finset.univ = 8 * (G.edgeFinset.card : ℤ) - 11 * Fintype.card V := by
    rw [dIn_eq_sum]
    simp only [hdeg]
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.card_univ]
    push_cast
    ring
  rcases density_le_of_admissible_in G Finset.univ hconn ha with h | ⟨e, he⟩
  · left
    rw [hd] at h
    omega
  · right
    have hbij : Function.Bijective e := ⟨e.injective, fun v =>
      (he v).1 (Finset.mem_univ v)⟩
    exact ⟨({ toEquiv := Equiv.ofBijective e hbij
              map_rel_iff' := e.map_rel_iff } : CG.x15.graph ≃g G).symm⟩

end Hypostructure.Graph.DensityCert
