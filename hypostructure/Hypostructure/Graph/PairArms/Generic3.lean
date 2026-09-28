import Hypostructure.Graph.PairArms.Generic2

/-!
# Arm B, generic layer, part 3: B1(ii) under slack independence

* G8  under `slackIndependent` (no edge between two vertices above `δ`), the
      reversed-port case of G7(ii) is impossible, so on the `[182]`
      systemRealizability arm EVERY forward connector route inside `U` meets
      EVERY backward connector route;
* G9  the confinement obstruction: every vertex of a canonical support
      `X = select? S` outside its seed `S` is a cut vertex of `G[X]`
      (`X.erase v` is not connected) — the reason `G`-level connectivity facts
      do not produce disjoint routes inside the connector.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **G8.** On the systemRealizability arm, under slack independence, every
forward connector route whose vertices lie in `U` shares a vertex with every
backward connector route. -/
theorem realizabilityFails_routes_meet (returns : PairDemandReturns data object)
    (slack : SlackIndependentStatement data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family) :
    ∃ v ∈ routes.forward.support, v ∈ routes.backward.support := by
  by_contra h
  push_neg at h
  obtain ⟨h₁, h₂⟩ := realizabilityFails_reversed_high returns fails routes inside h
  exact slack _ _ h₁ h₂ returns.leftDemand_adj

open Classical in
/-- **G9.** A vertex of the canonical minimum connected superset `X` of `S`
outside `S` is a cut vertex of `G[X]`. -/
theorem select_steiner_cut {S X : Finset object.Vertex}
    (sel : Graph.CanonicalSupport.select? object S = some X)
    {v : object.Vertex} (hv : v ∈ X) (hS : v ∉ S) :
    ¬ Graph.SupportComponents.Connected.ConnectedOn object (X.erase v) := by
  classical
  intro conn
  have cand := Graph.CanonicalSupport.mem_candidates_iff.1
    (Graph.CanonicalSupport.select?_mem_candidates sel)
  have le := Graph.CanonicalSupport.select?_card_le sel
    (Graph.CanonicalSupport.mem_candidates_iff.2 ⟨fun x hx =>
      Finset.mem_erase.2 ⟨fun e => hS (by rw [← e]; exact hx), cand.1 hx⟩, conn⟩)
  have := Finset.card_erase_of_mem hv
  have : 0 < X.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

end Hypostructure.Graph.PairArms
