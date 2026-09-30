import Hypostructure.Graph.Contracts.Spine.SparseExitResidual

/-!
# Pair code, arm B: generic layer

Facts about the canonical objects of the pair-code chain `[178]→[179]→[180]`,
stated over the live generic definitions, with every hypothesis explicit.

* G1  the declared support of every obstruction coordinate is a response
      support `X_π` of a pair of the minimal obstruction, hence lies in the
      obstruction's connected overlap support `U = ⋃_{π∈𝒰} X_π`;
* G2  (B2) the canonical support of two meeting response supports is their
      union (the target defect of the obstruction coordinates, exit (b)
      stated about G, is empty at G);
* G3  (B1(ii)) two vertex-disjoint connector routes, the forward one inside
      `U`, build a one-cell serial system, i.e. a covered `[179]` outcome;
      so on the `[182]` systemRealizability arm every such disjoint pair is
      the degenerate reversed-port pair of length `0`;
* G4  (B3) the handoff's separator is a vertex of `U` of degree `> δ`, its two
      next vertices are distinct neighbours in `U`, `G` has no label collision
      at `P₀`, and the canonical envelope escapes.
-/

namespace Hypostructure.Graph.PairArms

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## G1: obstruction coordinates live in the overlap support -/

open Classical in
/-- **G1.** Every obstruction coordinate `r` is `r_π` for a pair `π` of the
minimal overlap obstruction `𝒰`, with declared support the selected response
support `X_π`; in particular `X_π ⊆ U = ⋃_{π∈𝒰} X_π`. -/
theorem obstructionCoordinate_support
    (returns : PairDemandReturns data object)
    {r : object.PairCoordinate} (hr : r ∈ returns.obstructionCoordinates) :
    ∃ p ∈ returns.overlap.family,
      pairCoordinateSupport r = returns.overlap.system.responseSupport p ∧
      pairCoordinateSupport r ⊆
        returns.overlap.system.overlapSupport returns.overlap.family := by
  classical
  unfold PairDemandReturns.obstructionCoordinates
    Graph.FiniteObject.DemandActivation.pairFamily at hr
  obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hπ
  have sel := returns.overlap.system.responseSupport_selected p
  have eq : pairCoordinateSupport
      (Graph.FiniteObject.DemandActivation.pairCoordinate p.1
        (((Graph.pairResponseActivation
          returns.overlap.system.first.active).pairSupport p.1).getD ∅)) =
      returns.overlap.system.responseSupport p := by
    rw [sel]
    rfl
  refine ⟨p, hp, eq, ?_⟩
  rw [eq]
  intro v hv
  change v ∈ returns.overlap.system.toSkeletonModel.responseSupportUnion
    returns.overlap.family
  unfold Graph.SparsePairSkeletonModel.responseSupportUnion
  rw [Finset.mem_biUnion]
  exact ⟨p, hp, hv⟩

/-! ## G2: the canonical support of meeting response supports -/

open Classical in
theorem sparseDeclaredSupport_pair (r : object.PairCoordinate) :
    sparseDeclaredSupport data object (Sum.inr (Sum.inl r)) = pairCoordinateSupport r := by
  show Graph.DeclaredSignature.Coordinate.support r = _
  congr 1
  exact Subsingleton.elim _ _

open Classical in
/-- **G2b.** When the two response supports meet, the witness support is
exactly their union: `Z'' = X₁ ∪ X₂` (a connected superset of minimum size). -/
theorem support_eq_union_of_meet
    {X₁ X₂ Z : Finset object.Vertex}
    (c₁ : Graph.SupportComponents.Connected.ConnectedOn object X₁)
    (c₂ : Graph.SupportComponents.Connected.ConnectedOn object X₂)
    (sel : Graph.CanonicalSupport.select? object (X₁ ∪ X₂) = some Z)
    {v : object.Vertex} (v₁ : v ∈ X₁) (v₂ : v ∈ X₂) :
    Z = X₁ ∪ X₂ := by
  classical
  have cand := Graph.CanonicalSupport.mem_candidates_iff.1
    (Graph.CanonicalSupport.select?_mem_candidates sel)
  have conn : Graph.SupportComponents.Connected.ConnectedOn object (X₁ ∪ X₂) :=
    Graph.SameTokenRoutingGerms.connectedOn_union_of_common c₁ c₂ v₁ v₂
  have le := Graph.CanonicalSupport.select?_card_le sel
    (Graph.CanonicalSupport.mem_candidates_iff.2 ⟨subset_refl _, conn⟩)
  exact (Finset.eq_of_subset_of_card_le cand.1 le).symm

/-! ## G3: disjoint connector routes give a covered `[179]` (B1(ii)) -/

/-- The cycle `a → b ⇝ c → d ⇝ a` of two vertex-disjoint paths and two edges. -/
theorem cycle_of_disjoint {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) (f : G.Walk b c) (g : G.Walk d a)
    (hf : f.IsPath) (hg : g.IsPath)
    (disj : ∀ v ∈ f.support, v ∉ g.support)
    (pos : 0 < f.length + g.length) :
    (SimpleGraph.Walk.cons hab (f.append (SimpleGraph.Walk.cons hcd g))).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons, List.tail_cons]
    rw [List.nodup_append]
    refine ⟨hf.support_nodup, hg.support_nodup, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact disj x hx hy
  · intro h
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, List.mem_append,
      List.mem_cons] at h
    rcases h with h | h | h
    · exact disj a (f.fst_mem_support_of_mem_edges h) g.end_mem_support
    · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact disj a f.end_mem_support g.end_mem_support
      · have f0 : f = SimpleGraph.Walk.nil := SimpleGraph.Walk.isPath_iff_eq_nil.mp hf
        have g0 : g = SimpleGraph.Walk.nil := SimpleGraph.Walk.isPath_iff_eq_nil.mp hg
        subst f0; subst g0
        simp at pos
    · exact disj b f.start_mem_support (g.snd_mem_support_of_mem_edges h)

/-- **G3, the one-cell serial system.** Two connector routes of the return
system that are vertex-disjoint, the forward one inside the obstruction's overlap
support, and not both trivial, are alternative (v) of
`lem:pair-system-realizability`: one cell (the forward route), closing
`|backward| + 2`, offset `0`. -/
noncomputable def serialOfDisjoint (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support)
    (pos : 0 < routes.forward.length + routes.backward.length) :
    PairSerialDemandSystem data object :=
  let interfaces : Fin 2 → object.Vertex := fun j =>
    if j.val = 0 then returns.leftDemand.2 else returns.rightDemand.1
  have h₁ : ∀ i : Fin 1, returns.leftDemand.2 = interfaces i.castSucc := by
    intro i
    have : (i.castSucc : Fin 2).val = 0 := by
      have := i.isLt; simp only [Fin.coe_castSucc]; omega
    simp only [interfaces, this, if_true]
  have h₂ : ∀ i : Fin 1, returns.rightDemand.1 = interfaces i.succ := by
    intro i
    have : (i.succ : Fin 2).val ≠ 0 := by simp
    simp only [interfaces, this, if_false]
  { returns := returns
    cells := 1
    cells_pos := Nat.one_pos
    interfaces := interfaces
    lengths := fun _ => {routes.forward.length}
    lengths_nonempty := fun _ => Finset.singleton_nonempty _
    piece := fun i _ _ => routes.forward.copy (h₁ i) (h₂ i)
    piece_isPath := fun i _ _ => by
      rw [SimpleGraph.Walk.isPath_copy]; exact routes.forward_isPath
    piece_length := fun i length member => by
      rw [SimpleGraph.Walk.length_copy]; exact (Finset.mem_singleton.mp member).symm
    piece_inside := fun i _ _ v hv => by
      rw [SimpleGraph.Walk.support_copy] at hv; exact inside v hv
    cell_internal_disjoint := fun i left leftMem right rightMem ne => by
      exact absurd ((Finset.mem_singleton.mp leftMem).trans
        (Finset.mem_singleton.mp rightMem).symm) ne
    cells_internal_disjoint := fun l r ne => by
      exact absurd (Subsingleton.elim l r) ne
    routes := routes
    start_eq := by simp [interfaces]
    end_eq := by simp [interfaces]
    closing := routes.backward.length + 2
    closing_eq := rfl
    closing_internal_disjoint := fun i _ _ v hb hp => by
      rw [SimpleGraph.Walk.support_copy] at hp; exact disj v hp hb
    offsets := {0}
    offsets_nonempty := Finset.singleton_nonempty _
    increments_bounded := fun i left leftMem right rightMem => by
      rw [Finset.mem_singleton.mp leftMem, Finset.mem_singleton.mp rightMem,
        Nat.dist_self]
      exact Nat.zero_le _
    realized_route := fun choice mem offset offMem => by
      have c0 : choice 0 = routes.forward.length := Finset.mem_singleton.mp (mem 0)
      have o0 : offset = 0 := Finset.mem_singleton.mp offMem
      rw [Fin.sum_univ_one, c0, o0]
      exact ⟨{ vertex := returns.leftDemand.1
               walk := SimpleGraph.Walk.cons returns.leftDemand_adj
                 (routes.forward.append
                   (SimpleGraph.Walk.cons returns.rightDemand_adj routes.backward))
               isCycle := cycle_of_disjoint _ _ _ _ routes.forward_isPath
                 routes.backward_isPath disj pos
               length_eq := by
                 simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_append]
                 omega }⟩ }

/-- G3: the serial system built from disjoint routes has the given returns. -/
theorem realizability_of_disjoint (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support)
    (pos : 0 < routes.forward.length + routes.backward.length) :
    Nonempty (PairSystemRealizabilityOutcome returns) :=
  ⟨.serial (serialOfDisjoint returns routes inside disj pos) rfl⟩

/-- **G3 (B1(ii)), exact form.** If the `[179]` coverage test fails at the
return system, every pair of vertex-disjoint connector routes whose forward
route lies in `U` is the trivial pair: both routes have length `0`, i.e.
`d_p.2 = d_q.1` and `d_q.2 = d_p.1` (the two demands are one edge in opposite
orientations). -/
theorem disjointRoutes_trivial_of_fails (returns : PairDemandReturns data object)
    (fails : ¬ Nonempty (PairSystemRealizabilityOutcome returns))
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (inside : ∀ v ∈ routes.forward.support,
      v ∈ returns.overlap.system.overlapSupport returns.overlap.family)
    (disj : ∀ v ∈ routes.forward.support, v ∉ routes.backward.support) :
    routes.forward.length = 0 ∧ routes.backward.length = 0 := by
  by_contra h
  exact fails (realizability_of_disjoint returns routes inside disj (by omega))

/-- **G3, same-centre case.** When the two demands share their centre
(`d_p.1 = d_q.1`) every forward and backward connector route meet (at that
centre), so G3 never applies there. -/
theorem routes_meet_of_same_centre (returns : PairDemandReturns data object)
    (routes : PairDemandReturns.ConnectorRoutes returns)
    (same : returns.leftDemand.1 = returns.rightDemand.1) :
    ∃ v ∈ routes.forward.support, v ∈ routes.backward.support :=
  ⟨returns.rightDemand.1, routes.forward.end_mem_support,
    same ▸ routes.backward.end_mem_support⟩

/-! ## G4: the obstruction handoff's local structure (B3) -/

theorem pairObstructionSeparator_spec_of_eq_some
    {returns : PairDemandReturns data object}
    {routes : PairObstructionRoutes object} {split : SameTokenFirstSeparator object}
    (selected : canonicalPairObstructionSeparator data object returns =
      some (routes, split)) :
    PairObstructionRoutesSpec data object returns routes ∧
      PairObstructionSeparatorSpec data object returns routes split := by
  unfold canonicalPairObstructionSeparator at selected
  cases hR : canonicalPairObstructionRoutes data object returns with
  | none => simp [hR] at selected
  | some chosen =>
    rw [hR, Option.bind_some] at selected
    cases hS : canonicalChoice (PairObstructionSeparatorSpec data object returns chosen) with
    | none => simp [hS] at selected
    | some chosenSplit =>
      rw [hS, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact ⟨canonicalChoice_spec_of_eq_some hR, canonicalChoice_spec_of_eq_some hS⟩

theorem pairObstructionEnvelope_conditions
    {returns : PairDemandReturns data object}
    {routes : PairObstructionRoutes object} {split : SameTokenFirstSeparator object}
    {envelope : SameTokenEnvelope data object}
    (selected : canonicalPairObstructionSeparator data object returns =
      some (routes, split))
    (env : canonicalPairObstructionEnvelope data object returns = some envelope) :
    SameTokenHandoffConditions data object split := by
  classical
  unfold canonicalPairObstructionEnvelope at env
  rw [selected] at env
  simp only at env
  split at env
  · next both => exact both.2
  · cases env

theorem mem_route_of_route {returns : PairDemandReturns data object}
    {path : List object.Vertex} {endpoint : object.Vertex}
    (route : PairObstructionRoute data object returns path endpoint)
    {v : object.Vertex} (hv : v ∈ path) :
    v ∈ returns.overlap.system.overlapSupport returns.overlap.family :=
  route.2.2.2 v hv

/-- **G4 (B3).** The obstruction handoff: the canonical first separator `h`
of the obstruction's canonical routes is a vertex of the overlap support `U`
with `deg h > δ`; its next vertices `a ≠ b` are neighbours of `h` in `U`; `G`
has no label collision at the node-`[19]` packing `P₀` (the handoff's
non-absorbing condition); and the canonical envelope escapes physically. -/
theorem handoff_structure {returns : PairDemandReturns data object}
    (handoff : PairObstructionHandoff data object returns) :
    ∃ routes split envelope,
      canonicalPairObstructionSeparator data object returns = some (routes, split) ∧
      canonicalPairObstructionEnvelope data object returns = some envelope ∧
      PairObstructionRoutesSpec data object returns routes ∧
      PairObstructionSeparatorSpec data object returns routes split ∧
      data.threshold < object.degree split.separator ∧
      ¬ Graph.HasCycleWithLength data.LengthOK object ∧
      ¬ Graph.WindowLabelCollision.LabelCollision object data.windowOrder
          data.LengthOK (canonicalWindowPacking data object) ∧
      split.nextFirst ≠ split.nextSecond ∧
      object.graph.Adj split.separator split.nextFirst ∧
      object.graph.Adj split.separator split.nextSecond ∧
      split.separator ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      split.nextFirst ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      split.nextSecond ∈ returns.overlap.system.overlapSupport returns.overlap.family ∧
      SameTokenEscape data object split envelope := by
  obtain ⟨core, centres, routes, split, envelope, hsep, henv, escape, -, -⟩ := handoff
  obtain ⟨rspec, sspec⟩ := pairObstructionSeparator_spec_of_eq_some hsep
  have cond := pairObstructionEnvelope_conditions hsep henv
  have route₁ := rspec.2.2.1
  have route₂ := rspec.2.2.2.1
  have e₁ := sspec.1
  have e₂ := sspec.2.1
  have ne := sspec.2.2.1
  have adj₁ := sspec.2.2.2.2.2.1
  have adj₂ := sspec.2.2.2.2.2.2.1
  have hmem : split.separator ∈ routes.first := by rw [e₁]; simp
  have amem : split.nextFirst ∈ routes.first := by rw [e₁]; simp
  have bmem : split.nextSecond ∈ routes.second := by rw [e₂]; simp
  exact ⟨routes, split, envelope, hsep, henv, rspec, sspec, cond.1, cond.2.1, cond.2.2.1,
    ne, adj₁, adj₂, mem_route_of_route route₁ hmem, mem_route_of_route route₁ amem,
    mem_route_of_route route₂ bmem, escape⟩

end Hypostructure.Graph.PairArms
