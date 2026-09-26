import Hypostructure.Graph.Statements.Spine

/-!
# Scratch: the (F4) charge of the cold corridors

Everything here is read-only use of the repo.  Goal: bound the number of
eligible cold half-edges whose routed first failure is (F4), i.e. whose
corridor first enters a support registered by `ColdDeclaredHandoffSupport`.
-/

namespace ColdF4Scratch

open Hypostructure Hypostructure.Graph
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

/-! ## 1. Stubs into a support are at most its boundary incidence -/

theorem card_stubs_le_boundaryIncidence (P : Finset object.Vertex)
    (S : Finset (object.Vertex × object.Vertex))
    (hS : ∀ p ∈ S, p.2 ∈ P ∧ p.1 ∉ P ∧ object.graph.Adj p.2 p.1) :
    S.card ≤ object.boundaryIncidence P := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  have maps : ∀ p ∈ S, p.2 ∈ P := fun p hp => (hS p hp).1
  rw [Finset.card_eq_sum_card_fiberwise maps]
  unfold FiniteObject.boundaryIncidence
  refine Finset.sum_le_sum fun v _ => ?_
  -- the fibre over `v` injects into `N(v) \ P`
  have inj : Set.InjOn (Prod.fst : object.Vertex × object.Vertex → object.Vertex)
      ((S.filter fun p => p.2 = v : Finset _) : Set (object.Vertex × object.Vertex)) := by
    intro a ha b hb same
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    exact Prod.ext same (ha.2.trans hb.2.symm)
  have into : ∀ p ∈ S.filter (fun p => p.2 = v),
      p.1 ∈ object.graph.neighborFinset v \ P := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨inP, notP, adj⟩ := hS p hp.1
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    exact ⟨hp.2 ▸ adj, notP⟩
  have le1 := Finset.card_le_card_of_injOn Prod.fst into inj
  have split := Finset.card_sdiff_add_card_inter
    (object.graph.neighborFinset v) P
  have degEq : object.degree v = (object.graph.neighborFinset v).card := by
    unfold FiniteObject.degree
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  have intEq : object.internalDegree P v =
      (object.graph.neighborFinset v ∩ P).card := by
    unfold FiniteObject.internalDegree
    congr
  omega

/-! ## 2. Boundary incidence against surplus and deficiency -/

/-- `e(X, G−X) ≤ σ(X) + def⁺(X)` on the standing baseline `δ(G) ≥ t`. -/
theorem boundaryIncidence_le_surplus_add_deficiency (P : Finset object.Vertex)
    (threshold : Nat) (baseline : ∀ v, threshold ≤ object.degree v) :
    object.boundaryIncidence P ≤
      object.ambientSurplus P threshold + object.positiveDeficiency P threshold := by
  unfold FiniteObject.boundaryIncidence FiniteObject.ambientSurplus
    FiniteObject.positiveDeficiency
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  have := baseline v
  omega

/-- On a zero-surplus support the boundary incidence is the deficiency. -/
theorem boundaryIncidence_eq_deficiency_of_zero_surplus (P : Finset object.Vertex)
    (threshold : Nat) (baseline : ∀ v, threshold ≤ object.degree v)
    (zero : object.ambientSurplus P threshold = 0) :
    object.boundaryIncidence P = object.positiveDeficiency P threshold := by
  unfold FiniteObject.ambientSurplus at zero
  unfold FiniteObject.boundaryIncidence FiniteObject.positiveDeficiency
  refine Finset.sum_congr rfl fun v hv => ?_
  have each := (Finset.sum_eq_zero_iff.mp zero) v hv
  have := baseline v
  have deg : object.degree v = threshold := by omega
  rw [deg]

/-- A route-8 declared piece (`NegativeNetCharge` and zero surplus) receives
fewer than `|X|/s` boundary stubs: `s · e(X,W) < |X|`. -/
theorem route8_boundary_lt (P : Finset object.Vertex) (threshold scale : Nat)
    (baseline : ∀ v, threshold ≤ object.degree v)
    (negative : object.NegativeNetCharge P threshold scale)
    (zero : object.ambientSurplus P threshold = 0) :
    scale * object.boundaryIncidence P < P.card := by
  rw [boundaryIncidence_eq_deficiency_of_zero_surplus P threshold baseline zero]
  unfold FiniteObject.NegativeNetCharge at negative
  rw [zero] at negative
  simpa using negative


/-! ## 3. Localization: an (F4) corridor lands in a declared piece at its entry

The registry `ColdDeclaredHandoffSupport` consists of whole canonical pieces of
`R = G − W`.  A corridor lives in one outside component `K ⊆ R`; so if any of
its heads lies in a registered piece, its entry foot `ε.2` lies in the same
piece. -/

/-- A walk inside an induced support `K ⊆ R` stays in one piece of `R`. -/
theorem mem_piece_of_walk {R component : Finset object.Vertex}
    (sub : component ⊆ R)
    (c : SupportComponents.Connected.Component object R)
    {a b : (object.induce component).Vertex}
    (walk : (object.induce component).graph.Walk a b)
    (hb : b.1 ∈ object.pieceSupport R c) :
    a.1 ∈ object.pieceSupport R c := by
  induction walk with
  | nil => exact hb
  | @cons x y z adj rest ih =>
      have hy := ih hb
      have adj' : object.graph.Adj y.1 x.1 := (SimpleGraph.induce_adj.mp adj).symm
      have := SupportComponents.Connected.neighbor_mem_vertices object R c
        (vertex := y.1) (neighbor := x.1) hy (sub x.2) adj'
      simpa [SupportComponents.Connected.vertices] using this

/-- The piece registry shape shared by both disjuncts of
`ColdDeclaredHandoffSupport`. -/
def PieceRegistry (R : Finset object.Vertex)
    (Declared : Finset object.Vertex → Prop) (S : Finset object.Vertex) : Prop :=
  ∃ c ∈ object.canonicalPieces R, object.pieceSupport R c = S ∧ Declared S

theorem foot_mem_of_firstFailureHandoff
    {windows component R : Finset object.Vertex}
    (sub : component ⊆ R)
    (Declared : Finset object.Vertex → Prop)
    (corridor : ColdCorridor.Corridor object windows component)
    (segment : corridor.Segment)
    (failure : ColdCorridor.Corridor.FirstFailureHandoff corridor
      (PieceRegistry R Declared) segment) :
    ∃ c ∈ object.canonicalPieces R, Declared (object.pieceSupport R c) ∧
      (ColdCorridor.stubFoot object windows component corridor.entry).1 ∈
        object.pieceSupport R c := by
  obtain ⟨S, ⟨c, hc, rfl, declared⟩, headMem⟩ := failure.1
  refine ⟨c, hc, declared, ?_⟩
  exact mem_piece_of_walk sub c (corridor.inside.1.take segment.1) headMem

/-- `ColdDeclaredHandoffSupport` is a piece registry. -/
theorem coldDeclared_isPieceRegistry
    (data : Strategy.Spine.Parameters) (S : Finset object.Vertex) :
    Strategy.Spine.ColdDeclaredHandoffSupport data object S ↔
      PieceRegistry (object.remainderSupport
          (Strategy.Spine.canonicalWindowPacking data object))
        (Strategy.Spine.ColdDeclaredHandoffSupport data object) S := by
  constructor
  · intro declared
    rcases id declared with ⟨c, hc, eq, _⟩ | ⟨c, hc, eq, _⟩
    · exact ⟨c, hc, eq, declared⟩
    · exact ⟨c, hc, eq, declared⟩
  · rintro ⟨_, _, _, declared⟩
    exact declared

/-! ## 4. Counting -/

/-- The number of stubs whose outside foot lies in a declared piece is at most
the total boundary incidence of the declared pieces. -/
theorem card_le_sum_declared_boundary (R : Finset object.Vertex)
    (Declared : Finset object.Vertex → Prop) [DecidablePred Declared]
    (F : Finset (object.Vertex × object.Vertex))
    (stub : ∀ p ∈ F, p.1 ∉ R ∧ object.graph.Adj p.2 p.1)
    (lands : ∀ p ∈ F, ∃ c ∈ object.canonicalPieces R,
      Declared (object.pieceSupport R c) ∧ p.2 ∈ object.pieceSupport R c) :
    F.card ≤ ∑ c ∈ (object.canonicalPieces R).filter
        (fun c => Declared (object.pieceSupport R c)),
      object.boundaryIncidence (object.pieceSupport R c) := by
  classical
  let D := (object.canonicalPieces R).filter
    (fun c => Declared (object.pieceSupport R c))
  have cover : F ⊆ D.biUnion
      (fun c => F.filter fun p => p.2 ∈ object.pieceSupport R c) := by
    intro p hp
    obtain ⟨c, hc, dc, mem⟩ := lands p hp
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_filter.mpr ⟨hc, dc⟩, Finset.mem_filter.mpr ⟨hp, mem⟩⟩
  refine (Finset.card_le_card cover).trans ((Finset.card_biUnion_le).trans ?_)
  refine Finset.sum_le_sum fun c _ => ?_
  refine card_stubs_le_boundaryIncidence _ _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  refine ⟨hp.2, fun inside => (stub p hp.1).1 ?_, (stub p hp.1).2⟩
  exact object.pieceSupport_subset R c inside

/-- The surplus part of the charge is globally at most `σ(G)`. -/
theorem sum_declared_surplus_le (R : Finset object.Vertex)
    (Declared : Finset object.Vertex → Prop) [DecidablePred Declared]
    (threshold : Nat) (baseline : ∀ v, threshold ≤ object.degree v) :
    ∑ c ∈ (object.canonicalPieces R).filter
        (fun c => Declared (object.pieceSupport R c)),
      object.ambientSurplus (object.pieceSupport R c) threshold ≤
        object.degreeSurplus threshold := by
  calc _ ≤ ∑ c ∈ object.canonicalPieces R,
        object.ambientSurplus (object.pieceSupport R c) threshold :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = object.ambientSurplus R threshold :=
        object.sum_ambientSurplus_canonicalPieces R threshold
    _ ≤ object.degreeSurplus threshold :=
        object.ambientSurplus_le_degreeSurplus R threshold baseline

/-- **The strongest unconditional (F4) bound.**  With `D` the declared pieces:
`#F4 ≤ σ(G) + Σ_{X ∈ D} def⁺(X)`. -/
theorem card_le_surplus_add_declared_deficiency (R : Finset object.Vertex)
    (Declared : Finset object.Vertex → Prop) [DecidablePred Declared]
    (threshold : Nat) (baseline : ∀ v, threshold ≤ object.degree v)
    (F : Finset (object.Vertex × object.Vertex))
    (stub : ∀ p ∈ F, p.1 ∉ R ∧ object.graph.Adj p.2 p.1)
    (lands : ∀ p ∈ F, ∃ c ∈ object.canonicalPieces R,
      Declared (object.pieceSupport R c) ∧ p.2 ∈ object.pieceSupport R c) :
    F.card ≤ object.degreeSurplus threshold +
      ∑ c ∈ (object.canonicalPieces R).filter
          (fun c => Declared (object.pieceSupport R c)),
        object.positiveDeficiency (object.pieceSupport R c) threshold := by
  refine (card_le_sum_declared_boundary R Declared F stub lands).trans ?_
  calc _ ≤ ∑ c ∈ (object.canonicalPieces R).filter
          (fun c => Declared (object.pieceSupport R c)),
        (object.ambientSurplus (object.pieceSupport R c) threshold +
          object.positiveDeficiency (object.pieceSupport R c) threshold) :=
        Finset.sum_le_sum fun c _ =>
          boundaryIncidence_le_surplus_add_deficiency _ threshold baseline
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_right
          (sum_declared_surplus_le R Declared threshold baseline) _

/-- **Conditional σ-bound.**  If every declared piece satisfies the ball bound
`|X| ≤ B·σ(X)` (true, with `B = 1 + 4·(2^{11}-1) = 8189`, for every
`P₁₃`-free connected piece of positive surplus on `δ ≥ 3`, see REPORT.md),
then `#F4 ≤ (1 + t·B)·σ(G)`, i.e. `24568·σ(G)` at `t = 3`. -/
theorem card_le_mul_surplus_of_ball (R : Finset object.Vertex)
    (Declared : Finset object.Vertex → Prop) [DecidablePred Declared]
    (threshold B : Nat) (baseline : ∀ v, threshold ≤ object.degree v)
    (ball : ∀ c ∈ object.canonicalPieces R, Declared (object.pieceSupport R c) →
      (object.pieceSupport R c).card ≤
        B * object.ambientSurplus (object.pieceSupport R c) threshold)
    (F : Finset (object.Vertex × object.Vertex))
    (stub : ∀ p ∈ F, p.1 ∉ R ∧ object.graph.Adj p.2 p.1)
    (lands : ∀ p ∈ F, ∃ c ∈ object.canonicalPieces R,
      Declared (object.pieceSupport R c) ∧ p.2 ∈ object.pieceSupport R c) :
    F.card ≤ (1 + threshold * B) * object.degreeSurplus threshold := by
  refine (card_le_sum_declared_boundary R Declared F stub lands).trans ?_
  have pointwise : ∀ c ∈ (object.canonicalPieces R).filter
        (fun c => Declared (object.pieceSupport R c)),
      object.boundaryIncidence (object.pieceSupport R c) ≤
        (1 + threshold * B) *
          object.ambientSurplus (object.pieceSupport R c) threshold := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have e := boundaryIncidence_le_surplus_add_deficiency
      (object.pieceSupport R c) threshold baseline
    have d : object.positiveDeficiency (object.pieceSupport R c) threshold ≤
        threshold * (object.pieceSupport R c).card := by
      unfold FiniteObject.positiveDeficiency
      calc _ ≤ ∑ _v ∈ object.pieceSupport R c, threshold :=
            Finset.sum_le_sum fun v _ => Nat.sub_le _ _
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have b := ball c hc.1 hc.2
    have tb := Nat.mul_le_mul_left threshold b
    calc _ ≤ _ := e
      _ ≤ object.ambientSurplus (object.pieceSupport R c) threshold +
            threshold * (B * object.ambientSurplus (object.pieceSupport R c) threshold) :=
          Nat.add_le_add_left (d.trans tb) _
      _ = _ := by ring
  refine (Finset.sum_le_sum pointwise).trans ?_
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left _ (sum_declared_surplus_le R Declared threshold baseline)


/-! ## 5. Instantiation on the retained first-failure occurrence of `G` -/

open Strategy.Spine in
/-- The subset clause of the retained corridor state: every corridor
component lies in `R(P₀)`. -/
theorem coldOccurrence_component_subset (data : Parameters)
    (occ : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) :
    coldOccurrenceComponentAt data object occ epsilon ⊆
      object.remainderSupport (canonicalWindowPacking data object) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec occ.state))))).2.2.2.1 epsilon

open Strategy.Spine in
theorem coldOccurrence_entryStub (data : Parameters)
    (occ : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object) :
    (coldOccurrenceCorridorAt data object occ epsilon).entryStub =
      (epsilon.1.2, epsilon.1.1) :=
  ((coldOccurrenceStateFacts data object occ) epsilon).2.1

open Strategy.Spine in
/-- **(F4) count on `G`.**  With the registry of `ColdDeclaredHandoffSupport`:
`#{ε : first failure (F4)} ≤ σ(G) + Σ_{declared pieces X} def⁺(X)`. -/
theorem coldF4_card_le (data : Parameters)
    (occ : ColdFirstFailureOccurrenceData data object)
    (baseline : ∀ v, data.threshold ≤ object.degree v) :
    letI : FinEnum object.Vertex := object.vertices
    haveI := Classical.decPred (ColdDeclaredHandoffSupport data object)
    haveI := Classical.decPred (ColdFirstFailureHandoffOccurrence data object occ)
    let R := object.remainderSupport (canonicalWindowPacking data object)
    (Finset.univ.filter (ColdFirstFailureHandoffOccurrence data object occ)).card ≤
      object.degreeSurplus data.threshold +
        ∑ c ∈ (object.canonicalPieces R).filter
            (fun c => ColdDeclaredHandoffSupport data object (object.pieceSupport R c)),
          object.positiveDeficiency (object.pieceSupport R c) data.threshold := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  intro R
  let F4 := Finset.univ.filter (ColdFirstFailureHandoffOccurrence data object occ)
  let F := F4.image (fun epsilon : ColdEligibleHalfEdge data object => epsilon.1)
  have cardEq : F.card = F4.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have registry : ColdDeclaredHandoffSupport data object =
      PieceRegistry R (ColdDeclaredHandoffSupport data object) :=
    funext fun S => propext (coldDeclared_isPieceRegistry data S)
  -- the per-ε facts
  have facts : ∀ epsilon ∈ F4,
      (epsilon.1.1 ∉ R ∧ object.graph.Adj epsilon.1.2 epsilon.1.1) ∧
      ∃ c ∈ object.canonicalPieces R,
        ColdDeclaredHandoffSupport data object (object.pieceSupport R c) ∧
          epsilon.1.2 ∈ object.pieceSupport R c := by
    intro epsilon hmem
    have hF4 := (Finset.mem_filter.mp hmem).2
    let corridor := coldOccurrenceCorridorAt data object occ epsilon
    have entry := coldOccurrence_entryStub data occ epsilon
    have isStub := (ColdCorridor.mem_boundaryStubs_iff object _ _ _).1
      (List.get_mem _ corridor.entry)
    change ColdCorridor.IsBoundaryStub object _ _ corridor.entryStub at isStub
    rw [entry] at isStub
    obtain ⟨_, windowMem, adj⟩ := isStub
    refine ⟨⟨?_, adj⟩, ?_⟩
    · intro inR
      obtain ⟨window, windowIn, inWindow⟩ :=
        (ColdCorridor.mem_windowsOf object _ _).1 windowMem
      exact FiniteObject.notMem_windowSupport_of_mem_remainderSupport inR
        (FiniteObject.mem_windowSupport windowIn inWindow)
    · obtain ⟨first, handoff, _⟩ := hF4
      change ColdCorridor.Corridor.FirstFailureHandoff corridor
        (ColdDeclaredHandoffSupport data object) first at handoff
      rw [registry] at handoff
      obtain ⟨c, hc, declared, footMem⟩ := foot_mem_of_firstFailureHandoff
        (coldOccurrence_component_subset data occ epsilon)
        (ColdDeclaredHandoffSupport data object) corridor first handoff
      refine ⟨c, hc, declared, ?_⟩
      have footEq : corridor.entryStub.1 = epsilon.1.2 := by rw [entry]
      rw [← footEq]
      exact footMem
  rw [← cardEq]
  refine card_le_surplus_add_declared_deficiency R
    (ColdDeclaredHandoffSupport data object) data.threshold baseline F ?_ ?_
  · intro p hp
    obtain ⟨epsilon, he, rfl⟩ := Finset.mem_image.mp hp
    exact (facts epsilon he).1
  · intro p hp
    obtain ⟨epsilon, he, rfl⟩ := Finset.mem_image.mp hp
    exact (facts epsilon he).2


/-! ## 6. The repaired registry: heavy centres

Registry `Heavy S :≡ ∃ z, S = {z} ∧ t < d(z)` ("the corridor first enters a
declared handoff centre", `lem:absorbed-germ-fan-data` (ii)).  Then an (F4)
head lies inside the (F5) trace prefix and is high, so the half-edge is a
first-high noncandidate, already paid by `corridorLoss ≤ (t+1)·B_cold·σ(G)`. -/

section Heavy

variable {windows component : Finset object.Vertex}

/-- A head lies in the prefix of length `n` exactly when its index is `≤ n`
(the corridor is a simple path). -/
theorem head_mem_prefixSupport_iff
    (corridor : ColdCorridor.Corridor object windows component)
    (s : corridor.Segment) (n : Nat) :
    corridor.head s ∈ corridor.prefixSupport n ↔ s.1 ≤ n := by
  classical
  constructor
  · intro mem
    obtain ⟨inner, innerMem, innerEq⟩ := (corridor.mem_prefixSupport n _).1 mem
    obtain ⟨i, hi, hiLe⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp innerMem
    rw [SimpleGraph.Walk.take_getVert] at hi
    have takeLen := SimpleGraph.Walk.take_length corridor.inside.1 n
    have eq : corridor.inside.1.getVert (min n i) = corridor.inside.1.getVert s.1 := by
      apply Subtype.ext
      rw [hi]
      exact innerEq
    have inj := corridor.inside.2.getVert_injOn
      (show min n i ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega)
      (show s.1 ∈ {j | j ≤ corridor.inside.1.length} by
        simp only [Set.mem_setOf_eq]; omega) eq
    omega
  · intro le
    refine (corridor.mem_prefixSupport n _).2
      ⟨(corridor.inside.1.take n).getVert s.1, ?_, ?_⟩
    · exact SimpleGraph.Walk.getVert_mem_support _ _
    · rw [SimpleGraph.Walk.take_getVert, Nat.min_eq_right le]
      rfl

/-- The last head of a repeated-state interval lies in the interval support. -/
theorem head_right_mem_intervalSupport
    (corridor : ColdCorridor.Corridor object windows component)
    (left right : corridor.Segment) (le : left.1 ≤ right.1) :
    corridor.head right ∈ corridor.intervalSupport left right := by
  classical
  refine (corridor.mem_intervalSupport left right _).2
    ⟨((corridor.inside.1.drop left.1).take (right.1 - left.1)).getVert
      (right.1 - left.1), SimpleGraph.Walk.getVert_mem_support _ _, ?_⟩
  rw [SimpleGraph.Walk.take_getVert, SimpleGraph.Walk.drop_getVert]
  have : left.1 + min (right.1 - left.1) (right.1 - left.1) = right.1 := by omega
  rw [this]
  rfl

/-- The repaired registry. -/
def Heavy (threshold : Nat) (S : Finset object.Vertex) : Prop :=
  ∃ z, S = {z} ∧ threshold < object.degree z

/-- **Repaired (F4) is a first-high event inside the trace.**  If the corridor
first enters a heavy centre at `first`, and `first` is not after the (F5)
segment `g` (minimality of the first failure), and the trace prefix `n`
covers the germ support containing `head g`, then the trace prefix is not
subcubic: the half-edge is a first-high noncandidate. -/
theorem heavy_handoff_not_subcubic
    (corridor : ColdCorridor.Corridor object windows component)
    (threshold n : Nat) (germSupport : Finset object.Vertex)
    (cover : germSupport ⊆ corridor.prefixSupport n)
    (g : corridor.Segment) (gMem : corridor.head g ∈ germSupport)
    (first : corridor.Segment) (firstLe : first.1 ≤ g.1)
    (handoff : ColdCorridor.Corridor.FirstFailureHandoff corridor
      (Heavy threshold) first) :
    ¬ ∀ vertex ∈ corridor.prefixSupport n, object.degree vertex ≤ threshold := by
  intro subcubic
  obtain ⟨S, ⟨z, rfl, high⟩, mem⟩ := handoff.1
  rw [Finset.mem_singleton] at mem
  have gLe := (head_mem_prefixSupport_iff corridor g n).1 (cover gMem)
  have firstIn := (head_mem_prefixSupport_iff corridor first n).2 (by omega)
  have := subcubic _ firstIn
  rw [mem] at this
  omega

/-- The (F5) segment of either subcase has its head in the germ support. -/
theorem germ_head_mem_terminal
    (corridor : ColdCorridor.Corridor object windows component) :
    corridor.head ⟨corridor.inside.1.length, Nat.lt_succ_self _⟩ ∈
      corridor.prefixSupport corridor.statesRead :=
  (head_mem_prefixSupport_iff corridor _ _).2 (by
    unfold ColdCorridor.Corridor.statesRead; omega)

end Heavy


/-! ## 7. Exactness: (F4) is *exactly* "the foot lies in a declared piece"

At segment `0` the head is the entry foot `ε.2`; `FirstFailureHandoff` at
segment `0` has no earlier-segment clause.  Hence the (F4) count on `G` is
exactly the number of selected cold stubs whose foot lies in a declared piece:
the bound of §5 is attained up to the `σ + def⁺ ↔ e(X,W)` slack, and no
cleverer charging of the current registry exists. -/

open Strategy.Spine in
theorem coldF4_of_foot_declared (data : Parameters)
    (occ : ColdFirstFailureOccurrenceData data object)
    (epsilon : ColdEligibleHalfEdge data object)
    (S : Finset object.Vertex)
    (declared : ColdDeclaredHandoffSupport data object S)
    (foot : epsilon.1.2 ∈ S) :
    ColdFirstFailureHandoffOccurrence data object occ epsilon := by
  let corridor := coldOccurrenceCorridorAt data object occ epsilon
  let zero : corridor.Segment := ⟨0, Nat.succ_pos _⟩
  have headEq : corridor.head zero = epsilon.1.2 := by
    have entry := coldOccurrence_entryStub data occ epsilon
    have : corridor.head zero = corridor.entryStub.1 := by
      simp [ColdCorridor.Corridor.head, zero, ColdCorridor.Corridor.entryStub,
        ColdCorridor.stubFoot]
    rw [this, entry]
  refine ⟨zero, ⟨⟨S, declared, headEq ▸ foot⟩, fun earlier h => ?_⟩, fun earlier h => ?_⟩
  · exact absurd h (Nat.not_lt_zero _)
  · exact absurd h (Nat.not_lt_zero _)

end ColdF4Scratch

#print axioms ColdF4Scratch.coldF4_card_le
#print axioms ColdF4Scratch.card_le_mul_surplus_of_ball
#print axioms ColdF4Scratch.route8_boundary_lt
#print axioms ColdF4Scratch.heavy_handoff_not_subcubic
#print axioms ColdF4Scratch.coldF4_of_foot_declared
