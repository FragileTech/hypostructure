import Hypostructure.Graph.CapacityFreeSide.Obstruct

/-!
# Blocked side: the clause-(f) chord sets of a separated pair are its single-port cycles

For a separated open pair `{p,q}` (as in `chordObstruction_of_separated`) whose
suppression path `Q_p` avoids `x_q`, the chord set `{p}` is a clause-(f)
obstruction of the pair: the cycle `Q_p + a_p b_p` survives the simultaneous
suppression.  So the (f)-blocker of such a pair is the single-port witness of
one of its members, re-read: it consumes no pair-specific resource.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}} {threshold : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- Any accepted cycle of the two-port suppression yields a clause-(f) chord set. -/
theorem mem_chordObstructions_of_cert
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjT : Disjoint (portT hp) (portT hq))
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (pair : Finset (object.Vertex × object.Vertex)) (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (cert : CycleCertificate (pairFamily active hp hq openP openQ disjT hpT hqT).suppressed
      LengthOK)
    (chords : Finset (object.Vertex × object.Vertex))
    (hchords : ∀ x, x ∈ chords ↔ ∃ i ∈ (pairFamily active hp hq openP openQ disjT hpT hqT).usedChords cert.walk,
      (((pairFamily active hp hq openP openQ disjT hpT hqT).configuration i).center,
        ((pairFamily active hp hq openP openQ disjT hpT hqT).configuration i).vertex) = x) :
    chords ∈ (pairResponseActivation active).chordObstructions pair := by
  classical
  let F := pairFamily active hp hq openP openQ disjT hpT hqT
  have e : chords = (F.usedChords cert.walk).image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)) := by
    ext x; rw [hchords, Finset.mem_image]
  subst e
  have cfgT : F.configuration ⟨true⟩ = portConfig active hp openP := rfl
  have cfgF : F.configuration ⟨false⟩ = portConfig active hq openQ := rfl
  have sub : pair ⊆ object.excessPorts threshold := by
    intro x hx
    rcases (hpair x).1 hx with rfl | rfl
    · exact hp
    · exact hq
  have portOf : ∀ i : F.Index,
      ((F.configuration i).center, (F.configuration i).vertex) = if i.down then p else q := by
    rintro ⟨i⟩
    cases i
    · simp only [cfgF, portConfig_center, portConfig_vertex, Bool.false_eq_true, if_false]
    · simp only [cfgT, portConfig_center, portConfig_vertex, if_true]
  have img : Finset.univ.image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)) = pair := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hpair, portOf]
    constructor
    · rintro ⟨⟨i⟩, rfl⟩
      cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨⟨true⟩, rfl⟩
      · exact ⟨⟨false⟩, rfl⟩
  have chordsSub : (F.usedChords cert.walk).image (fun i : F.Index =>
      ((F.configuration i).center, (F.configuration i).vertex)) ⊆
      object.excessPorts threshold := by
    refine Finset.Subset.trans ?_ sub
    rw [← img]
    exact Finset.image_subset_image (Finset.subset_univ _)
  unfold pairResponseActivation
  dsimp only
  rw [List.mem_filter]
  refine ⟨mem_orderedChordSets _ _ chordsSub, decide_eq_true ?_⟩
  refine ⟨sub, F, cert, img, ?_, rfl⟩
  rintro ⟨i⟩
  left
  cases i
  · rw [cfgF, portConfig_center, portConfig_vertex]
    exact portConfig_ends active hq openQ
  · rw [cfgT, portConfig_center, portConfig_vertex]
    exact portConfig_ends active hp openP

/-- Lift a walk of `G` that stays among the surviving vertices to the suppressed graph. -/
noncomputable def liftWalk (F : TightVertexSuppression.CompatibleFamily object) :
    ∀ {u v : object.Vertex} (w : object.graph.Walk u v)
      (h : ∀ z ∈ w.support, z ∈ F.remainingVertices),
      F.suppressed.graph.Walk ⟨u, h u w.start_mem_support⟩ ⟨v, h v w.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | _, _, .cons (v := m) hadj w, h =>
      .cons (by
          change F.suppressedGraph.Adj _ _
          rw [TightVertexSuppression.CompatibleFamily.suppressedGraph, SimpleGraph.fromRel_adj]
          refine ⟨fun e => object.graph.ne_of_adj hadj (congrArg Subtype.val e), Or.inl (Or.inl hadj)⟩)
        (liftWalk F w (fun z hz => h z (List.mem_cons_of_mem _ hz)))

theorem liftWalk_length (F : TightVertexSuppression.CompatibleFamily object) :
    ∀ {u v : object.Vertex} (w : object.graph.Walk u v) h, (liftWalk F w h).length = w.length
  | _, _, .nil, _ => rfl
  | _, _, .cons _ w, h => by
      simp only [liftWalk, SimpleGraph.Walk.length_cons]
      rw [liftWalk_length F w]

theorem liftWalk_support (F : TightVertexSuppression.CompatibleFamily object) :
    ∀ {u v : object.Vertex} (w : object.graph.Walk u v) h,
      (liftWalk F w h).support.map Subtype.val = w.support
  | _, _, .nil, _ => rfl
  | _, _, .cons _ w, h => by
      exact congrArg (List.cons _) (liftWalk_support F w _)

theorem liftWalk_edges (F : TightVertexSuppression.CompatibleFamily object) :
    ∀ {u v : object.Vertex} (w : object.graph.Walk u v) h,
      (liftWalk F w h).edges.map (Sym2.map Subtype.val) = w.edges
  | _, _, .nil, _ => rfl
  | _, _, .cons _ w, h => by
      exact congrArg (List.cons _) (liftWalk_edges F w _)

theorem liftWalk_isPath (F : TightVertexSuppression.CompatibleFamily object)
    {u v : object.Vertex} (w : object.graph.Walk u v) h (hw : w.IsPath) :
    (liftWalk F w h).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  have := hw.support_nodup
  rw [← liftWalk_support F w h] at this
  exact List.Nodup.of_map _ this

/-- **The singleton chord set `{p}` is a clause-(f) obstruction** of a separated
open pair whenever some suppression path `Q_p` of `p` avoids `x_q`. -/
theorem singleton_chordObstruction
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjT : Disjoint (portT hp) (portT hq))
    (hpT : p.1 ∉ portT hq) (hqT : q.1 ∉ portT hp)
    (pair : Finset (object.Vertex × object.Vertex)) (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q)
    (W : FiniteObject.SurplusPort.OpenPortWitness object LengthOK p.2
      (pairResponseChordEnds active p).1 (pairResponseChordEnds active p).2)
    (avoidQ : q.2 ∉ W.path.support) :
    ({p} : Finset (object.Vertex × object.Vertex)) ∈
      (pairResponseActivation active).chordObstructions pair := by
  classical
  let F := pairFamily active hp hq openP openQ disjT hpT hqT
  have cfgT : F.configuration ⟨true⟩ = portConfig active hp openP := rfl
  have cfgF : F.configuration ⟨false⟩ = portConfig active hq openQ := rfl
  have ends := portConfig_ends active hp openP
  -- `Q_p` stays among the surviving vertices
  have remain : ∀ z ∈ W.path.support, z ∈ F.remainingVertices := by
    intro z hz
    simp only [TightVertexSuppression.CompatibleFamily.remainingVertices,
      TightVertexSuppression.CompatibleFamily.deletedVertices, Finset.mem_sdiff,
      object.mem_vertexFinset, true_and, Finset.mem_image, Finset.mem_univ, not_exists]
    rintro ⟨i⟩ h
    cases i
    · rw [cfgF, portConfig_vertex] at h
      exact avoidQ (h ▸ hz)
    · rw [cfgT, portConfig_vertex] at h
      exact W.avoids_endpoint (h ▸ hz)
  let a := (pairResponseChordEnds active p).1
  let b := (pairResponseChordEnds active p).2
  have ha : a ∈ F.remainingVertices := remain a W.path.start_mem_support
  have hb : b ∈ F.remainingVertices := remain b W.path.end_mem_support
  let Q := liftWalk F W.path remain
  have chordAdj : F.suppressed.graph.Adj ⟨b, hb⟩ ⟨a, ha⟩ := by
    change F.suppressedGraph.Adj _ _
    rw [TightVertexSuppression.CompatibleFamily.suppressedGraph, SimpleGraph.fromRel_adj]
    have ea : a = (portConfig active hp openP).left := congrArg Prod.fst ends
    have eb : b = (portConfig active hp openP).right := congrArg Prod.snd ends
    have hab : a ≠ b := by
      rw [ea, eb]; exact (portConfig active hp openP).left_ne_right
    refine ⟨fun e => hab (congrArg Subtype.val e).symm, Or.inr (Or.inr ⟨⟨true⟩, Or.inl ?_⟩)⟩
    rw [cfgT]
    exact ⟨ea, eb⟩
  let C : F.suppressed.graph.Walk ⟨b, hb⟩ ⟨b, hb⟩ := .cons chordAdj Q
  have edgesQ : ∀ e ∈ Q.edges, Sym2.map Subtype.val e ∈ W.path.edges := by
    intro e he
    rw [← liftWalk_edges F W.path remain]
    exact List.mem_map_of_mem he
  have notOld : ∀ {x y : object.Vertex}, s(x, y) ∈ W.path.edges → object.graph.Adj x y :=
    fun h => W.path.adj_of_mem_edges h
  have cyc : C.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨liftWalk_isPath F W.path remain W.isPath, fun h => ?_⟩
    have := notOld (edgesQ _ h)
    exact openP (by simpa using this.symm)
  have lenOK : LengthOK C.length := by
    simp only [C, SimpleGraph.Walk.length_cons]
    rw [liftWalk_length]
    exact W.restored_length_ok
  let cert : CycleCertificate F.suppressed LengthOK := ⟨⟨b, hb⟩, C, cyc, lenOK⟩
  have chordVal : ∀ i, Sym2.map Subtype.val (F.chord i) =
      s((F.configuration i).left, (F.configuration i).right) := fun i => rfl
  have ea : a = (portConfig active hp openP).left := congrArg Prod.fst ends
  have eb : b = (portConfig active hp openP).right := congrArg Prod.snd ends
  have u1 : F.chord ⟨true⟩ = s(⟨b, hb⟩, ⟨a, ha⟩) := by
    apply Sym2.map.injective Subtype.val_injective
    rw [chordVal]
    show s((F.configuration ⟨true⟩).left, (F.configuration ⟨true⟩).right) = s(b, a)
    rw [cfgT, ← ea, ← eb]
    exact Sym2.eq_swap
  have aP : a ∈ portT hp := ea ▸ portConfig_left_mem active hp openP
  have bP : b ∈ portT hp := eb ▸ portConfig_right_mem active hp openP
  have u2 : F.chord ⟨false⟩ ∉ C.edges := by
    intro h
    simp only [C, SimpleGraph.Walk.edges_cons, List.mem_cons] at h
    rcases h with h | h
    · have hv := congrArg (Sym2.map Subtype.val) h
      rw [chordVal] at hv
      have hm : (F.configuration ⟨false⟩).left ∈ s((F.configuration ⟨false⟩).left,
          (F.configuration ⟨false⟩).right) := Sym2.mem_mk_left _ _
      rw [hv] at hm
      have inP : (F.configuration ⟨false⟩).left ∈ portT hp := by
        rcases Sym2.mem_iff.1 hm with h | h
        · exact h ▸ bP
        · exact h ▸ aP
      exact Finset.disjoint_left.1 disjT inP (cfgF ▸ portConfig_left_mem active hq openQ)
    · have := edgesQ _ h
      rw [chordVal] at this
      have hadj := notOld this
      apply openQ
      rw [portConfig_ends active hq openQ]
      exact hadj
  have memUsed : ∀ i, i ∈ F.usedChords C ↔ F.chord i ∈ C.edges := by
    intro i
    unfold TightVertexSuppression.CompatibleFamily.usedChords
    simp
  refine mem_chordObstructions_of_cert active hp hq openP openQ disjT hpT hqT pair hpair cert
    {p} ?_
  intro x
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    refine ⟨⟨true⟩, (memUsed _).2 ?_, ?_⟩
    · rw [u1]; simp [C]
    · rw [cfgT]; rfl
  · rintro ⟨⟨i⟩, hi, hx⟩
    cases i
    · exact (u2 ((memUsed _).1 hi)).elim
    · rw [← hx, cfgT]; rfl

end Hypostructure.Graph.CapacityFreeSide
