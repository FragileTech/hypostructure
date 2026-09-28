import Hypostructure.Graph.CapacityFreeSide.Double
import Hypostructure.Graph.CapacityFreeSide.Free
import Hypostructure.Graph.SparseOrderArithmetic

/-!
# Extended surplus blockers: kinds (g) and (h)

EXTENSION of `def:surplus-blockers` — clauses (a)–(f) and `capacityCharge` are
untouched.  Two new finite-capacity blocker objects of G:

* **(g) centre–shoulder suppression** (`CentreShoulderBlocks`): two tight
  configurations `c₁ = (x_p; h, a_p, b_p)`, `c₂ = (x_q; h_q, h, b_q)` whose ports
  are the pair, with `c₂.left = c₁.center`, and the accepted cycle that
  minimality forces in the double suppression `G − x_p − x_q + a_p b_p + h b_q`
  (`double_suppression_forced`).
* **(h) triangular-port certificate** (`TriangularBlocks`): a port `(h,x)` of the
  pair with `N(x) = {h,a,b}`, the triangle `x a b`, and (forced by `C₄`-freeness)
  `h ≁ a`, `h ≁ b`.

`extended_coverage`: at a minimal object on the baseline with `H` independent and
no `C₄`, EVERY scheduled pair carries an old blocker, a (g) or an (h) blocker.
-/

namespace Hypostructure.Graph.CapacityFreeSide

open Hypostructure Hypostructure.Graph

universe u

variable {object : FiniteObject.{u}}

/-- The configuration with its two shoulders exchanged. -/
def configSwap (c : TightVertexSuppression.Configuration object) :
    TightVertexSuppression.Configuration object where
  vertex := c.vertex
  center := c.center
  left := c.right
  right := c.left
  vertex_center := c.vertex_center
  vertex_left := c.vertex_right
  vertex_right := c.vertex_left
  neighbors := fun o h => by
    rcases c.neighbors o h with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr e)
    · exact Or.inr (Or.inl e)
  center_ne_left := c.center_ne_right
  center_ne_right := c.center_ne_left
  left_ne_right := c.left_ne_right.symm
  shoulder_missing := fun h => c.shoulder_missing h.symm

/-- **Blocker (g): the centre–shoulder double suppression with its forced cycle.** -/
def CentreShoulderBlocks (LengthOK : Nat → Prop) (object : FiniteObject.{u})
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  ∃ c₁ c₂ : TightVertexSuppression.Configuration object,
    (∀ x, x ∈ pair ↔ x = (c₁.center, c₁.vertex) ∨ x = (c₂.center, c₂.vertex)) ∧
    ∃ (hl : c₂.left = c₁.center) (hx : c₂.vertex ≠ c₁.vertex)
      (hxl : c₂.vertex ≠ c₁.left) (hxr : c₂.vertex ≠ c₁.right)
      (hc : c₂.center ≠ c₁.vertex) (hr : c₂.right ≠ c₁.vertex),
      HasCycleWithLength LengthOK
        (singleFamily (secondConfig c₁ c₂ hl hx hxl hxr hc hr)).suppressed

/-- **Blocker (h): a triangular port of the pair, with its triangle.** -/
def TriangularBlocks (object : FiniteObject.{u})
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  ∃ p ∈ pair, ∃ a b : object.Vertex,
    object.graph.Adj p.1 p.2 ∧ object.graph.Adj p.2 a ∧ object.graph.Adj p.2 b ∧
    object.graph.Adj a b ∧ a ≠ p.1 ∧ b ≠ p.1 ∧
    (∀ o, object.graph.Adj p.2 o → o = p.1 ∨ o = a ∨ o = b) ∧
    ¬ object.graph.Adj p.1 a ∧ ¬ object.graph.Adj p.1 b

variable {threshold order : Nat}
  {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}

/-- A selected triangular port is an (h) blocker of any pair containing it. -/
theorem triangularBlocks_of_port
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (hL4 : LengthOK 4) (noC4 : ¬ HasCycleWithLength LengthOK object)
    {p : object.Vertex × object.Vertex} (hp : p ∈ object.excessPorts threshold)
    (tri : object.graph.Adj (pairResponseChordEnds active p).1 (pairResponseChordEnds active p).2)
    {pair : Finset (object.Vertex × object.Vertex)} (mem : p ∈ pair) :
    TriangularBlocks object pair := by
  classical
  have e : pairResponseChordEnds active p =
      ((active.shoulderPair p hp).choose, (active.shoulderPair p hp).choose_spec.choose) := by
    simp only [pairResponseChordEnds, dif_pos hp]
  rw [e] at tri
  set a := (active.shoulderPair p hp).choose
  set b := (active.shoulderPair p hp).choose_spec.choose
  have iff := (active.shoulderPair p hp).choose_spec.choose_spec.1
  have hab := (active.shoulderPair p hp).choose_spec.choose_spec.2
  have sa := (FiniteObject.SurplusPort.mem_shoulders_iff _ a).1 ((iff a).2 (Or.inl rfl))
  have sb := (FiniteObject.SurplusPort.mem_shoulders_iff _ b).1 ((iff b).2 (Or.inr rfl))
  have adj := FiniteObject.adj_of_mem_excessPorts hp
  have nbr : ∀ o, object.graph.Adj p.2 o → o = p.1 ∨ o = a ∨ o = b := by
    intro o ho
    by_cases hc : o = p.1
    · exact Or.inl hc
    · exact Or.inr ((iff o).1 ((FiniteObject.SurplusPort.mem_shoulders_iff _ o).2 ⟨hc, ho⟩))
  have xa : p.2 ≠ a := object.graph.ne_of_adj sa.2
  have xb : p.2 ≠ b := object.graph.ne_of_adj sb.2
  have hx : p.1 ≠ p.2 := object.graph.ne_of_adj adj
  refine ⟨p, mem, a, b, adj, sa.2, sb.2, tri, sa.1, sb.1, nbr, fun h => noC4 ?_, fun h => noC4 ?_⟩
  · -- `h a b x h`
    exact FiniteObject.hasC4_of_square hL4 (x := p.1) (y := b) (z := a) (w := p.2)
      sb.1.symm sa.1.symm hx hab.symm xb.symm xa.symm h tri sb.2.symm adj.symm
  · -- `h b a x h`
    exact FiniteObject.hasC4_of_square hL4 (x := p.1) (y := a) (z := b) (w := p.2)
      sa.1.symm sb.1.symm hx hab xa.symm xb.symm h tri.symm sa.2.symm adj.symm

/-- (g) from a centre–shoulder incidence of two open selected ports. -/
theorem centreShoulderBlocks_of_ports
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (baseline : threshold ≤ object.minDegree)
    (minimal : ∀ smaller : FiniteObject.{u}, smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    (indep : ∀ l r : object.Vertex, threshold < object.degree l →
      threshold < object.degree r → ¬ object.graph.Adj l r)
    {p q : object.Vertex × object.Vertex}
    (hp : p ∈ object.excessPorts threshold) (hq : q ∈ object.excessPorts threshold)
    (openP : ¬ object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2)
    (openQ : ¬ object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2)
    (disjT : Disjoint (portT hp) (portT hq)) (hpT : p.1 ∈ portT hq)
    {pair : Finset (object.Vertex × object.Vertex)} (hpair : ∀ x, x ∈ pair ↔ x = p ∨ x = q) :
    CentreShoulderBlocks LengthOK object pair := by
  classical
  letI : DecidableEq object.Vertex := @FinEnum.decEq _ object.vertices
  set c₁ := portConfig active hp openP
  set d := portConfig active hq openQ
  have hiP := FiniteObject.centre_high_of_mem_excessPorts hp
  have hiQ := FiniteObject.centre_high_of_mem_excessPorts hq
  -- `p.1` is a shoulder of `q` (not its endpoint: the endpoint touches the hub `q.1`)
  have sh : p.1 = d.left ∨ p.1 = d.right := by
    unfold portT FiniteObject.SurplusPort.support at hpT
    rcases Finset.mem_insert.1 hpT with h | h
    · exact (indep _ _ hiQ hiP
        (by rw [h]; exact FiniteObject.adj_of_mem_excessPorts hq)).elim
    · exact ((active.shoulderPair q hq).choose_spec.choose_spec.1 _).1 h
  -- the second configuration, oriented so that its left shoulder is `p.1`
  obtain ⟨c₂, hc₂l, hc₂v, hc₂c, hc₂T⟩ : ∃ c₂ : TightVertexSuppression.Configuration object,
      c₂.left = c₁.center ∧ c₂.vertex = q.2 ∧ c₂.center = q.1 ∧
      (c₂.vertex ∈ portT hq ∧ c₂.left ∈ portT hq ∧ c₂.right ∈ portT hq) := by
    rcases sh with h | h
    · exact ⟨d, h.symm, rfl, rfl, portConfig_vertex_mem active hq openQ,
        portConfig_left_mem active hq openQ, portConfig_right_mem active hq openQ⟩
    · exact ⟨configSwap d, h.symm, rfl, rfl, portConfig_vertex_mem active hq openQ,
        portConfig_right_mem active hq openQ, portConfig_left_mem active hq openQ⟩
  have inP : c₁.vertex ∈ portT hp ∧ c₁.left ∈ portT hp ∧ c₁.right ∈ portT hp :=
    ⟨portConfig_vertex_mem active hp openP, portConfig_left_mem active hp openP,
      portConfig_right_mem active hp openP⟩
  have sep : ∀ {u w}, u ∈ portT hq → w ∈ portT hp → u ≠ w := fun hu hw e =>
    Finset.disjoint_left.1 disjT (e ▸ hw) hu
  have hx : c₂.vertex ≠ c₁.vertex := sep hc₂T.1 inP.1
  have hxl : c₂.vertex ≠ c₁.left := sep hc₂T.1 inP.2.1
  have hxr : c₂.vertex ≠ c₁.right := sep hc₂T.1 inP.2.2
  have hr : c₂.right ≠ c₁.vertex := sep hc₂T.2.2 inP.1
  have hc : c₂.center ≠ c₁.vertex := by
    rw [hc₂c]
    intro e
    have h2 : threshold < object.degree p.2 := by
      have := hiQ; rw [show q.1 = p.2 from e] at this; exact this
    exact indep _ _ hiP h2 (FiniteObject.adj_of_mem_excessPorts hp)
  have hi₂ : threshold < object.degree c₂.center := hc₂c ▸ hiQ
  obtain ⟨-, -, -, cyc⟩ := double_suppression_forced (LengthOK := LengthOK) threshold c₁ c₂
    hc₂l hx hxl hxr hc hr baseline hiP hi₂ minimal
  refine ⟨c₁, c₂, fun x => ?_, hc₂l, hx, hxl, hxr, hc, hr, cyc⟩
  rw [hpair, hc₂c, hc₂v]
  rfl

/-- **Extended coverage.**  At a minimal object on the baseline, with `H`
independent and no `C₄`, every scheduled pair carries an old blocker, a
centre–shoulder (g) blocker, or a triangular (h) blocker. -/
theorem extended_coverage
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (data : CapacityPresentation object threshold order)
    (hact : data.activation = recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) (pairResponseActivation active)
      (object.portPairSchedule threshold))
    (baseline : threshold ≤ object.minDegree)
    (minimal : ∀ smaller : FiniteObject.{u}, smaller.LexicographicallySmaller object →
      threshold ≤ smaller.minDegree → HasCycleWithLength LengthOK smaller)
    (indep : ∀ l r : object.Vertex, threshold < object.degree l →
      threshold < object.degree r → ¬ object.graph.Adj l r)
    (hL4 : LengthOK 4) (noC4 : ¬ HasCycleWithLength LengthOK object)
    {pair : Finset (object.Vertex × object.Vertex)}
    (sched : pair ∈ object.portPairSchedule threshold) :
    (data.activation.blockers pair).Nonempty ∨ CentreShoulderBlocks LengthOK object pair ∨
      TriangularBlocks object pair := by
  classical
  by_cases blk : (data.activation.blockers pair).Nonempty
  · exact Or.inl blk
  right
  obtain ⟨p, q, hp, hq, hpq, hpair, -, dT, -, centres, -, -, -, noChord⟩ :=
    unblocked_structure active data hact sched blk
  have pm : p ∈ pair := (hpair p).2 (Or.inl rfl)
  have qm : q ∈ pair := (hpair q).2 (Or.inr rfl)
  by_cases tp : object.graph.Adj (pairResponseChordEnds active p).1
      (pairResponseChordEnds active p).2
  · exact Or.inr (triangularBlocks_of_port active hL4 noC4 hp tp pm)
  by_cases tq : object.graph.Adj (pairResponseChordEnds active q).1
      (pairResponseChordEnds active q).2
  · exact Or.inr (triangularBlocks_of_port active hL4 noC4 hq tq qm)
  left
  by_cases hpT : p.1 ∈ portT hq
  · exact centreShoulderBlocks_of_ports active baseline minimal indep hp hq tp tq dT hpT hpair
  by_cases hqT : q.1 ∈ portT hp
  · exact centreShoulderBlocks_of_ports active baseline minimal indep hq hp tq tp dT.symm hqT
      (fun x => (hpair x).trans or_comm)
  obtain ⟨chords, hc⟩ := chordObstruction_of_separated active baseline minimal hp hq tp tq dT
    centres hpT hqT pair hpair
  rw [noChord] at hc
  simp at hc

end Hypostructure.Graph.CapacityFreeSide
