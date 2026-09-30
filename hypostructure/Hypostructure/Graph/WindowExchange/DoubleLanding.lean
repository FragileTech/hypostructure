import Hypostructure.Graph.WindowExchange.X15Data
import Hypostructure.Graph.WindowExchange.DoubleLandingData
import Hypostructure.Graph.WindowExchange.Transport
import Hypostructure.Core.DyadicLength

/-!
# Two exits of one copy of `X15` on one window

Let `e` be an induced copy of `X15` inside the remainder `R` of a maximum window packing of
order 13, and `P` a member placed by `p`.  Suppose that the only edges between the copy and
`P` are `e x — p i` and `e y — p j` for two distinct exits `x, y ∈ {4, 6, 9}` (a *double
landing*), and that the object has no cycle of length a power of two.  Then
(`legal_of_double_landing`):

* `{x, y} = {6, 9}`: the exit `4` never double-lands;
* `{min i j, max i j}` is one of `(0,10)`, `(0,11)`, `(1,11)`, `(1,12)`, `(2,12)`.

The configuration `C ∪ P` is the 28-vertex graph `dlA x i y j` (vertices `0 … 14` the copy,
`15 + k` the position `k`).  Every other configuration carries a witness
(`doubleLandingData`, checked by `dl_cert`): a cycle of length `4`, `8` or `16`, or two
disjoint induced 13-vertex paths.  The positions `{0, 12}` are the configurations with the
two paths:

* `4@0, 6@12`: `c0-c8-c12-c2-c7-c14-c1-c6-P[12..8]` and `c3-c9-c5-c11-c4-P[0..7]`;
* `6@0, 9@12`: `c0-c8-c12-c2-c7-c14-c1-c6-P[0..4]` and `c10-c4-c11-c5-c9-P[12..5]`;

and the same for `4@0, 9@12` and the reflections.  Two disjoint windows inside `P ∪ R`
contradict maximality (`PackingExchange.false_of_two_windows_in_member_union_remainder`,
the exchange with `Q = {P}`).
-/

namespace Hypostructure.Graph.WindowExchange

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.LocalRigidity

universe u

/-! ## The configuration graph and its certificate -/

/-- Edge between the copy vertex `u` and the position `k`: the exit `x` lands at `i`, the
exit `y` at `j`. -/
def dlX (x i y j u k : ℕ) : Bool := (u == x && k == i) || (u == y && k == j)

/-- Adjacency of the configuration graph on `0 … 27`. -/
def dlA (x i y j u v : ℕ) : Bool :=
  if u < 15 then (if v < 15 then x15A u v else dlX x i y j u (v - 15))
  else if v < 15 then dlX x i y j v (u - 15) else (u + 1 == v || v + 1 == u)

/-- A witness of kind `C` (`kind = true`: a cycle of power-of-two length) or `P` (two
disjoint induced 13-vertex paths) in the configuration graph. -/
def dlWitness (x i y j : ℕ) (kind : Bool) (ns : List ℕ) : Bool :=
  if kind then chkCycle (dlA x i y j) 28 ns && decide (Core.DyadicLength.PowerOfTwoLength ns.length)
  else chkIndPath (dlA x i y j) 28 13 (ns.take 13) &&
    chkIndPath (dlA x i y j) 28 13 (ns.drop 13) &&
    (ns.take 13).all fun v => !(ns.drop 13).contains v

/-- Decode one line of `doubleLandingData` and check it against the configuration. -/
def dlLine (x i y j : ℕ) (s : String) : Bool :=
  let cs := s.toList
  let d := fun k => (cs.getD k '0').toNat - 48
  d 0 == x && d 1 == i && d 2 == y && d 3 == j &&
    dlWitness x i y j (cs.getD 4 'C' == 'C') ((cs.drop 5).map fun ch => ch.toNat - 48)

/-- Some line of the table is a valid witness for the configuration. -/
def dlGood (x i y j : ℕ) : Bool := (doubleLandingData.splitOn "\n").any (dlLine x i y j)

/-- The legal double landings: exits `{6, 9}` at an unordered position pair among
`(0,10)`, `(0,11)`, `(1,11)`, `(1,12)`, `(2,12)`. -/
def dlLegal (x i y j : ℕ) : Bool :=
  ((x == 6 && y == 9) || (x == 9 && y == 6)) &&
    [(0, 10), (0, 11), (1, 11), (1, 12), (2, 12)].contains (min i j, max i j)

theorem dlLegal_swap (x i y j : ℕ) : dlLegal y j x i = dlLegal x i y j := by
  unfold dlLegal
  rw [min_comm, max_comm]
  congr 1
  cases hx : x == 6 <;> cases hy : y == 9 <;> cases hx' : x == 9 <;> cases hy' : y == 6 <;>
    simp

/-- **The certificate.**  Every non-legal double landing `x < y` carries a witness. -/
theorem dl_cert : ∀ x ∈ x15Exits, ∀ y ∈ x15Exits, x < y → ∀ i < 13, ∀ j < 13,
    dlLegal x i y j = false → dlGood x i y j = true := by
  native_decide

/-! ## Deployment at a maximum packing -/

variable {object : FiniteObject.{u}}

/-- The realisation of the configuration graph: `u < 15 ↦ e u`, `15 + k ↦ p k`. -/
theorem exists_realisation (e : x15Graph ↪g object.graph) (p : Fin 13 → object.Vertex) :
    ∃ F : ℕ → object.Vertex, (∀ (u : ℕ) (h : u < 15), F u = e ⟨u, h⟩) ∧
      ∀ (v : ℕ) (h1 : 15 ≤ v) (h2 : v < 28), F v = p ⟨v - 15, by omega⟩ := by
  refine ⟨fun u => if h : u < 15 then e ⟨u, h⟩
    else if h2 : u - 15 < 13 then p ⟨u - 15, h2⟩ else p 0, fun u h => ?_, fun v h1 h2 => ?_⟩
  · simp only [dif_pos h]
  · simp only [dif_neg (show ¬ v < 15 by omega), dif_pos (show v - 15 < 13 by omega)]

theorem legal_core {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking 13 packing)
    (maximum : packing.card = object.windowPackingNumber 13)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
    (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ object.remainderSupport packing)
    {a b : Fin 15} (ha : a.1 ∈ x15Exits) (hb : b.1 ∈ x15Exits) (hab : a.1 < b.1)
    (i j : Fin 13)
    (land : ∀ u k, object.graph.Adj (e u) (p k) ↔ (u = a ∧ k = i) ∨ (u = b ∧ k = j)) :
    dlLegal a.1 i.1 b.1 j.1 = true := by
  classical
  by_contra hL
  have good := dl_cert a.1 ha b.1 hb hab i.1 i.2 j.1 j.2 (by simpa using hL)
  unfold dlGood at good
  rw [List.any_eq_true] at good
  obtain ⟨s, -, hs⟩ := good
  unfold dlLine at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨-, hw⟩ := hs
  generalize (s.toList.getD 4 'C' == 'C') = kind at hw
  generalize (s.toList.drop 5).map (fun ch => ch.toNat - 48) = ns at hw
  obtain ⟨F, hFe, hFp⟩ := exists_realisation e p
  have outR : ∀ v, v ∈ object.remainderSupport packing → v ∈ P → False := fun v hR hv =>
    FiniteObject.notMem_windowSupport_of_mem_remainderSupport hR
      (FiniteObject.mem_windowSupport hP hv)
  have hFadj : ∀ u v, u < 28 → v < 28 →
      (object.graph.Adj (F u) (F v) ↔ dlA a.1 i.1 b.1 j.1 u v = true) := by
    intro u v hu hv
    by_cases hu' : u < 15 <;> by_cases hv' : v < 15
    · rw [hFe u hu', hFe v hv', e.map_adj_iff, x15Graph_adj]
      simp only [dlA, if_pos hu', if_pos hv']
    · rw [hFe u hu', hFp v (by omega) hv, land]
      simp only [dlA, if_pos hu', if_neg hv', dlX, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, Fin.ext_iff]
    · rw [hFp u (by omega) hu, hFe v hv', object.graph.adj_comm, land]
      simp only [dlA, if_neg hu', if_pos hv', dlX, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, Fin.ext_iff]
    · rw [hFp u (by omega) hu, hFp v (by omega) hv, hp.2.2]
      simp only [dlA, if_neg hu', if_neg hv', Bool.or_eq_true, beq_iff_eq]
      omega
  have hinj : ∀ u v, u < 28 → v < 28 → F u = F v → u = v := by
    intro u v hu hv huv
    by_cases hu' : u < 15 <;> by_cases hv' : v < 15
    · rw [hFe u hu', hFe v hv'] at huv
      simpa using e.injective huv
    · rw [hFe u hu', hFp v (by omega) hv] at huv
      exact (outR _ (inR _) (huv ▸ hp.2.1 _)).elim
    · rw [hFp u (by omega) hu, hFe v hv'] at huv
      exact (outR _ (inR _) (huv ▸ hp.2.1 _)).elim
    · rw [hFp u (by omega) hu, hFp v (by omega) hv] at huv
      have := congrArg Fin.val (hp.1 huv)
      simp only at this
      omega
  have hmem : ∀ u, u < 28 → F u ∈ object.remainderSupport packing ∨ F u ∈ P := by
    intro u hu
    by_cases hu' : u < 15
    · exact Or.inl (hFe u hu' ▸ inR _)
    · exact Or.inr (hFp u (by omega) hu ▸ hp.2.1 _)
  cases kind with
  | true =>
    simp only [dlWitness, if_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hc, pow⟩ := hw
    obtain ⟨x, c, hcyc, hlen⟩ := cycle_of_chkCycle
      (fun u v hu hv h => (hFadj u v hu hv).2 h) hinj hc
    exact avoid (hasCycle_of_walk lengthLaw c hcyc (hlen ▸ pow))
  | false =>
    simp only [dlWitness, Bool.false_eq_true, if_false, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hw
    obtain ⟨⟨h1, h2⟩, hd⟩ := hw
    have lt1 : ∀ x ∈ ns.take 13, x < 28 := by
      simp only [chkIndPath, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h1
      exact h1.1.1.2
    have lt2 : ∀ x ∈ ns.drop 13, x < 28 := by
      simp only [chkIndPath, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
      exact h2.1.1.2
    obtain ⟨S, hS, memS⟩ := inducesWindow_of_chkIndPath hFadj hinj h1
    obtain ⟨T, hT, memT⟩ := inducesWindow_of_chkIndPath hFadj hinj h2
    refine PackingExchange.false_of_two_windows_in_member_union_remainder (by norm_num)
      valid maximum hP hS hT ?_ ?_ ?_
    · rw [Finset.disjoint_left]
      intro v hvS hvT
      obtain ⟨x, hx, rfl⟩ := (memS _).1 hvS
      obtain ⟨y, hy, hyx⟩ := (memT _).1 hvT
      have := hinj y x (lt2 y hy) (lt1 x hx) hyx
      rw [this] at hy
      exact hd x hx hy
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := (memS _).1 hv
      exact hmem x (lt1 x hx)
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := (memT _).1 hv
      exact hmem x (lt2 x hx)

/-- **Legal double landings.**  At a maximum window packing of order 13 of an object with no
cycle of power-of-two length, an induced copy `e` of `X15` inside the remainder whose only
edges to a member `P` (placed by `p`) are `e a — p i` and `e b — p j`, for two distinct
exits `a, b`, is a legal double landing: `{a, b} = {6, 9}` and the unordered position pair
is `(0,10)`, `(0,11)`, `(1,11)`, `(1,12)` or `(2,12)`. -/
theorem legal_of_double_landing {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {packing : Finset (Finset object.Vertex)}
    (valid : object.IsWindowPacking 13 packing)
    (maximum : packing.card = object.windowPackingNumber 13)
    {P : Finset object.Vertex} (hP : P ∈ packing)
    {p : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
    (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ object.remainderSupport packing)
    {a b : Fin 15} (ha : a.1 ∈ x15Exits) (hb : b.1 ∈ x15Exits) (hab : a ≠ b)
    (i j : Fin 13)
    (land : ∀ u k, object.graph.Adj (e u) (p k) ↔ (u = a ∧ k = i) ∨ (u = b ∧ k = j)) :
    dlLegal a.1 i.1 b.1 j.1 = true := by
  rcases lt_or_gt_of_ne (fun h : a.1 = b.1 => hab (Fin.ext h)) with lt | gt
  · exact legal_core avoid lengthLaw valid maximum hP hp e inR ha hb lt i j land
  · rw [← dlLegal_swap]
    exact legal_core avoid lengthLaw valid maximum hP hp e inR hb ha gt j i
      (fun u k => (land u k).trans or_comm)

/-- **Exit `4` never double-lands**, and a double landing of `6`, `9` lies in
`{0, 1, 2} × {10, 11, 12}` with gap at least `10`, positions `{0, 12}` excluded
(`legal_of_double_landing`, read off `dlLegal`). -/
theorem double_landing_positions {x i y j : ℕ} (h : dlLegal x i y j = true) :
    x ≠ 4 ∧ y ≠ 4 ∧ min i j ≤ 2 ∧ 10 ≤ max i j ∧ 10 ≤ max i j - min i j ∧
      ¬ (min i j = 0 ∧ max i j = 12) := by
  unfold dlLegal at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem,
    decide_eq_true_eq, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨hxy, hij⟩ := h
  refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩ <;> omega

end Hypostructure.Graph.WindowExchange
