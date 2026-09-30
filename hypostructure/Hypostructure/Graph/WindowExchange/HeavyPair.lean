import Hypostructure.Graph.WindowExchange.HeavyPairSound
import Hypostructure.Graph.WindowExchange.HeavyPairCert
import Hypostructure.Graph.WindowExchange.Rungs

/-!
# A copy of `X15` with exits on two windows bounds the rungs between them

Let `P`, `Q` be disjoint vertex sets placed as induced 13-vertex paths by `p`, `q`, with every
vertex of degree at most 3, and `e` an induced copy of `X15` in a set `R` disjoint from both.
Let the exit `x` of the copy be adjacent to `p a` and the exit `y ≠ x` to `q b`.  If the
object has no cycle of power-of-two length, the rungs `{(i, j) : p i ~ q j}` number at most
`6` when `4 ∈ {x, y}` and at most `8` when `{x, y} = {6, 9}` (`rungCount_le`).  In
particular a pair of windows with at least 9 rungs carries no such copy.

The proof reads a finite certificate (`HeavyPairCert`): for every configuration, every
increasing list of `7` (resp. `9`) rungs meets a sub-list with a checked witness (a cycle of
length `4`, `8`, `16` or `32` in the configuration graph, or a window vertex with four
neighbours).  The configurations are reduced to `a, b ≤ 6` by reversing `p` and `q`, to the
exits `(4, 6)` and `(6, 9)` by the automorphism `σ` of `X15` swapping `6` and `9`, and by
exchanging `P` and `Q`.
-/

namespace Hypostructure.Graph.WindowExchange

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.LocalRigidity

universe u

variable {object : FiniteObject.{u}}

/-! ## The certificate read at the object -/

/-- **Certified rung bound.**  Under the hypotheses of the module docstring, a certificate
`certCfg lo x a y b d₀ k` gives fewer than `k` rungs. -/
theorem rungCount_lt_of_cert {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {R P Q : Finset object.Vertex} (RP : ∀ v ∈ R, v ∉ P) (RQ : ∀ v ∈ R, v ∉ Q)
    (PQ : Disjoint P Q)
    {p q : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
    (hq : IsWindowPlacement object Q q)
    (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ R)
    {x y : Fin 15} {a b : Fin 13} (ex : object.graph.Adj (e x) (p a))
    (ey : object.graph.Adj (e y) (q b))
    (cubic : ∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3)
    {lo d₀ k : ℕ} (cert : certCfg lo x.1 a.1 y.1 b.1 d₀ k = true) :
    rungCount p q < k := by
  classical
  by_contra hk
  rw [not_lt] at hk
  let enc : Fin 13 × Fin 13 → ℕ := fun ij => 13 * ij.1.1 + ij.2.1
  have encInj : Function.Injective enc := by
    intro ij ij' h
    simp only [enc] at h
    have h1 := ij.2.2
    have h2 := ij'.2.2
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  let T := (rungSet p q).image enc
  have Tcard : T.card = rungCount p q := Finset.card_image_of_injective _ encInj
  obtain ⟨U, UT, Ucard⟩ := Finset.exists_subset_card_eq (s := T) (n := k) (by omega)
  have memT : ∀ r ∈ T, r < 169 ∧ ∃ (h1 : r / 13 < 13) (h2 : r % 13 < 13),
      object.graph.Adj (p ⟨r / 13, h1⟩) (q ⟨r % 13, h2⟩) := by
    intro r hr
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.1 hr
    have h1 := ij.1.2
    have h2 := ij.2.2
    refine ⟨by simp only [enc]; omega, by simp only [enc]; omega, by simp only [enc]; omega, ?_⟩
    have e1 : (⟨(13 * ij.1.1 + ij.2.1) / 13, by omega⟩ : Fin 13) = ij.1 :=
      Fin.ext (by simp only [Fin.val_mk]; omega)
    have e2 : (⟨(13 * ij.1.1 + ij.2.1) % 13, by omega⟩ : Fin 13) = ij.2 :=
      Fin.ext (by simp only [Fin.val_mk]; omega)
    simp only [enc]
    rw [e1, e2]
    exact mem_rungSet.1 hij
  let L := U.sort (· ≤ ·)
  have Lsorted : L.Pairwise (· < ·) := (Finset.sortedLT_sort U).pairwise
  have Llen : L.length = k := by simp [L, Ucard]
  have Lmem : ∀ r ∈ L, r ∈ T := fun r hr => UT ((Finset.mem_sort _).1 hr)
  obtain ⟨m, hm, hrej⟩ := noExtG_sound _ k [] 0 L cert Llen Lsorted
    (fun r hr => ⟨Nat.zero_le _, (memT r (Lmem r hr)).1⟩)
  obtain ⟨sub, subMem, hsub⟩ := tabRej_sound hrej
  have subT : ∀ r ∈ sub, r ∈ T := by
    intro r hr
    rcases List.mem_cons.1 (subMem r hr) with h | h
    · rw [h]; exact Lmem _ (List.getElem_mem _)
    · simp only [List.append_nil, List.mem_reverse] at h
      exact Lmem _ (List.mem_of_mem_take h)
  obtain ⟨w, hw⟩ := wRej_sound hsub
  -- the realisation of the configuration graph
  obtain ⟨F, hF1, hF2, hF3⟩ : ∃ F : ℕ → object.Vertex,
      (∀ (u : ℕ) (h : u < 15), F u = e ⟨u, h⟩) ∧
      (∀ (u : ℕ) (h1 : 15 ≤ u) (h2 : u < 28), F u = p ⟨u - 15, by omega⟩) ∧
      (∀ (u : ℕ) (h1 : 28 ≤ u) (h2 : u < 41), F u = q ⟨u - 28, by omega⟩) := by
    refine ⟨fun u => if h : u < 15 then e ⟨u, h⟩
      else if h2 : u < 28 then p ⟨u - 15, by omega⟩
      else if h3 : u - 28 < 13 then q ⟨u - 28, h3⟩ else q 0,
      fun u h => ?_, fun u h1 h2 => ?_, fun u h1 h2 => ?_⟩
    · simp only [dif_pos h]
    · simp only [dif_neg (show ¬ u < 15 by omega), dif_pos h2]
    · simp only [dif_neg (show ¬ u < 15 by omega), dif_neg (show ¬ u < 28 by omega),
        dif_pos (show u - 28 < 13 by omega)]
  have rung : ∀ i j, (i, j) ∈ toPairs sub → ∃ (h1 : i < 13) (h2 : j < 13),
      object.graph.Adj (p ⟨i, h1⟩) (q ⟨j, h2⟩) := by
    intro i j hij
    obtain ⟨r, hr, hrij⟩ := List.mem_map.1 hij
    obtain ⟨_, h1, h2, hadj⟩ := memT r (subT r hr)
    simp only [Prod.mk.injEq] at hrij
    obtain ⟨rfl, rfl⟩ := hrij
    exact ⟨h1, h2, hadj⟩
  have hFadj : ∀ u v, u < 41 → v < 41 → hpA x.1 a.1 y.1 b.1 (toPairs sub) u v = true →
      object.graph.Adj (F u) (F v) := by
    intro u v hu hv h
    unfold hpA at h
    by_cases hu15 : u < 15
    · rw [if_pos hu15] at h
      by_cases hv15 : v < 15
      · rw [if_pos hv15] at h
        rw [hF1 u hu15, hF1 v hv15, e.map_adj_iff]
        exact h
      · rw [if_neg hv15] at h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hF1 _ hu15, hF2 _ (by omega) (by omega)]
          convert ex using 2 <;> exact Fin.ext (by simp)
        · rw [hF1 _ hu15, hF3 _ (by omega) (by omega)]
          convert ey using 2 <;> exact Fin.ext (by simp)
    · rw [if_neg hu15] at h
      by_cases hv15 : v < 15
      · rw [if_pos hv15] at h
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        rw [object.graph.adj_comm]
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hF1 _ hv15, hF2 _ (by omega) (by omega)]
          convert ex using 2 <;> exact Fin.ext (by simp)
        · rw [hF1 _ hv15, hF3 _ (by omega) (by omega)]
          convert ey using 2 <;> exact Fin.ext (by simp)
      · rw [if_neg hv15] at h
        by_cases hu28 : u < 28
        · rw [if_pos hu28] at h
          by_cases hv28 : v < 28
          · rw [if_pos hv28] at h
            simp only [Bool.or_eq_true, beq_iff_eq] at h
            rw [hF2 u (by omega) hu28, hF2 v (by omega) hv28, hp.2.2]
            simp only
            omega
          · rw [if_neg hv28] at h
            obtain ⟨h1, h2, hadj⟩ := rung _ _ (List.contains_iff_mem.1 h)
            rw [hF2 u (by omega) hu28, hF3 v (by omega) hv]
            exact hadj
        · rw [if_neg hu28] at h
          by_cases hv28 : v < 28
          · rw [if_pos hv28] at h
            obtain ⟨h1, h2, hadj⟩ := rung _ _ (List.contains_iff_mem.1 h)
            rw [hF3 u (by omega) hu, hF2 v (by omega) hv28]
            exact hadj.symm
          · rw [if_neg hv28] at h
            simp only [Bool.or_eq_true, beq_iff_eq] at h
            rw [hF3 u (by omega) hu, hF3 v (by omega) hv, hq.2.2]
            simp only
            omega
  have outP : ∀ v, v ∈ R → v ∈ P → False := fun v hR hP => RP v hR hP
  have outQ : ∀ v, v ∈ R → v ∈ Q → False := fun v hR hQ => RQ v hR hQ
  have hinj : ∀ u v, u < 41 → v < 41 → F u = F v → u = v := by
    intro u v hu hv huv
    rcases (show u < 15 ∨ (15 ≤ u ∧ u < 28) ∨ 28 ≤ u by omega) with hu' | hu' | hu' <;>
      rcases (show v < 15 ∨ (15 ≤ v ∧ v < 28) ∨ 28 ≤ v by omega) with hv' | hv' | hv'
    · rw [hF1 u hu', hF1 v hv'] at huv
      simpa using e.injective huv
    · rw [hF1 u hu', hF2 v hv'.1 hv'.2] at huv
      exact (outP _ (inR _) (huv ▸ hp.2.1 _)).elim
    · rw [hF1 u hu', hF3 v hv' hv] at huv
      exact (outQ _ (inR _) (huv ▸ hq.2.1 _)).elim
    · rw [hF2 u hu'.1 hu'.2, hF1 v hv'] at huv
      exact (outP _ (inR _) (huv ▸ hp.2.1 _)).elim
    · rw [hF2 u hu'.1 hu'.2, hF2 v hv'.1 hv'.2] at huv
      have := congrArg Fin.val (hp.1 huv)
      simp only at this
      omega
    · rw [hF2 u hu'.1 hu'.2, hF3 v hv' hv] at huv
      exact (Finset.disjoint_left.1 PQ (hp.2.1 _) (huv ▸ hq.2.1 _)).elim
    · rw [hF3 u hu' hu, hF1 v hv'] at huv
      exact (outQ _ (inR _) (huv ▸ hq.2.1 _)).elim
    · rw [hF3 u hu' hu, hF2 v hv'.1 hv'.2] at huv
      exact (Finset.disjoint_left.1 PQ (hp.2.1 _) (huv ▸ hq.2.1 _)).elim
    · rw [hF3 u hu' hu, hF3 v hv' hv] at huv
      have := congrArg Fin.val (hq.1 huv)
      simp only at this
      omega
  cases w with
  | cyc l =>
    simp only [chkRWit, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hc, pow⟩ := hw
    obtain ⟨z, c, hcyc, hlen⟩ := cycle_of_chkCycle hFadj hinj hc
    exact avoid (hasCycle_of_walk lengthLaw c hcyc (hlen ▸ pow))
  | deg v l =>
    simp only [chkRWit, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
    obtain ⟨⟨⟨⟨⟨hv1, hv2⟩, hnd⟩, hlt⟩, hadj⟩, hlen⟩ := hw
    have sub4 : (l.map F).toFinset.card = l.length := by
      rw [List.toFinset_card_of_nodup, List.length_map]
      exact hnd.map_on fun a ha b hb hab => hinj a b (hlt a ha) (hlt b hb) hab
    have nbr : ∀ z ∈ (l.map F).toFinset, z ∈ object.graph.neighborSet (F v) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hz)
      exact hFadj v t hv2 (hlt t ht) (hadj t ht)
    have big : 4 ≤ object.degree (F v) := by
      rw [FiniteObject.degree_eq_ncard_neighborSet]
      haveI : Finite object.Vertex := by letI := object.vertices; infer_instance
      have fin : (object.graph.neighborSet (F v)).Finite := Set.toFinite _
      calc 4 ≤ (l.map F).toFinset.card := by omega
        _ = ((l.map F).toFinset : Set object.Vertex).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard (fun z hz => nbr z hz) fin
    by_cases hv28 : v < 28
    · rw [hF2 v hv1 hv28] at big
      have := (cubic ⟨v - 15, by omega⟩).1
      omega
    · rw [hF3 v (by omega) hv2] at big
      have := (cubic ⟨v - 28, by omega⟩).2
      omega

/-! ## Symmetries -/

/-- Reversing a placement keeps it a placement. -/
theorem placement_rev {S : Finset object.Vertex} {p : Fin 13 → object.Vertex}
    (hp : IsWindowPlacement object S p) : IsWindowPlacement object S (p ∘ Fin.rev) := by
  refine ⟨hp.1.comp Fin.rev_injective, fun i => hp.2.1 _, fun i j => ?_⟩
  simp only [Function.comp_apply, hp.2.2, Fin.val_rev]
  have := i.2
  have := j.2
  omega

theorem rungCount_rev_left (p q : Fin 13 → object.Vertex) :
    rungCount (p ∘ Fin.rev) q = rungCount p q := by
  classical
  unfold rungCount
  refine Finset.card_bij (fun ij _ => (Fin.rev ij.1, ij.2)) (fun ij h => ?_) (fun ij _ ij' _ h => ?_)
    (fun ij h => ⟨(Fin.rev ij.1, ij.2), ?_, ?_⟩)
  · have := (mem_rungSet (p := p ∘ Fin.rev) (q := q)).1 h
    exact mem_rungSet.2 this
  · simp only [Prod.mk.injEq, Fin.rev_inj] at h
    exact Prod.ext h.1 h.2
  · have := (mem_rungSet (p := p) (q := q)).1 h
    exact mem_rungSet.2 (by simpa using this)
  · simp

theorem rungCount_rev_right (p q : Fin 13 → object.Vertex) :
    rungCount p (q ∘ Fin.rev) = rungCount p q := by
  classical
  unfold rungCount
  refine Finset.card_bij (fun ij _ => (ij.1, Fin.rev ij.2)) (fun ij h => ?_) (fun ij _ ij' _ h => ?_)
    (fun ij h => ⟨(ij.1, Fin.rev ij.2), ?_, ?_⟩)
  · have := (mem_rungSet (p := p) (q := q ∘ Fin.rev)).1 h
    exact mem_rungSet.2 this
  · simp only [Prod.mk.injEq, Fin.rev_inj] at h
    exact Prod.ext h.1 h.2
  · have := (mem_rungSet (p := p) (q := q)).1 h
    exact mem_rungSet.2 (by simpa using this)
  · simp

theorem rungCount_swap (p q : Fin 13 → object.Vertex) :
    rungCount q p = rungCount p q := by
  classical
  unfold rungCount
  refine Finset.card_bij (fun ij _ => (ij.2, ij.1)) (fun ij h => ?_) (fun ij _ ij' _ h => ?_)
    (fun ij h => ⟨(ij.2, ij.1), ?_, ?_⟩)
  · have := (mem_rungSet (p := q) (q := p)).1 h
    exact mem_rungSet.2 this.symm
  · simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  · have := (mem_rungSet (p := p) (q := q)).1 h
    exact mem_rungSet.2 this.symm
  · simp

/-- The automorphism of `X15` swapping the exits `6` and `9` and fixing `4`. -/
def x15Sigma : Fin 15 → Fin 15 := fun i => ⟨[14, 5, 12, 13, 4, 1, 9, 8, 7, 6, 11, 10, 2, 3, 0].getD i.1 0,
  by have := i.2; interval_cases i.1 <;> simp⟩

theorem x15Sigma_ok : Function.Injective x15Sigma ∧
    ∀ i j, x15Graph.Adj (x15Sigma i) (x15Sigma j) ↔ x15Graph.Adj i j := by
  refine ⟨?_, ?_⟩
  · intro i j h
    revert i j
    decide
  · decide

/-- `σ` as a graph embedding. -/
def x15SigmaEmb : x15Graph ↪g x15Graph :=
  ⟨⟨x15Sigma, x15Sigma_ok.1⟩, fun {i j} => x15Sigma_ok.2 i j⟩

theorem x15Sigma_4 : x15Sigma ⟨4, by omega⟩ = ⟨4, by omega⟩ := by decide
theorem x15Sigma_6 : x15Sigma ⟨6, by omega⟩ = ⟨9, by omega⟩ := by decide
theorem x15Sigma_9 : x15Sigma ⟨9, by omega⟩ = ⟨6, by omega⟩ := by decide

/-! ## The rung bound -/

/-- Reduction to `a, b ≤ 6`. -/
theorem rungCount_le_of_small {P Q : Finset object.Vertex}
    {p q : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
    (hq : IsWindowPlacement object Q q)
    (cubic : ∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3)
    {e : x15Graph ↪g object.graph} {x y : Fin 15} {a b : Fin 13}
    (ex : object.graph.Adj (e x) (p a)) (ey : object.graph.Adj (e y) (q b)) (N : ℕ)
    (small : ∀ (p' q' : Fin 13 → object.Vertex), IsWindowPlacement object P p' →
      IsWindowPlacement object Q q' →
      (∀ k, object.degree (p' k) ≤ 3 ∧ object.degree (q' k) ≤ 3) →
      ∀ a' b' : Fin 13, a'.1 ≤ 6 → b'.1 ≤ 6 →
      object.graph.Adj (e x) (p' a') → object.graph.Adj (e y) (q' b') →
      rungCount p' q' ≤ N) :
    rungCount p q ≤ N := by
  have revCubic : ∀ (p' : Fin 13 → object.Vertex), (∀ k, object.degree (p' k) ≤ 3) →
      ∀ k, object.degree ((p' ∘ Fin.rev) k) ≤ 3 := fun p' h k => h _
  have fix : ∀ (p' : Fin 13 → object.Vertex) (a' : Fin 13), object.graph.Adj (e x) (p' a') →
      object.graph.Adj (e x) ((p' ∘ Fin.rev) (Fin.rev a')) := by
    intro p' a' h; simpa using h
  have fixy : ∀ (q' : Fin 13 → object.Vertex) (b' : Fin 13), object.graph.Adj (e y) (q' b') →
      object.graph.Adj (e y) ((q' ∘ Fin.rev) (Fin.rev b')) := by
    intro q' b' h; simpa using h
  by_cases ha : a.1 ≤ 6 <;> by_cases hb : b.1 ≤ 6
  · exact small p q hp hq cubic a b ha hb ex ey
  · rw [← rungCount_rev_right]
    exact small p (q ∘ Fin.rev) hp (placement_rev hq)
      (fun k => ⟨(cubic k).1, (cubic _).2⟩) a (Fin.rev b) ha (by simp; omega) ex (fixy q b ey)
  · rw [← rungCount_rev_left]
    exact small (p ∘ Fin.rev) q (placement_rev hp) hq
      (fun k => ⟨(cubic _).1, (cubic k).2⟩) (Fin.rev a) b (by simp; omega) hb (fix p a ex) ey
  · rw [← rungCount_rev_left, ← rungCount_rev_right]
    exact small (p ∘ Fin.rev) (q ∘ Fin.rev) (placement_rev hp) (placement_rev hq)
      (fun k => ⟨(cubic _).1, (cubic _).2⟩) (Fin.rev a) (Fin.rev b) (by simp; omega)
      (by simp; omega) (fix p a ex) (fixy q b ey)

/-- **Rung bound for a copy of `X15` between two windows.**  For disjoint `P`, `Q` placed by
`p`, `q` with all degrees at most 3, an induced copy `e` of `X15` in `R` (disjoint from `P`
and `Q`) with exits `x ≠ y` adjacent to `p a` and `q b`, and no cycle of power-of-two length:
at most `6` rungs if `4 ∈ {x, y}`, at most `8` otherwise. -/
theorem rungCount_le {LengthOK : ℕ → Prop}
    (avoid : ¬ HasCycleWithLength LengthOK object)
    (lengthLaw : ∀ length, LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    {R P Q : Finset object.Vertex} (RP : ∀ v ∈ R, v ∉ P) (RQ : ∀ v ∈ R, v ∉ Q)
    (PQ : Disjoint P Q)
    {p q : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
    (hq : IsWindowPlacement object Q q)
    (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ R)
    {x y : Fin 15} (hx : x.1 ∈ x15Exits) (hy : y.1 ∈ x15Exits) (hxy : x ≠ y)
    {a b : Fin 13} (ex : object.graph.Adj (e x) (p a)) (ey : object.graph.Adj (e y) (q b))
    (cubic : ∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3) :
    rungCount p q ≤ if x.1 = 4 ∨ y.1 = 4 then 6 else 8 := by
  -- the certified cores, for `a, b ≤ 6`
  have core46 : ∀ {P Q : Finset object.Vertex} (RP : ∀ v ∈ R, v ∉ P) (RQ : ∀ v ∈ R, v ∉ Q)
      (PQ : Disjoint P Q) {p q : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
      (hq : IsWindowPlacement object Q q) (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ R)
      (cubic : ∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3) (a b : Fin 13),
      object.graph.Adj (e ⟨4, by omega⟩) (p a) → object.graph.Adj (e ⟨6, by omega⟩) (q b) →
      rungCount p q ≤ 6 := by
    intro P Q RP RQ PQ p q hp hq e inR cubic a b ex ey
    refine rungCount_le_of_small hp hq cubic ex ey 6 ?_
    intro p' q' hp' hq' cubic' a' b' ha hb ex' ey'
    have := rungCount_lt_of_cert avoid lengthLaw RP RQ PQ hp' hq' e inR ex' ey' cubic'
      (cert46 a'.1 ha b'.1 hb)
    omega
  have core69 : ∀ {P Q : Finset object.Vertex} (RP : ∀ v ∈ R, v ∉ P) (RQ : ∀ v ∈ R, v ∉ Q)
      (PQ : Disjoint P Q) {p q : Fin 13 → object.Vertex} (hp : IsWindowPlacement object P p)
      (hq : IsWindowPlacement object Q q) (e : x15Graph ↪g object.graph) (inR : ∀ u, e u ∈ R)
      (cubic : ∀ k, object.degree (p k) ≤ 3 ∧ object.degree (q k) ≤ 3) (a b : Fin 13),
      object.graph.Adj (e ⟨6, by omega⟩) (p a) → object.graph.Adj (e ⟨9, by omega⟩) (q b) →
      rungCount p q ≤ 8 := by
    intro P Q RP RQ PQ p q hp hq e inR cubic a b ex ey
    refine rungCount_le_of_small hp hq cubic ex ey 8 ?_
    intro p' q' hp' hq' cubic' a' b' ha hb ex' ey'
    rcases le_total a'.1 b'.1 with hab | hab
    · have := rungCount_lt_of_cert avoid lengthLaw RP RQ PQ hp' hq' e inR ex' ey' cubic'
        (cert69 a'.1 b'.1 hab hb)
      omega
    · -- exchange `P` and `Q`, then apply `σ`
      have ex'' : object.graph.Adj ((e.comp x15SigmaEmb) ⟨6, by omega⟩) (q' b') := by
        show object.graph.Adj (e (x15Sigma ⟨6, by omega⟩)) (q' b')
        rw [x15Sigma_6]; exact ey'
      have ey'' : object.graph.Adj ((e.comp x15SigmaEmb) ⟨9, by omega⟩) (p' a') := by
        show object.graph.Adj (e (x15Sigma ⟨9, by omega⟩)) (p' a')
        rw [x15Sigma_9]; exact ex'
      have := rungCount_lt_of_cert avoid lengthLaw RQ RP PQ.symm hq' hp' (e.comp x15SigmaEmb)
        (fun u => inR _) ex'' ey'' (fun k => ⟨(cubic' k).2, (cubic' k).1⟩)
        (cert69 b'.1 a'.1 hab ha)
      rw [rungCount_swap] at this
      omega
  have eσ4 : (e.comp x15SigmaEmb) ⟨4, by omega⟩ = e ⟨4, by omega⟩ := by
    show e (x15Sigma ⟨4, by omega⟩) = _
    rw [x15Sigma_4]
  have eσ6 : (e.comp x15SigmaEmb) ⟨6, by omega⟩ = e ⟨9, by omega⟩ := by
    show e (x15Sigma ⟨6, by omega⟩) = _
    rw [x15Sigma_6]
  have eσ9 : (e.comp x15SigmaEmb) ⟨9, by omega⟩ = e ⟨6, by omega⟩ := by
    show e (x15Sigma ⟨9, by omega⟩) = _
    rw [x15Sigma_9]
  have inRσ : ∀ u, (e.comp x15SigmaEmb) u ∈ R := fun u => inR _
  have cubicS : ∀ k, object.degree (q k) ≤ 3 ∧ object.degree (p k) ≤ 3 :=
    fun k => ⟨(cubic k).2, (cubic k).1⟩
  simp only [x15Exits, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  obtain ⟨x, hxl⟩ := x
  obtain ⟨y, hyl⟩ := y
  simp only at hx hy
  have hxy' : x ≠ y := fun h => hxy (Fin.ext h)
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    simp only [true_or, or_true, if_true, if_false, show (6 : ℕ) ≠ 4 by decide,
      show (9 : ℕ) ≠ 4 by decide, or_self] at hxy' ⊢
  · exact absurd rfl hxy'
  · exact core46 RP RQ PQ hp hq e inR cubic a b ex ey
  · exact core46 RP RQ PQ hp hq (e.comp x15SigmaEmb) inRσ cubic a b (eσ4 ▸ ex) (eσ6 ▸ ey)
  · rw [← rungCount_swap]
    exact core46 RQ RP PQ.symm hq hp e inR cubicS b a ey ex
  · exact absurd rfl hxy'
  · exact core69 RP RQ PQ hp hq e inR cubic a b ex ey
  · rw [← rungCount_swap]
    exact core46 RQ RP PQ.symm hq hp (e.comp x15SigmaEmb) inRσ cubicS b a (eσ4 ▸ ey)
      (eσ6 ▸ ex)
  · exact core69 RP RQ PQ hp hq (e.comp x15SigmaEmb) inRσ cubic a b (eσ6 ▸ ex) (eσ9 ▸ ey)
  · exact absurd rfl hxy'

end Hypostructure.Graph.WindowExchange
