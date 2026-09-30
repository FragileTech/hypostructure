import Hypostructure.Graph.DensityCert.Blocks
import Hypostructure.Graph.DensityCert.Transport

/-!
# Density certificate: the tree DP over blocks

Given a list `L` of concrete graphs that covers every 2-connected admissible
`G[W]` (`hcl`) and satisfies the block profile inequalities `DPCert L`:

* `rooted_bound`: a connected admissible `G[W]` rooted at `r` of degree `≤ 2`
  has `dIn G W ≤ fTab (lamIn G W r)`.  Strong induction on `|W|`: split `W`
  into the block of `r` and the hanging pieces; the pieces are bounded by
  induction, the block by `DPCert` transported along the embedding onto it.
* `density_le_in`: a connected admissible `G[W]` has `dIn G W ≤ 0` or is a copy
  of `X15`.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

/-! ## Finite facts about `fTab` -/

theorem fTab_of_ge {a : ℕ} (h : 11 ≤ a) : fTab a = 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rfl

theorem fTab_le_three (a : ℕ) : fTab a ≤ 3 := by
  rcases le_or_gt 11 a with h | h
  · rw [fTab_of_ge h]
  · interval_cases a <;> decide

theorem fTab_mono {a b : ℕ} (h : a ≤ b) : fTab a ≤ fTab b := by
  rcases le_or_gt 11 b with hb | hb
  · rw [fTab_of_ge hb]; exact fTab_le_three a
  · have key : ∀ a < 11, ∀ b < 11, a ≤ b → fTab a ≤ fTab b := by decide
    exact key a (by omega) b hb h

theorem fTab_ge (a : ℕ) : -11 ≤ fTab a := fTab_mono (Nat.zero_le a)

theorem fTab_small {t : ℕ} (h : t ≤ 4) : fTab t + 8 ≤ 0 := by
  interval_cases t <;> decide

/-- One hanging piece at a singleton block. -/
theorem fTab_step1 (t : ℕ) (h : t + 1 ≤ 12) : -11 + (fTab t + 8) ≤ fTab (t + 1) := by
  have key : ∀ t < 12, -11 + (fTab t + 8) ≤ fTab (t + 1) := by decide
  exact key t (by omega)

/-- Two hanging pieces at a singleton block. -/
theorem fTab_step2 (t t' : ℕ) (h : t + 1 + t' ≤ 12) :
    -11 + ((fTab t + 8) + (fTab t' + 8)) ≤ fTab (max t t' + 1) := by
  have key : ∀ t < 12, ∀ t' < 12, t + 1 + t' ≤ 12 →
      -11 + ((fTab t + 8) + (fTab t' + 8)) ≤ fTab (max t t' + 1) := by decide
  exact key t (by omega) t' (by omega) h

/-- The unrooted split across a bridge. -/
theorem fTab_pair (a b : ℕ) (h : a + b ≤ 12) : fTab a + fTab b + 8 ≤ 0 := by
  have key : ∀ a < 13, ∀ b < 13, a + b ≤ 12 → fTab a + fTab b + 8 ≤ 0 := by decide
  exact key a (by omega) b (by omega) h

section DP

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem dIn_singleton (G : SimpleGraph V) (r : V) : dIn G {r} = -11 := by
  simp [dIn, Finset.filter_singleton]

omit [Fintype V] [DecidableEq V] in
theorem degIn_singleton_self (G : SimpleGraph V) (r : V) : degIn G {r} r = 0 := by
  simp [degIn, Finset.filter_singleton]

omit [Fintype V] [DecidableEq V] in
/-- `DPCert` of a member `M` of `L`, transported along an embedding of `M.graph`
onto `B`. -/
theorem dp_onto (G : SimpleGraph V) {L : List CG} (hdp : DPCert L) {M : CG} (hM : M ∈ L)
    {B : Finset V} (e : M.graph ↪g G) (hW : ∀ v, v ∈ B ↔ ∃ i, e i = v) :
    (dIn G B ≤ 0 ∨ Nonempty (M.graph ≃g CG.x15.graph)) ∧
    (∀ r ∈ B, degIn G B r ≤ 2 → dIn G B ≤ fTab (lamIn G B r)) ∧
    (∀ r ∈ B, ∀ p ∈ B, p ≠ r → degIn G B r ≤ 2 → degIn G B p ≤ 2 → ∀ t, 5 ≤ t → t ≤ 12 →
      lamIn G B p + t ≤ 12 → max (lamIn G B r) (LIn G B r p + t) ≤ 12 →
      dIn G B + fTab t + 8 ≤ fTab (max (lamIn G B r) (LIn G B r p + t))) ∧
    (∀ r ∈ B, ∀ p ∈ B, ∀ q ∈ B, p ≠ r → q ≠ r → p ≠ q →
      degIn G B r ≤ 2 → degIn G B p ≤ 2 → degIn G B q ≤ 2 →
      ∀ a b, 5 ≤ a → a ≤ 12 → 5 ≤ b → b ≤ 12 →
      lamIn G B p + a ≤ 12 → lamIn G B q + b ≤ 12 → a + LIn G B p q + b ≤ 12 →
      max (lamIn G B r) (max (LIn G B r p + a) (LIn G B r q + b)) ≤ 12 →
      dIn G B + fTab a + fTab b + 16 ≤
        fTab (max (lamIn G B r) (max (LIn G B r p + a) (LIn G B r q + b)))) ∧
    (∀ r ∈ B, ∀ p ∈ B, ∀ q ∈ B, ∀ s ∈ B, p ≠ r → q ≠ r → s ≠ r → p ≠ q → p ≠ s → q ≠ s →
      degIn G B p ≤ 2 → degIn G B q ≤ 2 → degIn G B s ≤ 2 →
      ¬ (LIn G B p q ≤ 2 ∧ LIn G B p s ≤ 2 ∧ LIn G B q s ≤ 2)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hdp M hM
  have ne : ∀ {i j : Fin M.n}, e i ≠ e j → i ≠ j := fun h hij => h (by rw [hij])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← dIn_onto e hW]; exact h1
  · intro r hr
    obtain ⟨i, rfl⟩ := (hW r).1 hr
    rw [← degIn_onto e hW, ← dIn_onto e hW, ← lamIn_onto e hW]
    exact h2 i
  · intro r hr p hp hpr
    obtain ⟨i, rfl⟩ := (hW r).1 hr
    obtain ⟨j, rfl⟩ := (hW p).1 hp
    simp only [← degIn_onto e hW, ← dIn_onto e hW, ← lamIn_onto e hW, ← LIn_onto e hW]
    exact h3 i j (ne hpr)
  · intro r hr p hp q hq hpr hqr hpq
    obtain ⟨i, rfl⟩ := (hW r).1 hr
    obtain ⟨j, rfl⟩ := (hW p).1 hp
    obtain ⟨k, rfl⟩ := (hW q).1 hq
    simp only [← degIn_onto e hW, ← dIn_onto e hW, ← lamIn_onto e hW, ← LIn_onto e hW]
    exact h4 i j k (ne hpr) (ne hqr) (ne hpq)
  · intro r hr p hp q hq s hs hpr hqr hsr hpq hps hqs
    obtain ⟨i, rfl⟩ := (hW r).1 hr
    obtain ⟨j, rfl⟩ := (hW p).1 hp
    obtain ⟨k, rfl⟩ := (hW q).1 hq
    obtain ⟨l, rfl⟩ := (hW s).1 hs
    simp only [← degIn_onto e hW, ← LIn_onto e hW]
    exact h5 i j k l (ne hpr) (ne hqr) (ne hsr) (ne hpq) (ne hps) (ne hqs)

/-- Rooted step, singleton block: all pieces hang at the root. -/
theorem rooted_singleton_case (G : SimpleGraph V) (W : Finset V) (hc : ConnIn G W)
    (ha : AdmIn G W) (r : V) (hr : r ∈ W) (hdeg : degIn G W r ≤ 2)
    (hB : (blk G W r).card < 2)
    (hkid : ∀ C ∈ kids G W r, dIn G C ≤ fTab (lamIn G C (att G W r C))) :
    dIn G W ≤ fTab (lamIn G W r) := by
  have hB1 := blk_eq_singleton G W r hc ha hr hB
  have hrB := mem_blk_self G W r hc ha hr
  have hd := dIn_blk_kids G W r hc ha hr
  have hdk := degIn_blk_kids G W r hc ha hr r hrB
  have hbr := kids_bridge G W r hc ha hr
  have hP2 := lam_att_add_L_add_lam_att_le G W r hc ha hr
  have hP3 := (lam_root_ge G W r hc ha hr).2
  have hW12 := lamIn_le_twelve G W ha r
  rw [hB1, dIn_singleton] at hd
  have hport : ∀ C ∈ kids G W r, port G W r C = r := by
    intro C hC
    have := (hbr C hC).1
    rw [hB1] at this
    exact mem_singleton.1 this
  have hL1 : LIn G {r} r r = 1 := (LIn_self G {r} r (mem_singleton_self r)).1
  have hroot : ∀ C ∈ kids G W r, lamIn G C (att G W r C) + 1 ≤ lamIn G W r := by
    intro C hC
    have := hP3 C hC
    rw [hB1, hport C hC, hL1] at this
    omega
  have hcard : (kids G W r).card ≤ 2 := by
    rw [hB1, degIn_singleton_self, filter_true_of_mem hport] at hdk
    omega
  rw [hd]
  interval_cases hk : (kids G W r).card
  · rw [card_eq_zero.1 hk, sum_empty]
    have := fTab_ge (lamIn G W r)
    omega
  · obtain ⟨C, hCeq⟩ := card_eq_one.1 hk
    have hC : C ∈ kids G W r := by rw [hCeq]; exact mem_singleton_self C
    rw [hCeq, sum_singleton]
    have h1 := hkid C hC
    have h2 := hroot C hC
    have h3 := fTab_step1 _ (h2.trans hW12)
    have h4 := fTab_mono h2
    linarith
  · obtain ⟨C, C', hne, hCeq⟩ := card_eq_two.1 hk
    have hC : C ∈ kids G W r := by rw [hCeq]; simp
    have hC' : C' ∈ kids G W r := by rw [hCeq]; simp
    rw [hCeq, sum_pair hne]
    have h1 := hkid C hC
    have h1' := hkid C' hC'
    have h2 := hroot C hC
    have h2' := hroot C' hC'
    have h5 := hP2 C hC C' hC' hne
    rw [hB1, hport C hC, hport C' hC', hL1] at h5
    have h3 := fTab_step2 _ _ h5
    have h4 := fTab_mono (show max (lamIn G C (att G W r C)) (lamIn G C' (att G W r C')) + 1 ≤
      lamIn G W r by omega)
    linarith

/-- Rooted step, 2-connected block. -/
theorem rooted_block_case (G : SimpleGraph V) (L : List CG)
    (hcl : ∀ W : Finset V, AdmIn G W → TwoConnIn G W → ∃ M ∈ L, EmbOnto M.graph G W)
    (hdp : DPCert L) (W : Finset V) (hc : ConnIn G W)
    (ha : AdmIn G W) (r : V) (hr : r ∈ W) (hdeg : degIn G W r ≤ 2)
    (hB : 2 ≤ (blk G W r).card)
    (hkid : ∀ C ∈ kids G W r, dIn G C ≤ fTab (lamIn G C (att G W r C))) :
    dIn G W ≤ fTab (lamIn G W r) := by
  obtain ⟨hB2, hmin⟩ := blk_twoConn G W r hc ha hr hB
  have hBa := blk_adm G W r hc ha hr
  obtain ⟨M, hM, e, hW⟩ := hcl _ hBa hB2
  obtain ⟨-, D2, D3, D4, D5⟩ := dp_onto G hdp hM e hW
  have hrB := mem_blk_self G W r hc ha hr
  have hdk := degIn_blk_kids G W r hc ha hr
  have hbr := kids_bridge G W r hc ha hr
  have hkf := kids_facts G W r hc ha hr
  have hd := dIn_blk_kids G W r hc ha hr
  have hP1 := lam_port_add_lam_att_le G W r hc ha hr
  have hP2 := lam_att_add_L_add_lam_att_le G W r hc ha hr
  have hP3 := lam_root_ge G W r hc ha hr
  have hW12 := lamIn_le_twelve G W ha r
  have hsub := blk_subset G W r
  -- the root carries no piece
  have hrk : ∀ C ∈ kids G W r, port G W r C ≠ r := by
    intro C hC hpc
    have h1 := hdk r hrB
    have h2 := hmin r hrB
    have h3 : 1 ≤ ((kids G W r).filter fun C => port G W r C = r).card :=
      card_pos.2 ⟨C, mem_filter.2 ⟨hC, hpc⟩⟩
    omega
  have hdrB : degIn G (blk G W r) r ≤ 2 := by
    have := hdk r hrB
    omega
  -- every port has block degree `≤ 2` and carries exactly one piece
  have hportdeg : ∀ C ∈ kids G W r, degIn G (blk G W r) (port G W r C) ≤ 2 := by
    intro C hC
    have hp := (hbr C hC).1
    have h1 := hdk _ hp
    have h3 := ha.1 _ (hsub hp)
    have h4 : 1 ≤ ((kids G W r).filter fun C' => port G W r C' = port G W r C).card :=
      card_pos.2 ⟨C, mem_filter.2 ⟨hC, rfl⟩⟩
    omega
  have hinj : ∀ C ∈ kids G W r, ∀ C' ∈ kids G W r, C ≠ C' →
      port G W r C ≠ port G W r C' := by
    intro C hC C' hC' hne heq
    have hp := (hbr C hC).1
    have h1 := hdk _ hp
    have h2 := hmin _ hp
    have h3 := ha.1 _ (hsub hp)
    have h4 : 2 ≤ ((kids G W r).filter fun C'' => port G W r C'' = port G W r C).card := by
      have hs : ({C, C'} : Finset (Finset V)) ⊆
          (kids G W r).filter fun C'' => port G W r C'' = port G W r C := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_filter.2 ⟨hC, rfl⟩
        · rw [mem_singleton.1 hx]; exact mem_filter.2 ⟨hC', heq.symm⟩
      have := card_le_card hs
      rwa [card_pair hne] at this
    omega
  have ht12 : ∀ C ∈ kids G W r, lamIn G C (att G W r C) ≤ 12 :=
    fun C hC => lamIn_le_twelve G C (hkf C hC).1 _
  -- dominance: only pieces of value `≥ 5` matter
  obtain ⟨S, hS⟩ : ∃ S : Finset (Finset V),
      S = (kids G W r).filter fun C => 5 ≤ lamIn G C (att G W r C) := ⟨_, rfl⟩
  have hSm : ∀ C, C ∈ S ↔ C ∈ kids G W r ∧ 5 ≤ lamIn G C (att G W r C) := by
    intro C; rw [hS, mem_filter]
  have hsum : ∑ C ∈ kids G W r, (dIn G C + 8) ≤
      ∑ C ∈ S, (fTab (lamIn G C (att G W r C)) + 8) := by
    rw [← sum_filter_add_sum_filter_not (kids G W r)
      (fun C => 5 ≤ lamIn G C (att G W r C)), ← hS]
    have h1 : ∑ C ∈ S, (dIn G C + 8) ≤ ∑ C ∈ S, (fTab (lamIn G C (att G W r C)) + 8) :=
      sum_le_sum fun C hC => by
        have := hkid C ((hSm C).1 hC).1
        linarith
    have h2 : ∑ C ∈ (kids G W r).filter (fun C => ¬ 5 ≤ lamIn G C (att G W r C)),
        (dIn G C + 8) ≤ 0 :=
      sum_nonpos fun C hC => by
        have hC' := mem_filter.1 hC
        have h3 := hkid C hC'.1
        have h4 := fTab_small (t := lamIn G C (att G W r C)) (by omega)
        linarith
    linarith
  -- at most two pieces of value `≥ 5`
  have hS2 : S.card ≤ 2 := by
    by_contra hlt
    obtain ⟨a, b, c, ha', hb', hc', hab, hac, hbc⟩ := two_lt_card_iff.1 (not_le.1 hlt)
    obtain ⟨haK, ha5⟩ := (hSm a).1 ha'
    obtain ⟨hbK, hb5⟩ := (hSm b).1 hb'
    obtain ⟨hcK, hc5⟩ := (hSm c).1 hc'
    have hab' := hP2 a haK b hbK hab
    have hac' := hP2 a haK c hcK hac
    have hbc' := hP2 b hbK c hcK hbc
    exact D5 r hrB _ (hbr a haK).1 _ (hbr b hbK).1 _ (hbr c hcK).1 (hrk a haK) (hrk b hbK)
      (hrk c hcK) (hinj a haK b hbK hab) (hinj a haK c hcK hac) (hinj b hbK c hcK hbc)
      (hportdeg a haK) (hportdeg b hbK) (hportdeg c hcK) ⟨by omega, by omega, by omega⟩
  rw [hd]
  interval_cases hk : S.card
  · rw [card_eq_zero.1 hk, sum_empty] at hsum
    have h1 := D2 r hrB hdrB
    have h2 := fTab_mono hP3.1
    linarith
  · obtain ⟨C, hCeq⟩ := card_eq_one.1 hk
    obtain ⟨hC, hC5⟩ := (hSm C).1 (by rw [hCeq]; exact mem_singleton_self C)
    rw [hCeq, sum_singleton] at hsum
    have hmax : max (lamIn G (blk G W r) r)
        (LIn G (blk G W r) r (port G W r C) + lamIn G C (att G W r C)) ≤ lamIn G W r :=
      max_le hP3.1 (hP3.2 C hC)
    have h1 := D3 r hrB _ (hbr C hC).1 (hrk C hC) hdrB (hportdeg C hC) _ hC5 (ht12 C hC)
      (hP1 C hC) (hmax.trans hW12)
    have h2 := fTab_mono hmax
    linarith
  · obtain ⟨C, C', hne, hCeq⟩ := card_eq_two.1 hk
    obtain ⟨hC, hC5⟩ := (hSm C).1 (by rw [hCeq]; simp)
    obtain ⟨hC', hC5'⟩ := (hSm C').1 (by rw [hCeq]; simp)
    rw [hCeq, sum_pair hne] at hsum
    have hmax : max (lamIn G (blk G W r) r)
        (max (LIn G (blk G W r) r (port G W r C) + lamIn G C (att G W r C))
          (LIn G (blk G W r) r (port G W r C') + lamIn G C' (att G W r C'))) ≤
          lamIn G W r :=
      max_le hP3.1 (max_le (hP3.2 C hC) (hP3.2 C' hC'))
    have h1 := D4 r hrB _ (hbr C hC).1 _ (hbr C' hC').1 (hrk C hC) (hrk C' hC')
      (hinj C hC C' hC' hne) hdrB (hportdeg C hC) (hportdeg C' hC') _ _ hC5 (ht12 C hC)
      hC5' (ht12 C' hC') (hP1 C hC) (hP1 C' hC') (hP2 C hC C' hC' hne) (hmax.trans hW12)
    have h2 := fTab_mono hmax
    linarith

/-- The rooted density bound. -/
theorem rooted_bound (G : SimpleGraph V) (L : List CG)
    (hcl : ∀ W : Finset V, AdmIn G W → TwoConnIn G W → ∃ M ∈ L, EmbOnto M.graph G W)
    (hdp : DPCert L) :
    ∀ W : Finset V, ConnIn G W → AdmIn G W → ∀ r ∈ W, degIn G W r ≤ 2 →
      dIn G W ≤ fTab (lamIn G W r) := by
  have key : ∀ n, ∀ W : Finset V, W.card = n → ConnIn G W → AdmIn G W → ∀ r ∈ W,
      degIn G W r ≤ 2 → dIn G W ≤ fTab (lamIn G W r) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W hn hc ha r hr hdeg
      have hkid : ∀ C ∈ kids G W r, dIn G C ≤ fTab (lamIn G C (att G W r C)) := by
        intro C hC
        obtain ⟨hCa, hCc, hlt, hdC⟩ := kids_facts G W r hc ha hr C hC
        exact ih C.card (hn ▸ hlt) C rfl hCc hCa _ (kids_bridge G W r hc ha hr C hC).2.1 hdC
      rcases lt_or_ge (blk G W r).card 2 with h | h
      · exact rooted_singleton_case G W hc ha r hr hdeg h hkid
      · exact rooted_block_case G L hcl hdp W hc ha r hr hdeg h hkid
  intro W
  exact key _ W rfl

/-- The unrooted density bound: `8 e ≤ 11 n` or a copy of `X15`. -/
theorem density_le_in (G : SimpleGraph V) (L : List CG)
    (hcl : ∀ W : Finset V, AdmIn G W → TwoConnIn G W → ∃ M ∈ L, EmbOnto M.graph G W)
    (hdp : DPCert L) :
    ∀ W : Finset V, ConnIn G W → AdmIn G W → dIn G W ≤ 0 ∨ EmbOnto CG.x15.graph G W := by
  intro W hc ha
  obtain ⟨r, hr⟩ := hc.1
  by_cases hk : kids G W r = ∅
  · have hBW := (kids_empty_iff G W r hc ha hr).1 hk
    rcases lt_or_ge (blk G W r).card 2 with h | h
    · left
      rw [← hBW, blk_eq_singleton G W r hc ha hr h, dIn_singleton]
      norm_num
    · have h2 := (blk_twoConn G W r hc ha hr h).1
      rw [hBW] at h2
      obtain ⟨M, hM, e, hW⟩ := hcl W ha h2
      rcases (dp_onto G hdp hM e hW).1 with h1 | hf
      · exact Or.inl h1
      · obtain ⟨f⟩ := hf
        exact Or.inr (EmbOnto.of_iso' f ⟨e, hW⟩)
  · left
    obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.2 hk
    obtain ⟨hRc, hRa, -, hpR, hpdeg, hsplit, hsum⟩ := split_at_kid G W r hc ha hr C hC
    obtain ⟨hCa, hCc, -, hdC⟩ := kids_facts G W r hc ha hr C hC
    have h1 := rooted_bound G L hcl hdp (W \ C) hRc hRa _ hpR hpdeg
    have h2 := rooted_bound G L hcl hdp C hCc hCa _ (kids_bridge G W r hc ha hr C hC).2.1 hdC
    have h3 := fTab_pair _ _ hsum
    rw [hsplit]
    linarith

end DP

end Hypostructure.Graph.DensityCert
