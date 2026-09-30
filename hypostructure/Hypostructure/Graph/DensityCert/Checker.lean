import Hypostructure.Graph.DensityCert.Basic

/-!
# Density certificate: verified Boolean checkers

Small Boolean checkers over concrete graphs `CG`, each with a soundness lemma
relating it to the propositions of `Basic.lean`:

* `indB`   — a list of naturals is an induced path (`IsIndPath`, via `lift`);
* `pathB`  — a list is a simple path of `M` (used to build cycles through an ear);
* `isoB`   — an array is an isomorphism between two concrete graphs;
* `degB`, `dB` — exact degree and `8e − 11n` of a concrete graph.

The ear-level checker `closureOK` and the profile checker `dpOK` combine them;
their soundness theorems (`closureOK_sound`, `dpOK_sound`) give the bodies of
`ClosureCert` and `DPCert` for a single member.  Every witness they check is
supplied by an arbitrary (untrusted) function, so the soundness theorems hold
for all witness producers.
-/

namespace Hypostructure.Graph.DensityCert

open Finset

namespace CG

theorem A_true_ne {M : CG} {i j : ℕ} (h : M.A i j = true) : i ≠ j := by
  rintro rfl; simp [A_irrefl] at h

/-- Inside the old vertex set, the ear extension has the adjacency of `M`. -/
theorem ear_A_lt (M : CG) (m x y : ℕ) (z : Option ℕ) {i j : ℕ} (hi : i < M.n) (hj : j < M.n) :
    (M.ear m x y z).A i j = M.A i j := by
  have hs := M.A_symm j i
  simp only [A, ear, hi, hj, if_true] at hs ⊢
  rw [hs]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem ear_A_x (M : CG) (m x y : ℕ) (z : Option ℕ) (hx : x < M.n) :
    (M.ear m x y z).A x M.n = true := by
  simp [A, ear, hx, Nat.ne_of_lt hx]

theorem ear_A_y (M : CG) (m x y : ℕ) (z : Option ℕ) (hm : 1 ≤ m) (hy : y < M.n) :
    (M.ear m x y z).A y (M.n + m - 1) = true := by
  have h1 : y ≠ M.n + m - 1 := by omega
  have h2 : ¬ M.n + m - 1 < M.n := by omega
  have h3 : M.n + m - 1 - M.n + 1 = m := by omega
  simp [A, ear, hy, h1, h2, h3]

theorem ear_A_z (M : CG) (x y w : ℕ) (hw : w < M.n) :
    (M.ear 1 x y (some w)).A w M.n = true := by
  simp [A, ear, hw, Nat.ne_of_lt hw]

theorem ear_A_step (M : CG) (m x y : ℕ) (z : Option ℕ) (k : ℕ) :
    (M.ear m x y z).A (M.n + k) (M.n + k + 1) = true := by
  have h1 : ¬ M.n + k < M.n := by omega
  have h2 : ¬ M.n + k + 1 < M.n := by omega
  simp [A, ear, h1, h2]

/-- For `m = 1` the ear extension only depends on the attachment set. -/
theorem ear1_graph_congr (M : CG) {x y x' y' : ℕ} {z z' : Option ℕ}
    (h : ∀ i, (i = x ∨ i = y ∨ z = some i) ↔ (i = x' ∨ i = y' ∨ z' = some i)) :
    (M.ear 1 x y z).graph = (M.ear 1 x' y' z').graph := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [graph_adj]
  simp only [ear] at hi hj
  have key : ∀ a b : ℕ, a < M.n + 1 → b < M.n + 1 →
      (M.ear 1 x y z).adj a b = (M.ear 1 x' y' z').adj a b := by
    intro a b ha hb
    simp only [ear]
    by_cases ha' : a < M.n
    · by_cases hb' : b < M.n
      · simp [ha', hb']
      · have hbn : b = M.n := by omega
        subst hbn
        simp only [ha', hb', if_true, if_false]
        rw [Bool.eq_iff_iff]
        simpa [or_assoc] using h a
    · simp [ha']
  simp only [A]
  rw [key _ _ hi hj, key _ _ hj hi]

end CG

namespace CertCheck

open CG

/-! ### Lifting lists of naturals to vertex lists -/

/-- A list of naturals below `n`, as a list of `Fin n`. -/
def lift (n : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < n) : List (Fin n) := l.pmap Fin.mk h

@[simp] theorem lift_length (n : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < n) :
    (lift n l h).length = l.length := List.length_pmap

theorem lift_getElem (n : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < n) (i : ℕ)
    (hi : i < (lift n l h).length) :
    (lift n l h)[i] = ⟨l[i]'(by simpa using hi), h _ (List.getElem_mem _)⟩ :=
  List.getElem_pmap _ _ _

theorem lift_nodup (n : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < n) (hl : l.Nodup) :
    (lift n l h).Nodup :=
  hl.pmap (fun a _ b _ e => by simpa using congrArg Fin.val e)

theorem lift_getElem? (n : ℕ) (l : List ℕ) (h : ∀ a ∈ l, a < n) (i v : ℕ)
    (hv : l[i]? = some v) : ∃ hvn : v < n, (lift n l h)[i]? = some ⟨v, hvn⟩ := by
  have hi : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hv; cases hv
  rw [List.getElem?_eq_getElem hi] at hv
  cases hv
  refine ⟨h _ (List.getElem_mem hi), ?_⟩
  rw [List.getElem?_eq_getElem (by simpa using hi), lift_getElem]

/-! ### Induced paths -/

/-- `l` is an induced path of `M`, stated on naturals. -/
def IndN (M : CG) (l : List ℕ) : Prop :=
  (∀ a ∈ l, a < M.n) ∧ l.Nodup ∧
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), (M.A l[i] l[j] = true ↔ (i + 1 = j ∨ j + 1 = i))

theorem IndN.isIndPath {M : CG} {l : List ℕ} (h : IndN M l) :
    IsIndPath M.graph (lift M.n l h.1) := by
  refine ⟨lift_nodup _ _ _ h.2.1, fun i j hi hj => ?_⟩
  simp only [lift_getElem, graph_adj]
  exact h.2.2 i j _ _

/-- Boolean check of `IndN`. -/
def indB (M : CG) (l : List ℕ) : Bool :=
  l.all (fun a => decide (a < M.n)) && decide l.Nodup &&
    (let a := l.toArray
     (List.range a.size).all fun j => (List.range j).all fun i =>
       M.A (a.getD i 0) (a.getD j 0) == (i + 1 == j))

theorem indB_sound {M : CG} {l : List ℕ} (h : indB M l = true) : IndN M l := by
  simp only [indB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.size_toArray, beq_iff_eq] at h
  obtain ⟨⟨hlt, hnd⟩, hA⟩ := h
  refine ⟨hlt, hnd, fun i j hi hj => ?_⟩
  have key : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j →
      (M.A l[i] l[j] = true ↔ i + 1 = j) := by
    intro i j hi hj hij
    have := hA j hj i hij
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some] at this
    rw [this]; simp
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [key i j hi hj hij]; omega
  · simp [A_irrefl]
  · rw [A_symm, key j i hj hi hij]; omega

theorem le_lamIn {M : CG} {l : List ℕ} (h : IndN M l) {v : ℕ} (hv : l[0]? = some v) (hvn : v < M.n) :
    l.length ≤ lamIn M.graph univ ⟨v, hvn⟩ := by
  classical
  unfold lamIn
  have hc : l.length ≤ (univ : Finset (Fin M.n)).card := by
    have := (lift_nodup _ _ h.1 h.2.1).length_le_card
    simpa using this
  refine Nat.le_findGreatest hc ⟨lift M.n l h.1, h.isIndPath, fun _ _ => mem_univ _, ?_, by simp⟩
  obtain ⟨_, e⟩ := lift_getElem? M.n l h.1 0 v hv
  rw [List.head?_eq_getElem?, e]

theorem le_LIn {M : CG} {l : List ℕ} (h : IndN M l) {u v : ℕ} (hu : l[0]? = some u)
    (hv : l[l.length - 1]? = some v) (hun : u < M.n) (hvn : v < M.n) :
    l.length ≤ LIn M.graph univ ⟨u, hun⟩ ⟨v, hvn⟩ := by
  classical
  unfold LIn
  have hc : l.length ≤ (univ : Finset (Fin M.n)).card := by
    have := (lift_nodup _ _ h.1 h.2.1).length_le_card
    simpa using this
  refine Nat.le_findGreatest hc ⟨lift M.n l h.1, h.isIndPath, fun _ _ => mem_univ _, ?_, ?_, by simp⟩
  · obtain ⟨_, e⟩ := lift_getElem? M.n l h.1 0 u hu
    rw [List.head?_eq_getElem?, e]
  · obtain ⟨_, e⟩ := lift_getElem? M.n l h.1 _ v hv
    rw [List.getLast?_eq_getElem?, lift_length, e]

theorem not_adm_of_ind {M : CG} {l : List ℕ} (h : IndN M l) (hl : l.length = 13) :
    ¬ AdmIn M.graph univ := fun hA =>
  hA.2.2 _ (fun _ _ => mem_univ _) h.isIndPath (by simpa using hl)

/-! ### Cycles -/

/-- `c` is a cycle of `E`, stated on naturals. -/
def CycN (E : CG) (c : List ℕ) : Prop :=
  (∀ a ∈ c, a < E.n) ∧ c.Nodup ∧ 3 ≤ c.length ∧ List.IsChain (fun a b => E.A a b = true) c ∧
    ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, E.A a b = true

theorem CycN.isCycleList {E : CG} {cs : List ℕ} (h : CycN E cs) :
    IsCycleList E.graph (lift E.n cs h.1) := by
  obtain ⟨hlt, hnd, h3, hch, hw⟩ := h
  refine ⟨lift_nodup _ _ _ hnd, by simpa using h3, fun i hi => ?_, fun hpos => ?_⟩
  · simp only [lift_getElem, graph_adj]
    exact List.isChain_iff_getElem.1 hch i (by simpa using hi)
  · simp only [lift_getElem, graph_adj, lift_length]
    have hl : 0 < cs.length := by simpa using hpos
    have e1 : cs.getLast? = some (cs[cs.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    have e2 : cs.head? = some (cs[0]'hl) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl]
    exact hw _ e1 _ e2

theorem not_adm_of_cyc {E : CG} {c : List ℕ} (h : CycN E c) (hf : forbiddenLen c.length) :
    ¬ AdmIn E.graph univ := fun hA =>
  hA.2.1 _ (fun _ _ => mem_univ _) h.isCycleList (by simpa using hf)

/-- Boolean forbidden-length test. -/
def forbB (c : ℕ) : Bool := c == 4 || c == 8 || c == 16 || c == 32

theorem forbB_sound {c : ℕ} (h : forbB c = true) : forbiddenLen c := by
  simp only [forbB, Bool.or_eq_true, beq_iff_eq] at h
  unfold forbiddenLen; tauto

/-- A simple path of `M`, stated on naturals. -/
def PathN (M : CG) (p : List ℕ) : Prop :=
  (∀ a ∈ p, a < M.n) ∧ p.Nodup ∧ List.IsChain (fun a b => M.A a b = true) p

/-- Consecutive adjacency. -/
def chainB (M : CG) : List ℕ → Bool
  | a :: b :: t => M.A a b && chainB M (b :: t)
  | _ => true

theorem chainB_sound (M : CG) : ∀ p : List ℕ, chainB M p = true →
    List.IsChain (fun a b => M.A a b = true) p
  | [], _ => List.IsChain.nil
  | [_], _ => List.IsChain.singleton _
  | a :: b :: t, h => by
    simp only [chainB, Bool.and_eq_true] at h
    exact List.isChain_cons_cons.2 ⟨h.1, chainB_sound M (b :: t) h.2⟩

def pathB (M : CG) (p : List ℕ) : Bool :=
  p.all (fun a => decide (a < M.n)) && decide p.Nodup && chainB M p

theorem pathB_sound {M : CG} {p : List ℕ} (h : pathB M p = true) : PathN M p := by
  simp only [pathB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, chainB_sound M p h.2⟩

/-- The cycle formed by the ear `n, …, n+m-1` and a path of `M` from `a` to `b`,
where `n+m-1 ~ a` and `b ~ n`. -/
theorem cyc_ear (M : CG) (m x y : ℕ) (z : Option ℕ) (hm : 1 ≤ m) {p : List ℕ} {a b : ℕ}
    (hp : PathN M p) (h2 : 2 ≤ p.length) (ha : p.head? = some a) (hb : p.getLast? = some b)
    (hEa : (M.ear m x y z).A (M.n + m - 1) a = true) (hEb : (M.ear m x y z).A b M.n = true) :
    CycN (M.ear m x y z) (List.range' M.n m ++ p) := by
  obtain ⟨hlt, hnd, hch⟩ := hp
  have hEn : (M.ear m x y z).n = M.n + m := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [hEn]
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hc; omega
    · have := hlt c hc; omega
  · refine List.nodup_append.2 ⟨List.nodup_range' _, hnd, fun u hu v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hu
    have := hlt v hv; omega
  · simp; omega
  · refine List.isChain_append.2 ⟨?_, ?_, ?_⟩
    · refine List.isChain_iff_getElem.2 fun i hi => ?_
      simp only [List.getElem_range', one_mul]
      rw [← Nat.add_assoc]; exact ear_A_step M m x y z i
    · refine List.isChain_iff_getElem.2 fun i hi => ?_
      rw [ear_A_lt M m x y z (hlt _ (List.getElem_mem _)) (hlt _ (List.getElem_mem _))]
      exact List.isChain_iff_getElem.1 hch i hi
    · intro u hu v hv
      rw [List.getLast?_range', if_neg (by omega)] at hu
      rw [ha] at hv
      cases hu; cases hv; exact hEa
  · intro u hu v hv
    have hpne : p ≠ [] := by rintro rfl; simp at h2
    rw [List.getLast?_append, hb] at hu
    rw [List.head?_append, List.head?_range', if_neg (by omega)] at hv
    simp at hu hv; subst hu; subst hv; exact hEb

/-! ### Verified path-length tables -/

/-- The lengths of the candidate paths `ps` that are verified paths of `M` from `a` to `b`
with at least two vertices. -/
def verLens (M : CG) (a b : ℕ) (ps : List (List ℕ)) : List ℕ :=
  ps.filterMap fun p =>
    if pathB M p && p.head? == some a && p.getLast? == some b && decide (2 ≤ p.length)
    then some p.length else none

theorem mem_verLens {M : CG} {a b k : ℕ} {ps : List (List ℕ)} (h : k ∈ verLens M a b ps) :
    ∃ p, PathN M p ∧ 2 ≤ p.length ∧ p.head? = some a ∧ p.getLast? = some b ∧ p.length = k := by
  simp only [verLens, List.mem_filterMap] at h
  obtain ⟨p, _, hp⟩ := h
  split at hp
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    cases hp
    exact ⟨p, pathB_sound hc.1.1.1, hc.2, hc.1.1.2, hc.1.2, rfl⟩
  · cases hp

def lensTab (M : CG) (pt : ℕ → ℕ → List (List ℕ)) : Array (Array (List ℕ)) :=
  Array.ofFn fun a : Fin M.n => Array.ofFn fun b : Fin M.n => verLens M a b (pt a b)

def lensAt (T : Array (Array (List ℕ))) (a b : ℕ) : List ℕ := (T.getD a #[]).getD b []

theorem mem_lensAt {M : CG} {pt : ℕ → ℕ → List (List ℕ)} {a b k : ℕ}
    (h : k ∈ lensAt (lensTab M pt) a b) :
    ∃ p, PathN M p ∧ 2 ≤ p.length ∧ p.head? = some a ∧ p.getLast? = some b ∧ p.length = k := by
  unfold lensAt lensTab at h
  by_cases ha : a < M.n
  · by_cases hb : b < M.n
    · have e : ((Array.ofFn fun a : Fin M.n => Array.ofFn fun b : Fin M.n =>
          verLens M a b (pt a b)).getD a #[]).getD b [] = verLens M a b (pt a b) := by
        simp [Array.getD_eq_getD_getElem?, ha, hb]
      rw [e] at h
      exact mem_verLens h
    · simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, ha, hb] at h
  · simp [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, ha] at h

/-- Some forbidden cycle through the ear is witnessed by a verified path. -/
def cycKill (T : Array (Array (List ℕ))) (m x y : ℕ) (z : Option ℕ) : Bool :=
  (lensAt T y x).any (fun k => forbB (m + k)) ||
    (m == 1 && match z with
      | none => false
      | some w => (lensAt T w x).any (fun k => forbB (1 + k)) ||
          (lensAt T w y).any (fun k => forbB (1 + k)))

theorem cycKill_sound {M : CG} {pt : ℕ → ℕ → List (List ℕ)} {m x y : ℕ} {z : Option ℕ}
    (h : cycKill (lensTab M pt) m x y z = true) (hm : 1 ≤ m) (hx : x < M.n) (hy : y < M.n)
    (hz : ∀ w, z = some w → w < M.n) : ¬ AdmIn (M.ear m x y z).graph univ := by
  simp only [cycKill, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨k, hk, hf⟩ | ⟨rfl, hz'⟩
  · obtain ⟨p, hp, h2, ha, hb, rfl⟩ := mem_lensAt hk
    have hc := cyc_ear M m x y z hm hp h2 ha hb
      (by rw [A_symm]; exact ear_A_y M m x y z hm hy) (ear_A_x M m x y z hx)
    exact not_adm_of_cyc hc (by simpa using forbB_sound hf)
  · cases z with
    | none => simp at hz'
    | some w =>
      have hw := hz w rfl
      simp only [Bool.or_eq_true, List.any_eq_true] at hz'
      rcases hz' with ⟨k, hk, hf⟩ | ⟨k, hk, hf⟩
      · obtain ⟨p, hp, h2, ha, hb, rfl⟩ := mem_lensAt hk
        have hc := cyc_ear M 1 x y (some w) le_rfl hp h2 ha hb
          (by rw [A_symm]; simpa using ear_A_z M x y w hw) (ear_A_x M 1 x y _ hx)
        exact not_adm_of_cyc hc (by simpa [Nat.add_comm] using forbB_sound hf)
      · obtain ⟨p, hp, h2, ha, hb, rfl⟩ := mem_lensAt hk
        have hc := cyc_ear M 1 x y (some w) le_rfl hp h2 ha hb
          (by rw [A_symm]; simpa using ear_A_z M x y w hw)
          (by simpa using ear_A_y M 1 x y (some w) le_rfl hy)
        exact not_adm_of_cyc hc (by simpa [Nat.add_comm] using forbB_sound hf)

/-! ### Degrees and `8e − 11n` -/

/-- Degree of `v` in `M`. -/
def degB (M : CG) (v : ℕ) : ℕ := ((Finset.range M.n).filter fun w => M.A v w = true).card

theorem degIn_eq (M : CG) (v : Fin M.n) : degIn M.graph univ v = degB M v := by
  classical
  unfold degIn degB
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext w
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    graph_adj, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨hw, ha⟩; exact ⟨⟨w, hw⟩, ha, rfl⟩

theorem degB_ear_ge (M : CG) (m x y : ℕ) (z : Option ℕ) {v u : ℕ} (hv : v < M.n) (hu : M.n ≤ u)
    (hu' : u < M.n + m) (hE : (M.ear m x y z).A v u = true) :
    degB M v + 1 ≤ degB (M.ear m x y z) v := by
  unfold degB
  have hsub : insert u ((Finset.range M.n).filter fun w => M.A v w = true) ⊆
      (Finset.range (M.ear m x y z).n).filter fun w => (M.ear m x y z).A v w = true := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hw ⊢
    have hEn : (M.ear m x y z).n = M.n + m := rfl
    rcases hw with rfl | ⟨hw, hA⟩
    · exact ⟨by omega, hE⟩
    · exact ⟨by omega, by rw [ear_A_lt M m x y z hv hw]; exact hA⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp; omega)] at this
  exact this

theorem not_adm_of_deg {E : CG} {v : ℕ} (hv : v < E.n) (h : 4 ≤ degB E v) :
    ¬ AdmIn E.graph univ := fun hA => by
  have := hA.1 ⟨v, hv⟩ (mem_univ _)
  rw [degIn_eq] at this
  simp at this; omega

/-- `8 e − 11 n`, computed. -/
def dB (M : CG) : ℤ :=
  4 * (((Finset.range M.n) ×ˢ (Finset.range M.n)).filter fun p => M.A p.1 p.2 = true).card
    - 11 * M.n

theorem dIn_eq (M : CG) : dIn M.graph univ = dB M := by
  classical
  unfold dIn dB
  have : ((univ ×ˢ univ : Finset (Fin M.n × Fin M.n)).filter fun p => M.graph.Adj p.1 p.2).card =
      (((Finset.range M.n) ×ˢ (Finset.range M.n)).filter fun p => M.A p.1 p.2 = true).card := by
    rw [← Finset.card_map (Fin.valEmbedding.prodMap Fin.valEmbedding)]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Function.Embedding.prodMap, Function.Embedding.coeFn_mk, Prod.map, Fin.valEmbedding_apply,
      graph_adj, Finset.mem_range, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨i, j, h, rfl, rfl⟩; exact ⟨⟨i.2, j.2⟩, h⟩
    · rintro ⟨⟨ha, hb⟩, h⟩; exact ⟨⟨a, ha⟩, ⟨b, hb⟩, h, rfl, rfl⟩
  have h2 : (univ : Finset (Fin M.n)).card = M.n := by simp
  rw [h2]
  congr 3
  convert this using 2
  ext p; simp

/-! ### Isomorphisms -/

/-- `π` (vertex `i` of `G` ↦ `π[i]` of `H`) is an isomorphism `G ≅ H`. -/
def isoB (G H : CG) (π : Array ℕ) : Bool :=
  G.n == H.n && π.size == G.n && π.all (fun a => decide (a < H.n)) && decide π.toList.Nodup &&
    (List.range G.n).all fun j => (List.range j).all fun i =>
      G.A i j == H.A (π.getD i 0) (π.getD j 0)

theorem isoB_sound {G H : CG} {π : Array ℕ} (h : isoB G H π = true) :
    Nonempty (G.graph ≃g H.graph) := by
  simp only [isoB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hn, hs⟩, hlt⟩, hnd⟩, hA⟩ := h
  have gd : ∀ i (hi : i < G.n), π.getD i 0 = π[i]'(by omega) := by
    intro i hi; simp [Array.getD_eq_getD_getElem?, show i < π.size by omega]
  let f : Fin G.n → Fin H.n := fun i => ⟨π[i.1]'(by omega), hlt _ _⟩
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [f, Fin.mk.injEq] at hij
    have hi : i.1 < π.toList.length := by simp; omega
    have hj : j.1 < π.toList.length := by simp; omega
    have e : π.toList[i.1] = π.toList[j.1] := by simpa using hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hn]⟩
  have key : ∀ i j : Fin G.n, H.A (f i) (f j) = G.A i j := by
    intro i j
    have lt : ∀ a b : Fin G.n, a.1 < b.1 → H.A (f a) (f b) = G.A a b := by
      intro a b hab
      have := hA b b.2 a hab
      rw [gd _ a.2, gd _ b.2] at this
      exact this.symm
    rcases lt_trichotomy i.1 j.1 with hij | hij | hij
    · exact lt i j hij
    · have : i = j := Fin.ext hij
      subst this; simp [A_irrefl]
    · rw [A_symm, lt j i hij, A_symm]
  exact ⟨⟨Equiv.ofBijective f hbij, fun {a b} => by
    simp only [Equiv.ofBijective_apply, graph_adj]; rw [key]⟩⟩

/-! ### Ear extensions of one member -/

/-- A witness for one ear extension: an induced path on 13 vertices, or an
isomorphism onto the member with the given index. -/
inductive Wit where
  | none
  | ip (l : List ℕ)
  | iso (k : ℕ) (π : Array ℕ)

/-- The conclusion of `ClosureCert` for one ear extension. -/
def EarGood (L : List CG) (M : CG) (m x y : ℕ) (z : Option ℕ) : Prop :=
  ¬ AdmIn (M.ear m x y z).graph univ ∨ ∃ M' ∈ L, Nonempty ((M.ear m x y z).graph ≃g M'.graph)

def candOK (L : Array CG) (M : CG) (m x y : ℕ) (z : Option ℕ) : Wit → Bool
  | .none => false
  | .ip l => l.length == 13 && indB (M.ear m x y z) l
  | .iso k π => decide (k < L.size) && isoB (M.ear m x y z) (L.getD k M) π

theorem candOK_sound {L : Array CG} {M : CG} {m x y : ℕ} {z : Option ℕ} {w : Wit}
    (h : candOK L M m x y z w = true) : EarGood L.toList M m x y z := by
  cases w with
  | none => simp [candOK] at h
  | ip l =>
    simp only [candOK, Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inl (not_adm_of_ind (indB_sound h.2) h.1)
  | iso k π =>
    simp only [candOK, Bool.and_eq_true, decide_eq_true_eq] at h
    refine Or.inr ⟨L[k]'h.1, Array.mem_toList_iff.2 (Array.getElem_mem _), ?_⟩
    have e : L.getD k M = L[k]'h.1 := by simp [Array.getD_eq_getD_getElem?, h.1]
    rw [e] at h
    exact isoB_sound h.2

/-- Vertices of degree at least 3. -/
def d3Arr (M : CG) : Array Bool := Array.ofFn fun v : Fin M.n => decide (3 ≤ degB M v)

theorem d3_sound {M : CG} {v : ℕ} (h : (d3Arr M).getD v false = true) : v < M.n ∧ 3 ≤ degB M v := by
  unfold d3Arr at h
  by_cases hv : v < M.n
  · simp [Array.getD_eq_getD_getElem?, hv] at h
    exact ⟨hv, h⟩
  · simp [Array.getD_eq_getD_getElem?, hv] at h

theorem earGood_of_deg (L : List CG) (M : CG) (m x y : ℕ) (z : Option ℕ) {v u : ℕ}
    (hv : v < M.n) (hu : M.n ≤ u) (hu' : u < M.n + m) (hE : (M.ear m x y z).A v u = true)
    (h3 : 3 ≤ degB M v) : EarGood L M m x y z := by
  refine Or.inl (not_adm_of_deg (show v < M.n + m by omega) ?_)
  have := degB_ear_ge M m x y z hv hu hu' hE
  omega

theorem earGood_congr1 {L : List CG} {M : CG} {x y x' y' : ℕ} {z z' : Option ℕ}
    (h : ∀ i, (i = x ∨ i = y ∨ z = some i) ↔ (i = x' ∨ i = y' ∨ z' = some i))
    (hg : EarGood L M 1 x' y' z') : EarGood L M 1 x y z := by
  unfold EarGood at hg ⊢
  rw [CG.ear1_graph_congr M h]
  exact hg

/-- The ear-extension check of one member `M`: pairs `x < y`, both orientations for
`m ≥ 2`, and for `m = 1` the attachment sets `{x, y}` and `{x, y, w}` with `y < w`. -/
def closureOK (L : Array CG) (M : CG) (pt : ℕ → ℕ → List (List ℕ))
    (find : ℕ → ℕ → ℕ → Option ℕ → Wit) : Bool :=
  let T := lensTab M pt
  let d3 := d3Arr M
  (List.range M.n).all fun y => (List.range y).all fun x =>
    d3.getD x false || d3.getD y false ||
    (((List.range 11).all fun k =>
        (cycKill T (k + 1) x y none || candOK L M (k + 1) x y none (find (k + 1) x y none)) &&
        (k == 0 || cycKill T (k + 1) y x none ||
          candOK L M (k + 1) y x none (find (k + 1) y x none))) &&
      (List.range M.n).all fun w => decide (w ≤ y) || d3.getD w false ||
        cycKill T 1 x y (some w) || candOK L M 1 x y (some w) (find 1 x y (some w)))

theorem pair_good {L : Array CG} {M : CG} {pt : ℕ → ℕ → List (List ℕ)}
    {find : ℕ → ℕ → ℕ → Option ℕ → Wit} (h : closureOK L M pt find = true)
    {x y : ℕ} (hxy : x < y) (hy : y < M.n) :
    (∀ m, 1 ≤ m → m ≤ 11 → EarGood L.toList M m x y none) ∧
    (∀ m, 2 ≤ m → m ≤ 11 → EarGood L.toList M m y x none) ∧
    (∀ w, y < w → w < M.n → EarGood L.toList M 1 x y (some w)) := by
  have hx : x < M.n := by omega
  simp only [closureOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h
  have hp := h y hy x hxy
  rcases hp with (hd | hd) | ⟨hm, hw⟩
  · obtain ⟨_, h3⟩ := d3_sound hd
    refine ⟨fun m hm1 _ => ?_, fun m hm2 _ => ?_, fun w _ _ => ?_⟩
    · exact earGood_of_deg _ M m x y none hx le_rfl (by omega) (ear_A_x M m x y none hx) h3
    · exact earGood_of_deg _ M m y x none hx (by omega) (by omega)
        (ear_A_y M m y x none (by omega) hx) h3
    · exact earGood_of_deg _ M 1 x y (some w) hx le_rfl (by omega) (ear_A_x M 1 x y _ hx) h3
  · obtain ⟨_, h3⟩ := d3_sound hd
    refine ⟨fun m hm1 _ => ?_, fun m hm2 _ => ?_, fun w _ _ => ?_⟩
    · exact earGood_of_deg _ M m x y none hy (by omega) (by omega)
        (ear_A_y M m x y none hm1 hy) h3
    · exact earGood_of_deg _ M m y x none hy le_rfl (by omega) (ear_A_x M m y x none hy) h3
    · exact earGood_of_deg _ M 1 x y (some w) hy (by omega) (by omega)
        (ear_A_y M 1 x y _ le_rfl hy) h3
  · refine ⟨fun m hm1 hm11 => ?_, fun m hm2 hm11 => ?_, fun w hyw hwn => ?_⟩
    · obtain ⟨h1, _⟩ := hm (m - 1) (by omega)
      rw [Nat.sub_add_cancel hm1] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (cycKill_sound h1 hm1 hx hy (by simp))
      · exact candOK_sound h1
    · obtain ⟨_, h2⟩ := hm (m - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h2
      rcases h2 with (h2 | h2) | h2
      · omega
      · exact Or.inl (cycKill_sound h2 (by omega) hy hx (by simp))
      · exact candOK_sound h2
    · rcases hw w hwn with ((h1 | h1) | h1) | h1
      · omega
      · obtain ⟨_, h3⟩ := d3_sound h1
        exact earGood_of_deg _ M 1 x y (some w) (by omega) le_rfl (by omega)
          (ear_A_z M x y w hwn) h3
      · exact Or.inl (cycKill_sound h1 le_rfl hx hy (by rintro _ ⟨⟩; exact hwn))
      · exact candOK_sound h1

theorem sort3 {x y w : ℕ} (h1 : x ≠ y) (h2 : w ≠ x) (h3 : w ≠ y) :
    ∃ a b c, a < b ∧ b < c ∧ ∀ i, (i = x ∨ i = y ∨ i = w) ↔ (i = a ∨ i = b ∨ i = c) := by
  rcases lt_or_gt_of_ne h1 with h | h <;> rcases lt_or_gt_of_ne h2 with h' | h' <;>
    rcases lt_or_gt_of_ne h3 with h'' | h''
  all_goals first
    | exact ⟨x, y, w, by omega, by omega, fun i => by omega⟩
    | exact ⟨x, w, y, by omega, by omega, fun i => by omega⟩
    | exact ⟨y, x, w, by omega, by omega, fun i => by omega⟩
    | exact ⟨y, w, x, by omega, by omega, fun i => by omega⟩
    | exact ⟨w, x, y, by omega, by omega, fun i => by omega⟩
    | exact ⟨w, y, x, by omega, by omega, fun i => by omega⟩
    | omega

theorem closureOK_sound {L : Array CG} {M : CG} {pt : ℕ → ℕ → List (List ℕ)}
    {find : ℕ → ℕ → ℕ → Option ℕ → Wit} (h : closureOK L M pt find = true) :
    ∀ m, 1 ≤ m → m ≤ 11 → ∀ x < M.n, ∀ y < M.n, x ≠ y → ∀ z : Option ℕ,
      (2 ≤ m → z = none) → (∀ w, z = some w → w < M.n ∧ w ≠ x ∧ w ≠ y) →
      ¬ AdmIn (M.ear m x y z).graph Finset.univ ∨
        ∃ M' ∈ L.toList, Nonempty ((M.ear m x y z).graph ≃g M'.graph) := by
  intro m hm1 hm11 x hx y hy hxy z hz2 hzw
  show EarGood L.toList M m x y z
  rcases z with _ | w
  · rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact (pair_good h hlt hy).1 m hm1 hm11
    · by_cases hm : m = 1
      · subst hm
        exact earGood_congr1 (fun i => by simp; omega) ((pair_good h hlt hx).1 1 le_rfl hm11)
      · exact (pair_good h hlt hx).2.1 m (by omega) hm11
  · have hm : m = 1 := by
      by_contra hc; have := hz2 (by omega); cases this
    subst hm
    obtain ⟨hwn, hwx, hwy⟩ := hzw w rfl
    obtain ⟨a, b, c, hab, hbc, hi⟩ := sort3 hxy hwx hwy
    have hcn : c < M.n := by
      have := (hi c).2 (Or.inr (Or.inr rfl)); omega
    refine earGood_congr1 (x' := a) (y' := b) (z' := some c) (fun i => ?_)
      ((pair_good h hab (by omega)).2.2 c hbc hcn)
    have := hi i
    rw [show (some w = some i) ↔ i = w from ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩,
      show (some c = some i) ↔ i = c from ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩]
    exact this

/-! ### Block profiles -/

theorem fTab_le3 (a : ℕ) : fTab a ≤ 3 := by
  unfold fTab; split <;> decide

theorem fTab_ge11 {a : ℕ} (h : 11 ≤ a) : fTab a = 3 := by
  unfold fTab; split <;> first | omega | rfl

theorem fTab_mono {a b : ℕ} (h : a ≤ b) : fTab a ≤ fTab b := by
  by_cases hb : 11 ≤ b
  · rw [fTab_ge11 hb]; exact fTab_le3 a
  · have ha : a ≤ 10 := by omega
    have hb' : b ≤ 10 := by omega
    interval_cases a <;> interval_cases b <;> simp_all [fTab]

/-- A verified lower bound for the longest induced path from `r`. -/
def lamV (M : CG) (r : ℕ) (l : List ℕ) : ℕ := if indB M l && l[0]? == some r then l.length else 0

theorem lamV_le (M : CG) (r : ℕ) (l : List ℕ) (hr : r < M.n) :
    lamV M r l ≤ lamIn M.graph univ ⟨r, hr⟩ := by
  unfold lamV
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact le_lamIn (indB_sound hc.1) hc.2 hr
  · exact Nat.zero_le _

/-- A verified lower bound for the longest induced `r`–`p` path. -/
def LV (M : CG) (r p : ℕ) (l : List ℕ) : ℕ :=
  if indB M l && l[0]? == some r && l[l.length - 1]? == some p then l.length else 0

theorem LV_le (M : CG) (r p : ℕ) (l : List ℕ) (hr : r < M.n) (hp : p < M.n) :
    LV M r p l ≤ LIn M.graph univ ⟨r, hr⟩ ⟨p, hp⟩ := by
  unfold LV
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact le_LIn (indB_sound hc.1.1) hc.1.2 hc.2 hr hp
  · exact Nat.zero_le _

/-- The profile inequalities on computed data. -/
def dpCore (n : ℕ) (d : ℤ) (pos : Bool) (deg lam : ℕ → ℕ) (LL : ℕ → ℕ → ℕ) : Bool :=
  let ports := (List.range n).filter fun v => decide (deg v ≤ 2)
  pos &&
  ports.all (fun r => decide (d ≤ fTab (lam r))) &&
  ports.all (fun r => ports.all fun p => r == p ||
    (List.range' 5 (8 - lam p)).all fun t =>
      decide (max (lam r) (LL r p + t) ≤ 12 → d + fTab t + 8 ≤ fTab (max (lam r) (LL r p + t)))) &&
  ports.all (fun r => ports.all fun p => r == p || ports.all fun q => r == q || p == q ||
    (List.range' 5 (8 - lam p)).all fun a => (List.range' 5 (8 - lam q)).all fun b =>
      decide (a + LL p q + b ≤ 12 → max (lam r) (max (LL r p + a) (LL r q + b)) ≤ 12 →
        d + fTab a + fTab b + 16 ≤ fTab (max (lam r) (max (LL r p + a) (LL r q + b))))) &&
  (decide (n ≤ 3) || ports.all (fun p => ports.all fun q => p == q || ports.all fun s => p == s ||
    q == s || decide (3 ≤ LL p q) || decide (3 ≤ LL p s) || decide (3 ≤ LL q s)))

/-- The body of `DPCert` for one graph. -/
def DPBody (M : CG) : Prop :=
    let lam := fun i => lamIn M.graph Finset.univ i
    let LL := fun i j => LIn M.graph Finset.univ i j
    let deg := fun i => degIn M.graph Finset.univ i
    let d := dIn M.graph Finset.univ
    (d ≤ 0 ∨ Nonempty (M.graph ≃g CG.x15.graph)) ∧
    (∀ r, deg r ≤ 2 → d ≤ fTab (lam r)) ∧
    (∀ r p, p ≠ r → deg r ≤ 2 → deg p ≤ 2 → ∀ t, 5 ≤ t → t ≤ 12 →
      lam p + t ≤ 12 → max (lam r) (LL r p + t) ≤ 12 →
      d + fTab t + 8 ≤ fTab (max (lam r) (LL r p + t))) ∧
    (∀ r p q, p ≠ r → q ≠ r → p ≠ q → deg r ≤ 2 → deg p ≤ 2 → deg q ≤ 2 →
      ∀ a b, 5 ≤ a → a ≤ 12 → 5 ≤ b → b ≤ 12 →
      lam p + a ≤ 12 → lam q + b ≤ 12 → a + LL p q + b ≤ 12 →
      max (lam r) (max (LL r p + a) (LL r q + b)) ≤ 12 →
      d + fTab a + fTab b + 16 ≤ fTab (max (lam r) (max (LL r p + a) (LL r q + b)))) ∧
    (∀ r p q s, p ≠ r → q ≠ r → s ≠ r → p ≠ q → p ≠ s → q ≠ s →
      deg p ≤ 2 → deg q ≤ 2 → deg s ≤ 2 →
      ¬ (LL p q ≤ 2 ∧ LL p s ≤ 2 ∧ LL q s ≤ 2))

theorem dpCert_iff (L : List CG) : DPCert L ↔ ∀ M ∈ L, DPBody M := Iff.rfl

/-- The profile check of one member, with untrusted longest-path witnesses. -/
def dpOK (M : CG) (π15 : Array ℕ) (lw : ℕ → List ℕ) (Lw : ℕ → ℕ → List ℕ) : Bool :=
  let dg := Array.ofFn fun v : Fin M.n => degB M v
  let la := Array.ofFn fun r : Fin M.n => lamV M r (lw r)
  let LA := Array.ofFn fun r : Fin M.n => Array.ofFn fun p : Fin M.n => LV M r p (Lw r p)
  dpCore M.n (dB M) (decide (dB M ≤ 0) || isoB M CG.x15 π15) (fun v => dg.getD v 0)
    (fun v => la.getD v 0) (fun a b => (LA.getD a #[]).getD b 0)

theorem dpCore_sound {n : ℕ} {d : ℤ} {pos : Bool} {deg lam : ℕ → ℕ} {LL : ℕ → ℕ → ℕ}
    (h : dpCore n d pos deg lam LL = true) :
    pos = true ∧ (∀ r < n, deg r ≤ 2 → d ≤ fTab (lam r)) ∧
    (∀ r < n, ∀ p < n, deg r ≤ 2 → deg p ≤ 2 → r ≠ p → ∀ t, 5 ≤ t → lam p + t ≤ 12 →
      max (lam r) (LL r p + t) ≤ 12 → d + fTab t + 8 ≤ fTab (max (lam r) (LL r p + t))) ∧
    (∀ r < n, ∀ p < n, ∀ q < n, deg r ≤ 2 → deg p ≤ 2 → deg q ≤ 2 → r ≠ p → r ≠ q → p ≠ q →
      ∀ a b, 5 ≤ a → 5 ≤ b → lam p + a ≤ 12 → lam q + b ≤ 12 → a + LL p q + b ≤ 12 →
      max (lam r) (max (LL r p + a) (LL r q + b)) ≤ 12 →
      d + fTab a + fTab b + 16 ≤ fTab (max (lam r) (max (LL r p + a) (LL r q + b)))) ∧
    (n ≤ 3 ∨ ∀ p < n, ∀ q < n, ∀ s < n, deg p ≤ 2 → deg q ≤ 2 → deg s ≤ 2 → p ≠ q → p ≠ s →
      q ≠ s → 3 ≤ LL p q ∨ 3 ≤ LL p s ∨ 3 ≤ LL q s) := by
  simp only [dpCore, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, List.mem_range'_1, and_imp] at h
  obtain ⟨⟨⟨⟨hpos, h2⟩, h3⟩, h4⟩, h6⟩ := h
  refine ⟨hpos, fun r hr hdr => h2 r hr hdr, ?_, ?_, ?_⟩
  · intro r hr p hp hdr hdp hrp t ht hpt hmax
    rcases h3 r hr hdr p hp hdp with e | h3'
    · exact absurd e hrp
    · exact h3' t (by omega) (by omega) hmax
  · intro r hr p hp q hq hdr hdp hdq hrp hrq hpq a b ha hb hpa hqb habq hmax
    rcases h4 r hr hdr p hp hdp with e | h4'
    · exact absurd e hrp
    rcases h4' q hq hdq with (e | e) | h4''
    · exact absurd e hrq
    · exact absurd e hpq
    exact h4'' a (by omega) (by omega) b (by omega) (by omega) habq hmax
  · rcases h6 with h6 | h6
    · exact Or.inl h6
    refine Or.inr fun p hp q hq s hs hdp hdq hds hpq hps hqs => ?_
    rcases h6 p hp hdp q hq hdq with e | h6'
    · exact absurd e hpq
    rcases h6' s hs hds with (((e | e) | e) | e) | e
    · exact absurd e hps
    · exact absurd e hqs
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

theorem dpOK_sound {M : CG} {π15 : Array ℕ} {lw : ℕ → List ℕ} {Lw : ℕ → ℕ → List ℕ}
    (h : dpOK M π15 lw Lw = true) : DPBody M := by
  unfold dpOK at h
  obtain ⟨hpos, h2, h3, h4, h6⟩ := dpCore_sound h
  have edeg : ∀ v : Fin M.n, degIn M.graph univ v =
      (Array.ofFn fun v : Fin M.n => degB M v).getD v 0 := by
    intro v; simp [Array.getD_eq_getD_getElem?, v.2, degIn_eq]
  have elam : ∀ v : Fin M.n, (Array.ofFn fun r : Fin M.n => lamV M r (lw r)).getD v 0 ≤
      lamIn M.graph univ v := by
    intro v; simpa [Array.getD_eq_getD_getElem?, v.2] using lamV_le M v (lw v) v.2
  have eLL : ∀ a b : Fin M.n, ((Array.ofFn fun r : Fin M.n => Array.ofFn fun p : Fin M.n =>
      LV M r p (Lw r p)).getD a #[]).getD b 0 ≤ LIn M.graph univ a b := by
    intro a b
    simpa [Array.getD_eq_getD_getElem?, a.2, b.2] using LV_le M a b (Lw a b) a.2 b.2
  have ed : dIn M.graph univ = dB M := dIn_eq M
  dsimp only [DPBody]
  rw [ed]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at hpos
    rcases hpos with hpos | hpos
    · exact Or.inl hpos
    · exact Or.inr (isoB_sound hpos)
  · intro r hr
    rw [edeg] at hr
    exact (h2 r r.2 hr).trans (fTab_mono (elam r))
  · intro r p hpr hr hp t ht5 ht12 hpt hmax
    rw [edeg] at hr hp
    have lp := elam p; have lr := elam r; have lrp := eLL r p
    have := h3 r r.2 p p.2 hr hp (fun e => hpr (Fin.ext e).symm) t ht5 (by omega) (by omega)
    refine this.trans (fTab_mono ?_)
    omega
  · intro r p q hpr hqr hpq hr hp hq a b ha5 ha12 hb5 hb12 hpa hqb habq hmax
    rw [edeg] at hr hp hq
    have lp := elam p; have lq := elam q; have lr := elam r
    have lrp := eLL r p; have lrq := eLL r q; have lpq := eLL p q
    have := h4 r r.2 p p.2 q q.2 hr hp hq (fun e => hpr (Fin.ext e).symm)
      (fun e => hqr (Fin.ext e).symm) (fun e => hpq (Fin.ext e)) a b ha5 hb5 (by omega) (by omega)
      (by omega) (by omega)
    refine this.trans (fTab_mono ?_)
    omega
  · intro r p q s hpr hqr hsr hpq hps hqs hp hq hs hc
    rcases h6 with h6 | h6
    · have := Fin.val_ne_of_ne hpr; have := Fin.val_ne_of_ne hqr; have := Fin.val_ne_of_ne hsr
      have := Fin.val_ne_of_ne hpq; have := Fin.val_ne_of_ne hps; have := Fin.val_ne_of_ne hqs
      have := r.2; have := p.2; have := q.2; have := s.2
      omega
    rw [edeg] at hp hq hs
    have lpq := eLL p q; have lps := eLL p s; have lqs := eLL q s
    have := h6 p p.2 q q.2 s s.2 hp hq hs (fun e => hpq (Fin.ext e)) (fun e => hps (Fin.ext e))
      (fun e => hqs (Fin.ext e))
    omega

end CertCheck

end Hypostructure.Graph.DensityCert
