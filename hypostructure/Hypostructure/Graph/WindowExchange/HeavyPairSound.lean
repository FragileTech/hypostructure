import Hypostructure.Graph.WindowExchange.HeavyPairSearch

/-!
# Soundness of the rung search

* `noExtG_sound`: if `noExtG rej F s k` holds, every strictly increasing list `L` of `k`
  indices in `[s, 169)` has a position `m` where `rej L[m] (reverse (take m L) ++ F)` holds.
* `tabRej_sound`: a cut `tabRej … (mkTabs …) r F` exhibits a sub-list of `r :: F` refuted by
  `wRej`.
* `wRej_sound`: `wRej` returns a checked witness.
-/

namespace Hypostructure.Graph.WindowExchange

theorem noExtG_sound (rej : ℕ → List ℕ → Bool) : ∀ (k : ℕ) (F : List ℕ) (s : ℕ) (L : List ℕ),
    noExtG rej F s k = true → L.length = k → L.Pairwise (· < ·) →
    (∀ r ∈ L, s ≤ r ∧ r < 169) →
    ∃ (m : ℕ) (h : m < L.length), rej L[m] ((L.take m).reverse ++ F) = true
  | 0, F, s, L, h, _, _, _ => by simp [noExtG] at h
  | k + 1, F, s, L, h, hlen, hsort, hrange => by
    obtain ⟨r, L', rfl⟩ : ∃ r L', L = r :: L' := by
      cases L with
      | nil => simp at hlen
      | cons r L' => exact ⟨r, L', rfl⟩
    simp only [noExtG, List.all_eq_true, List.mem_range', Bool.or_eq_true] at h
    have hr := hrange r List.mem_cons_self
    obtain ⟨hr1, hr2⟩ := hr
    rcases h r ⟨r - s, by omega, by omega⟩ with h1 | h2
    · exact ⟨0, by simp, by simpa using h1⟩
    · have sorted' : L'.Pairwise (· < ·) := (List.pairwise_cons.1 hsort).2
      have range' : ∀ z ∈ L', r + 1 ≤ z ∧ z < 169 := fun z hz =>
        ⟨(List.pairwise_cons.1 hsort).1 z hz, (hrange z (List.mem_cons_of_mem _ hz)).2⟩
      obtain ⟨m, hm, hrej⟩ := noExtG_sound rej k (r :: F) (r + 1) L' h2
        (by simpa using hlen) sorted' range'
      refine ⟨m + 1, by simp; omega, ?_⟩
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using hrej

theorem getD_ofFn_true {n : ℕ} {f : Fin n → Bool} {k : ℕ} {d : Bool}
    (h : (Array.ofFn f).getD k d = true) (hd : d = false) : ∃ hk : k < n, f ⟨k, hk⟩ = true := by
  subst hd
  unfold Array.getD at h
  split at h
  · rename_i hk
    simp only [Array.size_ofFn] at hk
    refine ⟨hk, ?_⟩
    simpa using h
  · simp at h

theorem mkTabs_single (lo x a y b : ℕ) : (mkTabs lo x a y b).single = tSingle lo x a y b := by
  simp only [mkTabs]

theorem mkTabs_pair (lo x a y b : ℕ) :
    (mkTabs lo x a y b).pair = tPair lo x a y b (mkTabs lo x a y b).allowed := by
  simp only [mkTabs]

theorem mkTabs_trip (lo x a y b : ℕ) :
    (mkTabs lo x a y b).trip =
      tTrip lo x a y b (mkTabs lo x a y b).allowed (mkTabs lo x a y b).pair := by
  simp only [mkTabs]

theorem anyPair_sound (f : ℕ → ℕ → Bool) : ∀ F : List ℕ, anyPair f F = true →
    ∃ s ∈ F, ∃ t ∈ F, f s t = true
  | [], h => by simp [anyPair] at h
  | s :: F, h => by
    simp only [anyPair, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨t, ht, hf⟩ | h
    · exact ⟨s, List.mem_cons_self, t, List.mem_cons_of_mem _ ht, hf⟩
    · obtain ⟨s', hs', t, ht, hf⟩ := anyPair_sound f F h
      exact ⟨s', List.mem_cons_of_mem _ hs', t, List.mem_cons_of_mem _ ht, hf⟩

/-- A cut exhibits a refuted sub-list of the candidate and the accepted rungs. -/
theorem tabRej_sound {lo x a y b d₀ r : ℕ} {F : List ℕ}
    (h : tabRej lo x a y b d₀ (mkTabs lo x a y b) r F = true) :
    ∃ sub : List ℕ, (∀ z ∈ sub, z ∈ r :: F) ∧ wRej lo x a y b sub = true := by
  simp only [tabRej, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with ((h | ⟨s, hs, h⟩) | h) | ⟨-, h⟩
  · rw [mkTabs_single] at h
    obtain ⟨_, hf⟩ := getD_ofFn_true h rfl
    exact ⟨[r], by simp, hf⟩
  · simp only [pairHit, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hk, e1⟩, e2⟩ := h
    rw [mkTabs_pair, tPair] at hk
    obtain ⟨_, hf⟩ := getD_ofFn_true hk rfl
    simp only [Bool.and_eq_true] at hf
    rw [e1, e2] at hf
    exact ⟨[r, s], by simp [hs], hf.2⟩
  · obtain ⟨s, hs, t, ht, h⟩ := anyPair_sound _ F h
    simp only [tripHit, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hk, e1⟩, e2⟩, e3⟩ := h
    rw [mkTabs_trip, tTrip] at hk
    obtain ⟨_, hf⟩ := getD_ofFn_true hk rfl
    simp only [Bool.and_eq_true] at hf
    rw [e1, e2, e3] at hf
    exact ⟨[r, s, t], by simp [hs, ht], hf.2⟩
  · exact ⟨r :: F, fun z hz => hz, h⟩

/-- `wRej` returns a checked witness. -/
theorem wRej_sound {lo x a y b : ℕ} {sub : List ℕ} (h : wRej lo x a y b sub = true) :
    ∃ w, chkRWit x a y b (toPairs sub) w = true := by
  unfold wRej at h
  split at h
  · exact ⟨_, h⟩
  · simp at h

end Hypostructure.Graph.WindowExchange
