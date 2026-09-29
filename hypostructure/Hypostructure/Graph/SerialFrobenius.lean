import Hypostructure.Graph.SerialSystemArithmetic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Frobenius filling of `lem:serial-system-sumset`

`SerialSystem.System.realized_progression` fills the progression `L + r + t·g`
from ONE frequent increment `g`.  This module fills the central interval from
SEVERAL frequent increments `d_j` with common divisor `g = gcd(d_j)`:

* `frobenius_fill`: with a distinguished generator `a = d_{i₀}` and the others
  capped at `≥ a − 1`, every multiple `n` of `g` with
  `a · Σ_{i≠i₀} d_i ≤ n ≤ a · M_{i₀}` is `Σ t_i d_i` with `t_i ≤ M_i`.
  (Bézout gives `g ≡ Σ c_i d_i`; reducing `k c_i` modulo `a` for `i ≠ i₀` leaves a
  multiple of `a`, which the distinguished generator supplies.)
* `System.realized_multiProgression`: disjoint frequent classes `F_j` of cells with
  increment `d_j` realize `L + o + Σ t_j d_j` for `t_j ≤ |F_j|`.
* `System.multiSpectrum`: the resulting `Spectrum` with modulus `g`, whose central
  range is `[⌈a Σ_{i≠i₀} d_i / g⌉, ⌊a M_{i₀} / g⌋]`.
-/

namespace Hypostructure.Graph.SerialSystem

open Finset

/-- **Frobenius filling with caps.** -/
theorem frobenius_fill {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (hpos : ∀ i, 0 < d i) (i0 : ι) (g : ℕ)
    (hbez : ∃ c : ι → ℤ, (g : ℤ) = ∑ i, (d i : ℤ) * c i)
    (M : ι → ℕ) (hM : ∀ i, i ≠ i0 → d i0 ≤ M i + 1)
    (n : ℕ) (hn : g ∣ n)
    (lower : d i0 * ∑ i ∈ univ.erase i0, d i ≤ n) (upper : n ≤ d i0 * M i0) :
    ∃ t : ι → ℕ, (∀ i, t i ≤ M i) ∧ ∑ i, t i * d i = n := by
  obtain ⟨c, hc⟩ := hbez
  obtain ⟨k, rfl⟩ := hn
  have aPos : 0 < d i0 := hpos i0
  set a : ℤ := (d i0 : ℤ) with ha
  have aPosZ : 0 < a := by rw [ha]; exact_mod_cast aPos
  let tau : ι → ℕ := fun i => ((k : ℤ) * c i % a).toNat
  have tauCast : ∀ i, (tau i : ℤ) = (k : ℤ) * c i % a := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ aPosZ.ne')
  have tauLt : ∀ i, tau i < d i0 := fun i => by
    have := Int.emod_lt_of_pos ((k : ℤ) * c i) aPosZ
    have h2 := tauCast i
    have : (tau i : ℤ) < (d i0 : ℤ) := by rw [h2]; exact this
    exact_mod_cast this
  let sigma : ℕ := ∑ i ∈ univ.erase i0, tau i * d i
  have sigmaLe : sigma ≤ d i0 * ∑ i ∈ univ.erase i0, d i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact Nat.mul_le_mul_right _ (tauLt i).le
  -- divisibility of `g k - sigma` by `a`
  have expand : ((g * k : ℕ) : ℤ) = a * (k * c i0) +
      ∑ i ∈ univ.erase i0, (d i : ℤ) * ((k : ℤ) * c i) := by
    push_cast
    rw [hc, Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    congr 1
    · rw [ha]; ring
    · apply Finset.sum_congr rfl; intro i _; ring
  have term : ∀ i, a ∣ (d i : ℤ) * ((k : ℤ) * c i) - (tau i : ℤ) * (d i : ℤ) := by
    intro i
    rw [tauCast i, Int.emod_def]
    exact ⟨(d i : ℤ) * ((k : ℤ) * c i / a), by ring⟩
  have sigmaCast : (sigma : ℤ) = ∑ i ∈ univ.erase i0, (tau i : ℤ) * (d i : ℤ) := by
    simp [sigma]
  have dvd : a ∣ ((g * k : ℕ) : ℤ) - (sigma : ℤ) := by
    have eq : ((g * k : ℕ) : ℤ) - (sigma : ℤ) = a * ((k : ℤ) * c i0) +
        ∑ i ∈ univ.erase i0, ((d i : ℤ) * ((k : ℤ) * c i) - (tau i : ℤ) * (d i : ℤ)) := by
      rw [expand, sigmaCast, Finset.sum_sub_distrib]; ring
    rw [eq]
    exact dvd_add (dvd_mul_right _ _) (Finset.dvd_sum fun i _ => term i)
  obtain ⟨q, hq⟩ := dvd
  have sigmaLeN : sigma ≤ g * k := sigmaLe.trans lower
  have qNonneg : 0 ≤ q := by
    by_contra neg
    push Not at neg
    have h1 : (sigma : ℤ) ≤ ((g * k : ℕ) : ℤ) := by exact_mod_cast sigmaLeN
    nlinarith
  let q0 : ℕ := q.toNat
  have q0Cast : (q0 : ℤ) = q := Int.toNat_of_nonneg qNonneg
  let t : ι → ℕ := fun i => if i = i0 then q0 else tau i
  have sumT : ∑ i, t i * d i = q0 * d i0 + sigma := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
    congr 1
    · simp [t]
    · apply Finset.sum_congr rfl
      intro i hi
      have : i ≠ i0 := (Finset.mem_erase.mp hi).1
      simp [t, this]
  have sumEq : q0 * d i0 + sigma = g * k := by
    have : ((q0 * d i0 + sigma : ℕ) : ℤ) = ((g * k : ℕ) : ℤ) := by
      push_cast
      rw [q0Cast]
      have h := hq
      rw [ha] at h
      push_cast at h
      linarith
    exact_mod_cast this
  refine ⟨t, fun i => ?_, by rw [sumT, sumEq]⟩
  by_cases hi : i = i0
  · subst hi
    simp only [t, if_pos rfl]
    have h1 : d i * q0 ≤ d i * M i := by
      calc d i * q0 = q0 * d i := by ring
        _ ≤ g * k := by omega
        _ ≤ d i * M i := upper
    exact Nat.le_of_mul_le_mul_left h1 (hpos i)
  · simp only [t, if_neg hi]
    have := tauLt i
    have := hM i hi
    omega

/-- **The gcd of the increments, with its Bézout coefficients.** -/
theorem exists_gcd_data {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    ∃ g : ℕ, (∀ i, g ∣ d i) ∧ (∃ c : ι → ℤ, (g : ℤ) = ∑ i, (d i : ℤ) * c i) ∧
      ∀ h : ℕ, (∀ i, h ∣ d i) → h ∣ g := by
  classical
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset ι) (fun i => (d i : ℤ))
  set G : ℤ := (Finset.univ : Finset ι).gcd (fun i => (d i : ℤ)) with hG
  have dvdAll : ∀ i, G ∣ (d i : ℤ) := fun i =>
    Finset.gcd_dvd (f := fun i => (d i : ℤ)) (Finset.mem_univ i)
  have bezG : ∀ h : ℕ, (∀ i, h ∣ d i) → (h : ℤ) ∣ G := by
    intro h hh
    rw [hc]
    exact Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (by exact_mod_cast hh i) _
  refine ⟨G.natAbs, fun i => ?_, ?_, fun h hh => ?_⟩
  · have := Int.natAbs_dvd_natAbs.mpr (dvdAll i)
    simpa using this
  · rcases Int.natAbs_eq G with hpos | hneg
    · exact ⟨c, by rw [← hpos, hc]⟩
    · refine ⟨fun i => - c i, ?_⟩
      have : (G.natAbs : ℤ) = -G := by omega
      rw [this, hc, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  · have := Int.natAbs_dvd_natAbs.mpr (bezG h hh)
    simpa using this

/-- **Disjoint frequent classes of cells realize the multi-generator progression.**
Cells in class `F j` have the increment `d j` (`base c + d j ∈ lengths c`); the
classes are pairwise disjoint.  Then `closing + Σ base + o + Σ_j t_j d_j` is
realized for every offset `o` and every `t_j ≤ |F j|`. -/
theorem System.realized_multiProgression {cells : Nat} (S : System cells)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (base : Fin cells → Nat) (baseMem : ∀ i, base i ∈ S.lengths i)
    (d : ι → ℕ) (F : ι → Finset (Fin cells))
    (increment : ∀ j, ∀ c ∈ F j, base c + d j ∈ S.lengths c)
    (disjoint : ∀ j j', j ≠ j' → Disjoint (F j) (F j'))
    (o : Nat) (oMem : o ∈ S.offsets) (t : ι → ℕ) (tLe : ∀ j, t j ≤ (F j).card) :
    S.Realized (S.closing + (∑ i, base i) + o + ∑ j, t j * d j) := by
  classical
  have chosenEx : ∀ j, ∃ ch : Finset (Fin cells), ch ⊆ F j ∧ ch.card = t j :=
    fun j => Finset.exists_subset_card_eq (tLe j)
  choose ch chSub chCard using chosenEx
  let choice : Fin cells → Nat := fun c => base c + ∑ j, if c ∈ ch j then d j else 0
  have choiceMem : ∀ c, choice c ∈ S.lengths c := by
    intro c
    by_cases ex : ∃ j, c ∈ ch j
    · obtain ⟨j0, hj0⟩ := ex
      have single : (∑ j, if c ∈ ch j then d j else 0) = d j0 := by
        rw [Finset.sum_eq_single j0]
        · simp [hj0]
        · intro j _ hne
          have : c ∉ ch j := fun hc =>
            Finset.disjoint_left.mp (disjoint j j0 hne) (chSub j hc) (chSub j0 hj0)
          simp [this]
        · simp
      simp only [choice, single]
      exact increment j0 c (chSub j0 hj0)
    · have zero : (∑ j, if c ∈ ch j then d j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have : c ∉ ch j := fun hc => ex ⟨j, hc⟩
        simp [this]
      simp only [choice, zero, add_zero]
      exact baseMem c
  have sumEq : (∑ c, choice c) = (∑ i, base i) + ∑ j, t j * d j := by
    simp only [choice, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, chCard j, smul_eq_mul]
  have := S.realized_route choice choiceMem o oMem
  rw [sumEq] at this
  have eq : S.closing + ((∑ i, base i) + ∑ j, t j * d j) + o =
      S.closing + (∑ i, base i) + o + ∑ j, t j * d j := by ring
  rw [eq] at this
  exact this

/-! ## The canonical full-modulus data of a serial system

Everything below is fixed by the serial system's own lengths: `cellBase` is the
shortest length of a cell, `cellIncrement` the gap to its next length, the
frequent increments are the values in `[1, D]` occurring at `≥ D` cells, `g` their
gcd, `smear` the longest initial segment of offsets, and the spectrum is the
Frobenius filling of the central range. -/

namespace System

variable {cells : Nat} (S : System cells) (hne : ∀ i, (S.lengths i).Nonempty)

/-- The shortest length of a cell. -/
noncomputable def cellBase (i : Fin cells) : ℕ := (S.lengths i).min' (hne i)

theorem cellBase_mem (i : Fin cells) : S.cellBase hne i ∈ S.lengths i :=
  Finset.min'_mem _ _

/-- The gap from the shortest length of a cell to its next length (`0` if the
cell has a single length). -/
noncomputable def cellIncrement (i : Fin cells) : ℕ :=
  open Classical in
  if h : ((S.lengths i).filter (fun x => S.cellBase hne i < x)).Nonempty then
    ((S.lengths i).filter (fun x => S.cellBase hne i < x)).min' h - S.cellBase hne i
  else 0

/-- The cells whose next length is `v` above their shortest one. -/
noncomputable def incrementClass (v : ℕ) : Finset (Fin cells) := by
  classical
  exact Finset.univ.filter (fun i => S.cellIncrement hne i = v)

theorem increment_mem {v : ℕ} (hv : 1 ≤ v) {c : Fin cells}
    (hc : c ∈ S.incrementClass hne v) :
    S.cellBase hne c + v ∈ S.lengths c := by
  classical
  have eq : S.cellIncrement hne c = v := by
    simpa [incrementClass] using hc
  unfold cellIncrement at eq
  split at eq
  · next h =>
    have mem := Finset.min'_mem _ h
    have lt := (Finset.mem_filter.mp mem).2
    have : S.cellBase hne c + v = ((S.lengths c).filter (fun x => S.cellBase hne c < x)).min' h := by
      omega
    rw [this]
    exact (Finset.mem_filter.mp mem).1
  · omega

theorem incrementClass_disjoint {v v' : ℕ} (h : v ≠ v') :
    Disjoint (S.incrementClass hne v) (S.incrementClass hne v') := by
  classical
  rw [Finset.disjoint_left]
  intro c hc hc'
  simp only [incrementClass, Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
  exact h (hc.symm.trans hc')

/-- The frequent increments: the values in `[1, D]` that occur at `≥ D` cells. -/
noncomputable def frequentValues (D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 D).filter (fun v => D ≤ (S.incrementClass hne v).card)

/-- The longest initial segment `{0, …, smear}` of the offsets. -/
noncomputable def canonicalSmear : ℕ :=
  Nat.findGreatest (fun s => ∀ r ≤ s, r ∈ S.offsets) (S.offsets.sup id)

theorem canonicalSmear_spec (zero : 0 ∈ S.offsets) :
    ∀ r ≤ S.canonicalSmear, r ∈ S.offsets :=
  Nat.findGreatest_spec (P := fun s => ∀ r ≤ s, r ∈ S.offsets) (Nat.zero_le _)
    (fun r hr => by
      have : r = 0 := Nat.le_zero.mp hr
      subst this; exact zero)

/-- **The full-modulus data of a serial system** at threshold `D`, with `g` the gcd
of the frequent increments. -/
structure FullModulus (D : ℕ) where
  values : Finset ℕ
  values_eq : values = S.frequentValues hne D
  values_nonempty : values.Nonempty
  /-- the modulus: the gcd of the frequent increments -/
  modulus : ℕ
  modulus_dvd : ∀ v : {v // v ∈ values}, modulus ∣ v.1
  modulus_bezout : ∃ c : {v // v ∈ values} → ℤ,
    (modulus : ℤ) = ∑ v, (v.1 : ℤ) * c v
  modulus_pos : 0 < modulus

/-- The canonical full-modulus data exists whenever some increment is frequent. -/
noncomputable def fullModulus (D : ℕ) (nonempty : (S.frequentValues hne D).Nonempty) :
    FullModulus S hne D := by
  classical
  let d : {v // v ∈ S.frequentValues hne D} → ℕ := fun v => v.1
  have spec := Classical.choose_spec (exists_gcd_data d)
  have pos : ∀ v : {v // v ∈ S.frequentValues hne D}, 0 < d v := fun v => by
    have := (Finset.mem_filter.mp v.2).1
    exact (Finset.mem_Icc.mp this).1
  let v0 : {v // v ∈ S.frequentValues hne D} := ⟨nonempty.choose, nonempty.choose_spec⟩
  exact
    { values := S.frequentValues hne D
      values_eq := rfl
      values_nonempty := nonempty
      modulus := Classical.choose (exists_gcd_data d)
      modulus_dvd := spec.1
      modulus_bezout := spec.2.1
      modulus_pos := Nat.pos_of_ne_zero fun h => by
        have := spec.1 v0
        rw [h] at this
        exact (pos v0).ne' (Nat.eq_zero_of_zero_dvd this) }

end System

namespace System

variable {cells : Nat} (S : System cells) (hne : ∀ i, (S.lengths i).Nonempty)

/-- The number of cells with increment `v`. -/
noncomputable def cap (v : ℕ) : ℕ := (S.incrementClass hne v).card

namespace FullModulus

variable {S hne} {D : ℕ} (fm : S.FullModulus hne D)

theorem mem_values {v : ℕ} (hv : v ∈ fm.values) : 1 ≤ v ∧ v ≤ D ∧ D ≤ S.cap hne v := by
  rw [fm.values_eq] at hv
  unfold frequentValues at hv
  have := Finset.mem_filter.mp hv
  exact ⟨(Finset.mem_Icc.mp this.1).1, (Finset.mem_Icc.mp this.1).2, this.2⟩

/-- The distinguished generator: the least frequent increment. -/
noncomputable def leastValue : {v // v ∈ fm.values} :=
  ⟨fm.values.min' fm.values_nonempty, Finset.min'_mem _ _⟩

/-- The lower end of the central range, in steps of `g`. -/
noncomputable def lowerStep : ℕ :=
  (fm.leastValue.1 * ∑ v ∈ Finset.univ.erase fm.leastValue, v.1) / fm.modulus + 1

/-- The upper end of the central range, in steps of `g`. -/
noncomputable def upperStep : ℕ := fm.leastValue.1 * S.cap hne fm.leastValue.1 / fm.modulus

/-- **The full-modulus spectrum**: the Frobenius filling of the central range
`[lowerStep, upperStep]` in steps of the gcd `g`, at the offsets `0, …, smear`. -/
noncomputable def spectrum (zero : 0 ∈ S.offsets) : Spectrum where
  base := S.closing + ∑ i, S.cellBase hne i
  modulus := fm.modulus
  smear := S.canonicalSmear
  lower := fm.lowerStep
  upper := fm.upperStep
  Realized := S.Realized
  realized_of_mem := by
    classical
    intro residue residueLe step lowerLe leUpper
    have gPos := fm.modulus_pos
    let d : {v // v ∈ fm.values} → ℕ := fun v => v.1
    have hpos : ∀ v, 0 < d v := fun v => (fm.mem_values v.2).1
    have lowerBound : (fm.leastValue.1 * ∑ v ∈ Finset.univ.erase fm.leastValue, v.1) ≤
        step * fm.modulus := by
      have h1 := Nat.lt_mul_div_succ
        (fm.leastValue.1 * ∑ v ∈ Finset.univ.erase fm.leastValue, v.1) gPos
      have h2 : fm.modulus * ((fm.leastValue.1 * ∑ v ∈ Finset.univ.erase fm.leastValue, v.1) /
          fm.modulus + 1) ≤ fm.modulus * step := Nat.mul_le_mul_left _ lowerLe
      rw [mul_comm step]
      exact h1.le.trans h2
    have upperBound : step * fm.modulus ≤ fm.leastValue.1 * S.cap hne fm.leastValue.1 := by
      calc step * fm.modulus ≤ (fm.leastValue.1 * S.cap hne fm.leastValue.1 / fm.modulus) *
            fm.modulus := Nat.mul_le_mul_right _ leUpper
        _ ≤ _ := Nat.div_mul_le_self _ _
    obtain ⟨t, tLe, tSum⟩ := frobenius_fill d hpos fm.leastValue fm.modulus fm.modulus_bezout
      (fun v => S.cap hne v.1)
      (fun v hv => by
        have h1 := (fm.mem_values v.2).2.2
        have h2 := (fm.mem_values fm.leastValue.2).2.1
        show fm.leastValue.1 ≤ S.cap hne v.1 + 1
        omega)
      (step * fm.modulus) (dvd_mul_left _ _) lowerBound upperBound
    have := S.realized_multiProgression (fun i => S.cellBase hne i)
      (fun i => S.cellBase_mem hne i) d (fun v => S.incrementClass hne v.1)
      (fun v c hc => S.increment_mem hne (hpos v) hc)
      (fun v v' hne' => S.incrementClass_disjoint hne (fun h => hne' (Subtype.ext h)))
      residue (S.canonicalSmear_spec zero residue residueLe) t tLe
    rw [tSum] at this
    exact this

end FullModulus

/-- **The full-modulus arithmetic arm of `lem:pair-system-increment-arithmetic`,
built from the serial system.**  Some increment is frequent; the offsets contain
`0`; with the canonical smear `s` and gcd modulus `g`, `s + 1 ≤ g`,
`g − (s+1) < ord_g(2)`, and the Frobenius-filled central range contains a full
doubling orbit. -/
def FullModulusArithmetic (D : ℕ) : Prop :=
  ∃ (nonempty : (S.frequentValues hne D).Nonempty) (zero : 0 ∈ S.offsets),
    S.canonicalSmear + 1 ≤ (S.fullModulus hne D nonempty).modulus ∧
    (S.fullModulus hne D nonempty).modulus - (S.canonicalSmear + 1) <
      orderOf (2 : ZMod (S.fullModulus hne D nonempty).modulus) ∧
    @Spectrum.ScaleSpanning ((S.fullModulus hne D nonempty).spectrum zero)
      ⟨(S.fullModulus hne D nonempty).modulus_pos.ne'⟩

/-- The full-modulus arithmetic realizes a power of two. -/
theorem FullModulusArithmetic.exists_pow_realized {D : ℕ}
    (h : S.FullModulusArithmetic hne D) : ∃ k, S.Realized (2 ^ k) := by
  obtain ⟨nonempty, zero, wide, criterion, spanning⟩ := h
  letI : NeZero ((S.fullModulus hne D nonempty).spectrum zero).modulus :=
    ⟨(S.fullModulus hne D nonempty).modulus_pos.ne'⟩
  exact Spectrum.exists_pow_realized ((S.fullModulus hne D nonempty).spectrum zero)
    wide criterion spanning

end System

end Hypostructure.Graph.SerialSystem
