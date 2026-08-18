import Hypostructure.Graph.ColdIncrementArithmetic

/-!
# Serial-system increment arithmetic (nodes `[172]` and `[180]`)

`lem:system-increment-arithmetic` and its strict-branch twin
`lem:pair-system-increment-arithmetic` close a *scale-spanning serial system*:
by `lem:serial-system-sumset` its realizable cycle-length spectrum contains, for
every offset residue `r ≤ smear` and every `t` in a central range `[C, T]`, the
length `L + r + t·g`, where `g` is the gcd of the frequent increments; the
doubling-orbit criterion of `lem:cold-increment-arithmetic` then produces a
power of two inside the spectrum (case (a)); otherwise the residue map is a
periodic carrier (case (b), routed at the graph level).

This module is the arithmetic core, stated on `Nat` with the realizable
spectrum as a predicate: no graph, corridor, window, or demand appears.  The
manuscript's "scale-spanning" hypothesis is read exactly as: some full doubling
orbit `k₀, …, k₀ + ord_g(2) − 1`, with `ord_g(2) ∣ k₀` (so `2^{k₀} ≡ 1 (mod g)`),
has all its powers inside the central range of the spectrum.  Under the hit
criterion `g − (smear+1) < ord_g(2)` of `exists_hit_of_orderOf_lt`, some `2^k`
of that orbit is congruent to `L + r` for an offset `r ≤ smear`, hence is a
displayed length and is realized.
-/

namespace Hypostructure.Graph.SerialSystem

/-- **A serial spectrum**: the central sumset interval of
`lem:serial-system-sumset`, read as a predicate on lengths.  `base` is the
shortest system length `L`, `modulus` the gcd `g` of the frequent increments,
`smear` the offset range (`12` at the manuscript's window order; the port-return
offsets on the strict branch), and the spectrum contains every `L + r + t·g`
with `r ≤ smear` and `lower ≤ t ≤ upper`. -/
structure Spectrum where
  /-- The shortest system length `L`. -/
  base : Nat
  /-- The gcd `g` of the frequent increments. -/
  modulus : Nat
  /-- The offset range: residues `0, …, smear` are all realized. -/
  smear : Nat
  /-- The central range `[lower, upper]` of `g`-steps. -/
  lower : Nat
  upper : Nat
  /-- The realizable lengths (actual simple cycles of the object). -/
  Realized : Nat → Prop
  /-- `lem:serial-system-sumset`: every displayed length is realized. -/
  realized_of_mem : ∀ residue ≤ smear, ∀ step, lower ≤ step → step ≤ upper →
    Realized (base + residue + step * modulus)

namespace Spectrum

/-- **Scale-spanning**: a full doubling orbit `k₀, …, k₀ + ord − 1`, with
`ord ∣ k₀`, lies inside the central range of the spectrum. -/
def ScaleSpanning (S : Spectrum) [NeZero S.modulus] : Prop :=
  ∃ start : Nat, orderOf (2 : ZMod S.modulus) ∣ start ∧
    ∀ i < orderOf (2 : ZMod S.modulus),
      S.base + S.lower * S.modulus ≤ 2 ^ (start + i) ∧
        2 ^ (start + i) ≤ S.base + S.upper * S.modulus

/-- A number in the central range that is congruent to `L + r` modulo `g`
(`r ≤ smear < g`) is a displayed length, hence realized. -/
theorem realized_of_congruent (S : Spectrum) [NeZero S.modulus]
    (narrow : S.smear < S.modulus) {length residue : Nat}
    (residueLe : residue ≤ S.smear)
    (congruent : length % S.modulus = (S.base + residue) % S.modulus)
    (lowerLe : S.base + S.lower * S.modulus ≤ length)
    (leUpper : length ≤ S.base + S.upper * S.modulus) :
    S.Realized length := by
  have posMod : 0 < S.modulus := Nat.pos_of_ne_zero (NeZero.ne _)
  have residueLt : residue < S.modulus := lt_of_le_of_lt residueLe narrow
  set d := length - S.base with hd
  have baseLe : S.base ≤ length := le_trans (Nat.le_add_right _ _) lowerLe
  have lengthEq : length = S.base + d := by omega
  -- `d ≡ residue (mod g)`.
  have dMod : d % S.modulus = residue := by
    have hm : (S.base + d) ≡ (S.base + residue) [MOD S.modulus] := by
      rw [← lengthEq]; exact congruent
    have hd' : d ≡ residue [MOD S.modulus] := Nat.ModEq.add_left_cancel' _ hm
    have : d % S.modulus = residue % S.modulus := hd'
    rw [this, Nat.mod_eq_of_lt residueLt]
  -- The step `q := d / g` lies in `[lower, upper]`.
  set q := d / S.modulus with hq
  have dEq : d = q * S.modulus + residue := by
    have h := Nat.div_add_mod d S.modulus
    rw [dMod, ← hq, Nat.mul_comm S.modulus q] at h
    omega
  have lowerLeq : S.lower ≤ q := by
    by_contra lt
    push_neg at lt
    have : (q + 1) * S.modulus ≤ S.lower * S.modulus := Nat.mul_le_mul_right _ lt
    have : d < S.lower * S.modulus := by nlinarith
    omega
  have qLeUpper : q ≤ S.upper := by
    by_contra lt
    push_neg at lt
    have : (S.upper + 1) * S.modulus ≤ q * S.modulus := Nat.mul_le_mul_right _ lt
    have : S.upper * S.modulus < d := by nlinarith
    omega
  have := S.realized_of_mem residue residueLe q lowerLeq qLeUpper
  have eq : S.base + residue + q * S.modulus = length := by omega
  rw [eq] at this
  exact this

/-- **`lem:system-increment-arithmetic` (a) / `lem:pair-system-increment-arithmetic`
(a)**: on a scale-spanning serial spectrum whose modulus satisfies the doubling
orbit criterion `g − (smear+1) < ord_g(2)`, some power of two is a realized
length. -/
theorem exists_pow_realized (S : Spectrum) [NeZero S.modulus]
    (wide : S.smear + 1 ≤ S.modulus)
    (criterion : S.modulus - (S.smear + 1) < orderOf (2 : ZMod S.modulus))
    (spanning : S.ScaleSpanning) :
    ∃ k, S.Realized (2 ^ k) := by
  obtain ⟨start, dvd, inRange⟩ := spanning
  obtain ⟨i, iLt, residue, residueLe, congruent⟩ :=
    Graph.ColdCorridor.exists_hit_of_orderOf_lt (increment := S.modulus)
      (base := S.base) (smear := S.smear) wide criterion
  refine ⟨start + i, ?_⟩
  -- `2^{start} ≡ 1 (mod g)` because `ord ∣ start`.
  have posMod : 0 < S.modulus := Nat.pos_of_ne_zero (NeZero.ne _)
  have unitPow : ((2 : ZMod S.modulus)) ^ start = 1 := by
    obtain ⟨c, hc⟩ := dvd
    rw [hc, pow_mul, pow_orderOf_eq_one, one_pow]
  have shift : 2 ^ (start + i) % S.modulus = 2 ^ i % S.modulus := by
    have cast : ((2 ^ (start + i) : Nat) : ZMod S.modulus) = ((2 ^ i : Nat) : ZMod S.modulus) := by
      push_cast
      rw [pow_add, unitPow, one_mul]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 cast
  have congruent' : 2 ^ (start + i) % S.modulus = (S.base + residue) % S.modulus := by
    rw [shift, congruent]
  obtain ⟨lowerLe, leUpper⟩ := inRange i iLt
  exact S.realized_of_congruent (lt_of_lt_of_le (Nat.lt_succ_self _) wide) residueLe
    congruent' lowerLe leUpper

end Spectrum

end Hypostructure.Graph.SerialSystem

namespace Hypostructure.Graph.SerialSystem

/-! ## Serial systems and their spectra (`def:serial-window-system`, `lem:serial-system-sumset`)

A serial system has ordered cells; at each cell a nonempty finite set of
corridor lengths; two fixed closing pieces; and a set of available offsets.
Choosing one length per cell and one offset closes an actual simple cycle
(`lem:window-system-realizability` (v)), which is the `realized_route` field.
`lem:serial-system-sumset` reads the realizable spectrum as a central sumset
interval; the case proved here is its first step — a frequent increment `g`
occurring at `M` distinct cells fills the progression `L + r + t·g`,
`0 ≤ t ≤ M`, `r ≤ smear` — which is a `Spectrum` and feeds
`Spectrum.exists_pow_realized`.  The Frobenius filling with several frequent
generators (`g = gcd`) is the manuscript's remaining sentence of that lemma. -/
structure System (cells : Nat) where
  /-- The corridor lengths available at each cell. -/
  lengths : Fin cells → Finset Nat
  /-- The two fixed closing pieces. -/
  closing : Nat
  /-- The available offsets. -/
  offsets : Finset Nat
  /-- The realizable cycle lengths (actual simple cycles of the object). -/
  Realized : Nat → Prop
  /-- `lem:window-system-realizability` (v): every choice of one corridor per
  cell and one offset closes a simple cycle. -/
  realized_route : ∀ choice : Fin cells → Nat, (∀ i, choice i ∈ lengths i) →
    ∀ offset ∈ offsets, Realized (closing + (∑ i, choice i) + offset)

namespace System

variable {cells : Nat} (S : System cells)

/-- **The frequent-increment progression.**  If a base corridor `base i` is
available at every cell, the increment `g` is available at each of `M` cells
(`base i + g ∈ lengths i`), and the offsets `0, …, smear` are all available,
then every `L + r + t·g` with `r ≤ smear`, `t ≤ M` is realized, where
`L = closing + Σ base`. -/
theorem realized_progression (base : Fin cells → Nat)
    (baseMem : ∀ i, base i ∈ S.lengths i) (g : Nat) (frequent : Finset (Fin cells))
    (increment : ∀ i ∈ frequent, base i + g ∈ S.lengths i)
    (smear : Nat) (offsets : ∀ r ≤ smear, r ∈ S.offsets)
    (residue : Nat) (residueLe : residue ≤ smear) (step : Nat) (stepLe : step ≤ frequent.card) :
    S.Realized (S.closing + (∑ i, base i) + residue + step * g) := by
  classical
  obtain ⟨chosen, chosenSub, chosenCard⟩ := Finset.exists_subset_card_eq stepLe
  let choice : Fin cells → Nat := fun i => base i + if i ∈ chosen then g else 0
  have choiceMem : ∀ i, choice i ∈ S.lengths i := by
    intro i
    by_cases mem : i ∈ chosen
    · simpa [choice, mem] using increment i (chosenSub mem)
    · simpa [choice, mem] using baseMem i
  have sumEq : (∑ i, choice i) = (∑ i, base i) + step * g := by
    simp only [choice, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, chosenCard, smul_eq_mul]
  have := S.realized_route choice choiceMem residue (offsets residue residueLe)
  rw [sumEq] at this
  have eq : S.closing + ((∑ i, base i) + step * g) + residue =
      S.closing + (∑ i, base i) + residue + step * g := by ring
  rw [eq] at this
  exact this

/-- The spectrum of a serial system with a frequent increment. -/
noncomputable def spectrum (base : Fin cells → Nat)
    (baseMem : ∀ i, base i ∈ S.lengths i) (g : Nat) (frequent : Finset (Fin cells))
    (increment : ∀ i ∈ frequent, base i + g ∈ S.lengths i)
    (smear : Nat) (offsets : ∀ r ≤ smear, r ∈ S.offsets) : Spectrum where
  base := S.closing + ∑ i, base i
  modulus := g
  smear := smear
  lower := 0
  upper := frequent.card
  Realized := S.Realized
  realized_of_mem := fun residue residueLe step _ stepLe =>
    S.realized_progression base baseMem g frequent increment smear offsets residue residueLe
      step stepLe

end System

end Hypostructure.Graph.SerialSystem
