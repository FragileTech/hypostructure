import Hypostructure.Graph.ColdCorridor

/-!
# `lem:cold-increment-arithmetic`: the finite arithmetic of a germ's increment

A homogeneous cold germ of increment `δ` attains the length blocks
`[L + jδ, L + jδ + smear]`, one per number `j` of homogeneous copies, where
`smear` is the cold-window offset range `order − 1` that
`lem:cold-short-self-return-filter` already smears a self-return over.  The
manuscript exhausts the arithmetic of those blocks in four cases, and this
module proves each of them.

Everything here is arithmetic on `Nat`: the accepted-length predicate is a
parameter, no window, corridor, germ, or graph appears, and the manuscript's
`13` is `smear + 1` at whatever window order is registered.  The bridge back to
the germs is `ColdCorridor.SurvivesSmear`, which is the same filter
`lem:cold-short-self-return-filter` is stated with -- a block that does *not*
survive supplies the offset closing an accepted cycle, which is the trichotomy's
G1.
-/

namespace Hypostructure.Graph.ColdCorridor

/-! ## Case (a): `1 ≤ δ ≤ smear + 1`, the blocks overlap

*"If `1 ≤ δ ≤ 12`, then the achievable length blocks `[L+jδ, L+jδ+12]`
`(0 ≤ j ≤ N)` overlap … Hence their union is an interval."*

Consecutive blocks overlap because the next one begins at `L + (j+1)δ ≤
L + jδ + smear`, so every length of `[L, L + Nδ + smear]` lies in some block.
An interval containing an accepted length gives G1; if it contains none, the
whole family lies in one bounded gap. -/

/-- **The union of the overlapping blocks is the interval `[L, L + Nδ + smear]`.**
Every length of that interval lies in one of the `N + 1` blocks. -/
theorem exists_block_of_mem_interval {smear increment base copies length : Nat}
    (positive : 0 < increment) (overlapping : increment ≤ smear + 1)
    (lower : base ≤ length) (upper : length ≤ base + copies * increment + smear) :
    ∃ j ≤ copies, base + j * increment ≤ length ∧
      length ≤ base + j * increment + smear := by
  have division : increment * ((length - base) / increment) +
      (length - base) % increment = length - base :=
    Nat.div_add_mod _ _
  have remainder : (length - base) % increment < increment :=
    Nat.mod_lt _ positive
  have quotientComm : increment * ((length - base) / increment) =
      (length - base) / increment * increment := Nat.mul_comm _ _
  refine ⟨min copies ((length - base) / increment), Nat.min_le_left _ _, ?_, ?_⟩
  · rcases Nat.le_total ((length - base) / increment) copies with small | large
    · rw [Nat.min_eq_right small]
      omega
    · rw [Nat.min_eq_left large]
      have bounded : copies * increment ≤ (length - base) / increment * increment :=
        Nat.mul_le_mul_right increment large
      omega
  · rcases Nat.le_total ((length - base) / increment) copies with small | large
    · rw [Nat.min_eq_right small]
      omega
    · rw [Nat.min_eq_left large]
      omega

/-- **Case (a), the G1 half.**  If the interval the overlapping blocks cover
contains an accepted length, then one block fails the smear filter -- and a
block that fails it supplies the cold-window offset closing an accepted cycle,
which is the trichotomy's G1. -/
theorem exists_not_survivesSmear_of_mem_interval {LengthOK : Nat → Prop}
    {smear increment base copies length : Nat}
    (positive : 0 < increment) (overlapping : increment ≤ smear + 1)
    (lower : base ≤ length) (upper : length ≤ base + copies * increment + smear)
    (accepted : LengthOK length) :
    ∃ j ≤ copies, ¬ SurvivesSmear LengthOK smear (base + j * increment) := by
  obtain ⟨j, small, blockLower, blockUpper⟩ :=
    exists_block_of_mem_interval positive overlapping lower upper
  exact ⟨j, small, fun survives => survives length blockLower blockUpper accepted⟩

/-! ## Case (b): `δ ≥ smear + 1` and the doubling orbit hits a smear residue

*"If `δ ≥ 13` and the doubling orbit modulo `δ` hits one of the thirteen smear
residues `L, L+1, …, L+12`, the branch is G1."*

*"A congruence `2^k ≡ L + r (mod δ)` with `0 ≤ r ≤ 12` means that, after adding
the appropriate number of homogeneous copies, one attainable length is `2^k`.
This is exactly a hit-realized germ."* -/

/-- **Case (b), the attainable block.**  A power of two congruent to a smear
residue and at least as large as it is attained by the block of the
corresponding number of homogeneous copies. -/
theorem exists_block_of_pow_congruent {smear increment base exponent residue : Nat}
    (positive : 0 < increment) (small : residue ≤ smear)
    (reached : base + residue ≤ 2 ^ exponent)
    (congruent : 2 ^ exponent % increment = (base + residue) % increment) :
    ∃ j, base + j * increment ≤ 2 ^ exponent ∧
      2 ^ exponent ≤ base + j * increment + smear := by
  have divides : increment ∣ 2 ^ exponent - (base + residue) :=
    (Nat.modEq_iff_dvd' reached).mp congruent.symm
  obtain ⟨j, difference⟩ := divides
  have comm : increment * j = j * increment := Nat.mul_comm _ _
  exact ⟨j, by omega, by omega⟩

/-- **Case (b), the G1 half.**  The attained power of two, if accepted, makes
its own block fail the smear filter. -/
theorem exists_not_survivesSmear_of_pow_congruent {LengthOK : Nat → Prop}
    {smear increment base exponent residue : Nat}
    (positive : 0 < increment) (small : residue ≤ smear)
    (reached : base + residue ≤ 2 ^ exponent)
    (congruent : 2 ^ exponent % increment = (base + residue) % increment)
    (accepted : LengthOK (2 ^ exponent)) :
    ∃ j, ¬ SurvivesSmear LengthOK smear (base + j * increment) := by
  obtain ⟨j, blockLower, blockUpper⟩ :=
    exists_block_of_pow_congruent positive small reached congruent
  exact ⟨j, fun survives => survives _ blockLower blockUpper accepted⟩

/-! ## The hit criterion `ord_δ(2) > δ − 13`

*"For odd `δ`, the sufficient hit criterion `ord_δ(2) > δ − 13` forces case
(b)."*

*"If `δ` is odd and `ord_δ(2) > δ − 13`, the doubling orbit has more residues
than the complement of the thirteen smear residues.  Therefore it must hit a
smear residue, giving (b)."*

The pigeonhole is exactly that.  The `smear + 1` residues `L, …, L + smear` are
distinct modulo `δ` because `δ ≥ smear + 1`, so their complement has
`δ − (smear + 1)` classes; the doubling orbit contributes `ord_δ(2)` distinct
classes, being injective below the multiplicative order; and an orbit larger
than the complement cannot avoid the residues. -/

/-- **The pigeonhole of the hit criterion**, stated on the orbit itself.

An injective doubling orbit of length exceeding the complement of the smear
residues must meet them.  `pow_injOn_Iio_orderOf` is what supplies the
injectivity at `length = ord_δ(2)`, and `exists_hit_of_orderOf_lt` below is that
instance. -/
theorem exists_hit_of_injective {increment base smear length : Nat}
    (wide : smear + 1 ≤ increment)
    (injective : ∀ i < length, ∀ j < length,
      2 ^ i % increment = 2 ^ j % increment → i = j)
    (large : increment - (smear + 1) < length) :
    ∃ k < length, ∃ residue ≤ smear,
      2 ^ k % increment = (base + residue) % increment := by
  classical
  have positive : 0 < increment := by omega
  by_contra missing
  push_neg at missing
  -- The orbit classes and the smear classes, as subsets of `Fin increment`.
  set orbit : Finset (Fin increment) :=
    (Finset.range length).image
      (fun k => (⟨2 ^ k % increment, Nat.mod_lt _ positive⟩ : Fin increment))
    with orbitDef
  set residues : Finset (Fin increment) :=
    (Finset.range (smear + 1)).image
      (fun r => (⟨(base + r) % increment, Nat.mod_lt _ positive⟩ : Fin increment))
    with residuesDef
  have orbitCard : orbit.card = length := by
    rw [orbitDef, Finset.card_image_of_injOn, Finset.card_range]
    intro i iMem j jMem same
    simp only [Finset.coe_range, Set.mem_Iio] at iMem jMem
    exact injective i iMem j jMem (congrArg Fin.val same)
  -- The `smear + 1` smear residues are distinct classes, because the width
  -- hypothesis `smear + 1 ≤ increment` keeps them inside one period.
  have residuesCard : residues.card = smear + 1 := by
    rw [residuesDef, Finset.card_image_of_injOn, Finset.card_range]
    intro left leftMem right rightMem same
    simp only [Finset.coe_range, Set.mem_Iio] at leftMem rightMem
    have shifted : (base + left) % increment = (base + right) % increment :=
      congrArg Fin.val same
    have cancelled : left % increment = right % increment :=
      Nat.ModEq.add_left_cancel' base shifted
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at cancelled
    exact cancelled
  have disjointSets : Disjoint orbit residues := by
    rw [Finset.disjoint_left]
    intro value valueOrbit valueResidues
    rw [orbitDef, Finset.mem_image] at valueOrbit
    rw [residuesDef, Finset.mem_image] at valueResidues
    obtain ⟨k, kMem, kValue⟩ := valueOrbit
    obtain ⟨r, rMem, rValue⟩ := valueResidues
    rw [Finset.mem_range] at kMem rMem
    exact missing k kMem r (by omega)
      (congrArg Fin.val (kValue.trans rValue.symm))
  have total : (orbit ∪ residues).card ≤ Fintype.card (Fin increment) :=
    Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint disjointSets, Fintype.card_fin] at total
  omega

/-- **`ord_δ(2) > δ − (smear + 1)` forces case (b).**

The doubling orbit is injective below the multiplicative order of `2` modulo
`δ`, so the previous pigeonhole applies at `length = ord_δ(2)` and the orbit
hits one of the smear residues.  Nothing is assumed of `δ` beyond the width
`smear + 1 ≤ δ`: for even `δ` the order of `2` is zero and the criterion is
unsatisfiable, which is why the manuscript states the criterion for odd `δ` and
reduces the even case to its odd part below. -/
theorem exists_hit_of_orderOf_lt {increment base smear : Nat} [NeZero increment]
    (wide : smear + 1 ≤ increment)
    (criterion : increment - (smear + 1) < orderOf (2 : ZMod increment)) :
    ∃ k < orderOf (2 : ZMod increment), ∃ residue ≤ smear,
      2 ^ k % increment = (base + residue) % increment := by
  refine exists_hit_of_injective wide ?_ criterion
  intro i iLt j jLt same
  have cast : ((2 : ZMod increment)) ^ i = ((2 : ZMod increment)) ^ j := by
    have left : ((2 : ZMod increment)) ^ i = ((2 ^ i : Nat) : ZMod increment) := by
      push_cast
      rfl
    have right : ((2 : ZMod increment)) ^ j = ((2 ^ j : Nat) : ZMod increment) := by
      push_cast
      rfl
    rw [left, right, ZMod.natCast_eq_natCast_iff']
    exact same
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr iLt) (Set.mem_Iio.mpr jLt) cast

/-! ## The even transient

*"For even `δ = 2^a u`, the same criterion applies to the odd part `u` after the
bounded transient `k < a`."*

*"If `δ = 2^a u`, the initial powers with `k < a` form a bounded transient, and
for `k ≥ a` the congruence reduces to the odd modulus `u`."*

That reduction is an exact identity, not an approximation: past the transient
the residue modulo `2^a u` is `2^a` times the residue modulo `u`. -/

/-- **Past the transient, the doubling orbit modulo `2^a u` is `2^a` times the
doubling orbit modulo `u`.** -/
theorem pow_mod_of_le {transient exponent odd : Nat} (past : transient ≤ exponent) :
    2 ^ exponent % (2 ^ transient * odd) =
      2 ^ transient * (2 ^ (exponent - transient) % odd) := by
  rw [show exponent = transient + (exponent - transient) by omega, pow_add,
    Nat.add_sub_cancel_left, Nat.mul_mod_mul_left]

end Hypostructure.Graph.ColdCorridor
