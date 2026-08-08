import Hypostructure.Graph.TypeBFanIncidence
import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.TypeBRefinedSupport
import Hypostructure.Graph.TypeADischarge

/-!
# The augmented Type B fan-envelope charge

`def:typeB-assigned-ledger` measures an assigned Type B support with two
charges: a core vertex by `ch_X(y) = max{0, δ − d(y)} − α` and an assigned
high-degree centre by `ch_X(h) = −(d_G(h) − δ) − α`, where `α = 1/s` is one
discharge unit.  Both are carried at the scale `s` below, so no reciprocal is
ever written and the truncation is `Nat` subtraction.  There is no third charge
formula: the fan estimates read the core charge against the assigned envelope
`E_h` and the accounting identity reads it against the counted core `Y_X`, which
is the one parameter that distinguishes the manuscript's two uses.

Three manuscript statements are proved from them.

## Step 1 of `lem:typeB-exclusion`: the closed-neighbourhood charge

At a high centre `h` of degree `k` whose assigned envelope contains `N(h)`, the
manuscript computes

  `ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ (δ − (k+1)α) − c = −D_B(𝔉_h)`,

its `(11−k)/4 − c` at `δ = 3`, `α = 1/4`.  The three readings it is assembled
from are exactly the three cases of `d_E`: the centre sees all `k` of its
neighbours, a cubic-closed neighbour sees all `δ` of its own, and every other
fan neighbour misses at least one, so it sits at `d_E ≤ δ − 1` and contributes
at least `s − 1` — the manuscript's "internal degree at most `2` … contributes
at least `3/4`".  So a certificate-closed fan, one with `D_B ≤ 0`, carries
nonnegative closed-neighbourhood charge.

## `lem:typeB-bridge-deficit-bound`: the envelope negative part

The same three readings bound the *negative* part of the envelope: only the
centre and the `c` cubic-closed neighbours are negative, so at the scale `s` the
unpaid part is

  `s·(k − δ) + 1 + c`,

the manuscript's `(k − 3 + 1/4) + c/4`.  With `c ≤ k` this is below
`F·s·(k − δ)` for the registered bridge-mass factor `F` — the manuscript's
`5k/4 − 11/4 ≤ 8(k−3)`, valid because `27k ≥ 85`.  Summing over the assigned
centres of a support and then over the pieces of a decomposition bounds the
envelope mass by `F·S_B`, and `S_B` by the object's own surplus.

## `def:typeB-assigned-ledger`: the identity `(B-ledger)`

`No(X) = Ĉh_B(X) + α|H_X|`, which is what makes `Ĉh_B(X) ≥ 0` the same
statement as `defp(X) − σ(X) ≥ α|V(X)|`.  It is an exact identity of the two
sums, and it is what both `lem:typeB-exclusion` and
`lem:typeB-bridge-deficit-bound` spend their charge estimates on.

Nothing here is specialized to a manuscript: the baseline, the discharge scale
and the mass factor are parameters, and no numeral is written.
-/

namespace Hypostructure.Graph.TypeBEnvelopeCharge

open Hypostructure
open Hypostructure.Graph.TypeBFanIncidence
open Hypostructure.Graph.TypeBRefinedSupport
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

open scoped Classical

/-! ## `def:typeB-assigned-ledger`: the two vertex charges

The manuscript measures a core vertex and an assigned centre by different
formulas, and both are used below:

  `ch_X(y) = max{0, δ − d(y)} − α`   for a core vertex,
  `ch_X(h) = −(d_G(h) − δ) − α`      for an assigned centre,

carried at the scale `s`, so `α = 1/s` never appears as a reciprocal and the
truncation is `Nat` subtraction.  The set the core degree is read against is a
parameter: the accounting identity reads it against the counted core `Y_X`, and
the fan estimates read it against the assigned envelope `E_h`, which is the
manuscript's own "internal degree at most `2` **in the assigned fan
envelope**". -/

/-! ## `def:typeB-assigned-ledger`: the augmented ledger and `(B-ledger)`

The two readings of `def:typeB-assigned-ledger` are distinct and the manuscript
uses both.  The *envelope* reading above measures a fan vertex against the
assigned envelope `E_h`, which is what its per-centre estimates are stated in;
the *core* reading below measures a core vertex against the counted core `Y_X`,
which is what the accounting identity is stated in.  They agree at the centre
and at a cubic-closed neighbour -- the two negative species -- because both see
the same neighbours there.

The core reading is the manuscript's verbatim

  `ch_X(y) = max{0, δ − d_{Y_X}(y)} − α`   for a core vertex,
  `ch_X(h) = −(d_G(h) − δ) − α`            for an assigned centre,

carried at the scale `s`, so `α = 1/s` never appears as a reciprocal and the
truncation is `Nat` subtraction. -/

/-- **`σ(X) = Σ_{h ∈ H_X}(d_G(h) − δ)`.**  A vertex of the support that is not
an assigned centre carries no surplus at all, so the assigned centres already
account for the whole of it. -/
theorem sum_centres_surplus (object : FiniteObject.{u}) (threshold : Nat)
    (piece : Finset object.Vertex) :
    ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
        (object.degree centre - threshold) =
      object.ambientSurplus piece threshold := by
  classical
  unfold FiniteObject.ambientSurplus
  refine Finset.sum_subset TypeBRefinedSupport.centres_subset ?_
  intro vertex member notCentre
  have : ¬ IsHighCentre object threshold vertex := fun high =>
    notCentre (TypeBRefinedSupport.mem_centres.mpr ⟨member, high⟩)
  rw [IsHighCentre] at this
  omega

/-- **`(B-ledger)`.**  `No(X) = Ĉh_B(X) + ¼|H_X|`, at the discharge scale, with
`s·No(X) = s·def⁺(X) − s·σ(X) − |V(X)|` spelled out on the right.

The manuscript's own two-line derivation: the core sum is
`def⁺(Y_X) − α|Y_X|` and the centre sum is `−σ(X) − α|H_X|`, and
`def⁺(X) = def⁺(Y_X)`, `|V(X)| = |V(Y_X)|`. -/
theorem augmentedLedger_add_card_centres (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex) :
    augmentedLedger object threshold dischargeScale piece +
        ((TypeBRefinedSupport.centres object threshold piece).card : Int) =
      ((dischargeScale * object.positiveDeficiency piece threshold : Nat) : Int) -
        ((dischargeScale * object.ambientSurplus piece threshold : Nat) : Int) -
        (piece.card : Int) := by
  classical
  have core : ∑ vertex ∈ piece,
      scaledCoreCharge object threshold dischargeScale piece vertex =
        ((dischargeScale * object.positiveDeficiency piece threshold : Nat) : Int) -
          (piece.card : Int) := by
    unfold scaledCoreCharge FiniteObject.positiveDeficiency
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.mul_sum]
    push_cast
    rfl
  have centres : ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
      scaledCentreCharge object threshold dischargeScale centre =
        - ((dischargeScale * object.ambientSurplus piece threshold : Nat) : Int) -
          ((TypeBRefinedSupport.centres object threshold piece).card : Int) := by
    unfold scaledCentreCharge
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have inner : ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
        - ((dischargeScale * (object.degree centre - threshold) : Nat) : Int) =
          - ((dischargeScale * object.ambientSurplus piece threshold : Nat) : Int) := by
      rw [Finset.sum_neg_distrib, ← Nat.cast_sum, ← Finset.mul_sum,
        sum_centres_surplus object threshold piece]
    rw [inner]
  rw [augmentedLedger, core, centres]
  ring

/-- **The consumed consequence of `(B-ledger)`.**  `Ĉh_B(X) ≥ 0` gives
`No(X) ≥ 0`, that is `def⁺(X) − σ(X) ≥ ¼|V(X)|`, which is the last line of
`prop:typeB-bridge-reduction` and of `lem:typeB-exclusion`.

The comparison is the subtraction-free `NonNegativeNetCharge` of
`def:net-charge`, so nothing rounds. -/
theorem nonNegativeNetCharge_of_augmentedLedger_nonneg (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (piece : Finset object.Vertex)
    (nonneg : 0 ≤ augmentedLedger object threshold dischargeScale piece) :
    object.NonNegativeNetCharge piece threshold dischargeScale := by
  have identity :=
    augmentedLedger_add_card_centres object threshold dischargeScale piece
  have counted : ((TypeBRefinedSupport.centres object threshold piece).card : Int) ≤
      (piece.card : Int) := by
    exact_mod_cast Finset.card_le_card
      (TypeBRefinedSupport.centres_subset (threshold := threshold) (piece := piece))
  rw [FiniteObject.NonNegativeNetCharge]
  have cast :
      ((piece.card + dischargeScale * object.ambientSurplus piece threshold : Nat) : Int) ≤
        ((dischargeScale * object.positiveDeficiency piece threshold : Nat) : Int) := by
    push_cast
    push_cast at identity
    linarith [identity, nonneg, counted]
  exact_mod_cast cast

/-- The B2 ledger consequence used by the Type B exclusion row. -/
theorem nonNegativeNetCharge_of_augmentedLedger_add_centres_nonneg
    (object : FiniteObject.{u}) (threshold dischargeScale : Nat)
    (piece : Finset object.Vertex)
    (nonneg :
      0 ≤ augmentedLedger object threshold dischargeScale piece +
        ((TypeBRefinedSupport.centres object threshold piece).card : Int)) :
    object.NonNegativeNetCharge piece threshold dischargeScale := by
  have identity :=
    augmentedLedger_add_card_centres object threshold dischargeScale piece
  rw [FiniteObject.NonNegativeNetCharge]
  have cast :
      ((piece.card + dischargeScale * object.ambientSurplus piece threshold :
          Nat) : Int) ≤
        ((dischargeScale * object.positiveDeficiency piece threshold : Nat) :
          Int) := by
    push_cast
    push_cast at identity nonneg
    linarith
  exact_mod_cast cast

/-- The exact B2 partition gives the exclusion charge once the remaining core
has nonnegative scaled charge. -/
theorem nonNegativeNetCharge_of_disjointLedger_remainingCore_nonneg
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece : TypeBRefinedSupport.CanonicalPiece object packing}
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (exact : ledger.ExactAugmentedLedgerRefinement)
    (remainingNonnegative :
      0 ≤ ∑ vertex ∈ ledger.remainingCore,
        scaledCoreCharge object threshold dischargeScale piece.vertices vertex) :
    object.NonNegativeNetCharge piece.vertices threshold dischargeScale := by
  classical
  have centreCoreNonnegative :
      0 ≤ ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece.vertices,
        (scaledCoreCharge object threshold dischargeScale piece.vertices centre +
          1) := by
    refine Finset.sum_nonneg ?_
    intro centre _member
    rw [scaledCoreCharge]
    have nonneg :
        (0 : Int) ≤
          ((dischargeScale *
            (threshold - object.internalDegree piece.vertices centre) : Nat) :
            Int) := Int.natCast_nonneg _
    linarith
  have selectedNonnegative : 0 ≤ ledger.selectedEntryPayment₂ :=
    exact.selectedNonnegative
  have doubled :
      0 ≤ 2 *
        (augmentedLedger object threshold dischargeScale piece.vertices +
          ((TypeBRefinedSupport.centres object threshold piece.vertices).card :
            Int)) := by
    rw [exact.partition]
    nlinarith
  have ledgerNonnegative :
      0 ≤ augmentedLedger object threshold dischargeScale piece.vertices +
        ((TypeBRefinedSupport.centres object threshold piece.vertices).card :
          Int) := by
    nlinarith
  exact nonNegativeNetCharge_of_augmentedLedger_add_centres_nonneg object
    threshold dischargeScale piece.vertices ledgerNonnegative



/-! ## `lem:typeB-exclusion` Step 2: the canonical B2 refinement -/

/-- The unpaid negative fan-envelope part used by the later bridge-mass
estimate.  It is independent of any ledger representation. -/
noncomputable def envelopeNegativePart (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Nat :=
  dischargeScale * (object.degree centre - threshold) + 1 +
    closedCount object threshold envelope centre

/-- Membership in the finite candidate family exposes the exact local
augmented-ledger refinement; it is not a constructor field. -/
theorem candidate_refines_of_mem
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece : TypeBRefinedSupport.CanonicalPiece object packing}
    {hub : object.Vertex}
    {data : TypeBRefinedSupport.CandidateData object}
    (member : data ∈ TypeBRefinedSupport.candidateFamily object threshold
      dischargeScale piece hub) :
    data.EntryRefines threshold dischargeScale piece hub :=
  (TypeBRefinedSupport.mem_candidateFamily_iff.mp member).2.entryRefines

/-- B2(c) is read directly from the single canonical ledger: every chosen
entry refines the same augmented support ledger, and both its literal carrier
supports and indexed reserve units are pairwise disjoint. -/
theorem disjointLedger_exactAugmentedLedgerRefinement
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece : TypeBRefinedSupport.CanonicalPiece object packing}
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :
    ledger.ExactAugmentedLedgerRefinement :=
  ledger.exactAugmentedLedgerRefinement

/-- The selected entry at a centre has nonnegative exact scaled contribution to
its support's augmented ledger. -/
theorem disjointLedger_entry_refines
    {threshold dischargeScale : Nat}
    {packing : Finset (Finset object.Vertex)}
    {piece : TypeBRefinedSupport.CanonicalPiece object packing}
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) (hub : object.Vertex)
    (member : hub ∈ TypeBRefinedSupport.centres object threshold piece.vertices) :
    (ledger.choice.entry hub member).EntryRefines threshold dischargeScale
      piece hub :=
  ledger.entry_refines hub member

/-! ## `lem:typeB-bridge-deficit-bound`: the residual mass itself

Display (2) and the line after it.  The manuscript removes the fan envelopes and
discharges what is left; the same accounting is available directly on the
support, because the *only* vertices of an assigned Type B support that sit
above the baseline are its assigned centres.  Every other vertex is at the
baseline ambiently, so its core charge is the Type A charge and the discharging
calculation of `lem:typeA-unsaturated-discharge` runs on it unchanged -- with
the centres as the exceptional set, which is exactly the generality
`card_le_scaled_deficiency_off` was stated in.

A centre contributes `−(s(k−δ)+1)` through `ch_X(h)` and at worst `−1` more
through its own core term, so the whole ledger is bounded below by
`−Σ_h (s(k−δ) + 2)`, and the registered mass slack pays that against
`F·s·(k−δ)`.  Nothing here needs the ordinary deficiency reserve: no carrier is
deleted, so no boundary deficit is created. -/

/-- **`Ĉh_B(X) ≥ −Σ_{h∈H_X}(s(d_G(h) − δ) + 2)`.** -/
theorem neg_centreAllowance_le_augmentedLedger (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold dischargeScale : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (routes : ∀ vertex ∈ piece \ TypeBRefinedSupport.centres object threshold piece,
      object.internalDegree piece vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece threshold vertex = some receiver ∧
          object.IsReceiver piece threshold receiver ∧
            receiver ∉ TypeBRefinedSupport.centres object threshold piece)
    (unsaturated : ∀ receiver ∈ object.receivers piece threshold \
        TypeBRefinedSupport.centres object threshold piece,
      1 + object.restrictedLoad piece
          (TypeBRefinedSupport.centres object threshold piece) threshold
          receiver ≤
        dischargeScale * object.missingPorts piece threshold receiver) :
    - ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
          ((dischargeScale * (object.degree centre - threshold) + 2 : Nat) : Int) ≤
      augmentedLedger object threshold dischargeScale piece := by
  classical
  set centres := TypeBRefinedSupport.centres object threshold piece with centresDef
  -- Off the centres every vertex is at the baseline ambiently, so it is capped.
  have capped : ∀ vertex ∈ piece \ centres,
      object.internalDegree piece vertex ≤ threshold := by
    intro vertex member
    obtain ⟨inside, fresh⟩ := Finset.mem_sdiff.mp member
    have notHigh : ¬ IsHighCentre object threshold vertex := fun high =>
      fresh (TypeBRefinedSupport.mem_centres.mpr ⟨inside, high⟩)
    rw [IsHighCentre] at notHigh
    exact le_trans (object.internalDegree_le_degree piece vertex) (by omega)
  -- The Type A discharging, off the centres.
  have discharged := object.card_le_scaled_deficiency_off piece centres threshold
    dischargeScale capped routes unsaturated
  -- Off the centres the core charge is the Type A charge, so its sum is ≥ 0.
  have offCentres : (0 : Int) ≤ ∑ vertex ∈ piece \ centres,
      scaledCoreCharge object threshold dischargeScale piece vertex := by
    have expand : ∑ vertex ∈ piece \ centres,
        scaledCoreCharge object threshold dischargeScale piece vertex =
          ((∑ vertex ∈ piece \ centres,
            dischargeScale *
              (threshold - object.internalDegree piece vertex) : Nat) : Int) -
            ((piece \ centres).card : Int) := by
      unfold scaledCoreCharge
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.cast_sum]
    rw [expand]
    have cast : ((piece \ centres).card : Int) ≤
        ((∑ vertex ∈ piece \ centres,
          dischargeScale *
            (threshold - object.internalDegree piece vertex) : Nat) : Int) := by
      exact_mod_cast discharged
    linarith
  -- A centre's own core term is at worst `−1`.
  have centreCore : ∀ centre ∈ centres,
      (-1 : Int) ≤ scaledCoreCharge object threshold dischargeScale piece centre := by
    intro centre _
    rw [scaledCoreCharge]
    have : (0 : Int) ≤ ((dischargeScale *
        (threshold - object.internalDegree piece centre) : Nat) : Int) :=
      Int.natCast_nonneg _
    linarith
  have centreCoreSum : - (centres.card : Int) ≤
      ∑ centre ∈ centres,
        scaledCoreCharge object threshold dischargeScale piece centre := by
    have := Finset.sum_le_sum centreCore
    rw [Finset.sum_const, nsmul_eq_mul] at this
    linarith
  -- Split the core sum at the centres and assemble.
  have splitCore : ∑ vertex ∈ piece,
      scaledCoreCharge object threshold dischargeScale piece vertex =
        ∑ vertex ∈ piece \ centres,
            scaledCoreCharge object threshold dischargeScale piece vertex +
          ∑ centre ∈ centres,
            scaledCoreCharge object threshold dischargeScale piece centre :=
    (Finset.sum_sdiff (TypeBRefinedSupport.centres_subset
      (threshold := threshold) (piece := piece))).symm
  have centreCharges : - ∑ centre ∈ centres,
        ((dischargeScale * (object.degree centre - threshold) + 1 : Nat) : Int) =
      ∑ centre ∈ centres,
        scaledCentreCharge object threshold dischargeScale centre := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun centre _ => ?_
    rw [scaledCentreCharge]
    push_cast
    ring
  have allowance : ∑ centre ∈ centres,
      ((dischargeScale * (object.degree centre - threshold) + 2 : Nat) : Int) =
        ∑ centre ∈ centres,
            ((dischargeScale * (object.degree centre - threshold) + 1 : Nat) : Int) +
          (centres.card : Int) := by
    have pointwise : ∀ centre ∈ centres,
        ((dischargeScale * (object.degree centre - threshold) + 2 : Nat) : Int) =
          ((dischargeScale * (object.degree centre - threshold) + 1 : Nat) : Int)
            + 1 := by
      intro centre _
      push_cast
      ring
    rw [Finset.sum_congr rfl pointwise, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [augmentedLedger, splitCore, allowance, ← centreCharges]
  linarith [offCentres, centreCoreSum]


/-- **The centre allowance is inside the registered mass budget.**

`Σ_h (s(k−δ) + 1) ≤ F·s·σ(X)`: per centre this is `s·t + 1 ≤ F·s·t` at `t ≥ 1`,
which the registered `δ + 2 + s ≤ F·s` pays with room to spare. -/
theorem sum_centreAllowance_le {threshold dischargeScale massFactor : Nat}
    (object : FiniteObject.{u}) (piece : Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale) :
    ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
        (dischargeScale * (object.degree centre - threshold) + 1) ≤
      massFactor * dischargeScale * object.ambientSurplus piece threshold := by
  classical
  calc ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
          (dischargeScale * (object.degree centre - threshold) + 1)
      ≤ ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
          massFactor * dischargeScale * (object.degree centre - threshold) := by
        refine Finset.sum_le_sum fun centre member => ?_
        have high : threshold < object.degree centre :=
          (TypeBRefinedSupport.mem_centres.mp member).2
        obtain ⟨surplus, degree⟩ : ∃ surplus : Nat,
            object.degree centre = threshold + surplus + 1 :=
          ⟨object.degree centre - threshold - 1, by omega⟩
        have spent : (threshold + 2 + dischargeScale) * (surplus + 1) ≤
            massFactor * dischargeScale * (surplus + 1) :=
          Nat.mul_le_mul_right _ slack
        rw [degree]
        have reduce : threshold + surplus + 1 - threshold = surplus + 1 := by omega
        rw [reduce]
        nlinarith [spent]
    _ = massFactor * dischargeScale *
          ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
            (object.degree centre - threshold) := by rw [Finset.mul_sum]
    _ = massFactor * dischargeScale * object.ambientSurplus piece threshold := by
        rw [sum_centres_surplus object threshold piece]

/-- **`lem:typeB-bridge-deficit-bound`.**

`No_-(X) ≤ F·Σ_{h∈H_X}(d_G(h) − δ)`, written subtraction-free at the discharge
scale: `|V(X)| + s·σ(X) ≤ s·defp(X) + F·s·σ(X)`.  The manuscript's `8` is the
registered factor and its `27k ≥ 85` is `Data.bridgeMassSlack`.

The proof is the manuscript's: the ledger is bounded below by the centre
allowance, `(B-ledger)` converts that into a statement about `No(X)`, and the
registered slack pays the allowance out of the assigned surplus. -/
theorem bridgeDeficitBound {threshold dischargeScale massFactor : Nat}
    (object : FiniteObject.{u}) (piece : Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (routes : ∀ vertex ∈ piece \ TypeBRefinedSupport.centres object threshold piece,
      object.internalDegree piece vertex = threshold →
      ∃ receiver : object.Vertex,
        object.traceReceiver? piece threshold vertex = some receiver ∧
          object.IsReceiver piece threshold receiver ∧
            receiver ∉ TypeBRefinedSupport.centres object threshold piece)
    (unsaturated : ∀ receiver ∈ object.receivers piece threshold \
        TypeBRefinedSupport.centres object threshold piece,
      1 + object.restrictedLoad piece
          (TypeBRefinedSupport.centres object threshold piece) threshold
          receiver ≤
        dischargeScale * object.missingPorts piece threshold receiver) :
    piece.card + dischargeScale * object.ambientSurplus piece threshold ≤
      dischargeScale * object.positiveDeficiency piece threshold +
        massFactor * dischargeScale * object.ambientSurplus piece threshold := by
  classical
  set centres := TypeBRefinedSupport.centres object threshold piece with centresDef
  have ledger := neg_centreAllowance_le_augmentedLedger object piece threshold
    dischargeScale baseline routes unsaturated
  have identity :=
    augmentedLedger_add_card_centres object threshold dischargeScale piece
  -- `Σ_h (s·t_h + 2) = Σ_h (s·t_h + 1) + |H_X|`.
  have allowance : ∑ centre ∈ centres,
      ((dischargeScale * (object.degree centre - threshold) + 2 : Nat) : Int) =
        ((∑ centre ∈ centres,
          (dischargeScale * (object.degree centre - threshold) + 1) : Nat) : Int) +
          (centres.card : Int) := by
    push_cast
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [allowance] at ledger
  have budget := sum_centreAllowance_le (massFactor := massFactor) object piece slack
  have budgetCast :
      ((∑ centre ∈ centres,
        (dischargeScale * (object.degree centre - threshold) + 1) : Nat) : Int) ≤
        ((massFactor * dischargeScale *
          object.ambientSurplus piece threshold : Nat) : Int) := by
    exact_mod_cast budget
  have goal :
      ((piece.card + dischargeScale *
          object.ambientSurplus piece threshold : Nat) : Int) ≤
        ((dischargeScale * object.positiveDeficiency piece threshold +
          massFactor * dischargeScale *
            object.ambientSurplus piece threshold : Nat) : Int) := by
    push_cast
    push_cast at identity ledger budgetCast
    linarith
  exact_mod_cast goal


/-- **The two Type A conditions `lem:typeB-bridge-deficit-bound` reads on one
support**, off its assigned centres: the canonical routing is total and lands
off them, and every receiver outside them is unsaturated.

These are nodes `[88]` and `[90]` -- `lem:typeA-receiver-loads` and
`lem:typeA-unsaturated-discharge` -- read at the region
`lem:typeB-postledger-core-hygiene` leaves.  They are not restated here: this is
one name for the pair so that the family statements below do not spell it
twice. -/
def BridgeResidualComponentAt (object : FiniteObject.{u})
    (piece : Finset object.Vertex) (threshold dischargeScale : Nat) : Prop :=
  (∀ vertex ∈ piece \ TypeBRefinedSupport.centres object threshold piece,
    object.internalDegree piece vertex = threshold →
    ∃ receiver : object.Vertex,
      object.traceReceiver? piece threshold vertex = some receiver ∧
        object.IsReceiver piece threshold receiver ∧
          receiver ∉ TypeBRefinedSupport.centres object threshold piece) ∧
    ∀ receiver ∈ object.receivers piece threshold \
        TypeBRefinedSupport.centres object threshold piece,
      1 + object.restrictedLoad piece
          (TypeBRefinedSupport.centres object threshold piece) threshold
          receiver ≤
        dischargeScale * object.missingPorts piece threshold receiver

/-- The same pair at every piece of a decomposition. -/
def BridgeResidualComponents (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat) : Prop :=
  ∀ piece ∈ object.canonicalPieces support,
    BridgeResidualComponentAt object (object.pieceSupport support piece)
      threshold dischargeScale


/-- **`D_A(𝒜)`**, the large-budget Type A deficit of a collection of route-8
pieces, at the discharge scale: `Σ_Y (α|V(Y)| − defp(Y))` cleared of its
reciprocal. -/
noncomputable def route8Deficit (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold dischargeScale : Nat)
    (route8 : Finset (SupportComponents.Connected.Component object support)) :
    Nat :=
  ∑ piece ∈ route8,
    ((object.pieceSupport support piece).card -
      dischargeScale * object.positiveDeficiency
        (object.pieceSupport support piece) threshold)

/-- **`lem:typeB-bridge-with-route8-core`.**

`No(X) ≥ −D_A(𝒜_X) − F·Σ_h(d_G(h) − δ)`, summed over a decomposition: the pieces
carrying a route-8 residual profile are set aside and paid by `D_A`, and every
other piece is paid by the bridge estimate.  A route-8 piece is a Type A support,
so `σ(Y) = 0` and its whole negative part *is* its Type A deficit. -/
theorem bridgeResidualMass_le_route8 {threshold dischargeScale massFactor : Nat}
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (route8 : Finset (SupportComponents.Connected.Component object support))
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (route8Surplus : ∀ piece ∈ route8,
      object.ambientSurplus (object.pieceSupport support piece) threshold = 0)
    (components : ∀ piece ∈ object.canonicalPieces support, piece ∉ route8 →
      BridgeResidualComponentAt object (object.pieceSupport support piece)
        threshold dischargeScale) :
    ∑ piece ∈ object.canonicalPieces support,
        ((object.pieceSupport support piece).card +
            dischargeScale * object.ambientSurplus
              (object.pieceSupport support piece) threshold -
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport support piece) threshold) ≤
      route8Deficit object support threshold dischargeScale route8 +
        massFactor * dischargeScale * object.degreeSurplus threshold := by
  classical
  set pieces := object.canonicalPieces support with piecesDef
  set mass := fun piece => (object.pieceSupport support piece).card +
      dischargeScale * object.ambientSurplus
        (object.pieceSupport support piece) threshold -
    dischargeScale * object.positiveDeficiency
      (object.pieceSupport support piece) threshold with massDef
  have split := (Finset.sum_filter_add_sum_filter_not pieces
    (fun piece => piece ∈ route8) mass).symm
  have route8Bound : ∑ piece ∈ pieces.filter (fun piece => piece ∈ route8),
      mass piece ≤
        route8Deficit object support threshold dischargeScale route8 := by
    rw [route8Deficit]
    have pointwise : ∀ piece ∈ pieces.filter (fun piece => piece ∈ route8),
        mass piece = (object.pieceSupport support piece).card -
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport support piece) threshold := by
      intro piece member
      have zero := route8Surplus piece (Finset.mem_filter.mp member).2
      simp only [massDef, zero, Nat.mul_zero, Nat.add_zero]
    rw [Finset.sum_congr rfl pointwise]
    refine Finset.sum_le_sum_of_subset ?_
    exact fun piece member => (Finset.mem_filter.mp member).2
  have restBound : ∑ piece ∈ pieces.filter (fun piece => ¬ piece ∈ route8),
      mass piece ≤ massFactor * dischargeScale *
        object.degreeSurplus threshold := by
    calc ∑ piece ∈ pieces.filter (fun piece => ¬ piece ∈ route8), mass piece
        ≤ ∑ piece ∈ pieces.filter (fun piece => ¬ piece ∈ route8),
            massFactor * dischargeScale * object.ambientSurplus
              (object.pieceSupport support piece) threshold := by
          refine Finset.sum_le_sum fun piece member => ?_
          obtain ⟨inside, fresh⟩ := Finset.mem_filter.mp member
          obtain ⟨routes, unsaturated⟩ := components piece inside fresh
          have bound := bridgeDeficitBound (massFactor := massFactor) object
            (object.pieceSupport support piece) slack baseline routes
            unsaturated
          simp only [massDef]
          omega
      _ ≤ ∑ piece ∈ pieces,
            massFactor * dischargeScale * object.ambientSurplus
              (object.pieceSupport support piece) threshold :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = massFactor * dischargeScale *
            ∑ piece ∈ pieces, object.ambientSurplus
              (object.pieceSupport support piece) threshold := by
          rw [Finset.mul_sum]
      _ = massFactor * dischargeScale *
            object.ambientSurplus support threshold := by
          rw [piecesDef, object.sum_ambientSurplus_canonicalPieces support threshold]
      _ ≤ massFactor * dischargeScale * object.degreeSurplus threshold := by
          refine Nat.mul_le_mul_left _ ?_
          letI : FinEnum object.Vertex := object.vertices
          rw [← object.ambientSurplus_univ_eq_degreeSurplus threshold baseline]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ support)
  rw [split]
  omega

/-- **`def:typeB-residual-mass`, the at-most-twice occurrence convention.**

`S_B ≤ 2σ(G)`, hence `M_B ≤ F·S_B ≤ 2F·σ(G)` -- the manuscript's `16σ(G)`.  The
per-centre bound is the same at a grouped decorated envelope centre as at an
ordinary one, so `lem:decorated-envelope-deficit-bound` and
`lem:decorated-envelope-with-route8-core` are this theorem's second summand and
need no separate estimate. -/
theorem bridgeResidualMass_le_twice {threshold dischargeScale massFactor : Nat}
    (object : FiniteObject.{u}) (ordinary grouped : Finset object.Vertex)
    (ordinaryRoute8 :
      Finset (SupportComponents.Connected.Component object ordinary))
    (groupedRoute8 :
      Finset (SupportComponents.Connected.Component object grouped))
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (ordinarySurplus : ∀ piece ∈ ordinaryRoute8,
      object.ambientSurplus (object.pieceSupport ordinary piece) threshold = 0)
    (groupedSurplus : ∀ piece ∈ groupedRoute8,
      object.ambientSurplus (object.pieceSupport grouped piece) threshold = 0)
    (ordinaryComponents : ∀ piece ∈ object.canonicalPieces ordinary,
      piece ∉ ordinaryRoute8 →
      BridgeResidualComponentAt object (object.pieceSupport ordinary piece)
        threshold dischargeScale)
    (groupedComponents : ∀ piece ∈ object.canonicalPieces grouped,
      piece ∉ groupedRoute8 →
      BridgeResidualComponentAt object (object.pieceSupport grouped piece)
        threshold dischargeScale) :
    ∑ piece ∈ object.canonicalPieces ordinary,
        ((object.pieceSupport ordinary piece).card +
            dischargeScale * object.ambientSurplus
              (object.pieceSupport ordinary piece) threshold -
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport ordinary piece) threshold) +
      ∑ piece ∈ object.canonicalPieces grouped,
        ((object.pieceSupport grouped piece).card +
            dischargeScale * object.ambientSurplus
              (object.pieceSupport grouped piece) threshold -
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport grouped piece) threshold) ≤
      route8Deficit object ordinary threshold dischargeScale ordinaryRoute8 +
        route8Deficit object grouped threshold dischargeScale groupedRoute8 +
          2 * (massFactor * dischargeScale * object.degreeSurplus threshold) := by
  have first := bridgeResidualMass_le_route8 (massFactor := massFactor) object
    ordinary ordinaryRoute8 slack baseline ordinarySurplus ordinaryComponents
  have second := bridgeResidualMass_le_route8 (massFactor := massFactor) object
    grouped groupedRoute8 slack baseline groupedSurplus groupedComponents
  omega

/-- **`prop:typeB-bridge-sublinear`.**

`M_B(𝒳_B) ≤ F·S_B(𝒳_B) ≤ F·σ(G)`, the route-8-free case: no piece of the
decomposition carries a route-8 residual profile, so `𝒜_X` is empty and the
whole mass is paid by the assigned surplus. -/
theorem bridgeResidualMass_le {threshold dischargeScale massFactor : Nat}
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex)
    (components :
      BridgeResidualComponents object support threshold dischargeScale) :
    ∑ piece ∈ object.canonicalPieces support,
        ((object.pieceSupport support piece).card +
            dischargeScale * object.ambientSurplus
              (object.pieceSupport support piece) threshold -
          dischargeScale * object.positiveDeficiency
            (object.pieceSupport support piece) threshold) ≤
      massFactor * dischargeScale * object.degreeSurplus threshold := by
  have bound := bridgeResidualMass_le_route8 (massFactor := massFactor) object
    support ∅ slack baseline (by simp)
    (fun piece member _ => components piece member)
  rw [route8Deficit] at bound
  simpa using bound


/-! ## `lem:typeB-bridge-deficit-bound`: the envelope negative part -/

/-! **The unpaid part of the fan envelope at a centre, at the discharge scale.**

Only the centre and the `c` cubic-closed neighbours carry negative charge, by
`scaledCharge_openNeighbour_nonneg`; the centre contributes `s(k − δ) + 1` and
each cubic-closed neighbour `1`.  This is the manuscript's
`(k − 3 + 1/4) + c/4`, multiplied through by `s`. -/
/-- **`lem:typeB-bridge-deficit-bound`, display (1).**

`(k − 3 + 1/4) + c/4 ≤ 5k/4 − 11/4 ≤ 8(k − 3)`, at the discharge scale and for
the registered bridge-mass factor.  The first inequality is `c ≤ k`; the second
is the manuscript's `27k ≥ 85`, which here is the registered comparison
`δ + 2 + s ≤ F·s` spent against the centre surplus `k − δ ≥ 1`.

Nothing is written: `8`, `85` and `27` are the manuscript's readings of `F`,
`δ` and `s`. -/
theorem envelopeNegativePart_le {threshold dischargeScale massFactor : Nat}
    (envelope : Finset object.Vertex) {centre : object.Vertex}
    (high : threshold < object.degree centre)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale) :
    envelopeNegativePart object threshold dischargeScale envelope centre ≤
      massFactor * dischargeScale * (object.degree centre - threshold) := by
  obtain ⟨surplus, degree⟩ : ∃ surplus : Nat,
      object.degree centre = threshold + surplus + 1 :=
    ⟨object.degree centre - threshold - 1, by omega⟩
  have counted : closedCount object threshold envelope centre ≤ object.degree centre :=
    closedCount_le_degree object threshold envelope centre
  have spent : (threshold + 2 + dischargeScale) * (surplus + 1) ≤
      massFactor * dischargeScale * (surplus + 1) :=
    Nat.mul_le_mul_right _ slack
  rw [envelopeNegativePart, degree] at *
  have reduce : threshold + surplus + 1 - threshold = surplus + 1 := by omega
  rw [reduce] at *
  nlinarith [spent, counted]

/-- **`prop:typeB-bridge-sublinear`, `S_B ≤ σ(G)` for the ordinary role.**  The
assigned surplus of any region is below the global surplus, because the surplus
is a nonnegative vertex-local count. -/
theorem ambientSurplus_le_degreeSurplus (object : FiniteObject.{u})
    (support : Finset object.Vertex) (threshold : Nat)
    (baseline : ∀ vertex : object.Vertex, threshold ≤ object.degree vertex) :
    object.ambientSurplus support threshold ≤ object.degreeSurplus threshold := by
  letI : FinEnum object.Vertex := object.vertices
  classical
  rw [← object.ambientSurplus_univ_eq_degreeSurplus threshold baseline]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ support)

end Hypostructure.Graph.TypeBEnvelopeCharge
