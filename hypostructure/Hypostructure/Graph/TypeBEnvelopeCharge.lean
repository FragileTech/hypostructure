import Hypostructure.Graph.TypeBFanIncidence
import Hypostructure.Graph.NetCharge
import Hypostructure.Graph.TypeBRefinedSupport

/-!
# The augmented Type B fan-envelope charge

`def:typeB-assigned-ledger` measures a vertex of an assigned Type B support by

  `ch_X(v) = δ − d_E(v) − α`,

the baseline less the vertex's degree *inside the assigned fan envelope* less one
discharge unit `α = 1/s`.  Everything below is that reading, carried at the scale
`s` so that no reciprocal is ever written:

  `s·ch_X(v) = s·(δ − d_E(v)) − 1`.

Two manuscript statements are proved from it, and they are the two halves of the
Type B bridge.

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
centres of a support and then over the pieces of a decomposition gives its
`M_B ≤ 8 S_B ≤ 16σ(G)` for the ordinary assigned role.

Nothing here is specialized to a manuscript: the baseline, the discharge scale
and the mass factor are parameters, and no numeral is written.
-/

namespace Hypostructure.Graph.TypeBEnvelopeCharge

open Hypostructure
open Hypostructure.Graph.TypeBFanIncidence
open scoped BigOperators

universe u

variable {object : FiniteObject.{u}}

open scoped Classical

/-! ## The assigned fan envelope -/

/-- **The coherence an assigned fan envelope has at its centre.**

`def:typeB-assigned-ledger` builds `E_h` from the centre, its assigned fan
neighbours, and the non-`h` incidences of the cubic-closed ones.  Which vertices
the assignment picks is fan data and not a property of the graph, so the envelope
is a parameter here; what every charge reading below uses is only that the
envelope contains the centre and the whole of `N(h)`.  The incidences of the
cubic-closed neighbours are inside it already, by `IsCubicClosed`. -/
structure IsFanEnvelope (object : FiniteObject.{u}) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Prop where
  /-- The centre belongs to its own envelope. -/
  centreMem : centre ∈ envelope
  /-- Every fan neighbour is assigned to the envelope. -/
  fanMem : ∀ ⦃owner : object.Vertex⦄, object.graph.Adj centre owner → owner ∈ envelope

/-- **`s·ch_X(v)`**, the augmented Type B charge of a vertex at the discharge
scale: the baseline less the vertex's envelope-internal degree, less one
discharge unit.  Carried in `ℤ` because the charge is genuinely signed. -/
noncomputable def scaledCharge (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (vertex : object.Vertex) : Int :=
  (dischargeScale : Int) *
      ((threshold : Int) - (object.internalDegree envelope vertex : Int)) - 1

/-! ## The three readings of `d_E` -/

/-- **The centre sees all `k` of its neighbours.**  Its envelope-internal degree
is its ambient degree, because the envelope contains `N(h)`. -/
theorem internalDegree_centre {envelope : Finset object.Vertex}
    {centre : object.Vertex} (assigned : IsFanEnvelope object envelope centre) :
    object.internalDegree envelope centre = object.degree centre := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  have inside : object.graph.neighborFinset centre ∩ envelope =
      object.graph.neighborFinset centre := by
    refine Finset.inter_eq_left.mpr ?_
    intro owner member
    exact assigned.fanMem ((SimpleGraph.mem_neighborFinset _ _ _).mp member)
  simpa [FiniteObject.internalDegree, FiniteObject.degree, inside] using
    congrArg Finset.card inside

/-- **A cubic-closed neighbour sees all `δ` of its own.**  It sits at the
baseline, the centre is in the envelope, and its two other incidences are
assigned there by `IsCubicClosed`. -/
theorem internalDegree_closedNeighbour {threshold : Nat}
    {envelope : Finset object.Vertex} {centre owner : object.Vertex}
    (assigned : IsFanEnvelope object envelope centre)
    (closed : IsCubicClosed object threshold envelope centre owner) :
    object.internalDegree envelope owner = threshold := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  obtain ⟨adjacent, cubic, incidences⟩ := closed
  have inside : object.graph.neighborFinset owner ∩ envelope =
      object.graph.neighborFinset owner := by
    refine Finset.inter_eq_left.mpr ?_
    intro other member
    have adjacentOther : object.graph.Adj owner other :=
      (SimpleGraph.mem_neighborFinset _ _ _).mp member
    by_cases isCentre : other = centre
    · exact isCentre ▸ assigned.centreMem
    · exact incidences other adjacentOther isCentre
  have counted : object.internalDegree envelope owner = object.degree owner := by
    simpa [FiniteObject.internalDegree, FiniteObject.degree, inside] using
      congrArg Finset.card inside
  rw [counted, cubic]

/-- **Every other fan neighbour misses one.**  A fan neighbour of a high centre
sits exactly at the baseline (`lem:heavy-neighbourhood-normal-form` (a)); if it
is not cubic-closed, some incidence of it other than the centre is outside the
envelope, so its envelope-internal degree is at most `δ − 1`.  This is the
manuscript's "internal degree at most `2` in the assigned fan envelope". -/
theorem internalDegree_openNeighbour_lt {threshold : Nat}
    {envelope : Finset object.Vertex} {centre owner : object.Vertex}
    (adjacent : object.graph.Adj centre owner)
    (cubic : object.degree owner = threshold)
    (open' : ¬ IsCubicClosed object threshold envelope centre owner) :
    object.internalDegree envelope owner + 1 ≤ threshold := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  classical
  -- The first two clauses of `IsCubicClosed` hold, so the third fails.
  have escapes : ∃ other : object.Vertex, object.graph.Adj owner other ∧
      other ≠ centre ∧ other ∉ envelope := by
    by_contra none'
    push_neg at none'
    exact open' ⟨adjacent, cubic, fun other adjacentOther isCentre =>
      none' other adjacentOther isCentre⟩
  obtain ⟨other, adjacentOther, _isCentre, outside⟩ := escapes
  have member : other ∈ object.graph.neighborFinset owner :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr adjacentOther
  have contained : object.graph.neighborFinset owner ∩ envelope ⊆
      (object.graph.neighborFinset owner).erase other := by
    intro vertex inside
    rw [Finset.mem_inter] at inside
    refine Finset.mem_erase.mpr ⟨?_, inside.1⟩
    rintro rfl
    exact outside inside.2
  have counted := Finset.card_le_card contained
  rw [Finset.card_erase_of_mem member] at counted
  have total : (object.graph.neighborFinset owner).card = threshold := by
    simpa [FiniteObject.degree] using cubic
  have positive : 1 ≤ (object.graph.neighborFinset owner).card :=
    Finset.card_pos.mpr ⟨other, member⟩
  have : object.internalDegree envelope owner ≤
      (object.graph.neighborFinset owner).card - 1 := by
    simpa [FiniteObject.internalDegree] using counted
  omega

/-! ## Step 1 of `lem:typeB-exclusion`: the closed-neighbourhood charge -/

/-- **`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u)`**, at the discharge scale. -/
noncomputable def closedNeighbourhoodCharge (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Int :=
  scaledCharge object threshold dischargeScale envelope centre +
    ∑ owner ∈ (object.orderedNeighbors centre).toFinset,
      scaledCharge object threshold dischargeScale envelope owner

/-- **The cubic-closed neighbours sit inside `N(h)`.** -/
theorem closedNeighbours_subset_neighbourFinset (threshold : Nat)
    (envelope : Finset object.Vertex) (centre : object.Vertex) :
    closedNeighbours object threshold envelope centre ⊆
      (object.orderedNeighbors centre).toFinset :=
  closedNeighbours_subset object threshold envelope centre

/-- **Step 1 of `lem:typeB-exclusion`.**

`ch_X(h) + Σ_{u ∈ N(h)} ch_X(u) ≥ −D_B(𝔉_h)`, at the discharge scale.

The manuscript's own calculation: the centre contributes `δ − k − α`, each of
the `c` cubic-closed neighbours `−α`, and each of the remaining `k − c` fan
neighbours at least `1 − α`.  Collecting,

  `(δ − k − α) − cα + (1 − α)(k − c) = δ − (k+1)α − c = −D_B(𝔉_h)`,

which at `δ = 3`, `α = 1/4` is the manuscript's `(11−k)/4 − c`.

The hypothesis `tight` is `lem:heavy-neighbourhood-normal-form` (a): every fan
neighbour sits exactly at the baseline.  It is the only graph input; the rest is
the three envelope readings above. -/
theorem neg_scaledDeficit_le_closedNeighbourhoodCharge {threshold dischargeScale : Nat}
    {envelope : Finset object.Vertex} {centre : object.Vertex}
    (assigned : IsFanEnvelope object envelope centre)
    (tight : ∀ ⦃owner : object.Vertex⦄, object.graph.Adj centre owner →
      object.degree owner = threshold) :
    - scaledDeficit object threshold dischargeScale envelope centre ≤
      closedNeighbourhoodCharge object threshold dischargeScale envelope centre := by
  classical
  set neighbours := (object.orderedNeighbors centre).toFinset with neighboursDef
  set closed := closedNeighbours object threshold envelope centre with closedDef
  have contained : closed ⊆ neighbours :=
    closedNeighbours_subset_neighbourFinset threshold envelope centre
  -- `Σ_{N(h)} = Σ_{closed} + Σ_{N(h) ∖ closed}`.
  have split : ∑ owner ∈ neighbours \ closed,
        scaledCharge object threshold dischargeScale envelope owner +
      ∑ owner ∈ closed,
        scaledCharge object threshold dischargeScale envelope owner =
      ∑ owner ∈ neighbours,
        scaledCharge object threshold dischargeScale envelope owner :=
    Finset.sum_sdiff contained
  -- A cubic-closed neighbour contributes exactly `−1`.
  have closedValue : ∑ owner ∈ closed,
      scaledCharge object threshold dischargeScale envelope owner =
        - (closedCount object threshold envelope centre : Int) := by
    have pointwise : ∀ owner ∈ closed,
        scaledCharge object threshold dischargeScale envelope owner = (-1 : Int) := by
      intro owner member
      have isClosed : IsCubicClosed object threshold envelope centre owner :=
        mem_closedNeighbours_iff.mp (closedDef ▸ member)
      rw [scaledCharge, internalDegree_closedNeighbour assigned isClosed]
      ring
    rw [Finset.sum_congr rfl pointwise, Finset.sum_const, closedCount, ← closedDef,
      nsmul_eq_mul]
    ring
  -- Every other fan neighbour contributes at least `s − 1`.
  have openValue : ((neighbours \ closed).card : Int) * ((dischargeScale : Int) - 1) ≤
      ∑ owner ∈ neighbours \ closed,
        scaledCharge object threshold dischargeScale envelope owner := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun owner member => ?_
    rw [Finset.mem_sdiff, neighboursDef, List.mem_toFinset,
      object.mem_orderedNeighbors_iff] at member
    obtain ⟨adjacent, notClosed⟩ := member
    have missing : object.internalDegree envelope owner + 1 ≤ threshold :=
      internalDegree_openNeighbour_lt adjacent (tight adjacent)
        (fun isClosed => notClosed (mem_closedNeighbours_iff.mpr isClosed))
    have cast : (object.internalDegree envelope owner : Int) + 1 ≤ (threshold : Int) := by
      exact_mod_cast missing
    have step : (1 : Int) * (dischargeScale : Int) ≤
        ((threshold : Int) - (object.internalDegree envelope owner : Int)) *
          (dischargeScale : Int) :=
      mul_le_mul_of_nonneg_right (by linarith) (Int.natCast_nonneg _)
    rw [scaledCharge]
    linarith [step]
  -- The two cardinalities, and `c ≤ k`.
  have counted : neighbours.card = object.degree centre := by
    rw [neighboursDef, List.toFinset_card_of_nodup (object.orderedNeighbors_nodup centre),
      object.orderedNeighbors_length centre]
  have closedCard : closed.card = closedCount object threshold envelope centre := rfl
  have sdiffCard : (neighbours \ closed).card + closed.card = neighbours.card :=
    Finset.card_sdiff_add_card_eq_card contained
  have sdiffCast : ((neighbours \ closed).card : Int) =
      (object.degree centre : Int) -
        (closedCount object threshold envelope centre : Int) := by
    rw [counted, closedCard] at sdiffCard
    omega
  -- Assemble, and read off `−D_B`.
  rw [closedNeighbourhoodCharge, scaledCharge, internalDegree_centre assigned,
    ← split, closedValue, scaledDeficit]
  rw [sdiffCast] at openValue
  nlinarith [openValue]

/-- **A certificate-closed fan carries nonnegative closed-neighbourhood
charge.**  `D_B ≤ 0` is exactly `IsCertificateClosed`, so this is Step 1's
conclusion: "this proves nonnegative charge for every non-residual fan
neighbourhood". -/
theorem closedNeighbourhoodCharge_nonneg {threshold dischargeScale : Nat}
    {envelope : Finset object.Vertex} {centre : object.Vertex}
    (assigned : IsFanEnvelope object envelope centre)
    (tight : ∀ ⦃owner : object.Vertex⦄, object.graph.Adj centre owner →
      object.degree owner = threshold)
    (closed : IsCertificateClosed object threshold dischargeScale envelope centre) :
    0 ≤ closedNeighbourhoodCharge object threshold dischargeScale envelope centre := by
  have step := neg_scaledDeficit_le_closedNeighbourhoodCharge assigned tight
    (dischargeScale := dischargeScale)
  have : (0 : Int) ≤ - scaledDeficit object threshold dischargeScale envelope centre := by
    have := closed
    rw [IsCertificateClosed] at this
    omega
  omega

/-- **The fan neighbours that are not cubic-closed carry nonnegative charge.**

The manuscript's "every other fan neighbour has internal degree at most `2` in
the assigned fan envelope and contributes at least `3/4`": at the scale `s` the
contribution is at least `s − 1`, which is nonnegative for any registered scale.
This is what makes `envelopeNegativePart` below the *whole* negative part of the
envelope rather than a selection of its terms. -/
theorem scaledCharge_openNeighbour_nonneg {threshold dischargeScale : Nat}
    {envelope : Finset object.Vertex} {centre owner : object.Vertex}
    (positive : 0 < dischargeScale)
    (adjacent : object.graph.Adj centre owner)
    (cubic : object.degree owner = threshold)
    (open' : ¬ IsCubicClosed object threshold envelope centre owner) :
    0 ≤ scaledCharge object threshold dischargeScale envelope owner := by
  have missing : object.internalDegree envelope owner + 1 ≤ threshold :=
    internalDegree_openNeighbour_lt adjacent cubic open'
  have cast : (object.internalDegree envelope owner : Int) + 1 ≤ (threshold : Int) := by
    exact_mod_cast missing
  have scale : (1 : Int) ≤ (dischargeScale : Int) := by exact_mod_cast positive
  have step : (1 : Int) * (dischargeScale : Int) ≤
      ((threshold : Int) - (object.internalDegree envelope owner : Int)) *
        (dischargeScale : Int) :=
    mul_le_mul_of_nonneg_right (by linarith) (Int.natCast_nonneg _)
  rw [scaledCharge]
  linarith [step]

/-! ## `lem:typeB-bridge-deficit-bound`: the envelope negative part -/

/-- **The unpaid part of the fan envelope at a centre, at the discharge scale.**

Only the centre and the `c` cubic-closed neighbours carry negative charge, by
`scaledCharge_openNeighbour_nonneg`; the centre contributes `s(k − δ) + 1` and
each cubic-closed neighbour `1`.  This is the manuscript's
`(k − 3 + 1/4) + c/4`, multiplied through by `s`. -/
noncomputable def envelopeNegativePart (object : FiniteObject.{u})
    (threshold dischargeScale : Nat) (envelope : Finset object.Vertex)
    (centre : object.Vertex) : Nat :=
  dischargeScale * (object.degree centre - threshold) + 1 +
    closedCount object threshold envelope centre

/-- **The centre's own charge is the negative of its share.** -/
theorem scaledCharge_centre_eq {threshold dischargeScale : Nat}
    {envelope : Finset object.Vertex} {centre : object.Vertex}
    (assigned : IsFanEnvelope object envelope centre)
    (high : threshold < object.degree centre) :
    scaledCharge object threshold dischargeScale envelope centre =
      - ((dischargeScale * (object.degree centre - threshold) : Nat) : Int) - 1 := by
  rw [scaledCharge, internalDegree_centre assigned]
  have expand : ((dischargeScale * (object.degree centre - threshold) : Nat) : Int) =
      (dischargeScale : Int) *
        ((object.degree centre : Int) - (threshold : Int)) := by
    push_cast [Nat.cast_sub (le_of_lt high)]
    ring
  rw [expand]
  ring

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

/-- **`lem:typeB-bridge-deficit-bound`, display (2), at one support.**

`Ĉh_B(X) ≥ −8 Σ_{h ∈ H_X}(d_G(h) − 3)`: summing the envelope estimate over the
assigned centres of the support gives the assigned surplus back, because a
vertex of the support that is not a centre carries no surplus at all. -/
theorem sum_envelopeNegativePart_le {threshold dischargeScale massFactor : Nat}
    (piece : Finset object.Vertex)
    (envelope : object.Vertex → Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale) :
    ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
        envelopeNegativePart object threshold dischargeScale (envelope centre)
          centre ≤
      massFactor * dischargeScale * object.ambientSurplus piece threshold := by
  classical
  have surplus : ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
      (object.degree centre - threshold) =
        object.ambientSurplus piece threshold := by
    unfold FiniteObject.ambientSurplus
    refine Finset.sum_subset TypeBRefinedSupport.centres_subset ?_
    intro vertex member notCentre
    have : ¬ IsHighCentre object threshold vertex := fun high =>
      notCentre (TypeBRefinedSupport.mem_centres.mpr ⟨member, high⟩)
    rw [IsHighCentre] at this
    omega
  calc ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
          envelopeNegativePart object threshold dischargeScale (envelope centre)
            centre
      ≤ ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
          massFactor * dischargeScale * (object.degree centre - threshold) :=
        Finset.sum_le_sum fun centre member =>
          envelopeNegativePart_le _
            (TypeBRefinedSupport.mem_centres.mp member).2 slack
    _ = massFactor * dischargeScale *
          ∑ centre ∈ TypeBRefinedSupport.centres object threshold piece,
            (object.degree centre - threshold) := by rw [Finset.mul_sum]
    _ = massFactor * dischargeScale * object.ambientSurplus piece threshold := by
        rw [surplus]

/-- **`prop:typeB-bridge-sublinear` for the ordinary assigned role.**

`M_B(𝒳_B) ≤ 8 S_B(𝒳_B)`: the bridge mass of a whole canonical decomposition is
the sum of its pieces' envelope masses, and the assigned surpluses add over the
pieces because the decomposition partitions the region. -/
theorem sum_canonicalPieces_envelopeNegativePart_le
    {threshold dischargeScale massFactor : Nat}
    (support : Finset object.Vertex)
    (envelope : object.Vertex → Finset object.Vertex)
    (slack : threshold + 2 + dischargeScale ≤ massFactor * dischargeScale) :
    ∑ piece ∈ object.canonicalPieces support,
        ∑ centre ∈ TypeBRefinedSupport.centres object threshold
            (object.pieceSupport support piece),
          envelopeNegativePart object threshold dischargeScale (envelope centre)
            centre ≤
      massFactor * dischargeScale * object.ambientSurplus support threshold := by
  classical
  calc ∑ piece ∈ object.canonicalPieces support,
          ∑ centre ∈ TypeBRefinedSupport.centres object threshold
              (object.pieceSupport support piece),
            envelopeNegativePart object threshold dischargeScale
              (envelope centre) centre
      ≤ ∑ piece ∈ object.canonicalPieces support,
          massFactor * dischargeScale *
            object.ambientSurplus (object.pieceSupport support piece) threshold :=
        Finset.sum_le_sum fun piece _ => sum_envelopeNegativePart_le _ envelope slack
    _ = massFactor * dischargeScale *
          ∑ piece ∈ object.canonicalPieces support,
            object.ambientSurplus (object.pieceSupport support piece) threshold := by
        rw [Finset.mul_sum]
    _ = massFactor * dischargeScale * object.ambientSurplus support threshold := by
        rw [object.sum_ambientSurplus_canonicalPieces support threshold]

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
