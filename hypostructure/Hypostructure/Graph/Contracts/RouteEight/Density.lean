import Hypostructure.Graph.Statements.Route8Density
import Hypostructure.Graph.Statements.JointHubs
import Hypostructure.Graph.Statements.Route8PackingExchange
import Hypostructure.Graph.Route8X15Landing
import Hypostructure.Graph.WindowJoinIdentity

/-!
# Contracts: the density theorem at the pieces of `R` and the arm closure (keys `9700`–`9704`)

* `9700`: a hub-free piece of `R` has all degrees `δ = 3` (minimum-degree baseline and
  `σ_X = 0`), is connected, subcubic, has no dyadic cycle (G avoids the target) and no
  induced `P13` (`R` has none, key `remainderPathBounds`); its excess is `8e − 11n`, so the
  density theorem applies (`Route8HubFree.hubFree_density`).
* `9701`: the one-window exchange of key `9800` (`Q = {P}`) and G's dyadic-cycle avoidance
  give the `X15` landing lemmas; `Route8HubFree.two_le_longLandingWindows`.
* `9702`: `9700` and `9701`: a hub-free piece of positive excess is a copy of `X15`, of
  excess `3`, with `ν ≥ 2`, and `13·3 ≤ 30·2`.
* `9703`: key `9803` (negative hub pieces, `|X| + sσ ≤ s·def⁺ + F·s·σ`) or the nonnegative
  net charge (`|X| + sσ ≤ s·def⁺`), with `def⁺ ≤ |∂X|` on the baseline.
* `9704`: key `9807` at `c = 30` and a placement system of `P₀` reads
  `388T − 30σ_W < Σ_{excess>0} (13·excess − 30ν)` at `δ = 3`, `s = 4`, `W = 13`
  (with `F` kept: `(4 + 48F)T − 30σ_W`); the hub-free terms are `≤ 0` (`9702`), the hub terms
  `≤ 52(F−1)σ_X` (`9703`), and `σ_W + σ_R = σ(G) ≤ T` (key `surplusAtOrBelow`), so the right
  side is `≤ 52(F−1)(T − σ_W) ≤ (4 + 48F)T − 30σ_W` for `3 ≤ F ≤ 14`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- The baseline in vertex form at `δ = 3`. -/
theorem baseline_three {data : Parameters} {object : FiniteObject.{u}}
    (three : data.threshold = 3) (baseline : MinDegreeBaselineStatement data object) :
    ∀ v, 3 ≤ object.degree v := fun v =>
  three ▸ le_trans baseline (object.minDegree_le_degree v)

/-- A hub-free piece has all degrees `3`. -/
theorem hubFree_degree {data : Parameters} {object : FiniteObject.{u}}
    (three : data.threshold = 3) (baseline : MinDegreeBaselineStatement data object)
    {X : SupportComponents.Connected.Component object
      (object.remainderSupport (canonicalWindowPacking data object))}
    (hσ : route8PieceSurplus data object X = 0) :
    ∀ v ∈ object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) X,
      object.degree v = 3 := by
  unfold route8PieceSurplus at hσ
  rw [three] at hσ
  exact Route8HubFree.degree_eq_of_ambientSurplus_eq_zero (baseline_three three baseline) hσ

/-- **Key `9700`: the density theorem at the hub-free pieces.** -/
theorem route8HubFreeDensity (data : Parameters) (object : FiniteObject.{u})
    (three : data.threshold = 3) (four : data.dischargeScale = 4)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (paths : RemainderPathBoundsStatement data object) :
    Route8HubFreeDensityStatement data object := by
  unfold Route8HubFreeDensityStatement
  dsimp only
  intro X hX hσ
  have hdeg := hubFree_degree three baseline hσ
  have free : ∀ l : List object.Vertex, DensityCert.IsIndPath object.graph l →
      (∀ x ∈ l, x ∈ object.remainderSupport (canonicalWindowPacking data object)) →
      l.length ≠ 13 := by
    intro l hl hin h13
    letI : FinEnum object.Vertex := object.vertices
    letI : DecidableRel object.graph.Adj := object.decideAdj
    obtain ⟨g, hg, hgl⟩ := Route8HubFree.exists_inducedSeq_of_isIndPath hl h13
    obtain ⟨t, ht, hgt⟩ := paths.1 g ⟨hg.1, hg.2⟩
    exact hgt (Finset.mem_coe.2 (hin _ (hgl t ht)))
  rcases Route8HubFree.hubFree_density _ hX hdeg (JointObject.avoid_dyadic avoid lengthLaw)
      free with h | h
  · left
    unfold route8PieceExcess
    dsimp only
    rw [four]
    push_cast
    exact h
  · exact Or.inr h

/-- **Key `9701`: the long landings of a hub-free `X15` piece.** -/
theorem route8X15LongLandings (data : Parameters) (object : FiniteObject.{u})
    (three : data.threshold = 3) (order : data.windowOrder = 13)
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (baseline : MinDegreeBaselineStatement data object)
    (exchange : Route8PackingExchangeStatement data object) :
    Route8X15LongLandingsStatement data object := by
  unfold Route8X15LongLandingsStatement
  dsimp only
  intro place hplace X _ hσ hemb
  unfold route8LongLandingWindows
  exact Route8HubFree.two_le_longLandingWindows order
    (canonicalWindowPacking_spec data object).1
    (fun P hP W hW hin => by
      simpa using exchange {P} (Finset.singleton_subset_iff.2 hP) W hW
        (fun T hT v hv => (hin T hT v hv).imp
          (fun h => ⟨P, Finset.mem_singleton_self P, h⟩) id))
    (JointObject.avoid_dyadic avoid lengthLaw) place hplace X
    (hubFree_degree three baseline hσ) hemb

/-- **Key `9702`: `Π` at the hub-free pieces.** -/
theorem route8HubFreePi (data : Parameters) (object : FiniteObject.{u})
    (three : data.threshold = 3) (four : data.dischargeScale = 4)
    (baseline : MinDegreeBaselineStatement data object)
    (density : Route8HubFreeDensityStatement data object)
    (landings : Route8X15LongLandingsStatement data object) :
    Route8HubFreePiStatement data object := by
  unfold Route8HubFreePiStatement
  dsimp only
  intro place hplace X hX hσ hpos
  rcases density X hX hσ with h | hemb
  · exact absurd hpos (not_lt.2 h)
  have hν := landings place hplace X hX hσ hemb
  obtain ⟨e, he⟩ := hemb
  have hex : route8PieceExcess data object X = 3 := by
    unfold route8PieceExcess
    dsimp only
    rw [four]
    push_cast
    exact Route8HubFree.excess_x15 e he (hubFree_degree three baseline hσ)
  rw [hex, three, four]
  have : (2 : ℤ) ≤ (route8LongLandingWindows data object place X : ℤ) := by exact_mod_cast hν
  norm_num
  linarith

/-- The arithmetic of key `9703`. -/
theorem excess_le_of_mass {card s σ d cut F : ℕ} (key : card + s * σ ≤ F * s * σ + s * d)
    (hd : d ≤ cut) : (card : ℤ) - s * cut ≤ (((F - 1) * s : ℕ) : ℤ) * σ := by
  have hdZ : (s : ℤ) * d ≤ s * cut := by exact_mod_cast Nat.mul_le_mul_left s hd
  have keyZ : (card : ℤ) + s * σ ≤ F * s * σ + s * d := by exact_mod_cast key
  have nn : (0 : ℤ) ≤ s * σ := by positivity
  rcases F with _ | k
  · simp only [Nat.cast_zero, zero_mul] at keyZ
    simp only [Nat.zero_sub, zero_mul, Nat.cast_zero]
    linarith
  · rw [Nat.add_sub_cancel]
    push_cast at keyZ ⊢
    linarith

/-- **Key `9703`: the excess of a hub piece.** -/
theorem route8HubPieceExcess (data : Parameters) (object : FiniteObject.{u})
    (baseline : MinDegreeBaselineStatement data object)
    (mass : Route8HubPieceMassStatement data object) :
    Route8HubPieceExcessStatement data object := by
  classical
  unfold Route8HubPieceExcessStatement
  dsimp only
  intro X hX hpos
  unfold route8PieceExcess route8PieceSurplus
  unfold route8PieceSurplus at hpos
  dsimp only
  refine excess_le_of_mass (d := object.positiveDeficiency
      (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) X)
      data.threshold) ?_ ?_
  · by_cases neg : object.NegativeNetCharge
        (object.pieceSupport (object.remainderSupport (canonicalWindowPacking data object)) X)
        data.threshold data.dischargeScale
    · have hmem : X ∈ route8NegativeHubPieces data object := by
        simp only [route8NegativeHubPieces, Finset.mem_filter]
        exact ⟨hX, neg, hpos⟩
      have h := mass.1 X hmem
      dsimp only at h
      rw [Nat.sub_le_iff_le_add'] at h
      linarith
    · unfold FiniteObject.NegativeNetCharge at neg
      push Not at neg
      exact le_trans neg (Nat.le_add_left _ _)
  · rw [Route8.card_cutEdges_eq_boundaryIncidence]
    exact object.positiveDeficiency_le_boundaryIncidence _ data.threshold
      (fun v => le_trans baseline (object.minDegree_le_degree v))

/-- The arithmetic of key `9704`: at `δ = 3`, `s = 4`, `W = 13`, `c = 30`, the left side of
key `9807` is `(4 + 48F)T − 30σ_W`, and it dominates `13·(F−1)·4·σ_R` once
`σ_W + σ_R ≤ T` and `3 ≤ F ≤ 14`. -/
theorem armClosure_arith {δ s W p T σW σR F : ℕ} {S : ℤ}
    (h3 : δ = 3) (h4 : s = 4) (h13 : W = 13)
    (hsum : σW + σR ≤ T) (F3 : 3 ≤ F) (F14 : F ≤ 14)
    (hlt : ((s * (δ * (W * p) + T) : ℕ) : ℤ) - ((s * (2 * (W - 1) * p) : ℕ) : ℤ) +
        ((s * δ * (F * s * T) : ℕ) : ℤ) - ((30 : ℕ) : ℤ) * (((δ - 1) * p + σW : ℕ) : ℤ) < S)
    (hS : S ≤ ((δ * s + 1 : ℕ) : ℤ) * ((((F - 1) * s : ℕ) : ℤ) * (σR : ℤ))) : False := by
  subst h3 h4 h13
  have hF1 : ((F - 1 : ℕ) : ℤ) = (F : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ F)]; ring
  push_cast [Nat.cast_sub (by omega : 1 ≤ F)] at hlt hS
  have hsumZ : (σW : ℤ) + σR ≤ T := by exact_mod_cast hsum
  have hF14 : (F : ℤ) ≤ 14 := by exact_mod_cast F14
  have hF3 : (3 : ℤ) ≤ F := by exact_mod_cast F3
  have n1 : (0 : ℤ) ≤ σW := by positivity
  have n3 : (0 : ℤ) ≤ T := by positivity
  have a1 : ((F : ℤ) - 1) * σR ≤ ((F : ℤ) - 1) * (T - σW) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a2 : (4 * (F : ℤ) - 56) * T ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) n3
  have a3 : (0 : ℤ) ≤ (52 * (F : ℤ) - 82) * σW :=
    mul_nonneg (by linarith) n1
  nlinarith [a1, a2, a3]

/-- The canonical packing has a placement system once G has a vertex. -/
theorem exists_placement (data : Parameters) (object : FiniteObject.{u})
    [Nonempty object.Vertex] :
    ∃ place : Finset object.Vertex → Fin data.windowOrder → object.Vertex,
      ∀ P ∈ canonicalWindowPacking data object,
        LocalRigidity.IsWindowPlacement object P (place P) := by
  classical
  have h : ∀ P : Finset object.Vertex, ∃ q : Fin data.windowOrder → object.Vertex,
      P ∈ canonicalWindowPacking data object → LocalRigidity.IsWindowPlacement object P q := by
    intro P
    by_cases hP : P ∈ canonicalWindowPacking data object
    · obtain ⟨q, hq⟩ := LocalRigidity.exists_windowPlacement
        ((canonicalWindowPacking_spec data object).1.1 P hP)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨fun _ => Classical.arbitrary _, fun h => absurd h hP⟩
  choose place hplace using h
  exact ⟨place, fun P hP => hplace P hP⟩

/-- **Key `9704`: the arm closure** (Lean improvement: the paper's hub-free sufficiency
`lem:r8-hub-free-suffices`, closed at G from keys `9807`, `9702`, `9703` and the surplus
scale). -/
theorem route8ArmClosure (data : Parameters) (object : FiniteObject.{u})
    (three : data.threshold = 3) (four : data.dischargeScale = 4)
    (order : data.windowOrder = 13)
    (bridge : data.threshold + 2 + data.dischargeScale ≤
      data.bridgeMassFactor * data.dischargeScale)
    (baseline : MinDegreeBaselineStatement data object)
    (surplus : SurplusAtOrBelowStatement data object)
    (residual : Route8ArmClosureResidualStatement data object)
    (pi : Route8HubFreePiStatement data object)
    (hub : Route8HubPieceExcessStatement data object) :
    Route8ArmClosureStatement data object := by
  classical
  unfold Route8ArmClosureStatement
  intro hF large
  have npos : 0 < object.vertexCount := by
    have := large.2.2
    omega
  haveI : Nonempty object.Vertex := (@FinEnum.card_pos_iff _ object.vertices).1 npos
  obtain ⟨place, hplace⟩ := exists_placement data object
  unfold Route8ArmClosureResidualStatement at residual
  unfold Route8HubFreePiStatement at pi
  unfold Route8HubPieceExcessStatement at hub
  dsimp only at pi hub
  have h := residual (by omega) large place hplace 30
  dsimp only at h
  have split := object.ambientSurplus_windowSupport_add_remainderSupport
    (canonicalWindowPacking data object) data.threshold
    (fun v => le_trans baseline (object.minDegree_le_degree v))
  unfold SurplusAtOrBelowStatement at surplus
  have F3 : 3 ≤ data.bridgeMassFactor := by
    rw [three, four] at bridge
    omega
  refine armClosure_arith three four order (split ▸ surplus) F3 hF h ?_
  have c : (0 : ℤ) ≤ ((data.threshold * data.dischargeScale + 1 : ℕ) : ℤ) := by positivity
  have c' : (0 : ℤ) ≤ (((data.bridgeMassFactor - 1) * data.dischargeScale : ℕ) : ℤ) := by
    positivity
  calc _ ≤ ∑ X ∈ (object.canonicalPieces (object.remainderSupport
          (canonicalWindowPacking data object))).filter
            (fun X => 0 < route8PieceExcess data object X),
          ((data.threshold * data.dischargeScale + 1 : ℕ) : ℤ) *
            ((((data.bridgeMassFactor - 1) * data.dischargeScale : ℕ) : ℤ) *
              (route8PieceSurplus data object X : ℤ)) := by
        refine Finset.sum_le_sum fun X hX => ?_
        obtain ⟨hXp, hpos⟩ := Finset.mem_filter.1 hX
        have e30 : ((30 : ℕ) : ℤ) = 30 := by norm_num
        rw [e30]
        have hν : (0 : ℤ) ≤ (route8LongLandingWindows data object place X : ℤ) := by
          positivity
        rcases Nat.eq_zero_or_pos (route8PieceSurplus data object X) with h0 | hσ
        · have hpi := pi place hplace X hXp h0 hpos
          rw [h0]
          simp only [Nat.cast_zero, mul_zero]
          unfold route8PieceExcess at hpi
          dsimp only at hpi
          linarith
        · have hx := mul_le_mul_of_nonneg_left (hub X hXp hσ) c
          unfold route8PieceExcess at hx
          dsimp only at hx
          linarith
    _ ≤ ((data.threshold * data.dischargeScale + 1 : ℕ) : ℤ) *
          ((((data.bridgeMassFactor - 1) * data.dischargeScale : ℕ) : ℤ) *
            (object.ambientSurplus (object.remainderSupport
              (canonicalWindowPacking data object)) data.threshold : ℤ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ c') c
        have hall : ∑ X ∈ object.canonicalPieces (object.remainderSupport
              (canonicalWindowPacking data object)),
            (route8PieceSurplus data object X : ℤ) =
            (object.ambientSurplus (object.remainderSupport
              (canonicalWindowPacking data object)) data.threshold : ℤ) := by
          unfold route8PieceSurplus
          rw [← Nat.cast_sum, object.sum_ambientSurplus_canonicalPieces]
        rw [← hall]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)

end Hypostructure.Graph.Contracts.RouteEight
