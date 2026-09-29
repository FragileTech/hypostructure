import Hypostructure.Graph.Contracts.RouteEight.WindowRPath
import Hypostructure.Graph.Statements.Route8BlobStructure
import Hypostructure.Graph.BlobCycles

/-!
# Contracts: the pieces of the remainder against the windows of `P₀` (keys 9900–9902)

The three facts are instantiations at G's canonical data (the remainder of `P₀`, its
canonical pieces, the placements of the windows of `P₀`, the cut edges) of the generic
`BlobCycles` lemmas and of the existing one-window cycle `route8WindowSelfRPathGap`.
-/

namespace Hypostructure.Graph.Contracts.RouteEight

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open scoped BigOperators

universe u

/-- **Key `9900`: a piece attached twice to one window.**  The exclusion is the one-window
cycle `route8WindowSelfRPathGap` read at an internal path of the piece; the run bound is the
dyadic interval lemma `BlobCycles.interval_bound_of_no_pow_two` applied to the shifted run
`[lo + |i−i'| + 2, hi + |i−i'| + 2]`. -/
theorem route8PieceWindowAttachment (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8PieceWindowAttachmentStatement data object := by
  classical
  have selfGap := route8WindowSelfRPathGap data object avoid lengthLaw
  unfold Route8PieceWindowAttachmentStatement
  dsimp only
  intro X _ P hP p hp i i' a b _ _ e₁ e₂ ne
  have excl : ∀ ℓ ∈ pieceLengthSet object (object.pieceSupport
      (object.remainderSupport (canonicalWindowPacking data object)) X) a b,
      ¬ Core.DyadicLength.PowerOfTwoLength (Nat.dist i.1 i'.1 + ℓ + 2) := by
    rintro ℓ ⟨r, rp, rS, rfl⟩
    exact selfGap P hP p hp i i' a b r rp
      (fun v hv => object.pieceSupport_subset _ X (rS v hv)) e₁ e₂ ne
  refine ⟨excl, fun lo hi run => ?_⟩
  have bound := BlobCycles.interval_bound_of_no_pow_two
    (a := lo + Nat.dist i.1 i'.1 + 2) (b := hi + Nat.dist i.1 i'.1 + 2)
    (fun n lower upper pow => by
      refine excl (n - Nat.dist i.1 i'.1 - 2) (run _ (by omega) (by omega)) ?_
      rwa [show Nat.dist i.1 i'.1 + (n - Nat.dist i.1 i'.1 - 2) + 2 = n by omega])
  omega

/-- **Key `9901`: chain cycles through distinct pieces and distinct windows.**  The internal
paths realise the lengths `ℓ i`, the window segments of the placements realise
`|j i − j' i|`, and `BlobCycles.blob_chain_cycle` closes the cycle: pieces are pairwise
disjoint (distinct components), windows of `P₀` are pairwise disjoint, and pieces avoid every
window. -/
theorem route8PieceChainCycle (data : Parameters) (object : FiniteObject.{u})
    (avoid : ¬ HasCycleWithLength data.LengthOK object)
    (lengthLaw : ∀ length, data.LengthOK length ↔
      Core.DyadicLength.PowerOfTwoLength length) :
    Route8PieceChainCycleStatement data object := by
  classical
  unfold Route8PieceChainCycleStatement
  dsimp only
  intro n X P p j j' a b ℓ Xinj Pinj _ hP hp _ _ eIn eOut close hℓ long pow
  have valid := (canonicalWindowPacking_spec data object).1
  have inR : ∀ v, v ∈ object.remainderSupport (canonicalWindowPacking data object) →
      ∀ window ∈ canonicalWindowPacking data object, v ∉ window := by
    intro v hv window hwindow hvw
    have inW := FiniteObject.mem_windowSupport hwindow hvw
    unfold FiniteObject.remainderSupport at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hv
    exact hv inW
  have hℓ' : ∀ i, ∃ r : object.graph.Walk (a i) (b i), r.IsPath ∧
      (∀ v ∈ r.support, v ∈ object.pieceSupport
        (object.remainderSupport (canonicalWindowPacking data object)) (X i)) ∧
      r.length = ℓ i := hℓ
  choose r rp rS rl using hℓ'
  have seg : ∀ i, ∃ w : object.graph.Walk (p i (j i)) (p i (j' i)), w.IsPath ∧
      w.length = Nat.dist (j i).1 (j' i).1 ∧ ∀ v ∈ w.support, v ∈ Set.range (p i) :=
    fun i => LocalRigidity.exists_segment (hp i).isPlacedPath (j i) (j' i)
  choose w wp wl ws using seg
  have wP : ∀ i, ∀ v ∈ (w i).support, v ∈ P i := by
    intro i v hv
    obtain ⟨x, hx⟩ := ws i v hv
    exact hx ▸ (hp i).2.1 x
  have rRem : ∀ i, ∀ v ∈ (r i).support,
      v ∈ object.remainderSupport (canonicalWindowPacking data object) :=
    fun i v hv => object.pieceSupport_subset _ (X i) (rS i v hv)
  have rr : ∀ i k, i ≠ k → ∀ v ∈ (r i).support, v ∉ (r k).support := by
    intro i k ik v hv hv'
    have disjoint := SupportComponents.Connected.disjoint_members object
      (object.remainderSupport (canonicalWindowPacking data object))
      (fun e => ik (Xinj e))
    exact Finset.disjoint_left.mp disjoint (rS i v hv) (rS k v hv')
  have ww : ∀ i k, i ≠ k → ∀ v ∈ (w i).support, v ∉ (w k).support := by
    intro i k ik v hv hv'
    exact Finset.disjoint_left.mp
      (valid.2 (P i) (hP i) (P k) (hP k) (fun e => ik (Pinj e))) (wP i v hv) (wP k v hv')
  have rw' : ∀ i k, ∀ v ∈ (r i).support, v ∉ (w k).support := by
    intro i k v hv hv'
    exact inR v (rRem i v hv) (P k) (hP k) (wP k v hv')
  have hsum : (∑ i, ((r i).length + (w i).length)) =
      ∑ i, (ℓ i + Nat.dist (j i).1 (j' i).1) :=
    Finset.sum_congr rfl (fun i _ => by rw [rl i, wl i])
  obtain ⟨v, cyc, cc, cl⟩ := BlobCycles.blob_chain_cycle n a b (fun i => p i (j i))
    (fun i => p i (j' i)) r w rp wp rr ww rw' eIn eOut close (by rw [hsum]; exact long)
  obtain ⟨k, hk, e⟩ := (Core.DyadicLength.powerOfTwoLength_iff _).mp pow
  exact CycleCounting.no_dyadic_cycle avoid lengthLaw cyc cc k hk (by rw [cl, hsum]; exact e)

/-- **Key `9902`: the rate over the pieces.**  The canonical pieces partition the remainder
(`FiniteObject.sum_canonicalPieces`) and its cut (`sum_boundaryIncidence_canonicalPieces`
with `Route8.card_cutEdges_eq_boundaryIncidence`); the rate of `K .route8Rate` is then a sum
over the pieces, and some piece carries a positive summand. -/
theorem route8PiecewiseRate (data : Parameters) (object : FiniteObject.{u})
    (rate : Route8RateStatement data object) :
    Route8PiecewiseRateStatement data object := by
  classical
  unfold Route8PiecewiseRateStatement
  dsimp only
  set R := object.remainderSupport (canonicalWindowPacking data object) with hR
  have sizeSum : R.card = ∑ X ∈ object.canonicalPieces R, (object.pieceSupport R X).card := by
    have h := object.sum_canonicalPieces R (fun _ => 1)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    exact h.symm
  have exitSum : (Route8.cutEdges object R).card =
      ∑ X ∈ object.canonicalPieces R, (Route8.cutEdges object (object.pieceSupport R X)).card := by
    simp only [Route8.card_cutEdges_eq_boundaryIncidence]
    exact (sum_boundaryIncidence_canonicalPieces object R).symm
  have rateN : (data.threshold * data.dischargeScale + 1) *
        (∑ X ∈ object.canonicalPieces R, (Route8.cutEdges object (object.pieceSupport R X)).card) +
      data.threshold * (data.bridgeMassFactor * data.dischargeScale *
        data.surplusThreshold object.vertexCount) <
      data.threshold * ∑ X ∈ object.canonicalPieces R, (object.pieceSupport R X).card := by
    have r := rate
    unfold Route8RateStatement Graph.Route8Census.Rate Graph.Route8Census.supply at r
    rw [← hR, exitSum, sizeSum] at r
    exact r
  refine ⟨sizeSum, exitSum, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have cast := (Nat.cast_lt (α := ℤ)).2 rateN
    push_cast at cast ⊢
    linarith
  · by_contra none
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at none
    have le : data.threshold * ∑ X ∈ object.canonicalPieces R, (object.pieceSupport R X).card ≤
        (data.threshold * data.dischargeScale + 1) *
          ∑ X ∈ object.canonicalPieces R,
            (Route8.cutEdges object (object.pieceSupport R X)).card := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum (fun X hX => Nat.le_of_not_lt (none hX))
    omega

end Hypostructure.Graph.Contracts.RouteEight
