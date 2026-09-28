import Hypostructure.Graph.WindowCurvatureEnumeration

/-!
# The census determines the window order

Every singleton label is legal (a single outside vertex attached once closes a
cycle of length `2`, never a power of two `≥ 4`), so the first entry of the size
distribution of the legal labels of a path of order `N` is `N` itself
(`labelsOfSize_one_card`).  Hence a size distribution beginning with `m` fixes the
order to `m` (`order_eq_of_sizeDistribution_head`).
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Core.DyadicLength

/-- A singleton label is legal. -/
theorem singleton_legal {order : Nat} (i : Fin order) : Legal ({i} : Label order) := by
  refine ⟨Finset.singleton_nonempty i, ?_⟩
  intro a ha b hb forbidden
  rw [Finset.mem_singleton] at ha hb
  subst ha; subst hb
  simp only [Nat.dist_self] at forbidden
  revert forbidden
  unfold ForbiddenGap closingLength
  decide

/-- The legal labels of size `1` are exactly the singletons. -/
theorem labelsOfSize_one_eq (order : Nat) :
    labelsOfSize order 1 = Finset.powersetCard 1 Finset.univ := by
  ext label
  simp only [labelsOfSize, Labels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard, Finset.subset_univ]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h
    exact ⟨singleton_legal i, h⟩

/-- **There are exactly `order` legal labels of size `1`.** -/
theorem labelsOfSize_one_card (order : Nat) : (labelsOfSize order 1).card = order := by
  rw [labelsOfSize_one_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_one_right]

/-- **The size distribution fixes the order**: if it begins with `m`, the order is `m`. -/
theorem order_eq_of_sizeDistribution_head {order m : Nat} {rest : List Nat}
    (census : (sizeDistribution order).take 7 = m :: rest) : order = m := by
  cases order with
  | zero => simp [sizeDistribution] at census
  | succ k =>
      have : sizeDistribution (k + 1) =
          (labelsOfSize (k + 1) 1).card ::
            (List.range k).map fun index => (labelsOfSize (k + 1) (index + 2)).card := by
        simp only [sizeDistribution, List.range_succ_eq_map, List.map_cons, List.map_map]
        rfl
      rw [this, List.take_succ_cons, List.cons.injEq, labelsOfSize_one_card] at census
      exact census.1

end Hypostructure.Graph.WindowCurvature
