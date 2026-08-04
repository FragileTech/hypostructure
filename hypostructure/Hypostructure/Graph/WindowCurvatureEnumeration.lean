import Hypostructure.Graph.WindowCurvatureAlgebra

/-!
# `lem:labels`: the legal-label count and its size distribution

`original_erdos_64_proof.tex`:

> **Lemma (Legal label count).**  The number of legal nonempty labels is
> `|Labels| = 399`.  The distribution by size is `13, 60, 122, 122, 63, 17, 2`
> for sizes `1, 2, 3, 4, 5, 6, 7`, respectively.
>
> *Proof.*  This is a direct enumeration of nonempty subsets of `{0, …, 12}`
> avoiding pairwise differences `2` and `6`.

The enumeration below is that direct enumeration, run by the Lean **kernel**:
the proof is `decide`, so the powerset of the registered window order is
actually traversed and every label is actually tested against the derived
forbidden differences.  There is no `native_decide` and no stored table.

The order enumerated is `WindowCurvature.windowOrder`, i.e. the induced-path
order of the registered external theorem, and the differences tested are
`forbiddenGaps windowOrder 0`, i.e. the differences whose closing cycle the
registered dyadic target accepts.  Neither `13` nor `{2, 6}` is written here.

## What is retrieved

* `WindowCurvature.Labels` and `windowOrder` from
  `Graph/WindowCurvatureAlgebra.lean`;
* the kernel-`decide` precedent for a finite count on this algebra --
  `Graph.TypeBMarkedFan.packingCap_eq_eight` at `Graph/TypeBMarkedFan.lean:294`.
-/

namespace Hypostructure.Graph.WindowCurvature

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The legal labels of a given size.

*Provenance.* Follows `Graph.TypeBMarkedFan.compatibleParts` at
`Graph/TypeBMarkedFan.lean:338`.
-/
def labelsOfSize (order size : Nat) : Finset (Label order) :=
  (Labels order).filter fun label => label.card = size

/-- The size distribution of the legal labels, indexed by size `1, 2, …`.  The
list is as long as the order, which is a complete range of possible sizes: a
label is a set of coordinates, so it has at most `order` of them.

*Provenance.* Follows the `(List.range _).map` enumeration at
`Graph/Strategy/Official/Features/PackedResponseOverload.lean:230`.
-/
def sizeDistribution (order : Nat) : List Nat :=
  (List.range order).map fun index => (labelsOfSize order (index + 1)).card

/-- **`lem:labels`, kernel-checked.**  Both halves of the manuscript's lemma
in one traversal of the powerset of the registered window order.

*Provenance.* Follows `Graph.TypeBMarkedFan.packingCap_eq_eight` at
`Graph/TypeBMarkedFan.lean:294`, the framework's precedent for a
kernel-`decide`d finite count on this algebra; consumes
`WindowCurvature.Labels` and `windowOrder`.
-/
theorem labels_enumeration :
    (Labels windowOrder).card = 399 ∧
      sizeDistribution windowOrder = [13, 60, 122, 122, 63, 17, 2, 0, 0, 0, 0, 0, 0] := by
  decide

/-- **The legal label count.**  `|Labels| = 399`.

*Provenance.* Consumes `labels_enumeration` above.
-/
theorem labels_card : (Labels windowOrder).card = 399 :=
  labels_enumeration.1

/-- **The size distribution.**  `13, 60, 122, 122, 63, 17, 2` for sizes
`1, …, 7`, and no legal label is larger.

*Provenance.* Consumes `labels_enumeration` above.
-/
theorem labels_sizeDistribution :
    sizeDistribution windowOrder =
      [13, 60, 122, 122, 63, 17, 2, 0, 0, 0, 0, 0, 0] :=
  labels_enumeration.2

end Hypostructure.Graph.WindowCurvature
