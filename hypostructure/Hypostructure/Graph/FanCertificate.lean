import Hypostructure.Graph.WindowCurvatureAlgebra
import Hypostructure.Graph.HighCentrePorts

/-!
# Fan label packing: the certificate-marked fan-degree cap

`lem:fan-certificate` and `rem:fan-finite`.  The manuscript's fan-degree bound
`d_G(h) ≤ 8` is *not* a free parameter: it is the independence number of an
explicit difference graph on the window's own coordinates, and this module
derives it rather than naming it.

The manuscript's `D` is the graph on `{0, …, 12}` in which two distinct indices
are adjacent when their difference is `4` or `12`.  Those are exactly the
differences `d` for which the wedge `u — h — v` closes the window into a cycle
of length `4 + d` that the target accepts, so `D` is `ForbiddenGap 2` read as a
relation on coordinates -- which is what `WindowCurvatureAlgebra` already
derives from the registered target.  `α(D) = 2 + 2 + 2 + 2 = 8` at the
manuscript's own order; here it is `fanPackingCap`, a computed quantity, and no
node ever spells its value.

The certificate condition `C₂(S_h(u), S_h(v)) = 1` of `def:marked-typeB-fan` is
`Safe 2` of the same module: the wedge is the length-two outside path, and
`closingLength 2 d = 4 + d` is the manuscript's own display.
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Core.DyadicLength

universe u

/-! ## The difference graph `D` and its independence number -/

/-- **The manuscript's `D`.**  A set of window coordinates is *fan-independent*
when no two distinct members close an accepted cycle through the length-two
wedge.  This is exactly "independent set in `D`". -/
def FanIndependent {order : Nat} (indices : Finset (Fin order)) : Prop :=
  ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
    ¬ ForbiddenGap 2 (Nat.dist i.1 j.1)

instance fanIndependentDecidable {order : Nat} (indices : Finset (Fin order)) :
    Decidable (FanIndependent indices) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _ → _))

/-- **`α(D)`, the fan packing cap.**  The largest fan-independent set of window
coordinates.  At the manuscript's order this is its `2 + 2 + 2 + 2 = 8`; the
value is computed from the registered order and target, and no node writes
it. -/
def fanPackingCap (order : Nat) : Nat :=
  (((Finset.univ : Finset (Fin order)).powerset.filter
    FanIndependent).sup Finset.card)

theorem card_le_fanPackingCap_of_fanIndependent {order : Nat}
    {indices : Finset (Fin order)} (independent : FanIndependent indices) :
    indices.card ≤ fanPackingCap order :=
  Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      independent⟩)

/-- **The wedge through a coordinate and itself closes an accepted cycle.**
`closingLength 2 0 = 4`, and the quadrilateral is accepted.  This is what makes
distinct `C₂`-compatible labels carry distinct representatives, the manuscript's
"since `C₂(S,S) = 0`". -/
theorem forbiddenGap_two_zero : ForbiddenGap 2 0 := by
  have four : closingLength 2 0 = 4 := rfl
  rw [ForbiddenGap, four]
  exact powerOfTwoLength_four

/-! ## `lem:fan-certificate`, the packing bound -/

/-- **`lem:fan-certificate`, first sentence.**

A family of legal labels that is pairwise `C₂`-compatible has size at most
`α(D)`.

The manuscript's argument exactly: choose a representative from each label; the
compatibility relation says no cross-difference between two labels of the family
closes an accepted cycle, so the representatives are pairwise non-adjacent in
`D`, and they are *distinct* because a repeated representative would be a
cross-difference of `0`, which `forbiddenGap_two_zero` forbids.  A family of
distinct pairwise non-adjacent coordinates is an independent set of `D`. -/
theorem card_le_fanPackingCap {order : Nat} (family : Finset (Label order))
    (legal : ∀ label ∈ family, Legal label)
    (compatible : ∀ source ∈ family, ∀ target ∈ family, source ≠ target →
      Safe 2 source target) :
    family.card ≤ fanPackingCap order := by
  classical
  -- An empty family needs no argument; a nonempty one supplies a coordinate,
  -- which is what makes the representative choice available at all.
  rcases Finset.eq_empty_or_nonempty family with empty | ⟨witness, memWitness⟩
  · simp [empty]
  obtain ⟨someIndex, _⟩ := (legal witness memWitness).1
  haveI : Nonempty (Fin order) := ⟨someIndex⟩
  -- One representative index per label, available because a legal label is
  -- nonempty.
  have nonempty : ∀ label ∈ family, ∃ index, index ∈ label :=
    fun label member => (legal label member).1
  choose! representative mem_representative using nonempty
  -- Distinct labels of the family carry distinct representatives.
  have injective : Set.InjOn representative family := by
    intro source memSource target memTarget same
    by_contra different
    refine compatible source memSource target memTarget different
      (representative source) (mem_representative source memSource)
      (representative target) (mem_representative target memTarget) ?_
    rw [same, Nat.dist_self]
    exact forbiddenGap_two_zero
  have independent : FanIndependent (family.image representative) := by
    intro first memFirst second memSecond different
    obtain ⟨source, memSource, sourceEq⟩ := Finset.mem_image.mp memFirst
    obtain ⟨target, memTarget, targetEq⟩ := Finset.mem_image.mp memSecond
    have labelsDifferent : source ≠ target := by
      intro same
      exact different (by rw [← sourceEq, ← targetEq, same])
    subst sourceEq
    subst targetEq
    exact compatible source memSource target memTarget labelsDifferent
      (representative source) (mem_representative source memSource)
      (representative target) (mem_representative target memTarget)
  calc family.card
      = (family.image representative).card :=
        (Finset.card_image_of_injOn injective).symm
    _ ≤ fanPackingCap order :=
        card_le_fanPackingCap_of_fanIndependent independent

/-! ## The non-singleton refinement -/

/-- **`N_D[S]`, the closed `D`-neighbourhood of a label.**  A coordinate is
excluded by `S` when some index of `S` closes an accepted cycle with it through
the wedge.  Because `forbiddenGap_two_zero` holds, `S ⊆ N_D[S]`, so the
neighbourhood really is closed. -/
def fanClosedNeighbourhood {order : Nat} (label : Label order) :
    Finset (Fin order) :=
  (Finset.univ : Finset (Fin order)).filter
    (fun index => ∃ i ∈ label, ForbiddenGap 2 (Nat.dist i.1 index.1))

theorem subset_fanClosedNeighbourhood {order : Nat} (label : Label order) :
    label ⊆ fanClosedNeighbourhood label := by
  intro index member
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, index, member, ?_⟩
  rw [Nat.dist_self]
  exact forbiddenGap_two_zero

/-- **`α(D[A])` for `A` the complement of an excluded set.**  The largest
fan-independent set of coordinates avoiding `excluded`. -/
def fanPackingCapAvoiding (order : Nat) (excluded : Finset (Fin order)) :
    Nat :=
  (((Finset.univ : Finset (Fin order)).powerset.filter
    (fun indices => FanIndependent indices ∧ Disjoint indices excluded)).sup
      Finset.card)

/-- **`lem:fan-certificate`, second sentence.**

A pairwise `C₂`-compatible family containing the label `S` has size at most
`1 + α(D[A])`, where `A` is the complement of `N_D[S]`.

The manuscript's argument exactly: every *other* label of the family is
compatible with `S`, so none of its indices lies in `N_D[S]`; the
representatives of the others therefore form an independent set of `D` avoiding
`N_D[S]`.  The manuscript then computes `α(D[A]) ≤ 6` when `S` is a
non-singleton, which is where its `≤ 7` comes from; that computation is a
consequence of this bound at the registered order, not a separate hypothesis. -/
theorem card_le_one_add_fanPackingCapAvoiding {order : Nat}
    (family : Finset (Label order)) (label : Label order)
    (member : label ∈ family)
    (legal : ∀ other ∈ family, Legal other)
    (compatible : ∀ source ∈ family, ∀ target ∈ family, source ≠ target →
      Safe 2 source target) :
    family.card ≤ 1 + fanPackingCapAvoiding order
      (fanClosedNeighbourhood label) := by
  classical
  obtain ⟨someIndex, _⟩ := (legal label member).1
  haveI : Nonempty (Fin order) := ⟨someIndex⟩
  have nonempty : ∀ other ∈ family.erase label, ∃ index, index ∈ other :=
    fun other memOther =>
      (legal other (Finset.mem_of_mem_erase memOther)).1
  choose! representative mem_representative using nonempty
  have injective : Set.InjOn representative (family.erase label) := by
    intro source memSource target memTarget same
    by_contra different
    exact compatible source (Finset.mem_of_mem_erase memSource) target
      (Finset.mem_of_mem_erase memTarget) different
      (representative source) (mem_representative source memSource)
      (representative target) (mem_representative target memTarget)
      (by rw [same, Nat.dist_self]; exact forbiddenGap_two_zero)
  have independent : FanIndependent ((family.erase label).image representative) := by
    intro first memFirst second memSecond different
    obtain ⟨source, memSource, sourceEq⟩ := Finset.mem_image.mp memFirst
    obtain ⟨target, memTarget, targetEq⟩ := Finset.mem_image.mp memSecond
    have labelsDifferent : source ≠ target := by
      intro same
      exact different (by rw [← sourceEq, ← targetEq, same])
    subst sourceEq
    subst targetEq
    exact compatible source (Finset.mem_of_mem_erase memSource) target
      (Finset.mem_of_mem_erase memTarget) labelsDifferent
      (representative source) (mem_representative source memSource)
      (representative target) (mem_representative target memTarget)
  have avoids :
      Disjoint ((family.erase label).image representative)
        (fanClosedNeighbourhood label) := by
    rw [Finset.disjoint_left]
    intro index memImage memExcluded
    obtain ⟨other, memOther, otherEq⟩ := Finset.mem_image.mp memImage
    obtain ⟨i, memI, forbidden⟩ :=
      (Finset.mem_filter.mp memExcluded).2
    -- `other` is compatible with `label`, so no cross-difference is forbidden.
    refine compatible label member other (Finset.mem_of_mem_erase memOther)
      (Ne.symm (Finset.ne_of_mem_erase memOther)) i memI
      (representative other) (mem_representative other memOther) ?_
    rwa [otherEq]
  have bound :
      ((family.erase label).image representative).card ≤
        fanPackingCapAvoiding order (fanClosedNeighbourhood label) :=
    Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        independent, avoids⟩)
  have erased : (family.erase label).card = family.card - 1 :=
    Finset.card_erase_of_mem member
  have positive : 1 ≤ family.card := Finset.card_pos.mpr ⟨label, member⟩
  rw [Finset.card_image_of_injOn injective, erased] at bound
  omega

end Hypostructure.Graph.WindowCurvature

/-! ## `def:marked-typeB-fan`: the certificate-marked fan, and its degree cap -/

namespace Hypostructure.Graph

universe u

open Hypostructure.Graph.WindowCurvature

/-- **`def:marked-typeB-fan`.**  A fan-certificate labelling of a high centre
`h` assigns to each neighbour of `h` a legal window label, pairwise
`C₂`-compatible.

The manuscript's `S_h : N(h) → 𝓛`.  Nothing else of the marked fan is recorded
here: the neighbour set is `N_G(h)` and the centre's own data is the pair. -/
structure FanCertificateLabelling (object : FiniteObject.{u}) (order : Nat)
    (centre : object.Vertex) where
  /-- `S_h`, defined on the neighbours of `h`. -/
  label : object.Vertex → Label order
  /-- Every assigned label is a legal nonempty `P₁₃` label of `lem:labels`. -/
  legal : ∀ ⦃neighbour : object.Vertex⦄,
    object.graph.Adj centre neighbour → Legal (label neighbour)
  /-- `C₂(S_h(u), S_h(v)) = 1` for distinct neighbours: the wedge `u — h — v` is
  the length-two outside path, and it must close no accepted cycle. -/
  compatible : ∀ ⦃left right : object.Vertex⦄,
    object.graph.Adj centre left → object.graph.Adj centre right →
    left ≠ right → Safe 2 (label left) (label right)

namespace FanCertificateLabelling

variable {object : FiniteObject.{u}} {order : Nat} {centre : object.Vertex}

/-- **Distinct neighbours of a marked fan carry distinct labels.**  The
manuscript's "since `C₂(S,S) = 0`, the labels of distinct neighbours are
distinct".  Stated pointwise, so that it mentions no finite carrier and needs no
decidable equality on the object's vertices. -/
theorem label_inj (marking : FanCertificateLabelling object order centre)
    ⦃left right : object.Vertex⦄
    (adjLeft : object.graph.Adj centre left)
    (adjRight : object.graph.Adj centre right)
    (same : marking.label left = marking.label right) : left = right := by
  by_contra different
  obtain ⟨index, memIndex⟩ := (marking.legal adjLeft).1
  refine marking.compatible adjLeft adjRight different index memIndex index
    (same ▸ memIndex) ?_
  rw [Nat.dist_self]
  exact forbiddenGap_two_zero

/-- **`lem:fan-certificate`, third sentence — the certificate-marked fan-degree
cap.**

`d_G(h) ≤ α(D)`.  At the manuscript's registered order this is its `d_G(h) ≤ 8`,
and `rem:fan-finite` is the observation being made: the bound is the label
algebra's own packing constraint, read off the registered target, not a
parameter of the proof.

The degree is the size of the label family, because distinct neighbours carry
distinct labels; the family is legal and pairwise compatible by the marking; so
`card_le_fanPackingCap` applies. -/
theorem degree_le_fanPackingCap
    (marking : FanCertificateLabelling object order centre) :
    object.degree centre ≤ fanPackingCap order := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  classical
  have neighbours : ∀ vertex ∈ (object.orderedNeighbors centre).toFinset,
      object.graph.Adj centre vertex := fun vertex member =>
    (object.mem_orderedNeighbors_iff centre vertex).mp (List.mem_toFinset.mp member)
  have degreeEq :
      object.degree centre = (object.orderedNeighbors centre).toFinset.card := by
    rw [List.toFinset_card_of_nodup (object.orderedNeighbors_nodup centre),
      object.orderedNeighbors_length centre]
  have imageCard :
      ((object.orderedNeighbors centre).toFinset.image marking.label).card =
        (object.orderedNeighbors centre).toFinset.card :=
    Finset.card_image_of_injOn fun left memLeft right memRight same =>
      marking.label_inj (neighbours left memLeft) (neighbours right memRight) same
  rw [degreeEq, ← imageCard]
  refine card_le_fanPackingCap _ ?_ ?_
  · intro assigned member
    obtain ⟨vertex, memVertex, vertexEq⟩ := Finset.mem_image.mp member
    exact vertexEq ▸ marking.legal (neighbours vertex memVertex)
  · intro source memSource target memTarget different
    obtain ⟨left, memLeft, leftEq⟩ := Finset.mem_image.mp memSource
    obtain ⟨right, memRight, rightEq⟩ := Finset.mem_image.mp memTarget
    subst leftEq
    subst rightEq
    exact marking.compatible (neighbours left memLeft) (neighbours right memRight)
      (fun same => different (by rw [same]))

end FanCertificateLabelling

end Hypostructure.Graph
