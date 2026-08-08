import Mathlib.Data.Finset.Max
import Hypostructure.Graph.DecoratedFan

/-!
# Certificate-marked Type B fans and the fan-degree label-packing cap

This file is pure finite graph mathematics.  It formalises two manuscript
items of `original_erdos_64_proof.tex`:

* `def:marked-typeB-fan` (node `[70]`): a *fan-certificate labelling* of a
  high-degree centre `h` is a map `S_h : N(h) → 𝓛` into the legal nonempty
  `P₁₃` labels with `C₂(S_h u, S_h v) = 1` for distinct neighbours; a *marked
  Type B fan* is the data of `h`, its neighbour set `N(h)` and such a
  labelling.  A high-degree centre carrying no such labelling is a
  *fan-certificate residual centre*.  The definition also names the
  *cubic-closed* neighbours, those whose two non-`h` incidences are carried by
  the assigned fan support, so that `N_G(u) = {h, x_u, y_u}`.

* `rem:fan-finite` (node `[71]`): the fan-degree bound `d_G(h) ≤ 8` is a
  label-packing statement.  Two neighbours attaching to a common packed `P₁₃`
  window with labels `S, T` are fan-return-safe through that window exactly
  when `C₂(S, T) = 1`; the wedge `u - h - v` is the length-two outside path,
  closing the window into a cycle of length `4 + |i - j|`, which must avoid the
  powers of two.  The bound is then a packing bound for the auxiliary
  difference graph `D`, not a free parameter.

The cap is *derived*: `Marked` records only the manuscript data (hub, rim
equal to the neighbourhood, degree at least four, and a pairwise
`C₂`-compatible labelling).  The cap itself is `packingCap`, the block count of
`packingClass`'s explicit clique cover of `D`, computed rather than declared;
`packingCap_eq_eight` is the only place the numeral `8` is produced, and the
constant `7` of the non-singleton refinement enters solely through
`compatibleParts`.  No numeric degree hypothesis is assumed.

Both constants are functions of the label algebra — the window coordinates
`Index` of a packed `P₁₃` and the target's dyadic length set, through
`isDyadic_wedgeCycle_iff`'s forbidden gaps `{0, 4, 12}`.  Neither is a function
of the presentation's baseline degree: `k` occurs in no definition of this
file.

One presentation constant *is* still written out here, and it is a different
one: `Marked.highDegree`'s `4` (and its companions in
`IsFanCertificateResidual`) is `baselineDegree + 1` at the registered baseline
`k = 3`, i.e. `def:marked-typeB-fan`'s "high-degree centre".  Parameterising
`Marked` by `k` would change the signature of every Type B lemma that consumes
it in the live `TypeBProfileSchedule` and `TypeBHybridLedger` chain; it is
recorded here rather than silently rewritten.

Manuscript invariants used: 16 (certificate-marked fan degree) and 25 (legal
`P₁₃` labels).

The fan object is `Hypostructure.Graph.DecoratedFan.Certificate`; no second
fan structure is introduced here.
-/

namespace Hypostructure.Graph.TypeBMarkedFan

open Hypostructure

universe u v

/-! ## The `P₁₃` label algebra (manuscript invariant 25) -/

/-- Coordinates of an induced `P₁₃ = v₀v₁⋯v₁₂`. -/
abbrev Index : Type := Fin 13

/-- The manuscript's set `Pow` of powers of two, as a predicate on lengths. -/
def IsDyadic (length : Nat) : Prop := ∃ exponent : Nat, length = 2 ^ exponent

/-- Distance between two window coordinates: the manuscript's `|i - j|`. -/
def gap (i j : Index) : Nat := max i.val j.val - min i.val j.val

@[simp]
theorem gap_self (i : Index) : gap i i = 0 := by simp [gap]

theorem gap_comm (i j : Index) : gap i j = gap j i := by
  simp [gap, Nat.max_comm, Nat.min_comm]

theorem gap_le_twelve (i j : Index) : gap i j ≤ 12 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [gap]
  omega

theorem gap_eq_zero_iff {i j : Index} : gap i j = 0 ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simp only [gap] at h
    omega
  · rintro rfl; simp

/-- Powers of two below `16` are exactly `1, 2, 4, 8, 16`. -/
theorem isDyadic_iff_of_le_sixteen {length : Nat} (bound : length ≤ 16) :
    IsDyadic length ↔
      length = 1 ∨ length = 2 ∨ length = 4 ∨ length = 8 ∨ length = 16 := by
  constructor
  · rintro ⟨exponent, rfl⟩
    have small : exponent ≤ 4 := by
      by_contra contra
      have step : 2 ^ 5 ≤ 2 ^ exponent :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at step
      omega
    interval_cases exponent <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

/-- The cycle produced by one outside vertex attaching at two window
coordinates: the subpath `vᵢ⋯vⱼ` closed by the two attachment edges. -/
def attachmentCycleLength (i j : Index) : Nat := gap i j + 2

/-- The cycle produced by an outside path of length `s` joining two attachment
coordinates.  For `s = 2` this is the fan wedge `u - h - v` of
`rem:fan-finite`, closing the window into a cycle of length `4 + |i - j|`. -/
def outsideCycleLength (s : Nat) (i j : Index) : Nat := s + 2 + gap i j

/-- A nonempty label is legal when no single outside vertex carrying it closes
a power-of-two cycle with the window.  The manuscript's characterisation is
`|i - j| ∉ {2, 6}`. -/
def IsLegal (indices : Finset Index) : Prop :=
  ∀ i ∈ indices, ∀ j ∈ indices, gap i j ≠ 2 ∧ gap i j ≠ 6

/-- The single-vertex attachment cycle is dyadic exactly for the forbidden
gaps `0`, `2`, `6`; gap `0` is the degenerate coincidence `i = j`. -/
theorem isDyadic_attachmentCycleLength_iff (i j : Index) :
    IsDyadic (attachmentCycleLength i j) ↔
      gap i j = 0 ∨ gap i j = 2 ∨ gap i j = 6 := by
  have hle := gap_le_twelve i j
  have bound : attachmentCycleLength i j ≤ 16 := by
    unfold attachmentCycleLength; omega
  rw [isDyadic_iff_of_le_sixteen bound]
  unfold attachmentCycleLength
  omega

theorem isLegal_iff_attachment_not_dyadic (indices : Finset Index) :
    IsLegal indices ↔
      ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
        ¬ IsDyadic (attachmentCycleLength i j) := by
  constructor
  · intro legal i hi j hj distinct
    rw [isDyadic_attachmentCycleLength_iff]
    obtain ⟨two, six⟩ := legal i hi j hj
    have zero : gap i j ≠ 0 := fun h => distinct (gap_eq_zero_iff.1 h)
    tauto
  · intro safe i hi j hj
    by_cases hij : i = j
    · subst hij; exact ⟨by simp, by simp⟩
    · have hsafe := safe i hi j hj hij
      rw [isDyadic_attachmentCycleLength_iff] at hsafe
      tauto

/-- The legal nonempty `P₁₃` labels `𝓛` of `lem:labels`. -/
structure Label where
  indices : Finset Index
  nonempty : indices.Nonempty
  legal : IsLegal indices

/-- Every singleton attachment set is a legal label. -/
def Label.ofIndex (i : Index) : Label where
  indices := {i}
  nonempty := ⟨i, by simp⟩
  legal := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    exact ⟨by simp, by simp⟩

@[simp]
theorem Label.indices_ofIndex (i : Index) : (Label.ofIndex i).indices = {i} := rfl

/-- The manuscript's safety relation `C_s(S, T) = 1`: every outside path of
length `s` between the two labels closes a non-dyadic cycle. -/
def SafeAtDistance (s : Nat) (source target : Finset Index) : Prop :=
  ∀ i ∈ source, ∀ j ∈ target, ¬ IsDyadic (outsideCycleLength s i j)

/-- `C₂(S, T) = 1`: the fan wedge `u - h - v` is a safe length-two outside
path through the common window. -/
def WedgeSafe (source target : Finset Index) : Prop := SafeAtDistance 2 source target

/-- The arithmetic step of `rem:fan-finite`: the fan wedge closes the window
into a cycle of length `4 + |i - j|`, which is a power of two exactly for the
cross-differences `0`, `4`, `12`. -/
theorem isDyadic_wedgeCycle_iff (i j : Index) :
    IsDyadic (outsideCycleLength 2 i j) ↔
      gap i j = 0 ∨ gap i j = 4 ∨ gap i j = 12 := by
  have hle := gap_le_twelve i j
  have bound : outsideCycleLength 2 i j ≤ 16 := by
    unfold outsideCycleLength; omega
  rw [isDyadic_iff_of_le_sixteen bound]
  unfold outsideCycleLength
  omega

/-- The explicit content of `C₂`: no cross-difference is `0`, `4` or `12`. -/
theorem wedgeSafe_iff (source target : Finset Index) :
    WedgeSafe source target ↔
      ∀ i ∈ source, ∀ j ∈ target,
        gap i j ≠ 0 ∧ gap i j ≠ 4 ∧ gap i j ≠ 12 := by
  unfold WedgeSafe SafeAtDistance
  constructor
  · intro safe i hi j hj
    have hsafe := safe i hi j hj
    rw [isDyadic_wedgeCycle_iff] at hsafe
    tauto
  · intro cross i hi j hj
    rw [isDyadic_wedgeCycle_iff]
    have hcross := cross i hi j hj
    tauto

/-- Two singleton labels are wedge-safe exactly when their gap avoids the
dyadic cross-differences. -/
theorem wedgeSafe_ofIndex {i j : Index}
    (cross : gap i j ≠ 0 ∧ gap i j ≠ 4 ∧ gap i j ≠ 12) :
    WedgeSafe (Label.ofIndex i).indices (Label.ofIndex j).indices := by
  rw [wedgeSafe_iff]
  intro a ha b hb
  simp only [Label.indices_ofIndex, Finset.mem_singleton] at ha hb
  subst ha; subst hb
  exact cross

theorem wedgeSafe_comm {source target : Finset Index} (safe : WedgeSafe source target) :
    WedgeSafe target source := by
  rw [wedgeSafe_iff] at safe ⊢
  intro i hi j hj
  have := safe j hj i hi
  rw [gap_comm i j]
  exact this

/-- `C₂(S, S) = 0` for every nonempty label: a neighbour is never wedge-safe
against its own label.  This is why distinct fan neighbours carry distinct
labels. -/
theorem not_wedgeSafe_self {indices : Finset Index} (nonempty : indices.Nonempty) :
    ¬ WedgeSafe indices indices := by
  obtain ⟨i, hi⟩ := nonempty
  intro safe
  have := ((wedgeSafe_iff indices indices).1 safe) i hi i hi
  simp at this

/-! ## The difference graph `D` and its clique cover -/

/-- The manuscript's auxiliary graph `D` on `{0, …, 12}`: distinct indices are
adjacent exactly when their difference is `4` or `12`.  Its components are the
four-cycle `0-4-8-12-0` and the three paths `1-5-9`, `2-6-10`, `3-7-11`. -/
def DAdj (i j : Index) : Prop := i ≠ j ∧ (gap i j = 4 ∨ gap i j = 12)

instance decidableDAdj (i j : Index) : Decidable (DAdj i j) :=
  inferInstanceAs (Decidable (i ≠ j ∧ (gap i j = 4 ∨ gap i j = 12)))

/-- Independent sets of `D`. -/
def DIndep (support : Finset Index) : Prop :=
  ∀ i ∈ support, ∀ j ∈ support, ¬ DAdj i j

instance decidableDIndep (support : Finset Index) : Decidable (DIndep support) :=
  inferInstanceAs (Decidable (∀ i ∈ support, ∀ j ∈ support, ¬ DAdj i j))

/-- An explicit cover of `D` by cliques:
`{0,4} {8,12} {1,5} {9} {2,6} {10} {3,7} {11}`.
Each block is an edge or an isolated vertex of `D`, so an independent set of
`D` meets each block at most once.  This is where the cap of
`rem:fan-finite` comes from. -/
def packingClass (i : Index) : Nat :=
  match i.val with
  | 0 => 0 | 4 => 0
  | 8 => 1 | 12 => 1
  | 1 => 2 | 5 => 2
  | 9 => 3
  | 2 => 4 | 6 => 4
  | 10 => 5
  | 3 => 6 | 7 => 6
  | _ => 7

/-- **The fan-degree cap of `rem:fan-finite`, as a computed quantity.**

The cap is the number of blocks of the clique cover above, i.e. the number of
distinct values `packingClass` takes on the window coordinates.  It is not
written as a numeral anywhere: it is read off the cover, which in turn is
determined by the two data of the label algebra — the window order (`Index`,
the coordinates of a packed `P₁₃`) and the forbidden wedge gaps `{0, 4, 12}`
of `isDyadic_wedgeCycle_iff`, i.e. the target's dyadic length set.

It is *not* a function of the presentation's baseline degree.  The baseline
`k` never enters `DAdj`, `packingClass` or any statement below; the manuscript
says the same in `rem:fan-finite` ("the clique bound `d_G(h) ≤ ω(𝔉safe_h)` is
an explicit structural consequence of the label algebra"), and the numeral it
records — `8` — is `packingCap_eq_eight`, a computation on the label algebra
alone. -/
def packingCap : Nat :=
  ((Finset.univ : Finset Index).image packingClass).card

/-- The cover has eight blocks, so `rem:fan-finite`'s recorded cap is `8`.
This is the *only* place the numeral is produced, and it is produced by
computing the cover rather than by declaring it. -/
theorem packingCap_eq_eight : packingCap = 8 := by decide

theorem packingClass_lt_eight (i : Index) : packingClass i < 8 := by
  revert i; decide

/-- Every block of the cover is a clique of `D`. -/
theorem dAdj_of_packingClass_eq {i j : Index}
    (same : packingClass i = packingClass j) (distinct : i ≠ j) : DAdj i j := by
  refine ⟨distinct, ?_⟩
  revert same distinct
  revert i j
  decide

/-- `α(D) ≤ packingCap`: an independent set of `D` meets every block of the
cover at most once, so it has at most as many elements as the cover has
blocks.  No numeral occurs. -/
theorem card_le_packingCap_of_dIndep {support : Finset Index}
    (indep : DIndep support) : support.card ≤ packingCap :=
  Finset.card_le_card_of_injOn (s := support)
    (t := (Finset.univ : Finset Index).image packingClass) packingClass
    (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a))
    (by
      intro a ha b hb same
      by_contra distinct
      exact indep a ha b hb (dAdj_of_packingClass_eq same distinct))

/-- `α(D) ≤ 8`: the previous bound with the cover's block count computed. -/
theorem card_le_eight_of_dIndep {support : Finset Index} (indep : DIndep support) :
    support.card ≤ 8 :=
  packingCap_eq_eight ▸ card_le_packingCap_of_dIndep indep

/-- The constant `8` is exactly `α(D)`, not a slack bound: the eight indices
`{0, 8, 1, 9, 2, 10, 3, 11}` — two per component of `D` — are pairwise
non-adjacent.  Hence `card_le_eight_of_dIndep` cannot be improved. -/
theorem dIndep_card_eight_witness :
    DIndep ({0, 8, 1, 9, 2, 10, 3, 11} : Finset Index) ∧
      ({0, 8, 1, 9, 2, 10, 3, 11} : Finset Index).card = 8 := by
  constructor
  · decide
  · decide

/-- Cover blocks still reachable after deleting the closed `D`-neighbourhoods
of two distinct indices `a` and `b`.  Two full blocks are always destroyed,
which is where the constant `7` of the non-singleton refinement comes from. -/
def compatibleParts (a b : Index) : Finset Nat :=
  ((Finset.univ : Finset Index).filter
    (fun x => gap x a ≠ 0 ∧ gap x a ≠ 4 ∧ gap x a ≠ 12 ∧
              gap x b ≠ 0 ∧ gap x b ≠ 4 ∧ gap x b ≠ 12)).image packingClass

theorem card_compatibleParts_le_six {a b : Index} (distinct : a ≠ b) :
    (compatibleParts a b).card ≤ 6 := by
  revert distinct; revert a b; decide

/-! ## Label packing (`rem:fan-finite`) -/

section Packing

variable {Carrier : Type v}

/-- Canonical representative of a label: its least window coordinate. -/
def Label.representative (label : Label) : Index :=
  label.indices.min' label.nonempty

theorem Label.representative_mem (label : Label) :
    label.representative ∈ label.indices :=
  Finset.min'_mem _ _

/-- **Fan label packing.**  A family of legal labels that is pairwise
`C₂`-compatible has at most `packingCap` members.  Representatives of the
labels are distinct and form an independent set in the difference graph `D`,
whose independence number is bounded by the explicit clique cover.  The bound
is the cover's own block count; no numeral is written. -/
theorem card_le_packingCap_of_pairwise_wedgeSafe
    (carrier : Finset Carrier) (labelling : Carrier → Label)
    (pairwise : ∀ u ∈ carrier, ∀ v ∈ carrier, u ≠ v →
      WedgeSafe (labelling u).indices (labelling v).indices) :
    carrier.card ≤ packingCap := by
  classical
  set rep : Carrier → Index := fun v => (labelling v).representative with hrep
  have cross : ∀ u ∈ carrier, ∀ v ∈ carrier, u ≠ v →
      gap (rep u) (rep v) ≠ 0 ∧ gap (rep u) (rep v) ≠ 4 ∧
        gap (rep u) (rep v) ≠ 12 := by
    intro u hu v hv distinct
    exact ((wedgeSafe_iff _ _).1 (pairwise u hu v hv distinct))
      _ (labelling u).representative_mem _ (labelling v).representative_mem
  have inj : Set.InjOn rep ↑carrier := by
    intro u hu v hv same
    by_contra distinct
    exact (cross u hu v hv distinct).1
      (by rw [same]; simp)
  have image_card : (carrier.image rep).card = carrier.card :=
    Finset.card_image_of_injOn inj
  rw [← image_card]
  refine card_le_packingCap_of_dIndep ?_
  intro i hi j hj adjacent
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
  have distinct : u ≠ v := by
    rintro rfl
    exact adjacent.1 rfl
  obtain ⟨zero, four, twelve⟩ := cross u hu v hv distinct
  rcases adjacent.2 with h | h
  exacts [four h, twelve h]

/-- The same packing bound with the cover's block count computed: at most
eight pairwise `C₂`-compatible legal labels. -/
theorem card_le_eight_of_pairwise_wedgeSafe
    (carrier : Finset Carrier) (labelling : Carrier → Label)
    (pairwise : ∀ u ∈ carrier, ∀ v ∈ carrier, u ≠ v →
      WedgeSafe (labelling u).indices (labelling v).indices) :
    carrier.card ≤ 8 :=
  packingCap_eq_eight ▸
    card_le_packingCap_of_pairwise_wedgeSafe carrier labelling pairwise

/-- **Non-singleton refinement.**  If some member of a pairwise
`C₂`-compatible family carries a label with at least two window coordinates,
the family has at most seven members. -/
theorem card_le_seven_of_pairwise_wedgeSafe_of_nonsingleton
    (carrier : Finset Carrier) (labelling : Carrier → Label)
    (pairwise : ∀ u ∈ carrier, ∀ v ∈ carrier, u ≠ v →
      WedgeSafe (labelling u).indices (labelling v).indices)
    {witness : Carrier} (mem : witness ∈ carrier)
    (nonsingleton : 2 ≤ (labelling witness).indices.card) :
    carrier.card ≤ 7 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 nonsingleton
  set rep : Carrier → Index := fun v => (labelling v).representative with hrep
  have cross : ∀ u ∈ carrier, ∀ v ∈ carrier, u ≠ v →
      gap (rep u) (rep v) ≠ 0 ∧ gap (rep u) (rep v) ≠ 4 ∧
        gap (rep u) (rep v) ≠ 12 := by
    intro u hu v hv distinct
    exact ((wedgeSafe_iff _ _).1 (pairwise u hu v hv distinct))
      _ (labelling u).representative_mem _ (labelling v).representative_mem
  have avoid : ∀ v ∈ carrier.erase witness,
      gap (rep v) a ≠ 0 ∧ gap (rep v) a ≠ 4 ∧ gap (rep v) a ≠ 12 ∧
      gap (rep v) b ≠ 0 ∧ gap (rep v) b ≠ 4 ∧ gap (rep v) b ≠ 12 := by
    intro v hv
    have distinct : v ≠ witness := Finset.ne_of_mem_erase hv
    have hvmem : v ∈ carrier := Finset.mem_of_mem_erase hv
    have safe := (wedgeSafe_iff _ _).1 (pairwise v hvmem witness mem distinct)
      _ (labelling v).representative_mem
    obtain ⟨za, fa, ta⟩ := safe a ha
    obtain ⟨zb, fb, tb⟩ := safe b hb
    exact ⟨za, fa, ta, zb, fb, tb⟩
  have erased : (carrier.erase witness).card ≤ 6 := by
    refine le_trans ?_ (card_compatibleParts_le_six hab)
    refine Finset.card_le_card_of_injOn (fun v => packingClass (rep v)) ?_ ?_
    · intro v hv
      refine Finset.mem_image_of_mem _ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact avoid v hv
    · intro u hu v hv same
      by_contra distinct
      have hum : u ∈ carrier := Finset.mem_of_mem_erase hu
      have hvm : v ∈ carrier := Finset.mem_of_mem_erase hv
      obtain ⟨zero, four, twelve⟩ := cross u hum v hvm distinct
      have repdistinct : rep u ≠ rep v := by
        intro same'; exact zero (by rw [same']; simp)
      rcases (dAdj_of_packingClass_eq same repdistinct).2 with h | h
      exacts [four h, twelve h]
  have restore : (carrier.erase witness).card + 1 = carrier.card :=
    Finset.card_erase_add_one mem
  omega

end Packing

/-! ## Marked Type B fans (`def:marked-typeB-fan`) -/

variable {object : FiniteObject.{u}}

/-- The neighbourhood `N(h)` of a hub as a support, taken from the framework's
declared neighbour order. -/
def neighbourRim (object : FiniteObject.{u}) (hub : object.Vertex) :
    Finset object.Vertex :=
  letI : DecidableEq object.Vertex := object.vertices.decEq
  (object.orderedNeighbors hub).toFinset

@[simp]
theorem mem_neighbourRim (object : FiniteObject.{u}) (hub vertex : object.Vertex) :
    vertex ∈ neighbourRim object hub ↔ object.graph.Adj hub vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  simp [neighbourRim]

/-- Any support that literally is `N(h)` has cardinality `d_G(h)`. -/
theorem card_eq_degree_of_isNeighbourhood
    (object : FiniteObject.{u}) (hub : object.Vertex)
    (rim : Finset object.Vertex)
    (spec : ∀ vertex, vertex ∈ rim ↔ object.graph.Adj hub vertex) :
    rim.card = object.degree hub := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  have rewrite : rim = (object.orderedNeighbors hub).toFinset := by
    ext vertex; simp [spec]
  rw [rewrite, List.toFinset_card_of_nodup (object.orderedNeighbors_nodup hub),
    object.orderedNeighbors_length]

/-- The ordinary adjacent fan: the special case in which every handoff arm has
length zero, so each decoration is the single edge `h u`. -/
def adjacentFan (object : FiniteObject.{u}) (hub : object.Vertex)
    (rim : Finset object.Vertex)
    (spec : ∀ vertex, vertex ∈ rim ↔ object.graph.Adj hub vertex) :
    DecoratedFan.Certificate object where
  hub := hub
  rim := rim
  hub_not_mem_rim := fun mem => object.graph.irrefl ((spec hub).1 mem)
  decoration := fun vertex mem =>
    { walk := SimpleGraph.Walk.cons ((spec vertex).1 mem) SimpleGraph.Walk.nil
      isPath := by
        rw [SimpleGraph.Walk.cons_isPath_iff]
        exact ⟨SimpleGraph.Walk.IsPath.nil, by simpa using ((spec vertex).1 mem).ne⟩
      nontrivial := by simp }
  internallyDisjoint := by
    intro left right _ _ distinct vertex leftMem rightMem
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_singleton] at leftMem rightMem
    exact distinct (leftMem.symm.trans rightMem)

/-- **A marked Type B fan** (`def:marked-typeB-fan`): a high-degree centre `h`,
its neighbour set `N(h)` carried by a proof-carrying decorated fan, and a
fan-certificate labelling `S_h : N(h) → 𝓛` with `C₂(S_h u, S_h v) = 1` for
distinct neighbours.

No degree cap is recorded here: `Marked.degree_le_eight` derives it. -/
structure Marked (object : FiniteObject.{u}) where
  /-- The proof-carrying decorated fan. -/
  fan : DecoratedFan.Certificate object
  /-- The rim is exactly the neighbour set `N(h)` of the centre. -/
  rim_eq_neighbourhood :
    ∀ vertex, vertex ∈ fan.rim ↔ object.graph.Adj fan.hub vertex
  /-- `h` is a high-degree centre: `d_G(h) ≥ 4`. -/
  highDegree : 4 ≤ object.degree fan.hub
  /-- The fan-certificate labelling `S_h : N(h) → 𝓛`. -/
  labelling : object.Vertex → Label
  /-- `C₂(S_h u, S_h v) = 1` for distinct fan neighbours. -/
  wedgeSafe : ∀ u ∈ fan.rim, ∀ v ∈ fan.rim, u ≠ v →
    WedgeSafe (labelling u).indices (labelling v).indices

namespace Marked

variable (marked : Marked object)

/-- The rim of a marked fan has cardinality `d_G(h)`. -/
theorem rim_card_eq_degree :
    marked.fan.rim.card = object.degree marked.fan.hub :=
  card_eq_degree_of_isNeighbourhood object marked.fan.hub marked.fan.rim
    marked.rim_eq_neighbourhood

/-- Distinct fan neighbours carry distinct labels, because `C₂(S, S) = 0`. -/
theorem labelling_injOn :
    Set.InjOn (fun vertex => (marked.labelling vertex).indices) ↑marked.fan.rim := by
  intro u hu v hv same
  by_contra distinct
  have safe := marked.wedgeSafe u hu v hv distinct
  simp only at same
  rw [same] at safe
  exact not_wedgeSafe_self (marked.labelling v).nonempty safe

/-- **The fan-degree label-packing cap** (`rem:fan-finite`, manuscript
invariant 16).  A certificate-marked Type B fan satisfies
`d_G(h) ≤ packingCap`, the block count of the label algebra's own clique
cover.

The bound is not assumed and no numeral is written: it is the packing bound
`card_le_packingCap_of_pairwise_wedgeSafe` for the difference graph `D`,
transported along `rim = N(h)`. -/
theorem degree_le_packingCap : object.degree marked.fan.hub ≤ packingCap := by
  rw [← marked.rim_card_eq_degree]
  exact card_le_packingCap_of_pairwise_wedgeSafe marked.fan.rim marked.labelling
    marked.wedgeSafe

/-- The same cap with the cover's block count computed: `d_G(h) ≤ 8`, the
numeral `rem:fan-finite` records. -/
theorem degree_le_eight : object.degree marked.fan.hub ≤ 8 :=
  packingCap_eq_eight ▸ marked.degree_le_packingCap

/-- The manuscript's degree window for a certificate-marked Type B fan centre:
`4 ≤ d_G(h) ≤ 8`. -/
theorem degree_mem_window :
    4 ≤ object.degree marked.fan.hub ∧ object.degree marked.fan.hub ≤ 8 :=
  ⟨marked.highDegree, marked.degree_le_eight⟩

/-- Non-singleton refinement of the cap: if some fan neighbour carries a
non-singleton label — the manuscript's same-window supported case — then
`d_G(h) ≤ 7`. -/
theorem degree_le_seven_of_nonsingleton
    {witness : object.Vertex} (mem : witness ∈ marked.fan.rim)
    (nonsingleton : 2 ≤ (marked.labelling witness).indices.card) :
    object.degree marked.fan.hub ≤ 7 := by
  rw [← marked.rim_card_eq_degree]
  exact card_le_seven_of_pairwise_wedgeSafe_of_nonsingleton marked.fan.rim
    marked.labelling marked.wedgeSafe mem nonsingleton

/-- The rim schedule of a marked fan is bounded by the cap, so the derived
schedule of the reused `DecoratedFan.Certificate` never exceeds eight entries. -/
theorem schedule_length_le_eight : marked.fan.schedule.length ≤ 8 := by
  rw [marked.fan.schedule_length, marked.rim_card_eq_degree]
  exact marked.degree_le_eight

/-! ### Cubic-closed fan neighbours -/

/-- A fan neighbour `u` is *cubic-closed* in the marked fan relative to an
assigned support when its two non-`h` incidences are also carried by that
support.  Deletion criticality forces `d_G(u) = 3` at every neighbour of a
high-degree centre, which is the form recorded here. -/
def IsCubicClosed (marked : Marked object)
    (support : Finset object.Vertex) (u : object.Vertex) : Prop :=
  u ∈ marked.fan.rim ∧ object.degree u = 3 ∧
    ∀ w, object.graph.Adj u w → w ≠ marked.fan.hub → w ∈ support

/-- The manuscript's normal form `N_G(u) = {h, x_u, y_u}` for a cubic-closed
neighbour, with both outside endpoints carried by the assigned support. -/
theorem cubicClosed_normal_form
    {support : Finset object.Vertex} {u : object.Vertex}
    (closed : IsCubicClosed marked support u) :
    ∃ x y : object.Vertex, x ≠ y ∧ x ≠ marked.fan.hub ∧ y ≠ marked.fan.hub ∧
      x ∈ support ∧ y ∈ support ∧
      ∀ w, object.graph.Adj u w ↔ (w = marked.fan.hub ∨ w = x ∨ w = y) := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  obtain ⟨rimMem, degreeThree, assigned⟩ := closed
  have hubAdj : object.graph.Adj u marked.fan.hub :=
    ((marked.rim_eq_neighbourhood u).1 rimMem).symm
  have hubMem : marked.fan.hub ∈ object.graph.neighborFinset u :=
    (SimpleGraph.mem_neighborFinset _ _ _).2 hubAdj
  have cardThree : (object.graph.neighborFinset u).card = 3 := degreeThree
  have cardTwo : ((object.graph.neighborFinset u).erase marked.fan.hub).card = 2 := by
    rw [Finset.card_erase_of_mem hubMem, cardThree]
  obtain ⟨x, y, distinct, pairEq⟩ := Finset.card_eq_two.1 cardTwo
  have xMem : x ∈ (object.graph.neighborFinset u).erase marked.fan.hub := by
    rw [pairEq]; simp
  have yMem : y ∈ (object.graph.neighborFinset u).erase marked.fan.hub := by
    rw [pairEq]; simp
  have xHub : x ≠ marked.fan.hub := Finset.ne_of_mem_erase xMem
  have yHub : y ≠ marked.fan.hub := Finset.ne_of_mem_erase yMem
  have xAdj : object.graph.Adj u x :=
    (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_of_mem_erase xMem)
  have yAdj : object.graph.Adj u y :=
    (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_of_mem_erase yMem)
  refine ⟨x, y, distinct, xHub, yHub, assigned x xAdj xHub, assigned y yAdj yHub, ?_⟩
  intro w
  constructor
  · intro adj
    by_cases hw : w = marked.fan.hub
    · exact Or.inl hw
    · have : w ∈ (object.graph.neighborFinset u).erase marked.fan.hub :=
        Finset.mem_erase.2 ⟨hw, (SimpleGraph.mem_neighborFinset _ _ _).2 adj⟩
      rw [pairEq] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact Or.inr this
  · rintro (rfl | rfl | rfl)
    exacts [hubAdj, xAdj, yAdj]

end Marked

/-! ## Fan-certificate residual centres (`def:marked-typeB-fan`) -/

/-- A high-degree centre assigned to a Type B support but carrying no
fan-certificate labelling is a *fan-certificate residual centre*.  Such centres
are routed to the Type B bridge-residual mass and are excluded from the
certificate-closed local discharging step. -/
def IsFanCertificateResidual (object : FiniteObject.{u}) (hub : object.Vertex) :
    Prop :=
  4 ≤ object.degree hub ∧ ∀ marked : Marked object, marked.fan.hub ≠ hub

/-- Contrapositive of the cap: a centre of degree at least nine can carry no
fan-certificate labelling at all, so it is a fan-certificate residual centre. -/
theorem isFanCertificateResidual_of_nine_le_degree
    {object : FiniteObject.{u}} {hub : object.Vertex}
    (degreeBound : 9 ≤ object.degree hub) :
    IsFanCertificateResidual object hub := by
  refine ⟨by omega, ?_⟩
  intro marked same
  have cap := marked.degree_le_eight
  rw [same] at cap
  omega

/-! ## Construction of marked fans -/

/-- Build a marked Type B fan from a hub, a high-degree witness and a pairwise
`C₂`-compatible labelling of its neighbours, using the ordinary adjacent fan. -/
def markedOfLabelling (object : FiniteObject.{u}) (hub : object.Vertex)
    (highDegree : 4 ≤ object.degree hub)
    (labelling : object.Vertex → Label)
    (compatible : ∀ u, object.graph.Adj hub u → ∀ v, object.graph.Adj hub v →
      u ≠ v → WedgeSafe (labelling u).indices (labelling v).indices) :
    Marked object where
  fan := adjacentFan object hub (neighbourRim object hub) (mem_neighbourRim object hub)
  rim_eq_neighbourhood := mem_neighbourRim object hub
  highDegree := highDegree
  labelling := labelling
  wedgeSafe := by
    intro u hu v hv distinct
    exact compatible u ((mem_neighbourRim object hub u).1 hu) v
      ((mem_neighbourRim object hub v).1 hv) distinct

/-! ## Non-vacuity and sharpness witness

`Marked` is inhabited and the cap is attained, so `degree_le_eight` is neither
vacuous nor slack: it cannot be replaced by any smaller constant. -/

namespace Witness

/-- `K_{1,8}`: a hub joined to eight leaves. -/
def star : FiniteObject where
  Vertex := Fin 9
  graph := SimpleGraph.fromRel fun left right => left.val = 0 ∨ right.val = 0
  vertices := inferInstance
  decideAdj := by
    intro left right
    simp only [SimpleGraph.fromRel_adj]
    infer_instance

theorem star_degree_hub : star.degree (0 : Fin 9) = 8 := by decide

/-- The eight window coordinates of `dIndep_card_eight_witness`, two per
component of `D`, assigned to the eight leaves.  Vertex `0` is the hub and its
value is unconstrained. -/
def starIndex : Fin 9 → Index := fun vertex =>
  match vertex.val with
  | 1 => 0
  | 2 => 8
  | 3 => 1
  | 4 => 9
  | 5 => 2
  | 6 => 10
  | 7 => 3
  | _ => 11

/-- A genuine certificate-marked Type B fan of degree exactly eight. -/
def starMarked : Marked star := by
  refine markedOfLabelling star (0 : Fin 9) (by decide)
    (fun vertex => Label.ofIndex (starIndex vertex)) ?_
  have key : ∀ a b : Fin 9, a ≠ 0 → b ≠ 0 → a ≠ b →
      gap (starIndex a) (starIndex b) ≠ 0 ∧
      gap (starIndex a) (starIndex b) ≠ 4 ∧
      gap (starIndex a) (starIndex b) ≠ 12 := by decide
  intro u hu v hv distinct
  exact wedgeSafe_ofIndex (key u v hu.ne' hv.ne' distinct)

/-- The cap of `Marked.degree_le_eight` is attained. -/
theorem cap_attained : star.degree starMarked.fan.hub = 8 := star_degree_hub

example : star.degree starMarked.fan.hub ≤ 8 := starMarked.degree_le_eight

end Witness

end Hypostructure.Graph.TypeBMarkedFan
