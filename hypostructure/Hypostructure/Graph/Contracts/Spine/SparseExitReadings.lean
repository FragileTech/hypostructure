import Hypostructure.Graph.Statements.SparseExitReadings
import Hypostructure.Graph.Contracts.Spine.SparseExitResidual

/-!
# Contracts: the readings of the canonical target-defect witness, and the edge
# switches of G

Proof-agnostic contract lemmas for `Statements/SparseExitReadings.lean`, one
`<statement>_holds` per statement.  Each is stated over a `Graph.FiniteObject`
with the registered `Parameters` as a parameter; its hypotheses are exactly
ledger facts: the selection (target avoidance and size minimality), the
presentation laws (`δ = 3`, the dyadic target law, the scale), the baseline,
return avoidance, no proper baseline subgraph and connectivity, the tight
endpoint and slack independence, bridgelessness, `surplusAbove` and
`C + 1 ≤ ⌈√n⌉`, `[125]`'s pinned target-defect witness, and the `[20a]` facts
already on the ledger (the path-spectrum split, the whole-case deficit
structure, the Steiner cut vertices) together with the facts of this module.
The mathematics is in the vocabulary-free modules `Graph/ReadingCounts`,
`Graph/SingleEdgeContext`, `Graph/ReadingSpectrumArms` and
`Graph/EdgeSwitchPaths`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SparseExitReadings

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

set_option linter.unusedVariables false

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-! ## Edge switches of G -/

theorem highSurplusConfiguration_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (scale : Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale)
    (above : SurplusAboveStatement data object)
    (ceil : CeilSqrtAboveScaleStatement data object) :
    HighSurplusConfigurationStatement data object := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  have base : ∀ v, 3 ≤ object.degree v := fun v => by
    have := le_trans baseline (object.minDegree_le_degree v)
    omega
  have σeq := SparseOrderArithmetic.sigma_eq_sum object base
  have above' : data.spineScale * Core.ceilSqrt object.vertexCount <
      object.degreeSurplus data.threshold := above
  have ceil' : data.spineScale + 1 ≤ Core.ceilSqrt object.vertexCount := ceil
  have q : Graph.TokenLoad.quadraticSafetyScale = 20 := rfl
  have two : 2 ≤ object.degreeSurplus 3 := by
    rw [three] at above'
    have s20 : 20 ≤ data.spineScale := q ▸ scale
    have one : 1 ≤ Core.ceilSqrt object.vertexCount := by omega
    have prod : 20 * 1 ≤ data.spineScale * Core.ceilSqrt object.vertexCount :=
      Nat.mul_le_mul s20 one
    omega
  unfold HighSurplusConfigurationStatement
  rw [three]
  by_contra hn
  push Not at hn
  obtain ⟨lt5, uniq⟩ := hn
  have le1 : Finset.univ.sum (fun v => object.degree v - 3) ≤ 1 := by
    by_cases ex : ∃ h, object.degree h = 3 + 1
    · obtain ⟨h, hh⟩ := ex
      rw [Finset.sum_eq_single h]
      · omega
      · intro v _ vh
        have := uniq h v (Ne.symm vh) hh
        have := lt5 v
        have := base v
        omega
      · simp
    · push Not at ex
      have : Finset.univ.sum (fun v => object.degree v - 3) = 0 :=
        Finset.sum_eq_zero fun v _ => by
          have := lt5 v; have := base v; have := ex v; omega
      omega
  omega

theorem highEndpointSwitch_holds (slack : SlackIndependentStatement data object)
    (twoSwitch : TwoSwitchForcedPathStatement data object)
    (sameVertex : SameVertexSwitchForcedPathStatement data object)
    (config : HighSurplusConfigurationStatement data object) :
    HighEndpointSwitchStatement data object := by
  intro h c dh dc a
  by_cases d5 : data.threshold + 2 ≤ object.degree h
  · left
    obtain ⟨u, hu, uc, cu⟩ := EdgeSwitchPaths.exists_nonadj_nbr dc dh
    obtain ⟨p, pp, ok, -⟩ := sameVertex a hu uc.symm cu d5
    exact ⟨d5, u, hu, uc, cu, p, pp, ok⟩
  · right
    have second : ∃ h₂, h₂ ≠ h ∧ data.threshold + 1 ≤ object.degree h₂ := by
      rcases config with ⟨h', h5⟩ | ⟨h₁, h₂, ne, e1, e2⟩
      · exact ⟨h', fun e => by subst e; omega, by omega⟩
      · by_cases e : h₁ = h
        · exact ⟨h₂, fun e' => ne (e.trans e'.symm), by omega⟩
        · exact ⟨h₁, e, by omega⟩
    obtain ⟨h₂, h2ne, d2⟩ := second
    obtain ⟨u₂, hu₂, u2c, cu₂⟩ := EdgeSwitchPaths.exists_nonadj_nbr dc d2
    have ch₂ : c ≠ h₂ := fun e => by subst e; omega
    have hu : h ≠ u₂ := fun e => slack h h₂ (by omega) (by omega) (by rw [e]; exact hu₂.symm)
    obtain ⟨p, pp, ok⟩ := twoSwitch a.symm hu₂.symm u2c.symm ch₂ hu (Ne.symm h2ne) cu₂
      dh d2
    exact ⟨h₂, u₂, h2ne, d2, hu₂.symm, u2c, cu₂, p, pp, ok⟩

/-! ## The spectrum split at every clause-(b) witness -/

theorem everyWitnessSpectrumSplit_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    EveryWitnessSpectrumSplitStatement data object := by
  intro w' spec
  obtain ⟨-, -, -, -, -, -, sep⟩ := spec
  have split : ∀ {P N : Finset object.Vertex},
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w'.support P) w'.outside) →
      ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w'.support N) w'.outside) → _ :=
    fun pos neg => GluedReadings.spectrum_split pos neg
      (GluedReadings.retainedPiece_avoids avoid _ _)
  by_cases h1 : Graph.HasCycleWithLength data.LengthOK (glue (w'.reading w'.first) w'.outside)
  · have h2 : ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (w'.reading w'.second) w'.outside) :=
      fun h2 => sep ⟨fun _ => h2, fun _ => h1⟩
    exact ⟨_, Or.inl rfl, _, Or.inr rfl, h1, h2, split h1 h2⟩
  · have h2 : Graph.HasCycleWithLength data.LengthOK
        (glue (w'.reading w'.second) w'.outside) := by
      by_contra h2
      exact sep ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    exact ⟨_, Or.inr rfl, _, Or.inl rfl, h2, h1, split h2 h1⟩

/-! ## The readings at a clause-(b) witness -/

section WitnessLevel

variable {w : SparseTargetDefectWitness data object}

theorem supports_subset_of_spec (spec : w.Spec) :
    (∀ v ∈ sparseDeclaredSupport data object w.first, v ∈ w.support) ∧
      ∀ v ∈ sparseDeclaredSupport data object w.second, v ∈ w.support := by
  classical
  obtain ⟨-, -, -, sel, -, -, -⟩ := spec
  have cand := CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates sel)
  exact ⟨fun v hv => cand.1 (Finset.mem_union_left _ hv),
    fun v hv => cand.1 (Finset.mem_union_right _ hv)⟩

theorem counts_of_spec (spec : w.Spec) :
    ∀ b, w.count w.first b = w.count w.second b := by
  obtain ⟨-, -, -, -, prof, -, -⟩ := spec
  exact (ReadingProfiles.profile_eq_iff_counts _ _ _).1 prof

/-- Orientation of the positive/negative readings at a clause-(b) witness. -/
theorem pair_orient (spec : w.Spec)
    {P N : Finset object.Vertex} (hP : P ∈ w.pairSupports) (hN : N ∈ w.pairSupports)
    (pos : Graph.HasCycleWithLength data.LengthOK
      (glue (SupportAtom.retainedPiece object w.support P) w.outside))
    (neg : ¬ Graph.HasCycleWithLength data.LengthOK
      (glue (SupportAtom.retainedPiece object w.support N) w.outside)) :
    w.Orientation P N ∧
    (SupportAtom.retainedPiece object w.support P).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object w.support N).boundaryDegreeProfile := by
  obtain ⟨-, -, -, -, prof, -, -⟩ := spec
  simp only [SparseTargetDefectWitness.pairSupports, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hP hN
  rcases hP with rfl | rfl <;> rcases hN with rfl | rfl
  · exact absurd pos neg
  · exact ⟨Or.inl ⟨rfl, rfl⟩, prof⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, prof.symm⟩
  · exact absurd pos neg

theorem two_active_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) :
    ∃ l₁ l₂ : (SupportAtom.boundary object w.support).Vertex, l₁ ≠ l₂ ∧
      0 < w.count w.first l₁ ∧ 0 < w.count w.first l₂ := by
  have counts := counts_of_spec spec
  have geo := SparseExitResidual.geometryAt_of_spec avoid spec
  rcases geo.2 with ps | ps
  · exact ReadingCounts.two_active_labels avoid ps.contextFree ps.positive
  · obtain ⟨l₁, l₂, ne, h1, h2⟩ := ReadingCounts.two_active_labels avoid ps.contextFree ps.positive
    exact ⟨l₁, l₂, ne, by rw [counts]; exact h1, by rw [counts]; exact h2⟩

theorem private_of_spec (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) :
    ∃ P N : Finset object.Vertex, w.Orientation P N ∧ w.Separates P N ∧
      w.CyclesUsePrivateEdge P N ∧
      ¬ ((SupportAtom.retainedPiece object w.support P).graph ≤
        (SupportAtom.retainedPiece object w.support N).graph) := by
  have geo := SparseExitResidual.geometryAt_of_spec avoid spec
  have main : ∀ {P N : Finset object.Vertex},
      (SupportAtom.retainedPiece object w.support P).boundaryDegreeProfile =
        (SupportAtom.retainedPiece object w.support N).boundaryDegreeProfile →
      ¬ Graph.HasCycleWithLength data.LengthOK
          (glue (SupportAtom.retainedPiece object w.support N) w.outside) →
      w.CyclesUsePrivateEdge P N := by
    intro P N prof neg c
    obtain ⟨pl, pr, mem, adj, hl, hr, notBoth⟩ := ReadingCounts.cycle_uses_private c neg
    have interior : ∀ {x y : (SupportAtom.boundary object w.support).Vertex ⊕
          SupportAtom.PieceInternal object w.support},
        object.graph.Adj (SupportAtom.pieceDecode object w.support x)
          (SupportAtom.pieceDecode object w.support y) →
        SupportAtom.pieceDecode object w.support x ∈ P →
        SupportAtom.pieceDecode object w.support y ∈ P →
        SupportAtom.pieceDecode object w.support y ∉ N →
        SupportAtom.pieceDecode object w.support y ∉
          SupportAtom.cutBoundary object w.support := by
      intro x y adj hx hy hyN hyB
      exact hyN (ReadingProfiles.mem_of_profile_eq prof ⟨_, hyB⟩ hy
        (ReadingProfiles.pieceDecode_mem w.support x) hx adj.symm)
    by_cases hrN : SupportAtom.pieceDecode object w.support pr ∈ N
    · have hlN : SupportAtom.pieceDecode object w.support pl ∉ N :=
        fun h => notBoth ⟨h, hrN⟩
      refine ⟨pr, pl, ?_, adj.symm, hr, hl, hlN, interior adj.symm hr hl hlN⟩
      rw [Sym2.eq_swap]; exact mem
    · exact ⟨pl, pr, mem, adj, hl, hr, hrN, interior adj hl hr hrN⟩
  have notLe : ∀ {P N : Finset object.Vertex},
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support P) w.outside) →
      w.CyclesUsePrivateEdge P N →
      ¬ ((SupportAtom.retainedPiece object w.support P).graph ≤
        (SupportAtom.retainedPiece object w.support N).graph) := by
    intro P N pos priv le
    obtain ⟨c⟩ := pos
    obtain ⟨pl, pr, -, adj, hl, hr, hrN, -⟩ := priv c
    have hP : (SupportAtom.retainedPiece object w.support P).graph.Adj pl pr := by
      refine ⟨adj, ?_⟩
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      exact ⟨adj.ne, Or.inl ⟨hl, hr⟩⟩
    exact hrN (GluedReadings.retained_adj_mem (le hP)).2
  obtain ⟨-, -, -, -, prof, -, -⟩ := spec
  rcases geo.2 with ps | ps
  · have priv := main prof ps.negative
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, ⟨ps.positive, ps.negative⟩, priv,
      notLe ps.positive priv⟩
  · have priv := main prof.symm ps.negative
    exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, ⟨ps.positive, ps.negative⟩, priv,
      notLe ps.positive priv⟩

theorem wholeCycle_at (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (spec : w.Spec) {x y : SparseDeclaredCoordinate data object}
    (xy : (x = w.first ∧ y = w.second) ∨ (x = w.second ∧ y = w.first)) :
    WholeCycleMeetsDeficitAt w x y := by
  intro whole
  obtain ⟨AZ, BZ⟩ := supports_subset_of_spec spec
  obtain ⟨P, N, orient, ⟨pos, neg⟩, priv, -⟩ := private_of_spec avoid spec
  have direct : ∀ {X Y : Finset object.Vertex},
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support X) w.outside) →
      ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support Y) w.outside) →
      w.CyclesUsePrivateEdge X Y →
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support X) w.outside) ∧
      ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support Y) w.outside) ∧
      ∀ c : Graph.CycleCertificate
          (glue (SupportAtom.retainedPiece object w.support X) w.outside) data.LengthOK,
        ∃ i : SupportAtom.PieceInternal object w.support, i.1 ∉ Y ∧
          (Sum.inr (Sum.inl i) :
            GluedVertex (SupportAtom.retainedPiece object w.support X) w.outside) ∈
              c.walk.support := by
    intro X Y pos neg priv
    refine ⟨pos, neg, fun c => ?_⟩
    obtain ⟨pl, pr, mem, -, -, -, hrN, hrB⟩ := priv c
    rcases pr with l | i
    · exact absurd l.2 hrB
    · exact ⟨i, hrN, c.walk.snd_mem_support_of_mem_edges mem⟩
  have wrong : ∀ {X Y : Finset object.Vertex},
      Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support X) w.outside) →
      w.CyclesUsePrivateEdge X Y → (∀ v ∈ X, v ∈ Y) → False := by
    intro X Y pos priv sub
    obtain ⟨c⟩ := pos
    obtain ⟨pl, pr, -, -, -, hrP, hrN, -⟩ := priv c
    exact hrN (sub _ hrP)
  rcases xy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact direct pos neg priv
  · exact (wrong pos priv fun v hv => whole (BZ v hv)).elim
  · exact (wrong pos priv fun v hv => whole (AZ v hv)).elim
  · exact direct pos neg priv

theorem wholePrivate_at (spec : w.Spec) {x y : SparseDeclaredCoordinate data object}
    (hx : ∀ v ∈ sparseDeclaredSupport data object x, v ∈ w.support)
    (deficit : WholeDeficitStructure w x y) :
    WholePrivateEdgesAt w x y := by
  intro whole s t adj
  have inside : ∀ {p q : object.Vertex}, object.graph.Adj p q →
      p ∈ w.support → p ∉ sparseDeclaredSupport data object y → q ∈ w.support := by
    intro p q pq pZ pY
    by_contra qZ
    exact (deficit whole p pZ pY).1
      ((SupportAtom.mem_cutBoundary_iff object w.support p).2 ⟨pZ, q, pq, qZ⟩)
  constructor
  · rintro ⟨hs, ht, nb⟩
    by_cases hsY : s ∈ sparseDeclaredSupport data object y
    · exact Or.inr ⟨hx t ht, fun h => nb ⟨hsY, h⟩⟩
    · exact Or.inl ⟨hx s hs, hsY⟩
  · rintro (⟨sZ, sY⟩ | ⟨tZ, tY⟩)
    · exact ⟨whole sZ, whole (inside adj sZ sY), fun h => sY h.1⟩
    · exact ⟨whole (inside adj.symm tZ tY), whole tZ, fun h => tY h.2⟩

end WitnessLevel

/-! ## The readings at every clause-(b) witness, and at the canonical one

Each witness-level contract `<key>_of_spec` holds at every `w` with `w.Spec`;
`<key>_holds` instantiates it at the canonical witness through
`SparseExitResidual.atWitness_of_spec`. -/

section Spec

variable {w : SparseTargetDefectWitness data object}

theorem witnessReadingCounts_of_spec (spec : w.Spec) : WitnessReadingCountsAtWitness w := by
  obtain ⟨AZ, BZ⟩ := supports_subset_of_spec spec
  have prof := spec.2.2.2.2.1
  refine ⟨counts_of_spec spec, ?_, ?_⟩
  · intro b hb x hx adj
    exact ReadingProfiles.mem_of_profile_eq prof b hb (AZ x hx) hx adj
  · intro b hb x hx adj
    exact ReadingProfiles.mem_of_profile_eq prof.symm b hb (BZ x hx) hx adj

theorem witnessActiveLabels_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    WitnessActiveLabelsAtWitness w := by
  have counts := counts_of_spec spec
  obtain ⟨l₁, l₂, ne, h1, h2⟩ := two_active_of_spec avoid spec
  have facts : ∀ l, (l = l₁ ∨ l = l₂) →
      0 < w.count w.first l ∧ w.count w.first l = w.count w.second l ∧
      l.1 ∈ sparseDeclaredSupport data object w.first ∧
      l.1 ∈ sparseDeclaredSupport data object w.second ∧
      w.count w.first l + 1 ≤ object.degree l.1 := by
    intro l hl
    have pos : 0 < w.count w.first l := by rcases hl with rfl | rfl <;> assumption
    have posB : 0 < w.count w.second l := by rw [← counts]; exact pos
    exact ⟨pos, counts l, (ReadingProfiles.readingCount_pos pos).1,
      (ReadingProfiles.readingCount_pos posB).1, ReadingProfiles.readingCount_add_one_le _ _ l⟩
  haveI : Finite (SupportAtom.boundary object w.support).Vertex := by
    letI := (SupportAtom.boundary object w.support).vertices; infer_instance
  have card : 2 ≤ {l : (SupportAtom.boundary object w.support).Vertex |
      0 < w.count w.first l}.ncard := by
    have sub : ({l₁, l₂} : Set (SupportAtom.boundary object w.support).Vertex) ⊆
        {l | 0 < w.count w.first l} := by
      intro l hl
      rcases hl with rfl | hl
      · exact h1
      · rw [Set.mem_singleton_iff.1 hl]; exact h2
    have := Set.ncard_le_ncard sub (Set.toFinite _)
    rwa [Set.ncard_pair ne] at this
  obtain ⟨-, -, iA, iB, -⟩ := facts l₁ (Or.inl rfl)
  exact ⟨card, ⟨l₁.1, iA, l₁.2⟩, ⟨l₁.1, iB, l₁.2⟩, l₁, l₂, ne, facts⟩

theorem twoBoundaryAllActive_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    TwoBoundaryAllActiveAtWitness w := by
  classical
  obtain ⟨-, -, -, l₁, l₂, ne, h⟩ := witnessActiveLabels_of_spec avoid spec
  intro two b
  have hb : b = l₁ ∨ b = l₂ := by
    by_contra hn
    push Not at hn
    have sub : ({l₁.1, l₂.1, b.1} : Finset object.Vertex) ⊆
        SupportAtom.cutBoundary object w.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact l₁.2
      · exact l₂.2
      · exact b.2
    have c3 : ({l₁.1, l₂.1, b.1} : Finset object.Vertex).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨l₁.1, l₂.1, b.1, fun e => ne (Subtype.ext e),
        fun e => hn.1 (Subtype.ext e.symm), fun e => hn.2 (Subtype.ext e.symm), rfl⟩
    have := Finset.card_le_card sub
    omega
  obtain ⟨p, -, iA, iB, -⟩ := h b hb
  exact ⟨p, iA, iB⟩

theorem boundaryPartition_of_spec (spec : w.Spec) : BoundaryPartitionAtWitness w := by
  classical
  have cut := SparseExitResidual.steinerVerticesCut_of_spec spec
  have counts := counts_of_spec spec
  obtain ⟨AZ, BZ⟩ := supports_subset_of_spec spec
  intro b
  have bZ : b.1 ∈ w.support := ((SupportAtom.mem_cutBoundary_iff _ _ b.1).1 b.2).1
  rcases Nat.eq_zero_or_pos (w.count w.first b) with zA | pA
  · have zB : w.count w.second b = 0 := by rw [← counts]; exact zA
    have iso : ∀ {X : Finset object.Vertex}, (∀ v ∈ X, v ∈ w.support) →
        ReadingProfiles.readingCount w.support X b = 0 → b.1 ∈ X → ∀ x ∈ X,
          ¬ object.graph.Adj b.1 x := by
      intro X XZ z hb x hx adj
      have : 0 < ReadingProfiles.readingCount w.support X b := by
        unfold ReadingProfiles.readingCount
        exact (Set.ncard_pos (Set.toFinite _)).2 ⟨x, XZ x hx, adj, hb, hx⟩
      omega
    by_cases inU : b.1 ∈ sparseDeclaredSupport data object w.first ∨
        b.1 ∈ sparseDeclaredSupport data object w.second
    · exact Or.inr (Or.inl ⟨zA, zB, inU, iso AZ zA, iso BZ zB⟩)
    · push Not at inU
      exact Or.inr (Or.inr ⟨inU.1, inU.2, cut b.1 bZ inU.1 inU.2⟩)
  · have pB : 0 < w.count w.second b := by rw [← counts]; exact pA
    exact Or.inl ⟨pA, (ReadingProfiles.readingCount_pos pA).1,
      (ReadingProfiles.readingCount_pos pB).1⟩

theorem positiveCyclePrivateEdge_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    PositiveCyclePrivateEdgeAtWitness w :=
  private_of_spec avoid spec

theorem wholeCycleMeetsDeficit_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    WholeCycleMeetsDeficitAtWitness w :=
  ⟨wholeCycle_at avoid spec (Or.inl ⟨rfl, rfl⟩), wholeCycle_at avoid spec (Or.inr ⟨rfl, rfl⟩)⟩

theorem wholePrivateEdges_of_spec (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    WholePrivateEdgesAtWitness w := by
  obtain ⟨AZ, BZ⟩ := supports_subset_of_spec spec
  exact ⟨wholePrivate_at spec AZ (SparseExitResidual.firstWholeDeficitStructure_of_spec three avoid spec),
    wholePrivate_at spec BZ (SparseExitResidual.secondWholeDeficitStructure_of_spec three avoid spec)⟩

theorem spectrumArmOneRefined_of_spec
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object) (spec : w.Spec) :
    SpectrumArmOneRefinedAtWitness w := by
  have hL : data.LengthOK = Core.DyadicLength.PowerOfTwoLength :=
    funext fun n => propext (lengthLaw n)
  have avoidP : ¬ Graph.HasCycleWithLength Core.DyadicLength.PowerOfTwoLength object := by
    rw [← hL]; exact avoid
  have retP : ∀ dart : object.graph.Dart, Disjoint (Graph.returnLengthSet object dart)
      (Graph.shiftedAcceptedSet Core.DyadicLength.PowerOfTwoLength) := by
    rw [← hL]; exact ret
  obtain ⟨P, hP, N, hN, pos, neg, arms⟩ :=
    SparseExitResidual.pathSpectrumSplit_of_spec lengthLaw avoid spec
  obtain ⟨orient, prof⟩ := pair_orient spec hP hN pos neg
  have arms' : ReadingSpectrumArms.ArmOneRefined w.support P N w.outside ∨
      w.CyclesMeetThreeLabels P := by
    rcases arms with ⟨a, b, ab, π, hπ, σ, hσ, lab, hk, spc⟩ | many
    · exact Or.inl (ReadingSpectrumArms.armOneRefined_of_arm avoidP retP prof ab π hπ σ hσ
        lab hk spc)
    · exact Or.inr many
  refine ⟨P, N, orient, ⟨pos, neg⟩, arms', fun two => ?_⟩
  rcases arms' with done | many
  · exact done
  · exact (GluedReadings.armII_two_false two pos many).elim

theorem separatingEdgeContextWitness_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object) (spec : w.Spec) :
    SeparatingEdgeContextWitnessAtWitness w := by
  refine fun a b ne differ => ⟨fun adj => differ ?_, ?_⟩
  · have neg : ∀ X, ¬ Graph.HasCycleWithLength data.LengthOK
        (glue (SupportAtom.retainedPiece object w.support X)
          (ReadingSpectrum.EdgeContext.edgeContext w.support a b)) := by
      intro X cyc
      obtain ⟨p, hp, hf, hl⟩ := ReadingSpectrum.EdgeContext.path_of_edgeContext_cycle avoid cyc
      exact ReadingSpectrum.EdgeContext.no_spectrum_of_adj (L := data.LengthOK) ret adj.symm p hp hf hl
    exact iff_of_false (neg _) (neg _)
  · obtain ⟨fm, sm, ne', sel, prof, act, -⟩ := spec
    exact ⟨fm, sm, ne', sel, prof, act, differ⟩

theorem separatingEdgeContextSpectrum_of_spec
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object)
    (every : EveryWitnessSpectrumSplitStatement data object) (spec : w.Spec) :
    SeparatingEdgeContextSpectrumAtWitness w := by
  have sepW := separatingEdgeContextWitness_of_spec avoid ret spec
  refine fun a b ne differ => ?_
  obtain ⟨nadj, spec'⟩ := sepW a b ne differ
  refine ⟨nadj, ?_⟩
  obtain ⟨P, -, N, -, pos, neg, arms⟩ := every _ spec'
  refine ⟨P, N, pos, neg, ?_⟩
  rcases arms with ⟨a', b', ab', π, hπ, σ, hσ, -, ok, -, rest⟩ | many
  · have one := SingleEdgeContext.edgeContext_path_length ab'.symm σ hσ
    refine Or.inl ⟨a', b', ab', π, hπ, by rw [← one]; exact ok, fun π' hπ' => ?_⟩
    refine ⟨(rest π' hπ').1, fun h => ?_⟩
    have := (rest π' hπ').2 (Or.inl h)
    rwa [one] at this
  · exact Or.inr many

theorem privateEdgeSwap_of_spec (tight : TightEndpointStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    PrivateEdgeSwapAtWitness w := by
  obtain ⟨P, N, orient, ⟨pos, -⟩, cyc, -⟩ := private_of_spec avoid spec
  obtain ⟨c⟩ := pos
  obtain ⟨pl, pr, -, adj, hl, hr, hrN, hrB⟩ := cyc c
  refine ⟨P, N, orient, ⟨_, _, adj, hl, hr, hrN, ReadingProfiles.pieceDecode_mem _ pl,
    ReadingProfiles.pieceDecode_mem _ pr, hrB⟩, ?_⟩
  rcases ReadingProfiles.swap_exact tight N P with none | some
  · exact absurd (none _ _ adj hl hr).2 hrN
  · exact some

theorem privateEdgeSwitch_of_spec (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (switch : HighEndpointSwitchStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    PrivateEdgeSwitchAtWitness w := by
  obtain ⟨P, N, orient, ⟨x, y, adj, hx, hy, hyN, xZ, yZ, yB⟩, -⟩ :=
    privateEdgeSwap_of_spec tight avoid spec
  refine ⟨P, N, orient, x, y, adj, hx, hy, hyN, xZ, yZ, yB, ?_⟩
  have base : ∀ v, data.threshold ≤ object.degree v := fun v =>
    le_trans baseline (object.minDegree_le_degree v)
  have le : ReadingProfiles.swapGraph N P ≤ object.graph :=
    object.graph.deleteEdges_le _
  have drop : ¬ (ReadingProfiles.swapGraph N P).Adj x y := by
    intro h
    rw [ReadingProfiles.swapGraph, SimpleGraph.deleteEdges_adj] at h
    exact h.2 ⟨x, y, rfl, hx, hy, fun h => hyN h.2⟩
  by_cases dx : object.degree x = data.threshold
  · by_cases dy : object.degree y = data.threshold
    · left
      exact ⟨dx, dy, ReadingProfiles.spanning_degree_le_of_tight le adj drop dx,
        ReadingProfiles.spanning_degree_le_of_tight le adj.symm (fun h => drop h.symm) dy⟩
    · right
      have hy4 : data.threshold + 1 ≤ object.degree y := by have := base y; omega
      exact ⟨y, x, Or.inr ⟨rfl, rfl⟩, hy4, dx, switch y x hy4 dx adj.symm⟩
  · right
    have hx4 : data.threshold + 1 ≤ object.degree x := by have := base x; omega
    have dy : object.degree y = data.threshold := by
      rcases tight ⟨(x, y), adj⟩ with t | t
      · exact absurd t dx
      · exact t
    exact ⟨x, y, Or.inl ⟨rfl, rfl⟩, hx4, dy, switch x y hx4 dy adj⟩

theorem cubicLabelOutsidePath_of_spec (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    CubicLabelOutsidePathAtWitness w := by
  obtain ⟨-, -, -, l₁, l₂, ne, -⟩ := witnessActiveLabels_of_spec avoid spec
  have mdb : Graph.MinimumDegreeAtLeast 3 object := three ▸ baseline
  have np : ∀ sub : Graph.ProperSubgraph object, ¬ Graph.MinimumDegreeAtLeast 3 sub.value :=
    three ▸ noProper.1
  intro a aB cubic
  rw [three] at cubic
  obtain ⟨aZ, y, ay, yZ⟩ := (SupportAtom.mem_cutBoundary_iff _ _ a).1 aB
  have other : ∃ z ∈ w.support, z ≠ a := by
    by_cases e : l₁.1 = a
    · refine ⟨l₂.1, ((SupportAtom.mem_cutBoundary_iff _ _ _).1 l₂.2).1, fun e' => ne ?_⟩
      exact Subtype.ext (e.trans e'.symm)
    · exact ⟨l₁.1, ((SupportAtom.mem_cutBoundary_iff _ _ _).1 l₁.2).1, e⟩
  obtain ⟨z, zZ, za⟩ := other
  obtain ⟨v, b', vZ, vb, bZ, ba, p, hp⟩ :=
    ReadingSpectrumArms.cubic_outside_return mdb np bridgeless noProper.2 aZ cubic ay yZ zZ za
  have bB : b' ∈ SupportAtom.cutBoundary object w.support :=
    (SupportAtom.mem_cutBoundary_iff _ _ _).2 ⟨bZ, v, vb.symm, vZ⟩
  obtain ⟨τ, hτ, out, two⟩ :=
    ReadingSpectrumArms.outside_path_of_walk aZ bZ (Ne.symm ba) ay p hp vb
  exact ⟨b', bB, ba, τ, hτ, out, two⟩

theorem twoBoundaryOutsideBoth_of_spec (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) (spec : w.Spec) :
    TwoBoundaryOutsideBothAtWitness w := by
  have ret := cubicLabelOutsidePath_of_spec three baseline noProper bridgeless avoid spec
  intro x y xy hB cub
  have mem : ∀ v, v ∈ SupportAtom.cutBoundary object w.support ↔ v = x ∨ v = y := by
    intro v; rw [hB]; simp
  have fromX : object.degree x = data.threshold →
      ∃ τ : object.graph.Walk x y, τ.IsPath ∧
        (∀ v ∈ τ.support, v ∉ w.support ∨ v = x ∨ v = y) ∧ 2 ≤ τ.length := by
    intro d
    obtain ⟨b', bB, bx, τ, hτ, out, two⟩ := ret x ((mem x).2 (Or.inl rfl)) d
    have : b' = y := ((mem b').1 bB).resolve_left bx
    subst this
    exact ⟨τ, hτ, out, two⟩
  have fromY : object.degree y = data.threshold →
      ∃ τ : object.graph.Walk y x, τ.IsPath ∧
        (∀ v ∈ τ.support, v ∉ w.support ∨ v = y ∨ v = x) ∧ 2 ≤ τ.length := by
    intro d
    obtain ⟨b', bB, bx, τ, hτ, out, two⟩ := ret y ((mem y).2 (Or.inr rfl)) d
    have : b' = x := ((mem b').1 bB).resolve_right bx
    subst this
    exact ⟨τ, hτ, out, two⟩
  have rev : ∀ {p q : object.Vertex} (τ : object.graph.Walk p q),
      τ.IsPath → (∀ v ∈ τ.support, v ∉ w.support ∨ v = p ∨ v = q) → 2 ≤ τ.length →
      ∃ τ' : object.graph.Walk q p, τ'.IsPath ∧
        (∀ v ∈ τ'.support, v ∉ w.support ∨ v = q ∨ v = p) ∧ 2 ≤ τ'.length := by
    intro p q τ hτ out two
    refine ⟨τ.reverse, hτ.reverse, fun v hv => ?_, by simpa using two⟩
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    rcases out v hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  rcases cub with d | d
  · obtain ⟨τ, hτ, out, two⟩ := fromX d
    exact ⟨⟨τ, hτ, out, two⟩, rev τ hτ out two⟩
  · obtain ⟨τ, hτ, out, two⟩ := fromY d
    exact ⟨rev τ hτ out two, ⟨τ, hτ, out, two⟩⟩

end Spec

section Canonical

variable (residual : SparseTargetDefectResidualStatement data object)
include residual

theorem witnessReadingCounts_holds : WitnessReadingCountsStatement data object :=
  SparseExitResidual.atWitness_of_spec (fun _ spec => witnessReadingCounts_of_spec spec) residual

theorem witnessActiveLabels_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    WitnessActiveLabelsStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => witnessActiveLabels_of_spec avoid spec) residual

theorem twoBoundaryAllActive_holds (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    TwoBoundaryAllActiveStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => twoBoundaryAllActive_of_spec avoid spec) residual

theorem boundaryPartition_holds : BoundaryPartitionStatement data object :=
  SparseExitResidual.atWitness_of_spec (fun _ spec => boundaryPartition_of_spec spec) residual

theorem positiveCyclePrivateEdge_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    PositiveCyclePrivateEdgeStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => positiveCyclePrivateEdge_of_spec avoid spec) residual

theorem wholeCycleMeetsDeficit_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    WholeCycleMeetsDeficitStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => wholeCycleMeetsDeficit_of_spec avoid spec) residual

theorem wholePrivateEdges_holds (three : data.threshold = 3)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    WholePrivateEdgesStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => wholePrivateEdges_of_spec three avoid spec) residual

theorem spectrumArmOneRefined_holds
    (lengthLaw : ∀ length, data.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object) :
    SpectrumArmOneRefinedStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => spectrumArmOneRefined_of_spec lengthLaw avoid ret spec) residual

theorem separatingEdgeContextWitness_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object) :
    SeparatingEdgeContextWitnessStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => separatingEdgeContextWitness_of_spec avoid ret spec) residual

theorem separatingEdgeContextSpectrum_holds
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (ret : ReturnAvoidanceStatement data object)
    (every : EveryWitnessSpectrumSplitStatement data object) :
    SeparatingEdgeContextSpectrumStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => separatingEdgeContextSpectrum_of_spec avoid ret every spec) residual

theorem privateEdgeSwap_holds (tight : TightEndpointStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    PrivateEdgeSwapStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => privateEdgeSwap_of_spec tight avoid spec) residual

theorem privateEdgeSwitch_holds (baseline : MinDegreeBaselineStatement data object)
    (tight : TightEndpointStatement data object)
    (switch : HighEndpointSwitchStatement data object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    PrivateEdgeSwitchStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => privateEdgeSwitch_of_spec baseline tight switch avoid spec) residual

theorem cubicLabelOutsidePath_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    CubicLabelOutsidePathStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => cubicLabelOutsidePath_of_spec three baseline noProper bridgeless avoid spec)
    residual

theorem twoBoundaryOutsideBoth_holds (three : data.threshold = 3)
    (baseline : MinDegreeBaselineStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (bridgeless : BridgelessStatement object)
    (avoid : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    TwoBoundaryOutsideBothStatement data object :=
  SparseExitResidual.atWitness_of_spec
    (fun _ spec => twoBoundaryOutsideBoth_of_spec three baseline noProper bridgeless avoid spec)
    residual

end Canonical

end Hypostructure.Graph.Contracts.Spine.SparseExitReadings
