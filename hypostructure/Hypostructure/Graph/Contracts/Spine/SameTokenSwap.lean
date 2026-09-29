import Hypostructure.Graph.Statements.SameTokenSwap
import Hypostructure.Graph.Contracts.Spine.SameTokenPair
import Hypostructure.Graph.WholeBlocks
import Hypostructure.Graph.Statements.CycleCounting

/-!
# Contracts: G's pattern pair, tested at G (`[144a]`, G audit S144a)

Proof-agnostic contract lemmas for `Statements/SameTokenSwap.lean`.  The
hypotheses are exactly facts the `[144a]` ledger carries: the exact partition
(`K .sameTokenPairPartition`, which pins G's canonical routing and `X_p`,
`X_q`, `Z`), `K .noProperBaseline` (G connected), the selection (G avoids the
target and every strictly smaller baseline object has a target cycle) and
`K .minDegreeBaseline`.  The mathematics is the vocabulary-free libraries
`Graph/ReadingExactness.lean`, `Graph/RerouteSwap.lean`, `Graph/U2FreeWhole.lean`
and `Graph/Transplant.lean`.

This module imports no strategy, row, or vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine.SameTokenSwap

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Spine
open Hypostructure.Graph.Strategy.InterfaceReplacement
open Hypostructure.Graph.Contracts.Spine.SameTokenPair

universe u

variable {data : Parameters} {object : Graph.FiniteObject.{u}}

/-- **The entry test of `[144a]`, decided at G.** -/
theorem sameTokenUnresolvedDecided_holds
    (partition : SameTokenPairPartitionStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object) :
    SameTokenUnresolvedDecidedStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, different, -, -, selected, -⟩ := partition
  refine ⟨routing, routingEq, Xp, Xq, Z, ⟨hXp, hXq, selected⟩, different,
    Graph.ActualContext.not_target_actualGlue avoids Z Xp,
    Graph.ActualContext.not_target_actualGlue avoids Z Xq,
    Graph.ActualContext.actualGlue_agree avoids Z Xp Xq, ?_⟩
  exact fun h => h.2 (Graph.ActualContext.actualGlue_agree avoids Z Xp Xq)

/-- **A reading of G at `Z`, exactly.** -/
theorem readingExactAt_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (Z Y : Finset object.Vertex) :
    ReadingExactAt data object Z Y := by
  by_cases all : ∀ x y, object.graph.Adj x y → x ∈ Z → y ∈ Z →
      (x ∉ SupportAtom.cutBoundary object Z ∨ y ∉ SupportAtom.cutBoundary object Z) →
      x ∈ Y ∧ y ∈ Y
  · exact Or.inl all
  · right
    push Not at all
    obtain ⟨x, y, adj, xZ, yZ, cut, notBoth'⟩ := all
    have notBoth : ¬ (x ∈ Y ∧ y ∈ Y) := fun h => notBoth' h.1 h.2
    have lex : (Graph.ActualContext.actualGlue object Z Y).LexicographicallySmaller object := by
      rcases cut with hx | hy
      · exact Graph.ReadingExactness.actualGlue_lexicographicallySmaller adj xZ yZ hx notBoth
      · exact Graph.ReadingExactness.actualGlue_lexicographicallySmaller adj.symm yZ xZ hy
          (fun h => notBoth ⟨h.2, h.1⟩)
    refine ⟨x, y, adj, xZ, yZ, cut, notBoth, lex, fun base => ?_⟩
    exact Graph.ActualContext.not_target_actualGlue avoids Z Y (minimal _ lex base)

/-- **The two readings of G at `Z`, exactly.** -/
theorem sameTokenReadingsExact_holds
    (partition : SameTokenPairPartitionStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H) :
    SameTokenReadingsExactStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, -, -, selected, -⟩ := partition
  exact ⟨routing, routingEq, Xp, Xq, Z, ⟨hXp, hXq, selected⟩,
    readingExactAt_holds avoids minimal Z Xp, readingExactAt_holds avoids minimal Z Xq⟩

/-- A vertex of `Y` inside `Z` gives a vertex that is outside `int(Z) ∩ P`
or inside `int(Z) ∩ Y`. -/
theorem swap_vertex_exists {Z P Y : Finset object.Vertex} {y : object.Vertex}
    (yZ : y ∈ Z) (yY : y ∈ Y) :
    ∃ v, ¬ Graph.RerouteSwap.InteriorIn object Z P v ∨
      Graph.RerouteSwap.InteriorIn object Z Y v := by
  by_cases cut : y ∈ SupportAtom.cutBoundary object Z
  · exact ⟨y, Or.inl fun h => h.2.1 cut⟩
  · exact ⟨y, Or.inr ⟨yZ, cut, yY⟩⟩

/-- **The rerouted swap `P → Q`: conditions (i)-(iv) and the size relation.** -/
theorem sameTokenSwapAt_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (Z P Q : Finset object.Vertex)
    (hv : ∃ v, ¬ Graph.RerouteSwap.InteriorIn object Z P v ∨
      Graph.RerouteSwap.InteriorIn object Z Q v) :
    SameTokenSwapAt data object Z P Q := by
  have hne : Nonempty (Graph.glue (Graph.RerouteSwap.swapPiece object Z P Q)
      (SupportAtom.outside object Z)).Vertex := by
    obtain ⟨v, hv⟩ := hv
    rcases hv with h | h
    · obtain ⟨c, -, -⟩ := Graph.RerouteSwap.exists_nonCopy (Q := Q) h
      exact ⟨c⟩
    · obtain ⟨c, -, -⟩ := Graph.RerouteSwap.exists_copy (P := P) h
      exact ⟨c⟩
  exact ⟨hv, Graph.RerouteSwap.swapPiece_internalVertexCount Z P Q,
    Graph.RerouteSwap.swapPiece_profile_eq_iff Z P Q,
    fun b hc y => Graph.RerouteSwap.swap_attachment Z P Q b hc y,
    Graph.RerouteSwap.swap_baseline_iff Z P Q hne,
    Graph.RerouteSwap.swap_linkage_dichotomy Z P Q,
    fun sub => Graph.RerouteSwap.swap_linkageIncluded_of_subset sub,
    fun inc => Graph.RerouteSwap.swap_not_target avoids Z P Q inc,
    fun base inc => Graph.RerouteSwap.swap_size_le avoids minimal Z P Q base inc,
    fun base inc => Graph.RerouteSwap.swap_not_lexSmaller avoids minimal Z P Q base inc,
    fun av cert => Graph.RerouteSwap.swap_cycle_double_use av Z P Q cert⟩

/-- **The rerouted swaps of G's pattern supports**, in both directions. -/
theorem sameTokenSwap_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H) :
    SameTokenSwapStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, -, -, selected, pZ, qZ, -⟩ := partition
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := partition_supports_nonempty routing routingEq noProper.2 hXp hXq
  exact ⟨routing, routingEq, Xp, Xq, Z, ⟨hXp, hXq, selected⟩,
    sameTokenSwapAt_holds avoids minimal Z Xp Xq (swap_vertex_exists (qZ hq) hq),
    sameTokenSwapAt_holds avoids minimal Z Xq Xp (swap_vertex_exists (pZ hp) hp)⟩

/-- **The exact failure of the rerouted swap `P → Q`.** -/
theorem sameTokenSwapExactAt_holds
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (base : MinDegreeBaselineStatement data object)
    (Z P Q : Finset object.Vertex)
    (hv : ∃ v, ¬ Graph.RerouteSwap.InteriorIn object Z P v ∨
      Graph.RerouteSwap.InteriorIn object Z Q v) :
    SameTokenSwapExactAt data object Z P Q :=
  Graph.RerouteSwap.swap_exact avoids minimal base Z P Q hv

/-- **The exact failure of the two rerouted swaps**, and equal interior sizes
when both are valid. -/
theorem sameTokenSwapExact_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (base : MinDegreeBaselineStatement data object) :
    SameTokenSwapExactStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, -, -, selected, pZ, qZ, -⟩ := partition
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := partition_supports_nonempty routing routingEq noProper.2 hXp hXq
  exact ⟨routing, routingEq, Xp, Xq, Z, ⟨hXp, hXq, selected⟩,
    sameTokenSwapExactAt_holds avoids minimal base Z Xp Xq (swap_vertex_exists (qZ hq) hq),
    sameTokenSwapExactAt_holds avoids minimal base Z Xq Xp (swap_vertex_exists (pZ hp) hp),
    fun b1 i1 b2 i2 => le_antisymm
      (Graph.RerouteSwap.swap_size_le avoids minimal Z Xp Xq b1 i1)
      (Graph.RerouteSwap.swap_size_le avoids minimal Z Xq Xp b2 i2)⟩

/-- **Boundary-free configuration: valid transplants of both supports force the
whole graph, and the vertex-deletion shape of G then gives even degree at least
`4` outside the pair seeds.** -/
theorem sameTokenU2FreeWhole_holds
    (partition : SameTokenPairPartitionStatement data object)
    (noProper : NoProperBaselineStatement data object)
    (avoids : ¬ Graph.HasCycleWithLength data.LengthOK object)
    (minimal : ∀ H : Graph.FiniteObject.{u}, H.LexicographicallySmaller object →
      Graph.MinimumDegreeAtLeast data.threshold H → Graph.HasCycleWithLength data.LengthOK H)
    (shape : VertexDeletionComponentsStatement object)
    (base : MinDegreeBaselineStatement data object)
    (threshold : data.threshold = 3) :
    SameTokenU2FreeWholeStatement data object := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  obtain ⟨routing, routingEq, Xp, Xq, Z, hXp, hXq, -, selP, selQ, selected, pZ, qZ, -⟩ :=
    partition
  obtain ⟨⟨p, hp⟩, -⟩ := partition_supports_nonempty routing routingEq noProper.2 hXp hXq
  have connP : Graph.SupportComponents.Connected.ConnectedOn object Xp :=
    (CanonicalSupport.mem_candidates_iff.1 (CanonicalSupport.select?_mem_candidates selP)).2
  have base3 : ∀ v, 3 ≤ object.degree v := fun v => by
    have := le_trans base (object.minDegree_le_degree v)
    omega
  refine ⟨routing, routingEq, Xp, Xq, Z, ⟨hXp, hXq, selected⟩,
    fun freeP freeQ baseQ baseP => ?_⟩
  have fillP := Graph.Transplant.transplant_fills_of_baseline avoids minimal Z Xp baseP
  have fillQ := Graph.Transplant.transplant_fills_of_baseline avoids minimal Z Xq baseQ
  obtain ⟨eqP, eqQ, noCut, univ⟩ := Graph.U2FreeWhole.whole noProper.2 selected pZ qZ connP
    freeP freeQ
    (fun v vZ vb => by by_contra vP; exact fillP v ⟨vZ, vb, vP⟩)
    (fun v vZ vb => by by_contra vQ; exact fillQ v ⟨vZ, vb, vQ⟩) ⟨p, hp⟩
  have cutP : ∀ v, v ∈ Z → v ∉ routing.capacity.activation.pairSeed routing.demands.first →
      ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v) := by
    intro v vZ vSeed
    have := ReadingProfiles.select_nonseed_cut selP (eqP ▸ vZ) vSeed
    rw [eqP] at this
    convert this
  have cutQ : ∀ v, v ∈ Z → v ∉ routing.capacity.activation.pairSeed routing.demands.second →
      ¬ Graph.SupportComponents.Connected.ConnectedOn object (Z.erase v) := by
    intro v vZ vSeed
    have := ReadingProfiles.select_nonseed_cut selQ (eqQ ▸ vZ) vSeed
    rw [eqQ] at this
    convert this
  have evP : ∀ v, v ∉ routing.capacity.activation.pairSeed routing.demands.first →
      Even (object.degree v) ∧ 4 ≤ object.degree v := fun v hv =>
    Graph.WholeBlocks.cut_even_degree shape base3 univ (cutP v (univ v) hv)
  have evQ : ∀ v, v ∉ routing.capacity.activation.pairSeed routing.demands.second →
      Even (object.degree v) ∧ 4 ≤ object.degree v := fun v hv =>
    Graph.WholeBlocks.cut_even_degree shape base3 univ (cutQ v (univ v) hv)
  refine ⟨eqP, eqQ, noCut, univ, cutP, cutQ, evP, evQ, ?_, ?_⟩
  · intro v h3
    refine ⟨by_contra fun hv => ?_, by_contra fun hv => ?_⟩
    · have := evP v hv; omega
    · have := evQ v hv; omega
  · intro hall v
    refine ⟨by_contra fun hv => cutP v (univ v) hv (hall v),
      by_contra fun hv => cutQ v (univ v) hv (hall v)⟩

end Hypostructure.Graph.Contracts.Spine.SameTokenSwap
