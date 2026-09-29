import Hypostructure.Graph.Statements.BranchD

/-!
# Contracts: the rank split and Branch D, `[32]`--`[46]`

Proof-agnostic contract lemmas for `lem:target-rank-circuit`'s finite split,
`lem:curvature-dependence-routing`, `lem:context-universality`, `lem:proper-smearing`,
`lem:smearing-support-repair` and `lem:no-silent-global-smearing`.  Each lemma
is stated over a `Graph.FiniteObject` with the registered `Parameters` as a
parameter and every paper hypothesis explicit; its conclusion is exactly the
statement of the fact it proves.  This module imports no strategy, row, or
vocabulary module.
-/

namespace Hypostructure.Graph.Contracts.Spine

open Hypostructure
open Hypostructure.Graph.Strategy.Spine

universe u v

/-- **Node `[32]`, rank-drop arm** (the paragraph after
`lem:target-rank-circuit`).  At the fixed maximal packing, a strict rank drop
`r_Ω(R) < W₂(R)` leaves a raw curvature coordinate outside an attaining
independent family, and the circuit lemma determines it by a concrete proper
declared quotient. -/
theorem curvatureRankDrop_of_rankBelow (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (_rankFact : CurvatureTargetRankStatement data object)
    (circuit : TargetRankCircuitStatement data object)
    (below :
      remainderCurvatureTargetRank data object
          (canonicalWindowPacking data object) <
        remainderWedgeSupply object (canonicalWindowPacking data object)) :
    CurvatureRankDropStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  obtain ⟨independent, independentEq, extract⟩ := circuit.1
  obtain ⟨independentSubset, _survives, rank⟩ :=
    canonicalSurvivingFamily?_spec_of_eq_some data object independentEq
  refine ⟨below, independent, independentEq, ?_⟩
  have outside : ∃ test ∈
      object.internalWedgeFamily (object.remainderSupport packing),
      test ∉ independent := by
    by_contra noOutside
    push Not at noOutside
    have familySubset :
        object.internalWedgeFamily (object.remainderSupport packing) ⊆
          independent :=
      noOutside
    have equal : independent =
        object.internalWedgeFamily (object.remainderSupport packing) :=
      Finset.Subset.antisymm independentSubset familySubset
    rw [equal, Graph.FiniteObject.internalWedgeFamily_card] at rank
    exact (Nat.ne_of_lt below) rank.symm
  obtain ⟨test, testMember, testOutside⟩ := outside
  obtain ⟨determiners, determinersSubset, finite, proper, declared,
    functional, reducing, determines⟩ :=
    extract test testMember testOutside
  exact ⟨test, testMember, testOutside, determiners, determinersSubset, finite,
    proper, declared, functional, reducing, determines⟩

/-- **Node `[32]`, full-rank arm.**  Without a strict drop at the fixed maximal
packing, the curvature target rank equals the wedge supply: it never exceeds
the internal wedge count, since an attaining family is a subfamily. -/
theorem curvatureFullRank_of_not_rankBelow (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (notBelow :
      ¬ remainderCurvatureTargetRank data object
          (canonicalWindowPacking data object) <
        remainderWedgeSupply object (canonicalWindowPacking data object)) :
    CurvatureFullRankStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  have attained := Graph.FiniteObject.exists_attaining_curvatureTargetRank
    (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object
    (object.remainderSupport packing)
  let independent := Classical.choose attained
  have independentSpec := Classical.choose_spec attained
  have independentSubset : independent ⊆ _ := independentSpec.1
  have rank : independent.card = _ := independentSpec.2.2
  clear_value independent
  apply Nat.le_antisymm
  · change
      object.curvatureTargetRank
          (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK)
          (object.remainderSupport packing) ≤
        object.internalWedgeCount (object.remainderSupport packing)
    rw [← rank]
    calc
      independent.card ≤
          (object.internalWedgeFamily (object.remainderSupport packing)).card :=
        Finset.card_le_card independentSubset
      _ = object.internalWedgeCount (object.remainderSupport packing) :=
        Graph.FiniteObject.internalWedgeFamily_card
          (object := object) (support := object.remainderSupport packing)
  exact Nat.le_of_not_gt notBelow

/-- **Nodes `[33]`/`[35]`** (`lem:curvature-dependence-routing`, tex 9204).
Node `[19]`'s determined test at the canonical packing (the canonical choice
`curvatureRankDropTest?`) has a concrete determination; among all certificates
for that test, one has an inclusion-minimal connected declared support. -/
theorem branchDependence_of_curvatureRankDrop (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (drop : CurvatureRankDropStatement data object) :
    BranchDependenceStatement data object := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  obtain ⟨test, testEq, below, independent, independentEq, testMember, _testOutside,
      determiners, determinersInside, finite, proper, declared, functional,
      reducing, determines⟩ :=
    curvatureRankDropTest?_spec data object
      ((curvatureRankDrop_iff_exists_testSpec data object).1 drop)
  have determinersSubset := determinersInside.trans
    (Finset.coe_subset.mpr
      (canonicalSurvivingFamily?_spec_of_eq_some data object independentEq).1)
  have valid := (canonicalWindowPacking_spec data object).1
  have packingCard := (canonicalWindowPacking_spec data object).2.1
  let packing := canonicalWindowPacking data object
  let support := object.remainderSupport packing
  let family := object.internalWedgeFamily support
  let supportData := family
  have supportDataCarried : ∀ coordinate ∈ supportData,
      Graph.FiniteObject.internalWedgeSupport
          (region := support) coordinate ⊆ declared.support := by
    intro coordinate coordinateMember
    exact declared.carries coordinate coordinateMember
  have certified :
      DeterminationCertificate data object packing test
        determiners declared supportData :=
    ⟨testMember, determinersSubset, finite, proper, functional,
      reducing, determines, rfl, supportDataCarried⟩
  let Supports :=
    object.vertexFinset.powerset.filter
      fun candidateSupport =>
        ∃ basis candidate,
          candidate.support = candidateSupport ∧
            ∃ candidateSupportData,
              DeterminationCertificate data object
                packing test basis candidate candidateSupportData
  have inhabited : declared.support ∈ Supports := by
    simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by intro vertex _; simp, determiners, declared, rfl,
      supportData, certified⟩
  obtain ⟨leastSupport, leastMember, least⟩ :=
    Finset.exists_min_image Supports Finset.card ⟨_, inhabited⟩
  have leastInSupports := leastMember
  simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
    at leastInSupports
  rcases leastInSupports with ⟨_, leastInSupports⟩
  obtain ⟨chosenDeterminers, chosen, supportEq,
    chosenSupportData, chosenCertified⟩ := leastInSupports
  subst leastSupport
  refine ⟨⟨test, chosenDeterminers, chosen, chosenSupportData⟩,
    testEq, valid, packingCard, below, chosenCertified, ?_⟩
  intro smaller strict narrower narrowerSupport narrowerDeterminers
    narrowerSupportData narrowerCertified
  have carried : smaller ∈ Supports := by
    simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by intro vertex _; simp, narrowerDeterminers, narrower,
      narrowerSupport, narrowerSupportData, narrowerCertified⟩
  have minimum := least smaller carried
  have strict' : smaller ⊂ chosen.support := strict
  exact absurd (Finset.card_lt_card strict') (by omega)

/-- The certificate of `G` carries node `[21]`'s rank reduction on the raw
curvature tests. -/
theorem branchCertificate_rankReducing {data : Parameters}
    {object : Graph.FiniteObject.{u}}
    {certificate : BranchCertificateData data object}
    (eq : branchCertificate? data object = some certificate) :
    certificate.quotient.toRankQuotient.RankReducingOn
      ↑(remainderCurvatureTests object (canonicalWindowPacking data object)) :=
  (branchCertificate?_spec_of_eq_some data object eq).2.2.2.2.1.2.2.2.2.2.1

/-- **Node `[36]`, the context-validity test**, at the one certificate of `G`,
stated about G: the pieces constructed from G that it identifies agree in G's
own rest `G − Z`, or some identified pair is separated there (the exact
complement at the same certificate). -/
theorem contextDefect_or_contextUniversal (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dependence : BranchDependenceStatement data object) :
    ContextDefectStatement data object ∨ ContextUniversalStatement data object := by
  classical
  obtain ⟨certificate, eq, -⟩ := branchCertificate?_spec data object dependence
  by_cases universal : CertificateContextUniversal data certificate
  · exact .inr ⟨certificate, eq, universal⟩
  · refine .inl ⟨certificate, eq, ?_⟩
    by_contra absent
    exact universal fun left right identified => by
      by_contra failure
      exact absent ⟨left, right, identified, failure⟩

/-- **The terminal `[37]` closes against node `[12]`** (`lem:context-universality`;
`lem:full-rank`, tex 9388: "the first is excluded by the definition of
target-completeness").  The certificate's quotient is an admissible rank
quotient of G's declared coordinates at `R₀`: its condition (b) of
`def:target-complete-quotient` (node `[12]`'s content,
`DeclaredQuotient.contextUniversal`) makes every two constructed pieces it
identifies agree in `G − Z`. -/
theorem contextDefect_false_of_contextUniversality (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (_universality : TargetCompleteContextUniversalityStatement data object)
    (defect : ContextDefectStatement data object) : False := by
  obtain ⟨certificate, _eq, left, right, identified, separated⟩ := defect
  exact separated (certificate.quotient.contextUniversal left right identified)

/-- **Node `[36]` is decided at G**: the certificate of `G` is valid in every
context of G.  Its quotient is admissible, so condition (b) of
`def:target-complete-quotient` holds at G for every two constructed pieces it
identifies (`DeclaredQuotient.contextUniversal`). -/
theorem contextUniversal_of_selection
    {BranchState : Graph.FiniteObject.{u} → Type v}
    {Presentation : Type} {presentation : Presentation}
    (data : Parameters) (object : Graph.FiniteObject.{u})
    (dependence : BranchDependenceStatement data object)
    (_selection : SelectionStatement BranchState Presentation presentation data object) :
    ContextUniversalStatement data object := by
  obtain ⟨certificate, eq, -⟩ := branchCertificate?_spec data object dependence
  exact ⟨certificate, eq, fun left right identified =>
    certificate.quotient.contextUniversal left right identified⟩

/-- **Node `[38]`: is the determination certified already at `C = R(P₀)`?**
If the certificate's support lies in the remainder, it misses a window vertex of
the nonempty canonical packing, so `def:admissible-rank-quotient` supplies a
strictly smaller proper representative (`[39]`); otherwise its support strictly
enlarges the remainder (`[40]`). -/
theorem atomCompression_or_delocalizedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (universal : ContextUniversalStatement data object)
    (packingPositive : 0 < object.windowPackingNumber data.windowOrder) :
    AtomCompressionStatement data object ∨ DelocalizedSupportStatement data object := by
  classical
  obtain ⟨certificate, eq, -⟩ := universal
  have valid := (branchCertificate?_spec_of_eq_some data object eq).2.1
  have packingCard := (branchCertificate?_spec_of_eq_some data object eq).2.2.1
  have reducing := branchCertificate_rankReducing eq
  let quotient := certificate.quotient
  by_cases inside : quotient.support ⊆ canonicalRemainder data object
  · have packingNonempty : (canonicalWindowPacking data object).Nonempty :=
      Finset.card_pos.mp (packingCard ▸ packingPositive)
    obtain ⟨member, memberMem⟩ := packingNonempty
    have windowNonempty :=
      object.nonempty_of_inducesWindow data.windowOrder_pos
        (valid.1 member memberMem)
    obtain ⟨vertex, vertexMem⟩ := windowNonempty
    have supportProper : ∃ vertex, vertex ∉ quotient.support := by
      refine ⟨vertex, ?_⟩
      intro vertexInSupport
      have vertexInRemainder := inside vertexInSupport
      exact
        (object.notMem_windowSupport_of_mem_remainderSupport vertexInRemainder)
          (object.mem_windowSupport memberMem vertexMem)
    exact .inl ⟨certificate, eq, inside,
      quotient.properRepresentative supportProper reducing⟩
  · exact .inr ⟨certificate, eq, inside,
      remainderSupport_ssubset_delocalizationSupport data quotient inside⟩

/-- **Node `[41]`: is the certificate's support `Z` proper in `G`?**  If it
misses a vertex, the rank reduction yields a strictly smaller proper
representative (`[42]`, `lem:proper-smearing`); otherwise `Z = G` (`[43]`). -/
theorem properDelocalization_or_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (delocalized : DelocalizedSupportStatement data object) :
    ProperDelocalizationStatement data object ∨
      GlobalDelocalizationStatement data object := by
  classical
  obtain ⟨certificate, eq, -⟩ := delocalized
  by_cases proper : ∃ vertex, vertex ∉ certificate.quotient.support
  · exact .inl ⟨certificate, eq, proper,
      certificate.quotient.properRepresentative proper
        (branchCertificate_rankReducing eq)⟩
  · push Not at proper
    exact .inr ⟨certificate, eq, proper⟩

/-- **Node `[44]`, `lem:smearing-support-repair`**, at the certificate of the
whole-graph arm: at the cubic baseline every vertex of `G` has degree at least
three, so each delayed compensation component of its support is a `1`--`3`
repair network, and `s = p − 2 + 2β − σ`. -/
theorem repairIdentity_of_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (global : GlobalDelocalizationStatement data object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (cubic : CubicBaselineStatement data) :
    RepairIdentityStatement data object := by
  obtain ⟨certificate, eq, -⟩ := global
  refine ⟨certificate, eq, fun component =>
    Graph.RepairNetwork.repairIdentity _ component ?_⟩
  intro vertex _
  have atLeast : data.threshold ≤ object.degree vertex :=
    le_trans baseline (object.minDegree_le_degree vertex)
  rw [cubic.1] at atLeast
  exact atLeast

/-- **Node `[45]`, `lem:no-silent-global-smearing`.**  The certificate's
whole-graph rank-reducing quotient has, by the closed clause of
`def:admissible-rank-quotient`, a strictly smaller admissible closed
representative: a baseline graph with no power-of-two cycle. -/
theorem globalBarrier_of_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (global : GlobalDelocalizationStatement data object) :
    GlobalBarrierStatement data object := by
  obtain ⟨certificate, eq, covers⟩ := global
  exact ⟨certificate, eq, covers, branchCertificate_rankReducing eq,
    certificate.quotient.closedRepresentative covers
      (branchCertificate_rankReducing eq)⟩

/-- **The terminal `[39]`** (`lem:replacement`, node `[13]`; tex 9226
`cor:uncompressible`).  The strictly smaller proper representative the
certificate's admissible quotient supplies at `C = R(P₀)` is a replacement of
its support — G's boundary-degree profile, the baseline and no power-of-two
cycle in `glue X' (G − Z)`, strictly smaller — which node `[13]` excludes on
G. -/
theorem atomCompression_replacementExclusion_false (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (exclusion : ReplacementExclusionStatement data object)
    (compression : AtomCompressionStatement data object) : False := by
  obtain ⟨certificate, _eq, _inside, replacement⟩ := compression
  exact exclusion certificate.quotient.support replacement

/-- **The terminal `[42]`** (`lem:proper-smearing`, tex 9264).  The proper
support `Z ⊊ G` carries the certificate's rank-reducing admissible quotient,
whose strictly smaller proper representative is a replacement of `Z`, excluded
by node `[13]`. -/
theorem properDelocalization_replacementExclusion_false (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (exclusion : ReplacementExclusionStatement data object)
    (smearing : ProperDelocalizationStatement data object) : False := by
  obtain ⟨certificate, _eq, _proper, replacement⟩ := smearing
  exact exclusion certificate.quotient.support replacement

/-- **The terminal `[46]`** (`lem:no-silent-global-smearing`).  Selection
minimality puts a power-of-two cycle in the strictly smaller closed baseline
representative, which has none. -/
theorem globalBarrier_selection_false
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (barrier : GlobalBarrierStatement data object) : False := by
  obtain ⟨_certificate, _eq, _covers, _reducing, representative, smaller,
    representativeBaseline, noTarget⟩ := barrier
  exact noTarget (selected.2 representative smaller representativeBaseline)

end Hypostructure.Graph.Contracts.Spine
