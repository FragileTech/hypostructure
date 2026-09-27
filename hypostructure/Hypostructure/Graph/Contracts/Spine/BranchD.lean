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
    (circuit : TargetRankCircuitStatement data object)
    (below :
      remainderCurvatureTargetRank data object
          (canonicalWindowPacking data object) <
        remainderWedgeSupply object (canonicalWindowPacking data object)) :
    CurvatureRankDropStatement data object := by
  classical
  let packing := canonicalWindowPacking data object
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have packingCard : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have extract := circuit.1
  have attained := Graph.FiniteObject.exists_attaining_curvatureTargetRank
    (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object
    (object.remainderSupport packing)
  let independent := Classical.choose attained
  have independentSpec := Classical.choose_spec attained
  have independentSubset : independent ⊆ _ := independentSpec.1
  have survives : Graph.FiniteObject.SurvivesCurvatureSystem
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object
      (object.remainderSupport packing) independent := independentSpec.2.1
  have rank : independent.card = _ := independentSpec.2.2
  clear_value independent
  refine ⟨packing, rfl, valid, packingCard, below, ?_⟩
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
    extract independent independentSubset survives rank test testMember testOutside
  exact ⟨test, testMember, determiners,
    determinersSubset.trans independentSubset, finite, proper,
    declared, functional, reducing, determines⟩

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
  have valid : object.IsWindowPacking data.windowOrder packing :=
    (canonicalWindowPacking_spec data object).1
  have packingCard : packing.card = object.windowPackingNumber data.windowOrder :=
    (canonicalWindowPacking_spec data object).2.1
  have attained := Graph.FiniteObject.exists_attaining_curvatureTargetRank
    (Graph.MinimumDegreeAtLeast data.threshold)
    (Graph.HasCycleWithLength data.LengthOK) object
    (object.remainderSupport packing)
  let independent := Classical.choose attained
  have independentSpec := Classical.choose_spec attained
  have independentSubset : independent ⊆ _ := independentSpec.1
  have rank : independent.card = _ := independentSpec.2.2
  clear_value independent
  refine ⟨packing, rfl, valid, packingCard, ?_⟩
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
  obtain ⟨test, testEq, valid, packingCard, below, testMember, determiners,
      determinersSubset, finite, proper, declared, functional, reducing,
      determines⟩ :=
    curvatureRankDropTest?_spec data object
      ((curvatureRankDrop_iff_exists_testSpec data object).1 drop)
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

/-- **Node `[36]`, the context-validity test**, at the one certificate of `G`:
it is valid against every outside context, or some pair it identifies has a
concrete distinguishing (target-defect) context. -/
theorem contextDefect_or_contextUniversal (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dependence : BranchDependenceStatement data object) :
    ContextDefectStatement data object ∨ ContextUniversalStatement data object := by
  classical
  obtain ⟨certificate, eq, -⟩ := branchCertificate?_spec data object dependence
  by_cases universal : CertificateContextUniversal data certificate
  · exact .inr ⟨certificate, eq, universal⟩
  · refine .inl ⟨certificate, eq, ?_⟩
    unfold CertificateContextUniversal at universal
    push Not at universal
    obtain ⟨left, right, identified, failure⟩ := universal
    exact ⟨left, right, identified,
      Graph.Response.targetDefect_of_not_contextEquivalent failure⟩

/-- **The terminal `[37]` is uninhabited** (`lem:context-universality`;
`lem:no-silent-global-smearing`, second paragraph).  The certificate's quotient
is admissible, hence context-universal on its identified pairs, so no outside
context distinguishes an identified pair. -/
theorem contextDefect_false (data : Parameters) (object : Graph.FiniteObject.{u})
    (defect : ContextDefectStatement data object) : False := by
  obtain ⟨certificate, _eq, left, right, identified, outside, distinguishes⟩ :=
    defect
  exact distinguishes
    (certificate.quotient.contextUniversal left right identified outside)

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
representative. -/
theorem globalBarrier_of_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (global : GlobalDelocalizationStatement data object) :
    GlobalBarrierStatement data object := by
  obtain ⟨certificate, eq, covers⟩ := global
  exact ⟨certificate, eq,
    certificate.quotient.closedRepresentative covers
      (branchCertificate_rankReducing eq)⟩

/-- The selected minimal counterexample, as the context the replacement
lemma is stated against. -/
private theorem not_replacementSupport_of_selection
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u}) (state : BranchState object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (support : Finset object.Vertex)
    (replacement : Graph.Strategy.InterfaceReplacement.ReplacementSupport
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object support) : False :=
  Graph.Strategy.InterfaceReplacement.not_replacementSupport
    (Graph.MinimumDegreeAtLeast data.threshold) BranchState
    (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold)
    Presentation presentation
    (Core.Target.ofPredicate _ (Graph.HasCycleWithLength data.LengthOK))
    ((Graph.cycleTargetInterface data.LengthOK).coreInvariantWithPresentation
      (Graph.MinimumDegreeAtLeast data.threshold) BranchState
      Presentation presentation
      (Graph.minimumDegreeAtLeast_isomorphismInvariant data.threshold))
    { G := object, baseline := baseline, state := state,
      avoids := selected.1, minimal := selected.2.sizeMinimal }
    support replacement

/-- **The terminal `[39]`** (`cor:uncompressible`).  The proper-support
replacement derived at `[38]` is forbidden at the selected minimal
counterexample (`lem:replacement`). -/
theorem atomCompression_selection_false
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u}) (state : BranchState object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (compression : AtomCompressionStatement data object) : False := by
  obtain ⟨certificate, _eq, _inside, replacement⟩ := compression
  exact not_replacementSupport_of_selection BranchState Presentation presentation
    data object state baseline selected certificate.quotient.support replacement

/-- **The terminal `[42]`** (`lem:proper-smearing`).  The proper enlarged
support `Z ⊊ G` carries a target-complete rank reduction, hence a
replacement, forbidden by `cor:uncompressible`. -/
theorem properDelocalization_selection_false
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u}) (state : BranchState object)
    (baseline : Graph.MinimumDegreeAtLeast data.threshold object)
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (smearing : ProperDelocalizationStatement data object) : False := by
  obtain ⟨certificate, _eq, _proper, replacement⟩ := smearing
  exact not_replacementSupport_of_selection BranchState Presentation presentation
    data object state baseline selected certificate.quotient.support replacement

/-- **The terminal `[46]`** (`lem:no-silent-global-smearing`).  Selection
minimality puts the target in the strictly smaller closed representative,
target transfer puts it in the selected object, and selection avoidance gives
the contradiction. -/
theorem globalBarrier_selection_false
    (BranchState : Graph.FiniteObject.{u} → Type v)
    (Presentation : Type) (presentation : Presentation) (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (selected : SelectionStatement BranchState Presentation presentation data object)
    (barrier : GlobalBarrierStatement data object) : False := by
  obtain ⟨_certificate, _eq, representative, smaller, representativeBaseline,
    transfer⟩ := barrier
  exact selected.1 (transfer (selected.2 representative smaller representativeBaseline))

end Hypostructure.Graph.Contracts.Spine
