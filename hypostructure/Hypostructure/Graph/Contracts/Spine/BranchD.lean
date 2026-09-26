import Hypostructure.Graph.Statements.Spine

/-!
# Contracts: the rank split and Branch D, `[32]`--`[46]`

Proof-agnostic contract lemmas for `lem:target-rank-circuit`'s finite split,
`lem:curvature-dependence-routing`, `lem:separated-testers`,
`lem:context-universality`, `lem:proper-smearing`,
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
  have packingSpec := Classical.choose_spec
    (object.exists_windowPacking_card_eq data.windowOrder)
  have valid : object.IsWindowPacking data.windowOrder packing := packingSpec.1
  have packingCard : packing.card = object.windowPackingNumber data.windowOrder :=
    packingSpec.2
  have extract := (circuit packing valid packingCard).1
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
  have packingSpec := Classical.choose_spec
    (object.exists_windowPacking_card_eq data.windowOrder)
  have valid : object.IsWindowPacking data.windowOrder packing := packingSpec.1
  have packingCard : packing.card = object.windowPackingNumber data.windowOrder :=
    packingSpec.2
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

/-- **Nodes `[33]`/`[35]`** (`lem:curvature-dependence-routing`).  The
rank-drop arm contains a concrete determination; among all certificates for
that determined coordinate, one has an inclusion-minimal connected declared
support. -/
theorem branchDependence_of_curvatureRankDrop (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (drop : CurvatureRankDropStatement data object) :
    BranchDependenceStatement data object := by
  classical
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  rcases drop with
    ⟨packing, _canonical, valid, packingCard, below, test, testMember,
      determiners, determinersSubset, finite, proper, declared,
      functional, reducing, determines⟩
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
  refine ⟨packing, valid, packingCard, below, test, ?_⟩
  dsimp only
  set Supports :=
    object.vertexFinset.powerset.filter
      fun candidateSupport =>
        ∃ basis candidate,
          candidate.support = candidateSupport ∧
            ∃ candidateSupportData,
              DeterminationCertificate data object
                packing test basis candidate candidateSupportData
  change ∃ selectedDeterminers selectedQuotient selectedSupportData,
    DeterminationCertificate data object packing test
          selectedDeterminers selectedQuotient selectedSupportData ∧
      ∀ smaller : Finset object.Vertex,
        smaller ⊂ selectedQuotient.support →
          ∀ narrower : remainderQuotient data object packing,
            narrower.support = smaller →
              ∀ narrowerDeterminers narrowerSupportData,
                ¬ DeterminationCertificate data object
                  packing test narrowerDeterminers narrower
                    narrowerSupportData
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
  refine ⟨chosenDeterminers, chosen, chosenSupportData,
    chosenCertified, ?_⟩
  intro smaller strict narrower narrowerSupport narrowerDeterminers
    narrowerSupportData narrowerCertified
  have carried : smaller ∈ Supports := by
    simp only [Supports, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨by intro vertex _; simp, narrowerDeterminers, narrower,
      narrowerSupport, narrowerSupportData, narrowerCertified⟩
  have minimum := least smaller carried
  exact absurd (Finset.card_lt_card strict) (by omega)

/-- **Node `[35]`, `lem:separated-testers`.**  An owned decomposition whose
piece side covers two disjoint balls leaves every internal outside vertex in
their complement; for an attempted quotient identifying their labels, every
identified pair is context-universal or one has a concrete target defect. -/
theorem separatedTesters (data : Parameters) (object : Graph.FiniteObject.{u}) :
    SeparatedTestersStatement data object := by
  classical
  intro packing _valid _packingCard radius u v _uMem _vMem
  dsimp only
  intro leftWedge rightWedge _leftMem _rightMem _leftRoot _rightRoot
    _sameType _disjoint
  constructor
  · intro decomposition pieceCovers represented _separates internal
    constructor <;> intro inBall
    · obtain ⟨inside, same⟩ :=
        (pieceCovers _).mp (Or.inl inBall)
      have impossible :
          Graph.pieceEmbedding decomposition.piece
              decomposition.outside inside =
            Graph.contextEmbedding decomposition.piece
              decomposition.outside (.inr internal) := by
        apply decomposition.vertexEquiv.injective
        simpa [Graph.OwnedDecomposition.pieceIntoAmbient] using same
      cases inside <;>
        simp [Graph.pieceEmbedding, Graph.contextEmbedding] at impossible
    · obtain ⟨inside, same⟩ :=
        (pieceCovers _).mp (Or.inr inBall)
      have impossible :
          Graph.pieceEmbedding decomposition.piece
              decomposition.outside inside =
            Graph.contextEmbedding decomposition.piece
              decomposition.outside (.inr internal) := by
        apply decomposition.vertexEquiv.injective
        simpa [Graph.OwnedDecomposition.pieceIntoAmbient] using same
      cases inside <;>
        simp [Graph.pieceEmbedding, Graph.contextEmbedding] at impossible
  · intro attempt _identified
    by_cases universal :
        ∀ left right : Graph.BoundaryPiece
            (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary
              object attempt.support),
          attempt.Identifies left right →
            Graph.Response.ContextEquivalent
              (Graph.HasCycleWithLength data.LengthOK) left right
    · exact Or.inl universal
    · right
      push Not at universal
      obtain ⟨left, right, sameValues, failure⟩ := universal
      exact ⟨left, right, sameValues,
        Graph.Response.targetDefect_of_not_contextEquivalent failure⟩

/-- **Node `[36]`, the context-validity test.**  The inclusion-minimal
certificate of `[33]` is valid against every outside context, or some pair it
identifies has a concrete distinguishing (target-defect) context. -/
theorem contextDefect_or_contextUniversal (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (dependence : BranchDependenceStatement data object) :
    ContextDefectStatement data object ∨ ContextUniversalStatement data object := by
  classical
  obtain ⟨packing, valid, packingCard, _below, test, determiners, quotient,
    supportData, certified, minimal⟩ := dependence
  by_cases universal :
      ∀ left right, Identified quotient left right →
        Graph.Response.ContextEquivalent
          (Graph.HasCycleWithLength data.LengthOK) left right
  · exact .inr ⟨packing, valid, packingCard, test, determiners, quotient,
      supportData, certified, minimal, universal⟩
  · refine .inl ⟨packing, valid, packingCard, test, determiners, quotient,
      supportData, certified, minimal, ?_⟩
    push Not at universal
    obtain ⟨left, right, identified, failure⟩ := universal
    exact ⟨left, right, identified,
      Graph.Response.targetDefect_of_not_contextEquivalent failure⟩

/-- **The terminal `[37]` is uninhabited** (`lem:context-universality`).  The
certificate's admissible quotient is context-universal on its identified
pairs, so no outside context distinguishes an identified pair. -/
theorem contextDefect_false (data : Parameters) (object : Graph.FiniteObject.{u})
    (defect : ContextDefectStatement data object) : False := by
  obtain ⟨_packing, _valid, _packingCard, _test, _determiners, quotient,
    _supportData, _certificate, _minimal, left, right, identified,
    outside, distinguishes⟩ := defect
  exact distinguishes (quotient.contextUniversal left right identified outside)

/-- **Node `[38]`: is the determination certified already at `C`?**  A
context-universal certificate is target-complete (degree-profile fibres and
target-complete context universality).  If its support lies in the remainder,
it misses a window vertex, so `def:admissible-rank-quotient` supplies a
strictly smaller proper representative (`[39]`); otherwise its support
strictly enlarges the remainder (`[40]`). -/
theorem atomCompression_or_delocalizedSupport (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (universalFact : ContextUniversalStatement data object)
    (fibres : DegreeProfileFibresStatement data object)
    (completeUniversality : TargetCompleteContextUniversalityStatement data object)
    (maximalPacking : MaximalPackingStatement data object) :
    AtomCompressionStatement data object ∨ DelocalizedSupportStatement data object := by
  classical
  obtain ⟨packing, valid, packingCard, test, determiners, quotient, supportData,
    certified, _minimal, universal⟩ := universalFact
  have packingPositive := maximalPacking.1
  have complete : TargetCompleteAt data quotient := by
    intro left right identified
    have targetComplete : Graph.Response.TargetComplete
        Graph.BoundaryPiece.boundaryDegreeProfile
        (Graph.HasCycleWithLength data.LengthOK) left right :=
      ⟨quotient.fibrewise left right identified,
        universal left right identified⟩
    exact ⟨fibres quotient.support left right targetComplete,
      completeUniversality quotient.support left right targetComplete⟩
  by_cases inside : quotient.support ⊆ object.remainderSupport packing
  · have packingNonempty : packing.Nonempty :=
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
    have reducing : quotient.toRankQuotient.RankReducingOn
        ↑(remainderCurvatureTests object packing) :=
      certified.2.2.2.2.2.1
    have replacement := quotient.properRepresentative supportProper reducing
    exact .inl ⟨packing, valid, quotient,
      ⟨test, determiners, supportData, certified⟩, complete, inside,
      replacement⟩
  · exact .inr ⟨packing, valid, quotient,
      ⟨test, determiners, supportData, certified⟩, complete, inside,
      remainderSupport_ssubset_delocalizationSupport data quotient inside⟩

/-- **Node `[41]`: is the enlarged support proper in `G`?**  If the
quotient's connected determination support `Z` misses a vertex, the rank
reduction yields a strictly smaller proper representative (`[42]`,
`lem:proper-smearing`); otherwise `Z = G` (`[43]`). -/
theorem properDelocalization_or_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (delocalized : DelocalizedSupportStatement data object) :
    ProperDelocalizationStatement data object ∨
      GlobalDelocalizationStatement data object := by
  classical
  obtain ⟨packing, valid, quotient, certificate, complete, outside, _enlarged⟩ :=
    delocalized
  by_cases proper : ∃ vertex, vertex ∉ quotient.support
  · obtain ⟨vertex, vertexOutside⟩ := proper
    obtain ⟨test, determiners, supportData, certified⟩ := certificate
    have reducing : quotient.toRankQuotient.RankReducingOn
        ↑(remainderCurvatureTests object packing) :=
      certified.2.2.2.2.2.1
    have replacement :=
      quotient.properRepresentative ⟨vertex, vertexOutside⟩ reducing
    exact .inl ⟨packing, valid, quotient,
      ⟨test, determiners, supportData, certified⟩, complete, outside,
      vertex, vertexOutside, replacement⟩
  · push Not at proper
    exact .inr ⟨packing, valid, quotient, certificate, complete, outside, proper⟩

/-- **Node `[44]`, `lem:smearing-support-repair`.**  A delayed compensation
component with `p` boundary leaves, `s` internal vertices, cycle rank `β` and
surplus `σ` satisfies `s = p − 2 + 2β − σ`, by the handshake identity and the
cycle-rank formula. -/
theorem repairIdentity (object : Graph.FiniteObject.{u}) :
    RepairIdentityStatement object := by
  dsimp only [RepairIdentityStatement]
  intro component _componentOnActiveSupport
  have handshake :
      (3 : Int) * component.internal.card + component.surplus +
          component.boundary.card =
        2 * component.object.edgeCount := by
    exact_mod_cast component.handshake
  have rank := component.cycleRank_cast
  rw [component.vertexCard_eq] at rank
  push_cast at rank
  linarith

/-- **Node `[45]`, `lem:no-silent-global-smearing`.**  A whole-graph
rank-reducing dependence has, by the closed clause of
`def:admissible-rank-quotient`, a strictly smaller admissible closed
representative. -/
theorem globalBarrier_of_globalDelocalization (data : Parameters)
    (object : Graph.FiniteObject.{u})
    (global : GlobalDelocalizationStatement data object) :
    GlobalBarrierStatement data object := by
  dsimp only [GlobalBarrierStatement]
  obtain ⟨packing, _valid, quotient, certificate, _complete, _outside,
    covers⟩ := global
  obtain ⟨_test, _determiners, _supportData, certified⟩ := certificate
  have reducing : quotient.toRankQuotient.RankReducingOn
      ↑(remainderCurvatureTests object packing) :=
    certified.2.2.2.2.2.1
  exact quotient.closedRepresentative covers reducing

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
  obtain ⟨_packing, _valid, quotient, _certificate, _complete, _inside,
    replacement⟩ := compression
  exact not_replacementSupport_of_selection BranchState Presentation presentation
    data object state baseline selected quotient.support replacement

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
  obtain ⟨_packing, _valid, quotient, _certificate, _complete, _outside,
    _vertex, _vertexOutside, replacement⟩ := smearing
  exact not_replacementSupport_of_selection BranchState Presentation presentation
    data object state baseline selected quotient.support replacement

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
  obtain ⟨representative, smaller, representativeBaseline, transfer⟩ := barrier
  exact selected.1 (transfer (selected.2 representative smaller representativeBaseline))

end Hypostructure.Graph.Contracts.Spine
