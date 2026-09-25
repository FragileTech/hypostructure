# Routing-label identity integration

Status: **SUBMITTED_RESULT**. Implementation status: **kernel_checked**.

The owner-local identity `sameTokenActualRoutingLabel = routingLabel` is proved on the identical retained certified pattern, member pair, and selected demand. The complete theorem below concludes this equality for every proof `pairCard : pair.card = 2`; it does not merely check an unused equality in a theorem of `True`. There is no missing inference for this task and no immediate subobligation.

## Scope and integration

Instantiate `data = spineData`, `object = selected.object`, and `active`, `capacity`, `certified`, `token`, `role`, `pattern` with the identical handoff witnesses in the pinned conjunction. Use its retained `patternSubset`, `pairMem`, and demand membership. The proof is uniform in these parameters. Hence it applies under the complete residual without assuming any additional premise or identifying the separate class-audit or capacity-token-ledger witnesses. All other conjuncts, both selection minimalities, exclusions, strict surplus, `2m = 3n + s`, and retained ledger accounts remain intact.

For insertion in `sameTokenBottleneckRoutingRow`, take the `have label_identity ...` block from the theorem proof below, in the saved owner-local context preceding it. Its accepted pointwise body, beginning `have orderedSet` and ending `rw [dif_pos bound]`, is copied verbatim from P6-window-102 up to a two-space indentation shift, under the saved `funext index`. This exact reuse was checked by string comparison; no profile proof was rederived. The saved final tuple `change` and two profile rewrites are unchanged.

The theorem type repeats the literal owner-local definitions to expose the conclusion independently of its proof. After removing indentation, `selectedSupport`, `portStatus`, `selectedSupport_card`, `boundaryProfile`, `boundedSupport`, `windowLabel`, `chordFlag`, and `routingLabel` were each programmatically compared with the retained owner excerpt and matched. Both original profile fallbacks still return `index`, and the empty-support fallback is preserved. The comparison is asserted only on the retained domain.

## Seven-coordinate comparison

Membership in the same certified role fibre gives the original pair-schedule membership and hence both excess-port membership and cardinality two. Both labels use that same `pair.toList` and the same positions zero and one. Proof irrelevance accounts for different bound proofs; neither pair order nor selected demand changes.

| Coordinate | Checked common value |
| --- | --- |
| Role | `capacity.role pair` |
| Token subtype | `Graph.FiniteObject.CapacityToken.subtype token` |
| Endpoint | `if demand = first then 0 else 1 : Fin 2` |
| Status pair | `(portStatus first, portStatus second)` with the literal shoulder-adjacency tests |
| Profile pair | The accepted extensional equalities for `first` and `second`, preserving actual induced degrees and the fixed vertex ordering |
| Window positions | `windowLabel pair`, using the same `capacity.packing` and `capacity.sameTokenRoutingSupport token pair` |
| Blocker flag | `chordFlag pair`, using `canonicalBlocker capacity.activation pair` |

Lean accepts the displayed tuple `change`, so the six non-profile coordinates are definitionally identical in this exact context. Rewriting the two accepted profile equalities completes the product equality. No new structural payoff is supplied by this equality.

## Same source pair and supports

For the pending producer's existing equal-label source witnesses `(pair₁, demand₁)` and `(pair₂, demand₂)`, retain both pattern memberships, both demand memberships, and all their original conditions. Let `E₁ : named₁ = old₁` and `E₂ : named₂ = old₂` be the two instances of this identity. The existing `h : old₁ = old₂` transports as `E₁.trans (h.trans E₂.symm) : named₁ = named₂`; conversely use `E₁.symm.trans (h.trans E₂)`. Thus the exact same witnesses remain an equal-label source pair without selecting replacements.

For each original pair, `capacity.sameTokenRoutingSupport token pair` is literally unchanged, as are the port supports, fixed ordered profiles, and any routes already on those supports. This equality does not identify `capacity.packing` with the separate envelope packing, reconstruct an envelope, or establish a separator or forced non-skeleton edge. The source-bound producer remains the pending obligation from the assignment; it was not implemented. No object/domain representation or account changes occur, and no move or branch is declared closed.

## Kernel-check method

Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`, checked the complete block below with exit status **0**. The command was `/runtime/lean/bin/lean /proc/self/fd/3`, launched by Python 3 with the displayed Lean source in an inherited anonymous memory file (`os.memfd_create`, `pass_fds`). This avoided writing any file outside the two authorized output paths. No vocabulary rebuild or generated on-disk Lean module was performed. The successful run has empty stderr and only style warnings inherited from the literal owner definitions. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, new axiom, equality assumption, or callback.

The complete current-vocabulary package was first in `LEAN_PATH`. Its manifest reports successful compilation, unchanged source, and source SHA256 `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`, verified against the pinned source. The imported `SpineVocabulary.olean` was SHA256-recorded as `b5ef4f67ccc34ab1be9bfe6bd033cd402bbae59288d21aee99333e891ba80a8b`. All ten supplied source hashes were independently recomputed and matched.

The initial wrapper had `exact ∀ (pairCard : pair.card = 2) :` instead of a comma. Correcting that punctuation was the sole check repair. Its failed diagnostic is retained below; its axiom print is not evidence of success. The final diagnostic and final code hash certify the corrected theorem. Unsupported `pp.maxDepth` was omitted as instructed.

## Complete typed proof

```lean
import Hypostructure.Graph.Strategy.SpineVocabulary
namespace Hypostructure.Graph.Strategy.Spine
universe u
set_option maxHeartbeats 800000
theorem checkedRoutingLabelIdentity (data : Data.{u})
    (object : Graph.FiniteObject.{u})
    (active : Graph.ActiveSurplusDemands
      (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) data.LengthOK object data.threshold)
    (cubic : data.threshold = 3)
    (capacity : Graph.CapacityPresentation object data.threshold data.windowOrder)
    (certified : Graph.CertifiedObjectCapacityLedger object data.threshold
      data.windowOrder data.surplusScale capacity)
    (token : certified.ledger.presented.Token)
    (role : Graph.SameTokenBlockerRoles.Role)
    (pattern : Finset (Finset (object.Vertex × object.Vertex)))
    (patternSubset : pattern ⊆ certified.ledger.presented.roleFibre token role)
    (pair : Finset (object.Vertex × object.Vertex)) (pairMem : pair ∈ pattern)
    (demand : object.Vertex × object.Vertex) (_demandMem : demand ∈ pair) : (by
  classical
  let activation := capacity.activation
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let selectedSupport (demand : object.Vertex × object.Vertex) :
      Finset object.Vertex :=
    if member : demand ∈ object.excessPorts data.threshold then
      (object.surplusPortOfMem member).support
    else ∅
  
  -- The local open/triangular coordinate of the paper's routing
  -- label, obtained from the actual shoulder graph.
  let portStatus (demand : object.Vertex × object.Vertex) :
      Graph.SameTokenRoutingGerms.PortStatus :=
    if _ : ∃ member : demand ∈ object.excessPorts data.threshold,
        ∃ left ∈ (object.surplusPortOfMem member).shoulders,
          ∃ right ∈ (object.surplusPortOfMem member).shoulders,
            left ≠ right ∧ object.graph.Adj left right then
      .triangular
    else
      .openPort
  
  have selectedSupport_card (demand : object.Vertex × object.Vertex)
      (member : demand ∈ object.excessPorts data.threshold) :
      (selectedSupport demand).card = data.threshold := by
    let port := object.surplusPortOfMem member
    have endpointNotShoulder : port.endpoint ∉ port.shoulders := by
      intro endpointShoulder
      exact object.graph.loopless.irrefl _
        ((port.mem_shoulders_iff port.endpoint).1 endpointShoulder).2
    obtain ⟨left, right, shoulderPair, shouldersDifferent⟩ :=
      active.shoulderPair demand member
    have shouldersEq : port.shoulders = {left, right} := by
      ext vertex
      rw [shoulderPair vertex]
      simp
    have shoulderCard :
        port.shoulders.card = data.threshold - 1 := by
      rw [shouldersEq, Finset.card_pair shouldersDifferent, cubic]
    simp only [selectedSupport, dif_pos member]
    unfold Graph.FiniteObject.SurplusPort.support
    rw [Finset.card_insert_of_notMem endpointNotShoulder, shoulderCard,
      cubic]
  
  -- The boundary-degree profile of `T(p)`: enumerate its vertices in
  -- the object's fixed order and record their actual degrees in the
  -- induced active support.  The `Fin` bound is proved from
  -- `|T(p)| = threshold`, itself derived from the ledger's active-port
  -- shoulder pair and cubic-baseline facts.
  let boundaryProfile (demand : object.Vertex × object.Vertex) :
      data.BoundaryProfile := fun index => by
    if member : demand ∈ object.excessPorts data.threshold then
      let support := selectedSupport demand
      let ordered := object.orderedVertices.filter fun vertex =>
        vertex ∈ support
      if bound : index.1 < ordered.length then
        let vertex := ordered.get ⟨index.1, bound⟩
        have vertexMem : vertex ∈ support := by
          have inside : vertex ∈ ordered :=
            ordered.get_mem ⟨index.1, bound⟩
          simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
          exact inside.2
        have degreeBound :
            (object.induce support).degree ⟨vertex, vertexMem⟩ <
              data.threshold := by
          have finiteBound :=
            (object.induce support).degree_lt_vertexCount
              ⟨vertex, vertexMem⟩
          rw [Graph.FiniteObject.vertexCount_induce,
            selectedSupport_card demand member] at finiteBound
          exact finiteBound
        exact ⟨(object.induce support).degree ⟨vertex, vertexMem⟩,
          degreeBound⟩
      else
        exact index
    else
      exact index
  let boundedSupport
      (pair : Finset (object.Vertex × object.Vertex)) :
      Finset object.Vertex :=
    capacity.sameTokenRoutingSupport token pair
  
  -- The `P₁₃` coordinate consists of exactly the window positions
  -- met by the bounded routing support, read from presentations of the
  -- members of the actual maximal packing.
  let windowLabel
      (pair : Finset (object.Vertex × object.Vertex)) :
      Graph.WindowCurvature.Label data.windowOrder := by
    classical
    exact Finset.univ.filter fun index =>
      ∃ window ∈ capacity.packing,
        ∃ presentation :
            Graph.TypeBDirectCycle.Presentation object data.windowOrder,
          presentation.support = window ∧
            presentation.coordinate index.1 ∈ boundedSupport pair
  
  let chordFlag
      (pair : Finset (object.Vertex × object.Vertex)) : Bool :=
    match Graph.FiniteObject.canonicalBlocker activation pair with
    | some (.arithmeticChordSet _) => true
    | _ => false
  let routingLabel
      (pair : Finset (object.Vertex × object.Vertex))
      (pairCard : pair.card = 2)
      (demand : object.Vertex × object.Vertex) :
      Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder) := by
    let first := pair.toList.get
      ⟨0, by simpa [pairCard] using (show 0 < pair.card by omega)⟩
    let second := pair.toList.get
      ⟨1, by simpa [pairCard] using (show 1 < pair.card by omega)⟩
    let endpoint : Fin 2 := if demand = first then 0 else 1
    exact (capacity.role pair,
      Graph.FiniteObject.CapacityToken.subtype token,
      endpoint,
      (portStatus first, portStatus second),
      (boundaryProfile first, boundaryProfile second),
      windowLabel pair, chordFlag pair)
  exact ∀ (pairCard : pair.card = 2),
      sameTokenActualRoutingLabel data object active cubic capacity certified
        token role pattern patternSubset pair pairMem demand _demandMem =
      routingLabel pair pairCard demand
  ) := by
  classical
  let activation := capacity.activation
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : DecidableEq object.Vertex := object.vertices.decEq
  let selectedSupport (demand : object.Vertex × object.Vertex) :
      Finset object.Vertex :=
    if member : demand ∈ object.excessPorts data.threshold then
      (object.surplusPortOfMem member).support
    else ∅
  
  -- The local open/triangular coordinate of the paper's routing
  -- label, obtained from the actual shoulder graph.
  let portStatus (demand : object.Vertex × object.Vertex) :
      Graph.SameTokenRoutingGerms.PortStatus :=
    if _ : ∃ member : demand ∈ object.excessPorts data.threshold,
        ∃ left ∈ (object.surplusPortOfMem member).shoulders,
          ∃ right ∈ (object.surplusPortOfMem member).shoulders,
            left ≠ right ∧ object.graph.Adj left right then
      .triangular
    else
      .openPort
  
  have selectedSupport_card (demand : object.Vertex × object.Vertex)
      (member : demand ∈ object.excessPorts data.threshold) :
      (selectedSupport demand).card = data.threshold := by
    let port := object.surplusPortOfMem member
    have endpointNotShoulder : port.endpoint ∉ port.shoulders := by
      intro endpointShoulder
      exact object.graph.loopless.irrefl _
        ((port.mem_shoulders_iff port.endpoint).1 endpointShoulder).2
    obtain ⟨left, right, shoulderPair, shouldersDifferent⟩ :=
      active.shoulderPair demand member
    have shouldersEq : port.shoulders = {left, right} := by
      ext vertex
      rw [shoulderPair vertex]
      simp
    have shoulderCard :
        port.shoulders.card = data.threshold - 1 := by
      rw [shouldersEq, Finset.card_pair shouldersDifferent, cubic]
    simp only [selectedSupport, dif_pos member]
    unfold Graph.FiniteObject.SurplusPort.support
    rw [Finset.card_insert_of_notMem endpointNotShoulder, shoulderCard,
      cubic]
  
  -- The boundary-degree profile of `T(p)`: enumerate its vertices in
  -- the object's fixed order and record their actual degrees in the
  -- induced active support.  The `Fin` bound is proved from
  -- `|T(p)| = threshold`, itself derived from the ledger's active-port
  -- shoulder pair and cubic-baseline facts.
  let boundaryProfile (demand : object.Vertex × object.Vertex) :
      data.BoundaryProfile := fun index => by
    if member : demand ∈ object.excessPorts data.threshold then
      let support := selectedSupport demand
      let ordered := object.orderedVertices.filter fun vertex =>
        vertex ∈ support
      if bound : index.1 < ordered.length then
        let vertex := ordered.get ⟨index.1, bound⟩
        have vertexMem : vertex ∈ support := by
          have inside : vertex ∈ ordered :=
            ordered.get_mem ⟨index.1, bound⟩
          simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
          exact inside.2
        have degreeBound :
            (object.induce support).degree ⟨vertex, vertexMem⟩ <
              data.threshold := by
          have finiteBound :=
            (object.induce support).degree_lt_vertexCount
              ⟨vertex, vertexMem⟩
          rw [Graph.FiniteObject.vertexCount_induce,
            selectedSupport_card demand member] at finiteBound
          exact finiteBound
        exact ⟨(object.induce support).degree ⟨vertex, vertexMem⟩,
          degreeBound⟩
      else
        exact index
    else
      exact index
  let boundedSupport
      (pair : Finset (object.Vertex × object.Vertex)) :
      Finset object.Vertex :=
    capacity.sameTokenRoutingSupport token pair
  
  -- The `P₁₃` coordinate consists of exactly the window positions
  -- met by the bounded routing support, read from presentations of the
  -- members of the actual maximal packing.
  let windowLabel
      (pair : Finset (object.Vertex × object.Vertex)) :
      Graph.WindowCurvature.Label data.windowOrder := by
    classical
    exact Finset.univ.filter fun index =>
      ∃ window ∈ capacity.packing,
        ∃ presentation :
            Graph.TypeBDirectCycle.Presentation object data.windowOrder,
          presentation.support = window ∧
            presentation.coordinate index.1 ∈ boundedSupport pair
  
  let chordFlag
      (pair : Finset (object.Vertex × object.Vertex)) : Bool :=
    match Graph.FiniteObject.canonicalBlocker activation pair with
    | some (.arithmeticChordSet _) => true
    | _ => false
  let routingLabel
      (pair : Finset (object.Vertex × object.Vertex))
      (pairCard : pair.card = 2)
      (demand : object.Vertex × object.Vertex) :
      Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile
        (Graph.WindowCurvature.Label data.windowOrder) := by
    let first := pair.toList.get
      ⟨0, by simpa [pairCard] using (show 0 < pair.card by omega)⟩
    let second := pair.toList.get
      ⟨1, by simpa [pairCard] using (show 1 < pair.card by omega)⟩
    let endpoint : Fin 2 := if demand = first then 0 else 1
    exact (capacity.role pair,
      Graph.FiniteObject.CapacityToken.subtype token,
      endpoint,
      (portStatus first, portStatus second),
      (boundaryProfile first, boundaryProfile second),
      windowLabel pair, chordFlag pair)
  have label_identity (pairCard : pair.card = 2) :
      sameTokenActualRoutingLabel data object active cubic capacity certified
        token role pattern patternSubset pair pairMem demand _demandMem =
      routingLabel pair pairCard demand := by
    have fibreMem := patternSubset pairMem
    have scheduleMem : pair ∈ object.portPairSchedule data.threshold :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp fibreMem).1).1
    have pairFacts : pair ⊆ object.excessPorts data.threshold ∧ pair.card = 2 :=
      Finset.mem_powersetCard.mp scheduleMem
    have pairCard : pair.card = 2 := pairFacts.2
    let first := pair.toList.get
      ⟨0, by simp [pairCard]⟩
    let second := pair.toList.get
      ⟨1, by simp [pairCard]⟩
    have firstMem : first ∈ object.excessPorts data.threshold := by
      apply pairFacts.1
      exact Finset.mem_toList.mp (pair.toList.get_mem _)
    have secondMem : second ∈ object.excessPorts data.threshold := by
      apply pairFacts.1
      exact Finset.mem_toList.mp (pair.toList.get_mem _)
    have supportCard (u : object.Vertex × object.Vertex)
        (hu : u ∈ object.excessPorts data.threshold) :
        (object.surplusPortOfMem hu).support.card = data.threshold := by
      let port := object.surplusPortOfMem hu
      have endpointNotShoulder : port.endpoint ∉ port.shoulders := by
        intro endpointShoulder
        exact object.graph.loopless.irrefl _
          ((port.mem_shoulders_iff port.endpoint).1 endpointShoulder).2
      obtain ⟨left, right, shoulderPair, shouldersDifferent⟩ := active.shoulderPair u hu
      have shouldersEq : port.shoulders = {left, right} := by
        ext vertex
        rw [shoulderPair vertex]
        simp
      have shoulderCard : port.shoulders.card = data.threshold - 1 := by
        rw [shouldersEq, Finset.card_pair shouldersDifferent, cubic]
      change port.support.card = data.threshold
      unfold Graph.FiniteObject.SurplusPort.support
      rw [Finset.card_insert_of_notMem endpointNotShoulder, shoulderCard, cubic]
    have degreeBound (u : object.Vertex × object.Vertex)
        (hu : u ∈ object.excessPorts data.threshold)
        (v : object.Vertex) (hv : v ∈ (object.surplusPortOfMem hu).support) :
        (object.induce (object.surplusPortOfMem hu).support).degree ⟨v, hv⟩ <
          data.threshold := by
      have finiteBound :=
        (object.induce (object.surplusPortOfMem hu).support).degree_lt_vertexCount ⟨v, hv⟩
      rw [Graph.FiniteObject.vertexCount_induce, supportCard u hu] at finiteBound
      exact finiteBound
    let actualProfile (u : object.Vertex × object.Vertex)
        (hu : u ∈ object.excessPorts data.threshold) :
        Fin data.threshold → Fin data.threshold := fun index => by
      let support := (object.surplusPortOfMem hu).support
      let ordered := object.orderedVertices.filter fun vertex => vertex ∈ support
      have orderedSet : ordered.toFinset = support := by
        ext vertex
        simp [ordered, Graph.FiniteObject.orderedVertices, FinEnum.mem_toList]
      have orderedNodup : ordered.Nodup :=
        List.Nodup.filter _ FinEnum.nodup_toList
      have orderedLength : ordered.length = data.threshold := by
        rw [← List.toFinset_card_of_nodup orderedNodup, orderedSet]
        exact supportCard u hu
      let vertex := ordered.get ⟨index.1, by rw [orderedLength]; exact index.2⟩
      have vertexMem : vertex ∈ support := by
        have inside : vertex ∈ ordered := ordered.get_mem _
        simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
        exact inside.2
      exact ⟨(object.induce support).degree ⟨vertex, vertexMem⟩,
        degreeBound u hu vertex vertexMem⟩
    have profiles (u : object.Vertex × object.Vertex)
        (hu : u ∈ object.excessPorts data.threshold) :
        actualProfile u hu = boundaryProfile u := by
      funext index
      have orderedSet :
          (object.orderedVertices.filter fun vertex =>
            vertex ∈ (object.surplusPortOfMem hu).support).toFinset =
          (object.surplusPortOfMem hu).support := by
        ext vertex
        simp [Graph.FiniteObject.orderedVertices, FinEnum.mem_toList]
      have orderedNodup :
          (object.orderedVertices.filter fun vertex =>
            vertex ∈ (object.surplusPortOfMem hu).support).Nodup :=
        List.Nodup.filter _ FinEnum.nodup_toList
      have orderedLength :
          (object.orderedVertices.filter fun vertex =>
            vertex ∈ (object.surplusPortOfMem hu).support).length = data.threshold := by
        rw [← List.toFinset_card_of_nodup orderedNodup, orderedSet]
        exact supportCard u hu
      have bound : index.val <
          (object.orderedVertices.filter fun vertex =>
            vertex ∈ (object.surplusPortOfMem hu).support).length := by
        rw [orderedLength]
        exact index.isLt
      let entry (support : Finset object.Vertex) : Nat := by
        let ordered := object.orderedVertices.filter fun vertex => vertex ∈ support
        if bound : index.1 < ordered.length then
          let vertex := ordered.get ⟨index.1, bound⟩
          have vertexMem : vertex ∈ support := by
            have inside : vertex ∈ ordered := ordered.get_mem _
            simp only [ordered, List.mem_filter, decide_eq_true_eq] at inside
            exact inside.2
          exact (object.induce support).degree ⟨vertex, vertexMem⟩
        else
          exact index.1
      apply Fin.ext
      dsimp only [boundaryProfile]
      rw [dif_pos hu]
      rw [apply_dite (fun x : Fin data.threshold => x.val)]
      change (actualProfile u hu index).val = entry (selectedSupport u)
      have supportEq : selectedSupport u = (object.surplusPortOfMem hu).support := by
        exact dif_pos hu
      rw [supportEq]
      dsimp only [entry]
      rw [dif_pos bound]
    change (capacity.role pair, Graph.FiniteObject.CapacityToken.subtype token,
      (if demand = first then 0 else 1 : Fin 2),
      (portStatus first, portStatus second),
      (actualProfile first firstMem, actualProfile second secondMem),
      windowLabel pair, chordFlag pair) =
      (capacity.role pair, Graph.FiniteObject.CapacityToken.subtype token,
      (if demand = first then 0 else 1 : Fin 2),
      (portStatus first, portStatus second),
      (boundaryProfile first, boundaryProfile second),
      windowLabel pair, chordFlag pair)
    rw [profiles first firstMem, profiles second secondMem]
  exact label_identity
end Hypostructure.Graph.Strategy.Spine

#print axioms Hypostructure.Graph.Strategy.Spine.checkedRoutingLabelIdentity
```

## Check diagnostics

Code SHA256: `532a1fc4114ea233e5f9e97ddc577ce4ab14740ebdecd81744b74d6c9801e879`.

LEAN_PATH:
```text
/runtime/current-vocabulary:/runtime/build-cache/lib/lean:/runtime/packages/LeanSearchClient/.lake/build/lib/lean:/runtime/packages/Qq/.lake/build/lib/lean:/runtime/packages/aesop/.lake/build/lib/lean:/runtime/packages/batteries/.lake/build/lib/lean:/runtime/packages/importGraph/.lake/build/lib/lean:/runtime/packages/mathlib/.lake/build/lib/lean:/runtime/packages/plausible/.lake/build/lib/lean:/runtime/packages/proofwidgets/.lake/build/lib/lean
```

Exit status: 1

stdout:
```text
/proc/self/fd/3:142:39: error: unexpected token ')'; expected ','
/proc/self/fd/3:129:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
/proc/self/fd/3:131:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
'Hypostructure.Graph.Strategy.Spine.checkedRoutingLabelIdentity' does not depend on any axioms
```

stderr:
```text
```

## Final check diagnostics

Code SHA256: `df27dedc6177ae91e4eaa98cc1fff2f3c0c218a45c2a129d2555fbbc6a46fccc`.

Exit status: 0

stdout:
```text
/proc/self/fd/3:129:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
/proc/self/fd/3:131:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
/proc/self/fd/3:253:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
/proc/self/fd/3:255:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
/proc/self/fd/3:129:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/proc/self/fd/3:131:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/proc/self/fd/3:253:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/proc/self/fd/3:255:59: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/proc/self/fd/3:129:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/proc/self/fd/3:131:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/proc/self/fd/3:253:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/proc/self/fd/3:255:59: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
'Hypostructure.Graph.Strategy.Spine.checkedRoutingLabelIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

stderr:
```text
```

## Source evidence

- `audits/erdos-64-red-team/node144-residual-first/phase0-evidence.md` — SHA256 `113226b2f99eabccb9f3b1f00e1c4ce6eeb474eadf90fdd10099c2003476badd`. Common object and endpoint; retained quantitative accounts; window incoming arm.
- `audits/erdos-64-red-team/node144-residual-first/window-kernel-pointwise-profile.md` — SHA256 `be6b00be0a68559c55ef5d717e46190ac33a0b190e987c405a6f446347170b16`. Insertion-ready local proof; complete checked context; kernel-check record.
- `audits/erdos-64-red-team/node144-residual-first/window-record-attempts/ebd3bd6b381746ee9967532895ac82c3/executor/artifact/audits/erdos-64-red-team/node144-residual-first/window-kernel-routing-label-identity.md` — SHA256 `406daee611c368068a0dab747d43f3c08e5c6ce8e78e83a625c6255a4302f111`. Saved full Lean candidate: literal owner context, label_identity and final tuple comparison.
- `audits/erdos-64-red-team/node144-residual-first/window-reduction-acceptance.json` — SHA256 `7f885ab01eaab9bd0b59af960fad2d9f0be59eb5eb610379d20a5281a6d62d8a`. Required same-source and fixed-support structure; acceptance.
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-source.txt` — SHA256 `8570d28a60a84a9bbb02026e37b39af5fe9b92c59b7e7fb92c2267324b9efe70`. Owner excerpt lines 889–990; equal-label source selection lines 1230–1246.
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-transport.md` — SHA256 `c8c1a24820955fb645b7a1c83191d5d9d6ec250dc1dcb944e8d7b19ed030cfb0`. Pair/order/support preservation and seven-coordinate comparison.
- `hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean` — SHA256 `4345cd3ee152618b8ad726d24cd47d23684f80391fb297d1eb2de08800ecc03e`. presented, lines 295–301; HomogeneousBottleneckPatternStatement.
- `hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean` — SHA256 `cca0d7a8a6d32968b3bd01a9ea3b0a6fb0fa119a7f1380d98610c29815087e31`. RoutingLabel, lines 85–87.
- `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` — SHA256 `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`. sameTokenActualRoutingLabel, lines 3944–4057; source-bound SameTokenTypeBHandoffStatement.
- `tools/methodology_gate/evidence_snapshots/36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635` — SHA256 `36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`. Historical vocabulary snapshot: Data.BoundaryProfile and sameTokenActualRoutingLabel.

## Side observations

The checker emits only suggestions to replace `simpa` with `simp` and reports redundant or unreachable `omega` in the unchanged owner definitions. These are recorded without editing that source. The equality supplies no multiplicity bound, escape construction, or additional structural payoff.
