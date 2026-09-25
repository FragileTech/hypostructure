# Owner-local routing-label identity: kernel-check blocked

Status: **BLOCKED_WITH_REASON**. Implementation status: **none**.

The current vocabulary compilation exceeded the explicit 180-second subprocess limit. No current-vocabulary object file was produced, so the narrow identity check was not run. The accepted mathematical transport is unchanged; this result does not certify its Lean formalization and does not supply a counterexample. No move or branch is marked closed.

The first unvalidated inference is precisely:

```lean
sameTokenActualRoutingLabel data object active cubic capacity certified token role pattern patternSubset pair pairMem demand _demandMem = routingLabel pair pairCard demand
```

Here `object = selected.object`, `data = spineData`; `active`, `capacity`, `certified`, `token`, `role`, and `pattern` are the identical retained handoff witnesses, `cubic : data.threshold = 3`, `patternSubset : pattern ⊆ certified.ledger.presented.roleFibre token role`, `pairMem : pair ∈ pattern`, `_demandMem : demand ∈ pair`, and `pairCard : pair.card = 2`. The type is `Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile (Graph.WindowCurvature.Label data.windowOrder)`. No witness is identified with the separate class-audit or capacity-token witnesses. All unused conjuncts, minimality, exclusions, and accounts remain retained.

Immediate subobligation: kernel-validate this single owner-local identity against a successfully compiled copy of the pinned current vocabulary, using the literal old definitions below. There is no new mathematical decomposition or unsupported negative conclusion from the timeout.

## Check record

Lean version: `4.31.0`, commit `68218e876d2a38b1985b8590fff244a83c321783`.

The overlay was `/tmp/label-check`. Dependency object files were symlinked from `/runtime/build-cache/lib/lean`; the current `SpineVocabulary.lean` was copied byte-for-byte from the declared source and its cached vocabulary object and sidecars removed from the overlay. The current source compilation was attempted once after repairing an import-path setup error. The initial setup invocation exited 1 at import resolution (`WindowAttachmentShadow.olean` absent in the overlay), before vocabulary elaboration; it is not a completed source check.

The actual source build command was:

```text
/runtime/lean/bin/lean -o /tmp/label-check/Hypostructure/Graph/Strategy/SpineVocabulary.olean /tmp/label-check/Hypostructure/Graph/Strategy/SpineVocabulary.lean
```

`LEAN_PATH` placed the overlay first, followed by the two runtime build caches and each package's `.lake/build/lib/lean`. Python `subprocess.run(..., timeout=180)` raised `TimeoutExpired` and terminated the child. The Python wrapper exited **1**; no normal Lean exit status was returned. The source build log was empty. The earlier import failure's status file was not treated as the final source-build status. No current `.olean` was emitted. Narrow identity-check exit status: **not run**. No full owner or root compilation was attempted.

All seven supplied source hashes were verified and matched. Current vocabulary overrides the historical snapshot; no stale compiled vocabulary was used to assert the identity.

## Unvalidated candidate, not a completed proof

The following is the exact temporary check source. The owner-local definitions and `selectedSupport_card` were mechanically extracted from owner excerpt lines 889–961, 967–990, and 1230–1246, with only common indentation removed. The instances and activation alias match 640–643. The `label_identity` block is the proposed insertion, **not kernel-validated evidence**. No `sorry`, added axiom, or admitted placeholder occurs in it. Its construction isolates the genuine ordered-degree profile from the total fallback profile; the final `change` is intended to expose only the seven-coordinate product, avoiding global unfolding of owner-local lets. There is no claim that either this `change` or the preceding tactics has elaborated successfully.

```lean
import Hypostructure.Graph.Strategy.SpineVocabulary
namespace Hypostructure.Graph.Strategy.Spine
universe u
set_option maxHeartbeats 800000
set_option pp.maxDepth 12
example (data : Data.{u})
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
    (demand : object.Vertex × object.Vertex) (_demandMem : demand ∈ pair) : True := by
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
      dsimp only [boundaryProfile]
      simp only [dif_pos hu, selectedSupport, dif_pos hu, dif_pos bound]
      rfl
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
  exact True.intro
end Hypostructure.Graph.Strategy.Spine
```

## Source hashes

- `audits/erdos-64-red-team/node144-residual-first/phase0-evidence.md`: `113226b2f99eabccb9f3b1f00e1c4ce6eeb474eadf90fdd10099c2003476badd`
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-source.txt`: `8570d28a60a84a9bbb02026e37b39af5fe9b92c59b7e7fb92c2267324b9efe70`
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-transport.md`: `c8c1a24820955fb645b7a1c83191d5d9d6ec250dc1dcb944e8d7b19ed030cfb0`
- `hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean`: `4345cd3ee152618b8ad726d24cd47d23684f80391fb297d1eb2de08800ecc03e`
- `hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean`: `cca0d7a8a6d32968b3bd01a9ea3b0a6fb0fa119a7f1380d98610c29815087e31`
- `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean`: `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`
- `tools/methodology_gate/evidence_snapshots/36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`: `36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`

No completed Lean proof term is claimed. The accepted transport proof remains the mathematical evidence; the unresolved task is its kernel validation. No source objects, domains, orderings, supports, profile values, or accounts were changed. No production file or imported theorem was introduced. The named actual-profile auxiliary is only a proposed local definition on unchanged objects.
