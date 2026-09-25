# Routing-label identity: runtime import blocker

Status: **BLOCKED_WITH_REASON**. Implementation status: **none**.

The saved candidate was extracted unchanged from the supplied prior-attempt Markdown and submitted to a bounded narrow Lean check. Lean exited **1** at import resolution, before elaborating the candidate. No completed proof term or counterexample is certified. The accepted seven-coordinate mathematical transport remains unchanged.

## Exact unresolved identity and domain

```lean
sameTokenActualRoutingLabel data object active cubic capacity certified token role pattern patternSubset pair pairMem demand _demandMem = routingLabel pair pairCard demand
```

The complete typed `have label_identity` and its unvalidated proof are preserved below. Its result type is `Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile (Graph.WindowCurvature.Label data.windowOrder)`. Instantiate `data = spineData`, `object = selected.object`, and all active, capacity, certified, token, role and pattern arguments with the SAME retained handoff witnesses. `cubic : data.threshold = 3`; `patternSubset`, `pairMem` and `_demandMem` retain the original pattern, member pair and selected demand. The owner-local `pairCard` is any proof of that same pair's cardinality two. No witness equality with the class-audit or capacity-token-ledger witnesses is asserted. All other conjuncts, minimality, exclusions, strict-surplus and ledger accounts remain retained; no branch or move is marked closed.

First missing inference: Kernel validation of the exact same-witness owner-local routing-label identity remains unavailable: import resolution fails before candidate elaboration under the required LEAN_PATH.

Immediate subobligation: Provide an import-complete current-vocabulary runtime root compatible with the mandated first LEAN_PATH entry, retaining the pinned compiled SpineVocabulary, then kernel-check the saved candidate for sameTokenActualRoutingLabel data object active cubic capacity certified token role pattern patternSubset pair pairMem demand _demandMem = routingLabel pair pairCard demand.

## Narrow check diagnostics

All eight supplied source-manifest hashes were verified using Python SHA256. The `/runtime/current-vocabulary/manifest.json` source hash equals the supplied current vocabulary hash, `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`; its recorded build exit code is 0 and `source_unchanged` is true. The accepted dependency was not rebuilt or modified.

Working directory: `/tmp/routing-identity`. Command (Python subprocess, 120-second timeout):

```text
/runtime/lean/bin/lean -o /tmp/routing-identity/Candidate.olean /tmp/routing-identity/Candidate.lean
```

Exact `LEAN_PATH`:

```text
/runtime/current-vocabulary:/runtime/build-cache/lib/lean:/runtime/packages/LeanSearchClient/.lake/build/lib/lean:/runtime/packages/Qq/.lake/build/lib/lean:/runtime/packages/aesop/.lake/build/lib/lean:/runtime/packages/batteries/.lake/build/lib/lean:/runtime/packages/importGraph/.lake/build/lib/lean:/runtime/packages/mathlib/.lake/build/lib/lean:/runtime/packages/plausible/.lake/build/lib/lean:/runtime/packages/proofwidgets/.lake/build/lib/lean
```

Status: 1 elapsed=0.21474034199491143

```text
/tmp/routing-identity/Candidate.lean:1:0: error: object file '/runtime/current-vocabulary/Hypostructure/Graph/WindowAttachmentShadow.olean' of module Hypostructure.Graph.WindowAttachmentShadow does not exist

```

The missing dependency actually exists at `/runtime/build-cache/lib/lean/Hypostructure/Graph/WindowAttachmentShadow.olean`. Lean 4.31's `Lean/Util/Path.lean`, `SearchPath.findWithExt` (lines 61–65), selects the first directory containing the root package `Hypostructure`, without per-module fallback. Thus the required first path shadows the remaining Hypostructure dependencies. Reordering to use the stale vocabulary is not an admissible validation. No runtime directory was modified, consistent with the assigned write scope. An earlier invocation from `/output` exited 1 because the temporary source was outside Lean's root directory; correcting the working directory exposed the import blocker recorded above. Neither invocation reached proof elaboration. No timeout occurred and no candidate object file was produced.

The source excerpt's original lines 889–961, 967–990 and 1230–1246 match the candidate's old definitions after common indentation and whitespace-only blank-line normalization. In particular the two fallback cases remain literal, not replaced by an arbitrary profile callback. The attempted proof was not revised or rederived. No full owner or root check was run.

## Preserved saved candidate — UNVALIDATED

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
- `audits/erdos-64-red-team/node144-residual-first/window-record-attempts/afb5524193eb41bba0a9636c3328e313/executor/artifact/audits/erdos-64-red-team/node144-residual-first/window-kernel-routing-label-identity.md`: `76e6c764f4ace5dec204fe6ddd15fbe74535c8bb253dc0627cf9eb02b90e61aa`
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-source.txt`: `8570d28a60a84a9bbb02026e37b39af5fe9b92c59b7e7fb92c2267324b9efe70`
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-transport.md`: `c8c1a24820955fb645b7a1c83191d5d9d6ec250dc1dcb944e8d7b19ed030cfb0`
- `hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean`: `4345cd3ee152618b8ad726d24cd47d23684f80391fb297d1eb2de08800ecc03e`
- `hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean`: `cca0d7a8a6d32968b3bd01a9ea3b0a6fb0fa119a7f1380d98610c29815087e31`
- `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean`: `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`
- `tools/methodology_gate/evidence_snapshots/36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`: `36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`

No objects, domains, orderings, supports, profile values or accounts changed. Runtime package shadowing is the only side observation; no adjacent mathematical task was pursued.
