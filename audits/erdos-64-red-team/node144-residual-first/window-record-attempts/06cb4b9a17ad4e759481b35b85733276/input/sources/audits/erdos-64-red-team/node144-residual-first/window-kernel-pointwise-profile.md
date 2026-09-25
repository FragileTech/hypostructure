# Pointwise profile equality

Status: **SUBMITTED_RESULT**. Implementation status: **kernel_checked**.

For the identical `object`, `active`, `cubic`, `u`, `hu : u ∈ object.excessPorts data.threshold`, and `index : Fin data.threshold`, the supplied `actualProfile u hu index = boundaryProfile u index` is proved. No missing mathematical inference or immediate subobligation remains for this equality. This artifact does not certify the whole routing-label identity, owner integration, any move, or branch closure.

The complete check below declares a theorem whose conclusion is precisely the universally quantified pointwise equality under the literal local definitions. It does not merely check an unused `have` inside a theorem of `True`. The context is repeated in its type and proof to expose the local definitions without adding an assumption or callback. The support-cardinality and ordered-length arguments are replayed from the supplied candidate as retained context; no replacement structural argument is introduced.

## Repair and preservation

`Fin.ext` reduces the equality to natural-number values. The outer membership conditional reduces by `dif_pos hu`. The explicitly specialized `apply_dite (fun x : Fin data.threshold => x.val)` moves only the value projection through the inner conditional. The local `entry` packages that exact natural-number expression, including its original out-of-range fallback `index.val`, as a function of its support. Consequently `rw [supportEq]` transports all dependent vertex types, membership proofs and decidable instances together. The retained `bound` then eliminates the inner conditional. Lean's final `rw` closes the resulting reflexive equality, with proof irrelevance accounting for the distinct bound and membership proofs.

`entry` is a local proof abbreviation, not a modified profile or an extra premise. Both original `boundaryProfile` fallbacks still return `index`; the original empty `selectedSupport` fallback is also retained. The literal ordered list remains `object.orderedVertices.filter ...`, and the entry remains the degree in `object.induce support`. No vertex reordering, support substitution on another object, domain extension, witness identification, or account change occurs.

On the pinned complete residual, instantiate `data = spineData`, `object = selected.object`, and the parameters with the same retained handoff witnesses. The equality uses only those projections and the already retained membership `hu`; all other conjuncts, both minimality conditions, exclusions, and quantitative accounts remain intact. In particular no equality to the separate class-audit or capacity-token witnesses is asserted. The pair-selection argument is not repeated and the pair itself is not changed.

## Insertion-ready local proof

In the supplied candidate context, replace the pointwise portion of `profiles` with the following. If retaining its function-equality statement, its existing `funext index` supplies the same pointwise goal; the body below begins at `have orderedSet`.

```lean
  have profiles (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) (index : Fin data.threshold) :
      actualProfile u hu index = boundaryProfile u index := by
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
```

## Complete checked context and proof term

Extract this entire Lean block as `Pointwise.lean`. It imports the accepted vocabulary and checks only the pointwise comparison. `selectedSupport` (owner lines 889–893), `selectedSupport_card` (907–927), and the original `boundaryProfile` (934–961) were programmatically compared with the source excerpt after stripping leading indentation and matched exactly. `actualProfile` was compared the same way with the supplied failed candidate and matched exactly. The unsupported `pp.maxDepth` option is omitted.

```lean
import Hypostructure.Graph.Strategy.SpineVocabulary
namespace Hypostructure.Graph.Strategy.Spine
universe u
set_option maxHeartbeats 800000
theorem checkedPointwiseProfile (data : Data.{u})
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
  exact ∀ (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) (index : Fin data.threshold),
      actualProfile u hu index = boundaryProfile u index
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
  change ∀ (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) (index : Fin data.threshold),
      actualProfile u hu index = boundaryProfile u index
  have profiles (u : object.Vertex × object.Vertex)
      (hu : u ∈ object.excessPorts data.threshold) (index : Fin data.threshold) :
      actualProfile u hu index = boundaryProfile u index := by
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
  exact profiles
end Hypostructure.Graph.Strategy.Spine
#print axioms Hypostructure.Graph.Strategy.Spine.checkedPointwiseProfile
```

## Kernel-check record

- Lean: `4.31.0`, commit `68218e876d2a38b1985b8590fff244a83c321783`, Release.
- Working directory: `/tmp/pointwise-profile`.
- Command: `/runtime/lean/bin/lean -o Pointwise.olean Pointwise.lean`.
- Python subprocess timeout: 90 seconds. Final exit status: **0**, normal return.
- `Pointwise.lean` SHA256: `002a65f175348a37c06cda20bfe8eabb7029511eeca0e40bc1c55dfedc22e3a9`.
- Produced `Pointwise.olean` SHA256: `cc4838a1dff8ce12f48aa4c32c03255afdee599ba9f1dbb89bbf114a0f2c4aa4`.
- No `sorry`, added axiom, assumption of the desired equality, or callback. The axiom report lists only the standard imported logical axioms.
- `/runtime/current-vocabulary/manifest.json` reports source unchanged, exit code 0, and source SHA256 `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`, matching the hash-verified current vocabulary. The accepted vocabulary was not rebuilt.

Exact `LEAN_PATH` (current vocabulary first):

```text
/runtime/current-vocabulary:/runtime/build-cache/lib/lean:/runtime/packages/LeanSearchClient/.lake/build/lib/lean:/runtime/packages/Qq/.lake/build/lib/lean:/runtime/packages/aesop/.lake/build/lib/lean:/runtime/packages/batteries/.lake/build/lib/lean:/runtime/packages/importGraph/.lake/build/lib/lean:/runtime/packages/mathlib/.lake/build/lib/lean:/runtime/packages/plausible/.lake/build/lib/lean:/runtime/packages/proofwidgets/.lake/build/lib/lean
```

Exact final stdout:

```text
Pointwise.lean:17:5: warning: Variable name `patternSubset` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Pointwise.lean:18:53: warning: Variable name `pairMem` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Pointwise.lean:21:6: warning: Variable name `activation` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Hypostructure.Graph.Strategy.Spine.checkedPointwiseProfile' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Final stderr is empty. The only final diagnostics are unused-context warnings; those parameters are retained to match the supplied handoff context. Earlier direct simplification/rewrite repairs encountered dependent typing errors; a broad `congr 3` repair reached its 120-second temporary-check limit. These were routine tactic failures, not mathematical negative evidence. No reducibility override is present in the successful proof.

## Source hashes

All eight supplied manifest entries were rehashed and matched:

- `audits/erdos-64-red-team/node144-residual-first/phase0-evidence.md`: `113226b2f99eabccb9f3b1f00e1c4ce6eeb474eadf90fdd10099c2003476badd`.
- `audits/erdos-64-red-team/node144-residual-first/window-record-attempts/ebd3bd6b381746ee9967532895ac82c3/executor/artifact/audits/erdos-64-red-team/node144-residual-first/window-kernel-routing-label-identity.md`: `406daee611c368068a0dab747d43f3c08e5c6ce8e78e83a625c6255a4302f111`.
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-source.txt`: `8570d28a60a84a9bbb02026e37b39af5fe9b92c59b7e7fb92c2267324b9efe70`.
- `audits/erdos-64-red-team/node144-residual-first/window-routing-label-transport.md`: `c8c1a24820955fb645b7a1c83191d5d9d6ec250dc1dcb944e8d7b19ed030cfb0`.
- `hypostructure/Hypostructure/Graph/ObjectCapacityLedger.lean`: `4345cd3ee152618b8ad726d24cd47d23684f80391fb297d1eb2de08800ecc03e`.
- `hypostructure/Hypostructure/Graph/SameTokenRoutingGerms.lean`: `cca0d7a8a6d32968b3bd01a9ea3b0a6fb0fa119a7f1380d98610c29815087e31`.
- `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean`: `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`.
- `tools/methodology_gate/evidence_snapshots/36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`: `36ab8555e398179dd5c73fd4218acbe7dd6dde052dc2b41bb7a97ee71f06e635`.

## Scope and side observations

No original object representation or domain changes and no account changes require transport. The new local abbreviation is on the same objects. The final checker warnings concern unused context only. The full routing-label identity and its downstream product rewrite remain outside this task and are not claimed as checked here. No adjacent task, escape construction, branch selection, or closure was undertaken.
