# Routing-label identity: first missing kernel inference

Status: **NEEDS_DECOMPOSITION**. Implementation status: **none**.

The unchanged saved candidate was checked first, against the repaired current runtime. Imports resolved; Lean elaborated the local definitions and reached the pointwise profile comparison. The check exited **1**. The first unsupported mathematical inference is the `rfl` at `Candidate.lean:233:6` in `profiles`; no completed owner-local label identity is certified. This is a formalization failure, not a counterexample or a negative branch selection. No move or branch is marked closed.

## Exact target and retained domain

```lean
have label_identity (pairCard : pair.card = 2) :
    sameTokenActualRoutingLabel data object active cubic capacity certified
      token role pattern patternSubset pair pairMem demand _demandMem =
    routingLabel pair pairCard demand := by
  -- Saved candidate body reproduced below; not validated.
```

Instantiate `data = spineData`, `object = selected.object`, and all active/capacity/certified/token/role/pattern variables with the identical witnesses of the retained handoff. The context includes `cubic : data.threshold = 3`, `patternSubset : pattern ⊆ certified.ledger.presented.roleFibre token role`, `pairMem : pair ∈ pattern`, and `_demandMem : demand ∈ pair`. The label type is `Graph.SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile (Graph.WindowCurvature.Label data.windowOrder)`. The temporary example abstracts these projections only; application remains on the full retained conjunction, with all other hypotheses and accounts untouched. No equality with the separate class-audit or capacity-token witnesses is used.

## First missing inference and immediate subobligation

Kernel validation of actualProfile u hu index = boundaryProfile u index on hu : u ∈ object.excessPorts data.threshold: after the saved simplifications, the original profile still contains its dependent selected-support conditional, and rfl fails.

For the same object, active, cubic, u, hu and index : Fin data.threshold, prove the residual pointwise equality shown in the diagnostic: actualProfile u hu index equals the original induced-degree Fin value over (if member : u ∈ object.excessPorts data.threshold then (object.surplusPortOfMem member).support else ∅), with its original ordered-list selection and dependent membership/bound proofs. Preserve the original profile definition and both fallback semantics.

The residual RHS is displayed exactly in the diagnostic below. Schedule membership, the same ordered pair, cubic shoulder cardinality, and ordered-list length are the accepted transport strategy used by the candidate. The failed `rfl` cannot certify the final seven-coordinate identity. Its downstream `change` and product rewrite have no separately certified status here. No child obligation was attempted after this failure.

## Narrow check record

All eight supplied source hashes matched `/input/assignment.json`. The runtime manifest `/runtime/current-vocabulary/manifest.json` records `exit_code: 0`, `source_unchanged: true`, and source SHA256 `46b2cfd88ca9bd71826111c46b392e9a60d86d14fee505fe64a4714546439052`, equal to the supplied current vocabulary. The accepted dependency was not rebuilt. The old local definition blocks match excerpt lines 889–961, 967–990 and 1230–1246, after removing indentation only; fallback definitions were not edited.

The complete saved Lean block was extracted unchanged into `/tmp/routing-identity/Candidate.lean`. An initial invocation from `/output` was rejected before elaboration because the absolute input lay outside Lean's root directory. Repeating from the temporary source directory resolved that setup error. The actual narrow check was:

```text
cwd: /tmp/routing-identity
/runtime/lean/bin/lean -o Candidate.olean Candidate.lean
Python subprocess timeout: 120 seconds
Lean exit status: 1 (normal return, not timeout)
LEAN_PATH: /runtime/current-vocabulary:/runtime/build-cache/lib/lean:/runtime/packages/LeanSearchClient/.lake/build/lib/lean:/runtime/packages/Qq/.lake/build/lib/lean:/runtime/packages/aesop/.lake/build/lib/lean:/runtime/packages/batteries/.lake/build/lib/lean:/runtime/packages/importGraph/.lake/build/lib/lean:/runtime/packages/mathlib/.lake/build/lib/lean:/runtime/packages/plausible/.lake/build/lib/lean:/runtime/packages/proofwidgets/.lake/build/lib/lean
```

The saved candidate also contains an unsupported diagnostic option, `set_option pp.maxDepth 12`, which Lean reports as unknown. It did not prevent elaboration from exposing the mathematical residual. Neither this option nor the proof was changed after the first check. No full owner/root check was performed and no production theorem was introduced.

## Saved attempted proof, unchanged and unvalidated

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

## Exact check diagnostic and unresolved goal

```text
Candidate.lean:5:0: error: Unknown option `pp.maxDepth`
Candidate.lean:130:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Candidate.lean:132:13: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Candidate.lean:233:6: error: Tactic `rfl` failed: The left-hand side
  actualProfile u hu index
is not definitionally equal to the right-hand side
  ⟨(object.induce
          (if member : u ∈ object.excessPorts data.threshold then (FiniteObject.surplusPortOfMem member).support
          else ∅)).degree
      ⟨(List.filter
              (fun vertex =>
                decide
                  (vertex ∈
                    if member : u ∈ object.excessPorts data.threshold then
                      (FiniteObject.surplusPortOfMem member).support
                    else ∅))
              object.orderedVertices).get
          ⟨↑index, ⋯⟩,
        ⋯⟩,
    ⋯⟩

data : Data
object : FiniteObject
active :
  ActiveSurplusDemands (MinimumDegreeAtLeast data.threshold) (HasCycleWithLength data.LengthOK) data.LengthOK object
    data.threshold
cubic : data.threshold = 3
capacity : CapacityPresentation object data.threshold data.windowOrder
certified : CertifiedObjectCapacityLedger object data.threshold data.windowOrder data.surplusScale capacity
token : certified.ledger.presented.Token
role : SameTokenBlockerRoles.Role
pattern : Finset (Finset (object.Vertex × object.Vertex))
patternSubset : pattern ⊆ certified.ledger.presented.roleFibre token role
pair : Finset (object.Vertex × object.Vertex)
pairMem : pair ∈ pattern
demand : object.Vertex × object.Vertex
_demandMem : demand ∈ pair
activation : object.DemandActivation object.PairCoordinate (object.Vertex × object.Vertex) := capacity.activation
this✝¹ : FinEnum object.Vertex := object.vertices
this✝ : DecidableRel object.graph.Adj := object.decideAdj
this : DecidableEq object.Vertex := FinEnum.decEq
selectedSupport : object.Vertex × object.Vertex → Finset object.Vertex :=
  fun demand =>
    if member : demand ∈ object.excessPorts data.threshold then (FiniteObject.surplusPortOfMem member).support else ∅
portStatus : object.Vertex × object.Vertex → SameTokenRoutingGerms.PortStatus :=
  fun demand =>
    if x :
        ∃ (member : demand ∈ object.excessPorts data.threshold),
          ∃ left ∈ (FiniteObject.surplusPortOfMem member).shoulders,
            ∃ right ∈ (FiniteObject.surplusPortOfMem member).shoulders, left ≠ right ∧ object.graph.Adj left right then
      SameTokenRoutingGerms.PortStatus.triangular
    else SameTokenRoutingGerms.PortStatus.openPort
selectedSupport_card : ∀ demand ∈ object.excessPorts data.threshold, (selectedSupport demand).card = data.threshold
boundaryProfile : object.Vertex × object.Vertex → data.BoundaryProfile :=
  fun demand index =>
    if member : demand ∈ object.excessPorts data.threshold then
      let support := selectedSupport demand;
      let ordered := List.filter (fun vertex => decide (vertex ∈ support)) object.orderedVertices;
      if bound : ↑index < ordered.length then
        let vertex := ordered.get ⟨↑index, bound⟩;
        have vertexMem := ⋯;
        have degreeBound := ⋯;
        ⟨(object.induce support).degree ⟨vertex, vertexMem⟩, degreeBound⟩
      else index
    else index
boundedSupport : Finset (object.Vertex × object.Vertex) → Finset object.Vertex :=
  fun pair => capacity.sameTokenRoutingSupport token pair
windowLabel : Finset (object.Vertex × object.Vertex) → WindowCurvature.Label data.windowOrder :=
  fun pair =>
    {index |
      ∃ window ∈ capacity.packing,
        ∃ presentation, presentation.support = window ∧ presentation.coordinate ↑index ∈ boundedSupport pair}
chordFlag : Finset (object.Vertex × object.Vertex) → Bool :=
  fun pair =>
    match FiniteObject.canonicalBlocker activation pair with
    | some (FiniteObject.Blocker.arithmeticChordSet chords) => true
    | x => false
routingLabel : (pair : Finset (object.Vertex × object.Vertex)) →
  pair.card = 2 →
    object.Vertex × object.Vertex →
      SameTokenRoutingGerms.RoutingLabel data.BoundaryProfile (WindowCurvature.Label data.windowOrder) :=
  fun pair pairCard demand =>
    let first := pair.toList.get ⟨0, ⋯⟩;
    let second := pair.toList.get ⟨1, ⋯⟩;
    let endpoint := if demand = first then 0 else 1;
    (capacity.role pair, FiniteObject.CapacityToken.subtype token, endpoint, (portStatus first, portStatus second),
      (boundaryProfile first, boundaryProfile second), windowLabel pair, chordFlag pair)
pairCard✝ : pair.card = 2
fibreMem : pair ∈ certified.ledger.presented.roleFibre token role
scheduleMem : pair ∈ object.portPairSchedule data.threshold
pairFacts : pair ⊆ object.excessPorts data.threshold ∧ pair.card = 2
pairCard : pair.card = 2
first : object.Vertex × object.Vertex := pair.toList.get ⟨0, ⋯⟩
second : object.Vertex × object.Vertex := pair.toList.get ⟨1, ⋯⟩
firstMem : first ∈ object.excessPorts data.threshold
secondMem : second ∈ object.excessPorts data.threshold
supportCard :
  ∀ (u : object.Vertex × object.Vertex) (hu : u ∈ object.excessPorts data.threshold),
    (FiniteObject.surplusPortOfMem hu).support.card = data.threshold
degreeBound :
  ∀ (u : object.Vertex × object.Vertex) (hu : u ∈ object.excessPorts data.threshold) (v : object.Vertex)
    (hv : v ∈ (FiniteObject.surplusPortOfMem hu).support),
    (object.induce (FiniteObject.surplusPortOfMem hu).support).degree ⟨v, hv⟩ < data.threshold
actualProfile : (u : object.Vertex × object.Vertex) →
  u ∈ object.excessPorts data.threshold → Fin data.threshold → Fin data.threshold :=
  fun u hu index =>
    let support := (FiniteObject.surplusPortOfMem hu).support;
    let ordered := List.filter (fun vertex => decide (vertex ∈ support)) object.orderedVertices;
    have orderedSet := ⋯;
    have orderedNodup := ⋯;
    have orderedLength := ⋯;
    let vertex := ordered.get ⟨↑index, ⋯⟩;
    have vertexMem := ⋯;
    ⟨(object.induce support).degree ⟨vertex, vertexMem⟩, ⋯⟩
u : object.Vertex × object.Vertex
hu : u ∈ object.excessPorts data.threshold
index : Fin data.threshold
orderedSet :
  (List.filter (fun vertex => decide (vertex ∈ (FiniteObject.surplusPortOfMem hu).support))
        object.orderedVertices).toFinset =
    (FiniteObject.surplusPortOfMem hu).support
orderedNodup :
  (List.filter (fun vertex => decide (vertex ∈ (FiniteObject.surplusPortOfMem hu).support))
      object.orderedVertices).Nodup
orderedLength :
  (List.filter (fun vertex => decide (vertex ∈ (FiniteObject.surplusPortOfMem hu).support))
        object.orderedVertices).length =
    data.threshold
bound :
  ↑index <
    (List.filter (fun vertex => decide (vertex ∈ (FiniteObject.surplusPortOfMem hu).support))
        object.orderedVertices).length
⊢ actualProfile u hu index =
    ⟨(object.induce
            (if member : u ∈ object.excessPorts data.threshold then (FiniteObject.surplusPortOfMem member).support
            else ∅)).degree
        ⟨(List.filter
                (fun vertex =>
                  decide
                    (vertex ∈
                      if member : u ∈ object.excessPorts data.threshold then
                        (FiniteObject.surplusPortOfMem member).support
                      else ∅))
                object.orderedVertices).get
            ⟨↑index, ⋯⟩,
          ⋯⟩,
      ⋯⟩
Candidate.lean:232:17: warning: This simp argument is unused:
  dif_pos hu

Hint: Omit it from the simp argument list.
  simp only [̵d̵i̵f̵_̵p̵o̵s̵ ̵h̵u̵,̵ ̵s̵e̵l̵e̵c̵t̵e̵d̵S̵u̵p̵p̵o̵r̵t̵,̵[̲s̲e̲l̲e̲c̲t̲e̲d̲S̲u̲p̲p̲o̲r̲t̲,̲ dif_pos hu, dif_pos bound]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
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

## Preservation and side observations

The original object, active witness, cubic equality, capacity, certified ledger, token, role, pattern, member pair, demand, fixed vertex order, actual degree profiles, and full retained accounts are unchanged. Minimality and exclusions remain retained. The auxiliary `actualProfile` is a proposed local definition on those same objects, not a representation change. No escape, pair choice, owner reconstruction, or adjacent inference was attempted. The repaired runtime successfully resolved imports; the historical missing-package diagnosis does not apply to this check. The unknown pretty-printer option is a separate nonmathematical diagnostic, recorded without pursuing it.
