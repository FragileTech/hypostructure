import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePairResponse
import Hypostructure.Graph.BarrierOverlapSystem

/-!
# The sparse pair dependence dichotomy and the entropy sandwich

`lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence`,
`prop:sparse-pair-independence-dichotomy`, `cor:sparse-pair-entropy-saturation`,
`prop:sparse-entropy-sandwich` and `prop:sparse-entropy-sandwich-with-blockers`.

The six statements are two theorems and their readings.

**The dichotomy.**  All three dependence statements run the same case analysis
over an inclusion-minimal determination certificate, and that analysis is
`AttemptedQuotient.route`.  At an object that survives the sparse surplus exits
and admits no proper-support replacement, the two exit alternatives are
discharged — a smaller closed representative is the delocalization exit, and a
replacement is `lem:replacement` — so what remains is exactly the manuscript's
blocker alternative: two realizations the attempted determination identifies
which are separated, either by their boundary degree profiles, which is the
blocker of type (d), or by a boundaried context, which is the blocker of type
(e).  That is `blockerSeparation_of_reducing`, and it is
`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence` at
once: neither proof inspects which coordinates the family holds, which is why
the manuscript gives them the same four cases.

`prop:sparse-pair-independence-dichotomy` is registered at its concrete branch
decision.  A baseline-family instance at node `[129]` must be proved from that
node's literal incoming ledger; this module exposes no detached universal
survival theorem or quotient-system carrier, and it does not manufacture the
baseline demand that the manuscript currently assumes.

**The sandwich.**  `prop:sparse-entropy-sandwich-with-blockers` writes

  `|Π_free| ≤ E_spine(n) + (½σ(G) + 1) log₂ n`,

and its proof is three inequalities: the entropy count on the mixed family
`ℐ_spine ∪ {r_π : π ∈ Π_free}`, the baseline demand `|ℐ_spine| ≥ B₀(n) −
E_spine(n)`, and `lem:incremental-skeleton-room`.  `entropySandwich` below is
that composition with the logarithms cleared, in the same discipline
`def:baseline-spine-demand` is already stated in:

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`,  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`,

whose logarithm is the manuscript's display, because `m − m₀ ≤ ½σ(G) + 1` is
`lem:sparse-slack-surplus` at the branch.  `prop:sparse-entropy-sandwich` is the
same statement at the *full* pair schedule, and
`cor:sparse-pair-entropy-saturation` is its `ℐ_spine = ∅` reading,
`2^{C(|𝒜₀|,2)} ≤ C(N,m)`.

The theorem below is the reusable cancellation step, so its two inputs are the
two inequalities it cancels.  At node `[131]` the concrete mixed family, its
full-rank proof, its entropy count, and this cancellation must be derived inside
the atomic executor from facts on the incoming exact ledger and published as
the node's semantic output.  None of them is transported in a detached package.

The asymptotic tail of `prop:sparse-entropy-sandwich` — *"consequently, if
`E_spine(n) = O(n)` and `|𝒜₀| ≥ c₁σ(G)`, then `σ(G) = O(√n)`"* — is not stated
here.  It is a consequence of the displayed inequality at a branch that supplies
the two rate hypotheses, and it belongs to the node that supplies them.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

/-! ## The dependence dichotomy -/

/-- The canonical two ends of the shoulder chord named by a selected surplus
port.  A chord in the sparse ledger is named by its port `(h,x)`; this map reads
the actual shoulder pair selected by that port.  The fallback is used only off
the selected active family and is never charged by the blocker ledger. -/
noncomputable def pairResponseChordEnds
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex) :
    object.Vertex × object.Vertex := by
  classical
  if member : demand ∈ object.excessPorts threshold then
    let shoulders := active.shoulderPair demand member
    exact (shoulders.choose, shoulders.choose_spec.choose)
  else
    exact demand

/-- Clause (f), at one literal pair.  A chord is named by its selected surplus
port.  The full compatible suppression family is indexed by `pair`, while
`chords` is exactly the (possibly proper) subset of its added shoulder chords
used by the accepted cycle.  The endpoint clause identifies those names with
the actual shoulders of the compatible configurations; hence this predicate
contains precisely concrete suppressed-family chord sets, not a flag saying
that some obstruction exists. -/
noncomputable def SparsePairSuppressionChordObstruction
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pair chords : Finset (object.Vertex × object.Vertex)) : Prop := by
  classical
  exact pair ⊆ object.excessPorts threshold ∧
    ∃ (family : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate family.suppressed LengthOK),
      (Finset.univ.image (fun index : family.Index =>
          ((family.configuration index).center,
            (family.configuration index).vertex)) = pair) ∧
        (∀ index : family.Index,
          pairResponseChordEnds active
              ((family.configuration index).center,
                (family.configuration index).vertex) =
                ((family.configuration index).left,
                  (family.configuration index).right) ∨
            pairResponseChordEnds active
              ((family.configuration index).center,
                (family.configuration index).vertex) =
                ((family.configuration index).right,
                  (family.configuration index).left)) ∧
        (family.usedChords certificate.walk).image (fun index =>
          ((family.configuration index).center,
            (family.configuration index).vertex)) = chords

theorem chords_subset_pair_of_suppressionObstruction
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    {active : ActiveSurplusDemands Baseline Target LengthOK object threshold}
    {pair chords : Finset (object.Vertex × object.Vertex)}
    (obstruction : SparsePairSuppressionChordObstruction active pair chords) :
    chords ⊆ pair := by
  classical
  obtain ⟨_pairActive, family, certificate, pairImage, _ends, chordImage⟩ :=
    obstruction
  intro demand demandMem
  rw [← chordImage] at demandMem
  obtain ⟨index, _used, rfl⟩ := Finset.mem_image.mp demandMem
  rw [← pairImage]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ index)

/-- The active-family certificate determines the concrete response activation
used by `def:sparse-pair-response`.  Clauses (d) and (e) are populated by the
failed quotient at `[132]`; clause (f) is already the exact finite family of
actual compatible-suppression chord sets belonging to each pair. -/
noncomputable def pairResponseActivation
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    object.DemandActivation (object.PairCoordinate)
      (object.Vertex × object.Vertex) := by
  classical
  let bufferOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      (object.surplusPortOfMem member).support
    else ∅
  let responseOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      let port := object.surplusPortOfMem member
      let shoulders := active.shoulderPair demand member
      let left := shoulders.choose
      let right := shoulders.choose_spec.choose
      let description := shoulders.choose_spec.choose_spec.1
      let distinct := shoulders.choose_spec.choose_spec.2
      let activated := active.activated demand member left right description distinct
      port.responseSupport activated.1 activated.2.1
    else ∅
  let supportOf := fun demand : object.Vertex × object.Vertex =>
    FiniteObject.vertexSupportUnion object (bufferOf demand) (responseOf demand)
  let returnOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      let port := object.surplusPortOfMem member
      let shoulders := active.shoulderPair demand member
      let left := shoulders.choose
      let right := shoulders.choose_spec.choose
      let description := shoulders.choose_spec.choose_spec.1
      let distinct := shoulders.choose_spec.choose_spec.2
      let activated := active.activated demand member left right description distinct
      port.returnSupport activated.1
    else ∅
  let rawPorts : List (object.Vertex × object.Vertex) :=
    object.orderedVertices.flatMap fun centre =>
      (object.selectedPortEndpoints threshold centre).map fun endpoint =>
        (centre, endpoint)
  let vertexRank (vertex : object.Vertex) :=
    object.orderedVertices.idxOf vertex
  let radix := object.orderedVertices.length + 1
  let chordKey (demand : object.Vertex × object.Vertex) :=
    let ends := pairResponseChordEnds active demand
    let first := min (vertexRank ends.1) (vertexRank ends.2)
    let second := max (vertexRank ends.1) (vertexRank ends.2)
    (((first * radix + second) * radix + vertexRank demand.1) * radix +
      vertexRank demand.2)
  let orderedPorts := rawPorts.insertionSort fun left right =>
    chordKey left ≤ chordKey right
  let rec lexicographicSublists :
      List (object.Vertex × object.Vertex) →
        List (List (object.Vertex × object.Vertex))
    | [] => [[]]
    | head :: tail =>
        let rest := lexicographicSublists tail
        [] :: (rest.map (head :: ·) ++ rest.tail)
  let orderedChordSets :=
    ((lexicographicSublists orderedPorts).map List.toFinset).filter fun chords =>
      chords ∈ (object.excessPorts threshold).powerset
  exact {
    localBuffer := bufferOf
    responseSupport := responseOf
    declaredSupport := supportOf
    declaredSupport_eq := fun _ => rfl
    returnSupport := returnOf
    profileObstructions := fun _ => []
    responseObstructions := fun _ => []
    chordObstructions := fun pair =>
      orderedChordSets.filter fun chords =>
        SparsePairSuppressionChordObstruction active pair chords
    chordEnds := pairResponseChordEnds active
    chordPort := id }

@[simp] theorem pairResponseActivation_chordEnds
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    (pairResponseActivation active).chordEnds = pairResponseChordEnds active := by
  rfl

@[simp] theorem pairResponseActivation_chordPort
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    (pairResponseActivation active).chordPort = id := by
  rfl

theorem suppressionObstruction_of_mem_pairResponseChordObstructions
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {pair chords : Finset (object.Vertex × object.Vertex)}
    (member : chords ∈ (pairResponseActivation active).chordObstructions pair) :
    SparsePairSuppressionChordObstruction active pair chords := by
  classical
  simp only [pairResponseActivation] at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- The concrete activation reads the selected port's actual `T(p)` on every
member of the active family. -/
@[simp] theorem pairResponseActivation_localBuffer_of_mem
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    (pairResponseActivation active).localBuffer demand =
      (object.surplusPortOfMem member).support := by
  classical
  simp [pairResponseActivation, member]

/-- The two ends named by an active demand's shoulder chord both lie in its
selected support `T(p)`. -/
theorem pairResponseChordEnds_mem_localBuffer
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    let ends := pairResponseChordEnds active demand
    ends.1 ∈ (pairResponseActivation active).localBuffer demand ∧
      ends.2 ∈ (pairResponseActivation active).localBuffer demand := by
  classical
  let shoulders := active.shoulderPair demand member
  have leftShoulder : shoulders.choose ∈
      (object.surplusPortOfMem member).shoulders :=
    (shoulders.choose_spec.choose_spec.1 shoulders.choose).2 (Or.inl rfl)
  have rightShoulder : shoulders.choose_spec.choose ∈
      (object.surplusPortOfMem member).shoulders :=
    (shoulders.choose_spec.choose_spec.1 shoulders.choose_spec.choose).2
      (Or.inr rfl)
  simp only [pairResponseChordEnds, dif_pos member,
    pairResponseActivation_localBuffer_of_mem active member]
  exact ⟨FiniteObject.SurplusPort.mem_support_of_mem_shoulders _ leftShoulder,
    FiniteObject.SurplusPort.mem_support_of_mem_shoulders _ rightShoulder⟩

/-- The canonical return registered by the active-family fact starts at the
selected port endpoint. -/
theorem pairResponseActivation_endpoint_mem_returnSupport_of_mem
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    demand.2 ∈ (pairResponseActivation active).returnSupport demand := by
  classical
  simp only [pairResponseActivation, dif_pos member]
  exact FiniteObject.SurplusPort.endpoint_mem_returnSupport _ _

/-- The same registered canonical return terminates at the selected port's
centre. -/
theorem pairResponseActivation_centre_mem_returnSupport_of_mem
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    demand.1 ∈ (pairResponseActivation active).returnSupport demand := by
  classical
  simp only [pairResponseActivation, dif_pos member]
  exact FiniteObject.SurplusPort.centre_mem_returnSupport _ _

/-- The literal canonical return path used by `pairResponseActivation` at an
active demand.  This is not a second choice of return data: the shoulders,
activation witness, and length-major path selector are definitionally the same
ones used to compute the activation's `returnSupport`. -/
noncomputable def ActiveSurplusDemands.canonicalPairReturnPath
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    (object.surplusPortOfMem member).deletedPortGraph.Walk demand.2 demand.1 := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  let shoulders := active.shoulderPair demand member
  let activated := active.activated demand member shoulders.choose
    shoulders.choose_spec.choose shoulders.choose_spec.choose_spec.1
    shoulders.choose_spec.choose_spec.2
  exact ((object.surplusPortOfMem member).canonicalReturn activated.1).path.1

/-- The active demand's canonical return is a simple path. -/
theorem ActiveSurplusDemands.canonicalPairReturnPath_isPath
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    (active.canonicalPairReturnPath demand member).IsPath := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  unfold canonicalPairReturnPath
  exact ((object.surplusPortOfMem member).canonicalReturn _).path.2

/-- The same canonical return, included back into the ambient graph.  The map
is the identity-on-vertices inclusion of `G - c(p)x(p)` into `G`, so this
declaration does not select or transport a second return. -/
noncomputable def ActiveSurplusDemands.canonicalPairReturnAmbientPath
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    object.graph.Walk demand.2 demand.1 :=
  (active.canonicalPairReturnPath demand member).map
    (.ofLE (by
      unfold FiniteObject.SurplusPort.deletedPortGraph
      exact object.graph.deleteEdges_le {s(demand.1, demand.2)}))

/-- Ambient inclusion preserves simplicity of the registered return. -/
theorem ActiveSurplusDemands.canonicalPairReturnAmbientPath_isPath
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    (active.canonicalPairReturnAmbientPath demand member).IsPath := by
  classical
  apply SimpleGraph.Walk.map_isPath_of_injective
    (f := SimpleGraph.Hom.ofLE (by
      unfold FiniteObject.SurplusPort.deletedPortGraph
      exact object.graph.deleteEdges_le {s(demand.1, demand.2)}))
  · intro left right equal
    exact equal
  · exact active.canonicalPairReturnPath_isPath demand member

/-- Viewing the registered return in the ambient graph does not change its
length. -/
@[simp] theorem ActiveSurplusDemands.canonicalPairReturnAmbientPath_length
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    (active.canonicalPairReturnAmbientPath demand member).length =
      (active.canonicalPairReturnPath demand member).length := by
  unfold canonicalPairReturnAmbientPath
  exact SimpleGraph.Walk.length_map (f := SimpleGraph.Hom.ofLE (by
    unfold FiniteObject.SurplusPort.deletedPortGraph
    exact object.graph.deleteEdges_le {s(demand.1, demand.2)}))
    (p := active.canonicalPairReturnPath demand member)

/-- The registered return-length bound used by node `[179]`, derived from the
finite active object rather than hard-coded: every canonical port return has
strictly fewer than `vertexCount` edges. -/
theorem ActiveSurplusDemands.canonicalPairReturnPath_length_lt
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex)
    (member : demand ∈ object.excessPorts threshold) :
    (active.canonicalPairReturnPath demand member).length < object.vertexCount := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  rw [FiniteObject.vertexCount, FinEnum.card_eq_fintypeCard]
  exact (active.canonicalPairReturnPath_isPath demand member).length_lt

/-- Each canonical return entry `R_p` in the active-family activation is a
connected declared support. -/
theorem pairResponseActivation_connectedOn_returnSupport_of_mem
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    SupportComponents.Connected.ConnectedOn object
      ((pairResponseActivation active).returnSupport demand) := by
  classical
  simp only [pairResponseActivation, dif_pos member]
  exact FiniteObject.SurplusPort.connectedOn_returnSupport _ _

/-- `T(p)` is literally contained in the declared support `T(p) ∪ Γ(p)` of
the same activated demand. -/
theorem pairResponseActivation_localBuffer_subset_declaredSupport_of_mem
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {demand : object.Vertex × object.Vertex}
    (member : demand ∈ object.excessPorts threshold) :
    (pairResponseActivation active).localBuffer demand ⊆
      (pairResponseActivation active).declaredSupport demand := by
  exact (pairResponseActivation active).localBuffer_subset_declaredSupport demand

/-- The active-family fact constructs the concrete response activation. -/
theorem existsPairResponseActivation
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    Nonempty (object.DemandActivation (object.PairCoordinate)
      (object.Vertex × object.Vertex)) :=
  ⟨pairResponseActivation active⟩

/-! ## Exact conditional skeleton responses

The rank quotient detects a dependence, but the overlap argument at node
`[178]` uses the stronger graph statement in the manuscript: after fixing the
baseline word and the edges outside the port returns, separated pair supports
realize their response product in the actual fixed-edge skeleton class.  The
following model records exactly that class and no abstract state carrier. -/

/-- One graph-derived value of a sparse pair-response coordinate. -/
structure SparsePairSkeletonResponse (LengthOK : Nat → Prop) where
  boundary : Boundary.{u}
  response : OutsideContext boundary → Prop

/-- The exact skeleton response model for a nonempty subfamily of a declared
pair schedule.  Every support is the canonical `X_π`; every state is read from
an actual member of the current fixed-`(n,m)` skeleton class. -/
structure SparsePairSkeletonModel
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (schedule : Finset (Finset (object.Vertex × object.Vertex))) where
  BaseCoordinate : Type u
  baselineFamily : Finset BaseCoordinate
  baseline : BaselineCodeRealization object baselineFamily
  pairSet : Finset (Finset (object.Vertex × object.Vertex))
  pairSet_nonempty : pairSet.Nonempty
  pairSet_subset_schedule : pairSet ⊆ schedule
  responseSupport : {pair // pair ∈ pairSet} → Finset object.Vertex
  responseSupport_selected : ∀ pair,
    activation.pairSupport pair.1 = some (responseSupport pair)
  responseSupport_connected : ∀ pair,
    SupportComponents.Connected.ConnectedOn object (responseSupport pair)

namespace SparsePairSkeletonModel

abbrev Skeleton
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (_model : SparsePairSkeletonModel activation schedule) :=
  PackedWindowRealization.Skeleton object.vertexCount object.edgeCount

/-- The literal union of the selected port-return seeds fixed by
`def:pair-overlap-system`. -/
noncomputable def portReturns
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule) :
    Finset object.Vertex := by
  classical
  exact model.pairSet.biUnion activation.pairSeed

/-- The exact all-context target response of `X_π` in a labelled skeleton. -/
noncomputable def response
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (member : model.Skeleton) (pair : {pair // pair ∈ model.pairSet}) :
    SparsePairSkeletonResponse LengthOK :=
  let candidate : FiniteObject.{u} :=
    { Vertex := object.Vertex
      graph := member.1.graph.comap object.vertices.equiv
      vertices := object.vertices
      decideAdj := Classical.decRel _ }
  let support := model.responseSupport pair
  { boundary := Strategy.InterfaceReplacement.SupportAtom.boundary
      candidate support
    response := fun outside =>
      HasCycleWithLength LengthOK
        (glue
          (Strategy.InterfaceReplacement.SupportAtom.piece candidate support)
          outside) }

/-- The paper's conditioning datum: outside edges and the already realized
baseline word.  Earlier pair responses are conditioned by `conditionalValues`,
not hidden in this code. -/
noncomputable def outsideCode
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (member : model.Skeleton) :
    Finset (Sym2 (Fin object.vertexCount)) ×
      ({coordinate // coordinate ∈ model.baselineFamily} → Bool) :=
  (BarrierSystem.outsideEdges member.1
      (model.portReturns.map object.vertices.equiv.toEmbedding),
    model.baseline.response member.1)

def conditionalFibre
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (reference : model.Skeleton) : Set model.Skeleton :=
  {candidate | model.outsideCode candidate = model.outsideCode reference}

/-- Exact response values realized after the earlier coordinates in `order`
have been exposed. -/
def conditionalValues
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (reference : model.Skeleton) (index : Fin family.card) :
    Set (SparsePairSkeletonResponse LengthOK) :=
  {state | ∃ candidate,
    candidate ∈ model.conditionalFibre reference ∧
      (∀ earlier : Fin family.card, earlier.1 < index.1 →
        model.response (LengthOK := LengthOK) candidate (order earlier).1 =
          model.response (LengthOK := LengthOK) reference (order earlier).1) ∧
      model.response (LengthOK := LengthOK) candidate (order index).1 = state}

/-- An exposure order realizes one binary response coordinate at every step in
every nonempty conditional fibre. -/
def RealizingOrder
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet}) : Prop :=
  ∃ order : Fin family.card ≃ {pair // pair ∈ family},
    ∀ reference : model.Skeleton, ∀ index : Fin family.card,
      2 ≤ Nat.card (model.conditionalValues (LengthOK := LengthOK)
        family order reference index)

def Overlaps
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (left right : {pair // pair ∈ model.pairSet}) : Prop :=
  ∃ vertex,
    vertex ∈ model.responseSupport left ∧
      vertex ∈ model.responseSupport right ∧
      vertex ∉ activation.pairSeed left.1 ∧
      vertex ∉ activation.pairSeed right.1

def PairwiseSeparated
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet}) : Prop :=
  ∀ left, left ∈ family → ∀ right, right ∈ family → left ≠ right →
    ¬ model.Overlaps left right

noncomputable def familyUnion
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (left right : Finset {pair // pair ∈ model.pairSet}) :
    Finset {pair // pair ∈ model.pairSet} := by
  classical
  exact left ∪ right

noncomputable def responseSupportUnion
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet}) :
    Finset object.Vertex := by
  classical
  exact family.biUnion model.responseSupport

/-- The paper's conditional-factorization theorem on actual skeletons.  The
second clause is the component-concatenation step used to prove connectedness
of a minimal obstruction. -/
structure ConditionalFactorization
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule) : Prop where
  separated : ∀ family, model.PairwiseSeparated family →
    model.RealizingOrder (LengthOK := LengthOK) family
  concatenate : ∀ left right,
    left.Nonempty → right.Nonempty → Disjoint left right →
      (∀ leftPair, leftPair ∈ left → ∀ rightPair, rightPair ∈ right →
        ¬ model.Overlaps leftPair rightPair) →
      model.RealizingOrder (LengthOK := LengthOK) left →
        model.RealizingOrder (LengthOK := LengthOK) right →
          model.RealizingOrder (LengthOK := LengthOK)
            (model.familyUnion left right)


end SparsePairSkeletonModel

/-- Clause (d) at a specified pair: a functional attempted quotient is
rank-reducing, has an inclusion-minimal determination certificate for that
pair's actual response coordinate, and identifies two different boundary
degree profiles. -/
def SparsePairDEProfileObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  let coordinate := FiniteObject.DemandActivation.pairCoordinate pair
    ((activation.pairSupport pair).getD ∅)
  ∃ attempt : AttemptedQuotient Baseline
      (Graph.HasCycleWithLength LengthOK) object family coordinateSupport,
    attempt.toRankQuotient.FunctionalOn ↑family ∧
      ¬ Set.InjOn attempt.label ↑family ∧
      (∃ determiners : Finset object.PairCoordinate,
        coordinate ∈ family ∧
          determiners ⊆ family ∧
          coordinate ∉ determiners ∧
          attempt.toRankQuotient.Determines coordinate ↑determiners ∧
          ∀ candidate ⊆ determiners,
            attempt.toRankQuotient.Determines coordinate ↑candidate →
              determiners ⊆ candidate) ∧
      ∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile

/-- Clause (e) at a specified pair, with the same literal minimal
determination certificate.  Its final witness is exactly either a distinguishing
target context or the target-complete proper-support replacement supplied by
the attempted quotient. -/
def SparsePairDEResponseObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  let coordinate := FiniteObject.DemandActivation.pairCoordinate pair
    ((activation.pairSupport pair).getD ∅)
  ∃ attempt : AttemptedQuotient Baseline
      (Graph.HasCycleWithLength LengthOK) object family coordinateSupport,
    attempt.toRankQuotient.FunctionalOn ↑family ∧
      ¬ Set.InjOn attempt.label ↑family ∧
      (∃ determiners : Finset object.PairCoordinate,
        coordinate ∈ family ∧
          determiners ⊆ family ∧
          coordinate ∉ determiners ∧
          attempt.toRankQuotient.Determines coordinate ↑determiners ∧
          ∀ candidate ⊆ determiners,
            attempt.toRankQuotient.Determines coordinate ↑candidate →
              determiners ⊆ candidate) ∧
      ((∃ left right, attempt.Identifies left right ∧
          Response.TargetDefect (Graph.HasCycleWithLength LengthOK) left right) ∨
        ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
          attempt.support)

/-- A concrete type-(d) or type-(e) obstruction carried by its actual pair in
`Π`.  The pair is part of the local predicate, so this cannot be discharged by
an obstruction belonging to a different coordinate. -/
def HasSparsePairDEBlocker
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∃ pair ∈ pairs,
    SparsePairDEProfileObstructionAt
        (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair ∨
      SparsePairDEResponseObstructionAt
        (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair

/-- The declared coordinate used to record the certified pair obstruction. -/
noncomputable def sparsePairDECoordinate
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (certificate : HasSparsePairDEBlocker
      (Baseline := Baseline) (LengthOK := LengthOK) activation pairs) :
    object.PairCoordinate :=
  FiniteObject.DemandActivation.pairCoordinate certificate.choose
    ((activation.pairSupport certificate.choose).getD ∅)

/-- Install every concrete type-(d)/(e) obstruction into the same activation
used to define the pair-response family.  This is a canonical definition of the
full finite blocker family; it does not depend on which witness exposed the
blocked branch. -/
noncomputable def recordSparsePairDEBlockers
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) :
    object.DemandActivation (object.PairCoordinate) Chord := by
  classical
  exact {
    localBuffer := activation.localBuffer
    responseSupport := activation.responseSupport
    declaredSupport := activation.declaredSupport
    declaredSupport_eq := activation.declaredSupport_eq
    returnSupport := activation.returnSupport
    profileObstructions := fun pair =>
      if SparsePairDEProfileObstructionAt
          (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair then
        [FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)]
      else []
    responseObstructions := fun pair =>
      if SparsePairDEResponseObstructionAt
          (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair then
        [FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)]
      else []
    chordObstructions := activation.chordObstructions
    chordEnds := activation.chordEnds
    chordPort := activation.chordPort }

theorem coordinate_eq_of_mem_recordedProfileObstructions
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    {pair : Finset (object.Vertex × object.Vertex)}
    {coordinate : object.PairCoordinate}
    (member : coordinate ∈
      (recordSparsePairDEBlockers (Baseline := Baseline)
        (LengthOK := LengthOK) activation pairs).profileObstructions pair) :
    coordinate = FiniteObject.DemandActivation.pairCoordinate pair
      ((activation.pairSupport pair).getD ∅) := by
  classical
  simp only [recordSparsePairDEBlockers] at member
  split at member
  · simpa using member
  · simp at member

theorem coordinate_eq_of_mem_recordedResponseObstructions
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    {pair : Finset (object.Vertex × object.Vertex)}
    {coordinate : object.PairCoordinate}
    (member : coordinate ∈
      (recordSparsePairDEBlockers (Baseline := Baseline)
        (LengthOK := LengthOK) activation pairs).responseObstructions pair) :
    coordinate = FiniteObject.DemandActivation.pairCoordinate pair
      ((activation.pairSupport pair).getD ∅) := by
  classical
  simp only [recordSparsePairDEBlockers] at member
  split at member
  · simpa using member
  · simp at member

/-- `X_π` together with the canonical return entries of the demands in
`π` is connected.  This is the declared connector support used by
`def:same-token-routing-germs`: every `R_p` meets `X_π` at the endpoint of
`p`, which lies in `T(p)`. -/
theorem recordedPairConnector_connectedOn
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} [DecidableEq object.Vertex] {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    {pair : Finset (object.Vertex × object.Vertex)}
    {support : Finset object.Vertex}
    (pairSubset : pair ⊆ object.excessPorts threshold)
    (selected :
      (recordSparsePairDEBlockers (Baseline := Baseline)
        (LengthOK := LengthOK) (pairResponseActivation active)
        (object.portPairSchedule threshold)).pairSupport pair = some support) :
    SupportComponents.Connected.ConnectedOn object
      (support ∪ pair.biUnion
        (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) (pairResponseActivation active)
          (object.portPairSchedule threshold)).returnSupport) := by
  classical
  let activation := recordSparsePairDEBlockers (Baseline := Baseline)
    (LengthOK := LengthOK) (pairResponseActivation active)
    (object.portPairSchedule threshold)
  have supportFacts :=
    FiniteObject.DemandActivation.pairSupport_mem_candidates selected
  have build : ∀ members : Finset (object.Vertex × object.Vertex),
      members ⊆ pair →
      SupportComponents.Connected.ConnectedOn object
        (support ∪ members.biUnion activation.returnSupport) := by
    intro members membersSubset
    induction members using Finset.induction_on with
    | empty => simpa using supportFacts.2
    | @insert demand members fresh ih =>
        have demandPair : demand ∈ pair :=
          membersSubset (Finset.mem_insert_self demand members)
        have demandActive : demand ∈ object.excessPorts threshold :=
          pairSubset demandPair
        have restSubset : members ⊆ pair := by
          intro other otherMem
          exact membersSubset (Finset.mem_insert_of_mem otherMem)
        have previous := ih restSubset
        have returnConnected :
            SupportComponents.Connected.ConnectedOn object
              (activation.returnSupport demand) := by
          simpa [activation, recordSparsePairDEBlockers] using
            (pairResponseActivation_connectedOn_returnSupport_of_mem
              active demandActive)
        have endpointReturn :
            demand.2 ∈ activation.returnSupport demand := by
          simpa [activation, recordSparsePairDEBlockers] using
            (pairResponseActivation_endpoint_mem_returnSupport_of_mem
              active demandActive)
        have endpointLocal : demand.2 ∈ activation.localBuffer demand := by
          change demand.2 ∈
            (pairResponseActivation active).localBuffer demand
          rw [pairResponseActivation_localBuffer_of_mem active demandActive]
          exact FiniteObject.SurplusPort.endpoint_mem_support _
        have endpointSupport : demand.2 ∈ support := by
          apply supportFacts.1
          apply FiniteObject.DemandActivation.declaredSupport_subset_pairSeed
            activation demandPair
          exact activation.localBuffer_subset_declaredSupport demand endpointLocal
        have joined := SameTokenRoutingGerms.connectedOn_union_of_common previous
          returnConnected (Finset.mem_union_left _ endpointSupport) endpointReturn
        simpa [Finset.biUnion_insert, Finset.union_assoc, Finset.union_comm,
          Finset.union_left_comm] using joined
  exact build pair (fun _ member => member)

theorem recordedSparsePairDEBlocker_nonempty
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (certificate : HasSparsePairDEBlocker
      (Baseline := Baseline) (LengthOK := LengthOK) activation pairs) :
    ∃ pair ∈ pairs,
      ((recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        activation pairs).blockers pair).Nonempty := by
  classical
  let pair := certificate.choose
  have pairMem := certificate.choose_spec.1
  let coordinate := sparsePairDECoordinate activation pairs certificate
  refine ⟨pair, pairMem, ?_⟩
  rcases certificate.choose_spec.2 with profile | response
  · exact ((recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs).exists_blocks_iff_blockers_nonempty pair).mp
      ⟨.boundaryProfile,
        (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) activation pairs).blocks_boundaryProfile
          (coordinate := coordinate)
          (by
            change coordinate ∈
              (if SparsePairDEProfileObstructionAt
                  (Baseline := Baseline) (LengthOK := LengthOK)
                  activation pairs pair then [coordinate] else [])
            rw [if_pos profile]
            simp)⟩
  · exact ((recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs).exists_blocks_iff_blockers_nonempty pair).mp
      ⟨.targetResponse,
        (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) activation pairs).blocks_targetResponse
          (coordinate := coordinate)
          (by
            change coordinate ∈
              (if SparsePairDEResponseObstructionAt
                  (Baseline := Baseline) (LengthOK := LengthOK)
                  activation pairs pair then [coordinate] else [])
            rw [if_pos response]
            simp)⟩

/-- **`lem:sparse-pair-dependence-exit`.**

For the concrete response family `ℛ_Π`, failure to survive its declared
admissible quotient system produces exactly one of the paper's outcomes: a
sparse surplus exit, or a certified type-(d)/(e) blocker on a member of `Π`.
The four cases and their order are inherited directly from
`AttemptedQuotient.route`. -/
theorem sparsePairDependence_exit_or_blocker
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (attempt :
      let family := activation.pairFamily pairs
      let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
        letI := object.vertices.decEq
        exact DeclaredSignature.Coordinate.support
      AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK) object
        family coordinateSupport)
    (reducing :
      let family := activation.pairFamily pairs
      ¬ Set.InjOn attempt.label ↑family)
    (functional :
      let family := activation.pairFamily pairs
      attempt.toRankQuotient.FunctionalOn ↑family) :
    SparseSurplusExit Baseline (Graph.HasCycleWithLength LengthOK) LengthOK object ∨
      HasSparsePairDEBlocker (Baseline := Baseline) (LengthOK := LengthOK)
        activation pairs := by
  classical
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  change ¬ Set.InjOn attempt.label ↑family at reducing
  change attempt.toRankQuotient.FunctionalOn ↑family at functional
  let quotient := attempt.toRankQuotient
  let candidates : Finset (Finset object.PairCoordinate) :=
    family.powerset.filter fun independent =>
      Set.InjOn attempt.label ↑independent
  have candidatesNonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨independent, independentMember, maximum⟩ :=
    Finset.exists_mem_eq_sup candidates candidatesNonempty Finset.card
  have independentFacts : independent ⊆ family ∧
      Set.InjOn attempt.label ↑independent := by
    simpa [candidates] using independentMember
  obtain ⟨coordinate, coordinateMember, coordinateOutside⟩ :
      ∃ coordinate ∈ family, coordinate ∉ independent := by
    by_contra absent
    push Not at absent
    have equal : independent = family :=
      Finset.Subset.antisymm independentFacts.1 absent
    apply reducing
    rw [← equal]
    exact independentFacts.2
  let candidate := insert coordinate independent
  have candidateSubset : candidate ⊆ family := by
    intro member membership
    simp only [candidate, Finset.mem_insert] at membership
    rcases membership with rfl | membership
    · exact coordinateMember
    · exact independentFacts.1 membership
  have candidateNotInjective : ¬ Set.InjOn attempt.label ↑candidate := by
    intro candidateInjective
    have candidateMember : candidate ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨candidateSubset, candidateInjective⟩
    have bound := Finset.le_sup (f := Finset.card) candidateMember
    rw [maximum] at bound
    have larger : independent.card < candidate.card := by
      simp [candidate, coordinateOutside]
    omega
  have candidateReducing :
      ¬ quotient.LabelInjectiveOn
        (insert coordinate (↑independent : Set object.PairCoordinate)) := by
    change ¬ Set.InjOn attempt.label
      (insert coordinate (↑independent : Set object.PairCoordinate))
    simpa [candidate] using candidateNotInjective
  obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
    functional independentFacts.1 coordinateMember coordinateOutside
      independentFacts.2 candidateReducing
  let certificates : Finset (Finset object.PairCoordinate) :=
    finite.toFinset.powerset.filter fun certificate =>
      quotient.Determines coordinate ↑certificate
  have certificatesNonempty : certificates.Nonempty := by
    refine ⟨finite.toFinset, ?_⟩
    simp [certificates, quotient, determines]
  obtain ⟨minimalDeterminers, minimal⟩ :=
    certificates.exists_minimal certificatesNonempty
  have minimalFacts : minimalDeterminers ⊆ finite.toFinset ∧
      quotient.Determines coordinate ↑minimalDeterminers := by
    simpa [certificates] using minimal.1
  have minimalSubsetFamily : minimalDeterminers ⊆ family := by
    intro determiner membership
    exact independentFacts.1 (determinersSubset (by
      simpa using minimalFacts.1 membership))
  have coordinateNotMinimal : coordinate ∉ minimalDeterminers := by
    intro membership
    exact coordinateOutside (determinersSubset (by
      simpa using minimalFacts.1 membership))
  have inclusionMinimal : ∀ other ⊆ minimalDeterminers,
      quotient.Determines coordinate ↑other → minimalDeterminers ⊆ other := by
    intro other subset otherDetermines
    apply minimal.2
    · simp only [certificates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨subset.trans minimalFacts.1, otherDetermines⟩
    · exact subset
  obtain ⟨pair, pairMem, pairEq⟩ : ∃ pair ∈ pairs,
      FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅) = coordinate := by
    change coordinate ∈ pairs.image (fun pair =>
      FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅)) at coordinateMember
    exact Finset.mem_image.mp coordinateMember
  subst coordinate
  have determination :
      ∃ determiners : Finset object.PairCoordinate,
        FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅) ∈ family ∧
          determiners ⊆ family ∧
          FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅) ∉ determiners ∧
          quotient.Determines
              (FiniteObject.DemandActivation.pairCoordinate pair
                ((activation.pairSupport pair).getD ∅)) ↑determiners ∧
          ∀ candidate ⊆ determiners,
            quotient.Determines
                (FiniteObject.DemandActivation.pairCoordinate pair
                  ((activation.pairSupport pair).getD ∅)) ↑candidate →
              determiners ⊆ candidate := by
    refine ⟨minimalDeterminers, ?_, minimalSubsetFamily,
      coordinateNotMinimal, minimalFacts.2, inclusionMinimal⟩
    change FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅) ∈
      pairs.image (fun candidate =>
        FiniteObject.DemandActivation.pairCoordinate candidate
          ((activation.pairSupport candidate).getD ∅))
    exact Finset.mem_image_of_mem _ pairMem
  rcases attempt.route reducing with profiles | defect | replacement |
      ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inr ⟨pair, pairMem, Or.inl
      ⟨attempt, functional, reducing, determination, profiles⟩⟩
  · exact Or.inr ⟨pair, pairMem, Or.inr
      ⟨attempt, functional, reducing, determination, Or.inl defect⟩⟩
  · exact Or.inr ⟨pair, pairMem, Or.inr
      ⟨attempt, functional, reducing, determination, Or.inr replacement⟩⟩
  · exact Or.inl (.delocalization representative smaller baseline transfer)

/-- **`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence`,
at a survivor.**

> Suppose the coordinate family `ℛ_Π` does not survive every admissible rank
> quotient.  Then either `G` has a sparse surplus exit, or some `π ∈ Π` has a
> sparse surplus blocker of type (d) or (e).

The two exit alternatives the manuscript's proof produces are discharged by the
survivor's own hypotheses — the whole-graph case is the delocalization exit, and
the proper-support case is `lem:replacement` — so what a rank-reducing attempted
determination leaves is precisely the blocker: two realizations it identifies
which are separated by their boundary degree profiles (type (d)) or by a
boundaried context (type (e)).

Both witnesses are the concrete finite objects `def:surplus-blockers` names,
which is what `DemandActivation.blocks_boundaryProfile` and
`blocks_targetResponse` record on the ledger. -/
theorem blockerSeparation_of_reducing
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (survives : SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (noReplacement : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
        support)
    (attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object family coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
      (∃ left right, attempt.Identifies left right ∧
        Response.TargetDefect (Graph.HasCycleWithLength LengthOK) left right) := by
  rcases attempt.route reducing with profiles | defect | replacement |
    ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inl profiles
  · exact Or.inr defect
  · exact absurd replacement (noReplacement _)
  · exact absurd (SparseSurplusExit.delocalization representative smaller baseline
      transfer) survives

/-! ## The entropy sandwich -/

/-- **`prop:sparse-entropy-sandwich-with-blockers`, with the logarithms
cleared.**

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`  and  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`.

Taking `log₂` gives the manuscript's

  `|Π_free| ≤ E_spine(n) + (m − m₀)·log₂ n`,

and `m − m₀ ≤ ½σ(G) + 1` is the branch's own slack identity, which is why the
display carries `(½σ(G) + 1) log₂ n`.

The proof is the manuscript's three steps and nothing else: the entropy count on
the mixed family, `lem:incremental-skeleton-room` at the object's own edge count,
and the baseline demand.  The spine count cancels because it appears on both
sides, which is the sense in which the sandwich charges only the *free* pairs. -/
theorem entropySandwich (object : FiniteObject.{u})
    {baselineDegree spineCount freeCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + freeCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ freeCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) := by
  have room := skeletonBudget_le_cubicBaselineBudget_mul_pow object baseline above
  have chain :
      2 ^ spineCount * 2 ^ freeCount ≤
        2 ^ spineCount *
          (2 ^ deficit *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
    calc 2 ^ spineCount * 2 ^ freeCount
        = 2 ^ (spineCount + freeCount) := by rw [pow_add]
      _ ≤ skeletonBudget object := entropy
      _ ≤ cubicBaselineBudget object.vertexCount baselineDegree *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) := room
      _ ≤ 2 ^ (spineCount + deficit) *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
          Nat.mul_le_mul_right _ demand
      _ = 2 ^ spineCount *
            (2 ^ deficit *
              object.vertexCount ^
                (object.edgeCount -
                  cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
          rw [pow_add, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left chain (Nat.two_pow_pos spineCount)

/-- **`prop:sparse-entropy-sandwich`**: the same bound at the *full* pair
schedule.

The manuscript states it for `C(|𝒜₀|,2)` rather than for `|Π_free|`, under the
stronger hypothesis that *no* pair has a blocker — in which case `Π_free` is the
whole schedule.  So it is `entropySandwich` read at `freeCount = C(|𝒜₀|,2)`, and
nothing is proved twice. -/
theorem entropySandwich_of_unblocked (object : FiniteObject.{u})
    {baselineDegree spineCount pairCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + pairCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ pairCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
  entropySandwich object baseline above entropy demand

/-- **`cor:sparse-pair-entropy-saturation`, with the logarithm cleared.**

> If `G` survives the sparse surplus exits and no pair in `C(𝒜₀,2)` has a sparse
> surplus blocker, then `C(|𝒜₀|,2) ≤ log₂ C(C(n,2), m)`.

This is the entropy count at `ℐ_spine = ∅`: `2^{C(|𝒜₀|,2)} ≤ C(N,m)`, which is
`Graph.skeletonBudget` at the object's own order and edge count.  The manuscript
derives it from `prop:sparse-pair-independence-dichotomy` together with
`lem:independent-target-entropy` and `lem:skeleton-dominates`, and that is
exactly the composition the `entropy` hypothesis names. -/
theorem entropySaturation_of_unblocked (object : FiniteObject.{u})
    {pairCount : Nat}
    (entropy : 2 ^ (0 + pairCount) ≤ skeletonBudget object) :
    2 ^ pairCount ≤ skeletonBudget object := by
  simpa using entropy

end Hypostructure.Graph
