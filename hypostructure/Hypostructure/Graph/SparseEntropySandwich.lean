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

**The blockers.**  Blockers (d) and (e) of `def:surplus-blockers` are concrete
objects of G: the pair's actual response coordinate `r_π`, an inclusion-minimal
determination certificate for it in G's pair family whose quotient labels carry
G's canonical coordinate response (`SparsePairCanonicalValuation`), and — as the
final witness — for (d) a determiner the quotient *identifies* with `r_π` whose
reading on G's piece at the determination support lies in a different
boundary-degree fibre, and for (e) one of the three exit events
(`ResidualTargetDefect`, a replacement of the support, a smaller closed
representative).  No quotient label or value that is not G's response decides
either clause.

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
following model records exactly that class and no abstract state carrier.

Two ingredients are kept apart.  **The class count** ranges over the labelled
graphs with G's canonical data (`n = |V(G)|`, `m = |E(G)|`, G's labelling, G's
baseline word): it is an encoding bound whose published conclusion is an
inequality about G's own quantities, and it is kept exactly.  **The response**
of a member at `X_π` is read inside G: the member's reading of `X_π`, on G's
boundary `∂X_π`, glued into G's own surroundings `G − X_π` (`memberPiece`) -- no
boundaried context other than `G − X_π` is quantified. -/

/-- One graph-derived value of a sparse pair-response coordinate: whether a
member's reading of `X_π`, glued into G's surroundings `G − X_π`, carries a
target cycle. -/
abbrev SparsePairSkeletonResponse (_LengthOK : Nat → Prop) : Type := Prop

/-- A member's reading of G's support `Z`, on G's own boundary `∂Z`: the
vertices of G's piece at `Z` with the adjacency of `graph` (a labelled member of
the skeleton class, pulled back to `V(G)`).  Glued into `G − Z` it is
`glue X' (G − Z)` with `X'` the member's reading. -/
noncomputable def memberPiece (object : FiniteObject.{u})
    (graph : SimpleGraph object.Vertex) (support : Finset object.Vertex) :
    BoundaryPiece (Strategy.InterfaceReplacement.SupportAtom.boundary object support) where
  Internal := Strategy.InterfaceReplacement.SupportAtom.PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧
        vertex ∉ Strategy.InterfaceReplacement.SupportAtom.cutBoundary object support
  graph := SimpleGraph.comap
    (Strategy.InterfaceReplacement.SupportAtom.pieceDecode object support) graph
  decideAdj := Classical.decRel _

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

/-- The target response of `X_π` in a labelled skeleton, read in G's own
surroundings: the member's reading of `X_π` glued into `G − X_π`. -/
noncomputable def response
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (member : model.Skeleton) (pair : {pair // pair ∈ model.pairSet}) :
    SparsePairSkeletonResponse LengthOK :=
  HasCycleWithLength LengthOK
    (glue
      (memberPiece object (member.1.graph.comap object.vertices.equiv)
        (model.responseSupport pair))
      (Strategy.InterfaceReplacement.SupportAtom.outside object
        (model.responseSupport pair)))

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
have been exposed, among skeletons carrying the reference's baseline word.

The candidates are conditioned on the realized baseline word and on the
exposed prefix only — not on the outside edges of the reference.  Conditioning
on outside edges made the predicate depend on the reference's own edges among
the connector vertices of a support: a reference with a power-of-two cycle
there has one response on its whole fibre, so the ∀-reference branching
condition was false for every model with two connector vertices in some
support.  The `[178]` entropy count
(`HomogeneousBottleneckRows`) doubles the number of realized
`(baseline word, prefix)` signatures, which is exactly this set. -/
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
  {state | ∃ candidate : model.Skeleton,
    model.baseline.response candidate.1 = model.baseline.response reference.1 ∧
      (∀ earlier : Fin family.card, earlier.1 < index.1 →
        model.response (LengthOK := LengthOK) candidate (order earlier).1 =
          model.response (LengthOK := LengthOK) reference (order earlier).1) ∧
      model.response (LengthOK := LengthOK) candidate (order index).1 = state}

/-- The signature of a member of the skeleton class at level `length` of an exposure order: its
baseline word and its responses at the first `length` coordinates of the order. -/
noncomputable def signature
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (length : Nat) (bound : length ≤ family.card) (member : model.Skeleton) :
    ({coordinate // coordinate ∈ model.baselineFamily} → Bool) ×
      (Fin length → SparsePairSkeletonResponse LengthOK) :=
  (model.baseline.response member.1, fun index =>
    model.response (LengthOK := LengthOK) member (order (Fin.castLE bound index)).1)

/-- The number of `(baseline word, first `length` responses)` signatures realized by the
skeleton class: the aggregate the encoding bound counts. -/
noncomputable def signatureCount
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (length : Nat) (bound : length ≤ family.card) : Nat := by
  classical
  haveI : Fintype model.Skeleton := Fintype.ofFinite _
  exact (Finset.univ.image
    (model.signature (LengthOK := LengthOK) family order length bound)).card

/-- The number of realized signatures is the cardinality of the range of the signature map. -/
theorem signatureCount_eq
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet})
    (order : Fin family.card ≃ {pair // pair ∈ family})
    (length : Nat) (bound : length ≤ family.card) :
    model.signatureCount (LengthOK := LengthOK) family order length bound =
      Nat.card (Set.range
        (model.signature (LengthOK := LengthOK) family order length bound)) := by
  classical
  unfold signatureCount
  letI : Fintype model.Skeleton := Fintype.ofFinite _
  rw [Nat.card_eq_card_toFinset, Set.toFinset_range]

/-- An exposure order realizes one binary response coordinate at every step of every realized
`(baseline word, prefix)` signature, **in the aggregate form the counting consumes**: the number
of realized signatures doubles at every level, i.e. at the last level it is
`2 ^ |family|` times the number of realized baseline words.  (Each level has at most twice as
many signatures as the one before, so equality forces every realized signature to carry both
responses; a failure is the numerical inequality `N_{|family|} < 2 ^ |family| * N_0` about G's
labelled `(n, m)` class, not a member of the class that fails.) -/
def RealizingOrder
    {LengthOK : Nat → Prop} {object : FiniteObject.{u}}
    {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {schedule : Finset (Finset (object.Vertex × object.Vertex))}
    (model : SparsePairSkeletonModel activation schedule)
    (family : Finset {pair // pair ∈ model.pairSet}) : Prop :=
  ∃ order : Fin family.card ≃ {pair // pair ∈ family},
    model.signatureCount (LengthOK := LengthOK) family order family.card le_rfl =
      2 ^ family.card *
        model.signatureCount (LengthOK := LengthOK) family order 0 (Nat.zero_le _)

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

/-- The declared support `X_π` of a pair-response coordinate
(`def:sparse-pair-response`). -/
noncomputable abbrev sparsePairCoordinateSupport {object : FiniteObject.{u}} :
    object.PairCoordinate → Finset object.Vertex := by
  letI := object.vertices.decEq
  exact DeclaredSignature.Coordinate.support

/-- **The quotient reads G's exact response data**
(`def:exact-response-profile`, `ρ^ex_T(X) = (𝐝_∂(X), profile_T(X), ℛ^ex_T(X))`;
`def:declared-coordinate-signature`, `val_X(r)`; `def:target-complete-quotient`;
`lem:target-rank-circuit`, tex 9160-9180, whose quotient is a *functional
admissible* rank quotient).  The attempt's quotient labels carry a value, and
at every coordinate `c ∈ ℛ_Π` that value is G's own exact response data of `c`
at the determination support `Z`: the boundary-degree profile of `c` read on
G's piece at `Z` restricted to its declared support, and the target response of
that reading in G's own surroundings `G − Z` (`ActualContext.actualGlue`; G-only
restatement: the former component was the response against every
`∂Z`-boundaried context, which is not part of G).  An identification of two coordinates by the
quotient therefore preserves both components, as a target-complete quotient
must (`def:target-complete-quotient` (a), (b); `def:boundary-degree-profile`:
"All target-response states in this paper are taken fibrewise over `𝐝_∂`").
The labelling is not free. -/
def SparsePairExactValuation
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport) : Prop :=
  ∃ valuation : attempt.Label →
      ((SupportAtom.boundary object attempt.support).Vertex → Nat) × Prop,
    ∀ coordinate ∈ activation.pairFamily pairs,
      valuation (attempt.label coordinate) =
        ((SupportAtom.retainedPiece object attempt.support
            (sparsePairCoordinateSupport coordinate)).boundaryDegreeProfile,
          Graph.HasCycleWithLength LengthOK
            (ActualContext.actualGlue object attempt.support
              (sparsePairCoordinateSupport coordinate)))

/-- **An inclusion-minimal determination certificate of `r_π`**
(`lem:sparse-pair-dependence-exit`, tex 4675-4684; `lem:target-rank-circuit`):
a functional attempted declared quotient of G's pair-response family `ℛ_Π` at
the activation, whose labels carry G's exact response data
(`SparsePairExactValuation`), is rank-reducing, and on its connected
determination support `Z` it determines the pair's own response coordinate
`r_π` from the inclusion-minimal subfamily `determiners ⊆ ℛ_Π ∖ {r_π}`.  This
is the determination `def:surplus-blockers` (d) and (e) speak about: "a
quotient or replacement" of `r_π` with its determiners. -/
def SparsePairDetermination
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex))
    (attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport)
    (determiners : Finset object.PairCoordinate) : Prop :=
  let family := activation.pairFamily pairs
  let coordinate := FiniteObject.DemandActivation.pairCoordinate pair
    ((activation.pairSupport pair).getD ∅)
  attempt.toRankQuotient.FunctionalOn ↑family ∧
    ¬ Set.InjOn attempt.label ↑family ∧
    coordinate ∈ family ∧
    determiners ⊆ family ∧
    coordinate ∉ determiners ∧
    attempt.toRankQuotient.Determines coordinate ↑determiners ∧
    (∀ candidate ⊆ determiners,
      attempt.toRankQuotient.Determines coordinate ↑candidate →
        determiners ⊆ candidate) ∧
    SparsePairExactValuation (Baseline := Baseline) (LengthOK := LengthOK)
      activation pairs attempt

/-- **Clause (d) at a specified pair** (`def:surplus-blockers` (d), tex 2897:
"a boundary-degree-profile coordinate which prevents a quotient or replacement
from staying in a single fibre, in the sense of `lem:degree-profile-fibres`";
`lem:sparse-pair-dependence-exit`, tex 4686-4689: "If the determination
attempts to identify states with different boundary degree profiles ... The
offending boundary-degree entry is a blocker of type (d)").  At an
inclusion-minimal determination of `r_π` whose quotient reads G's canonical
response (`SparsePairDetermination`), the quotient **identifies** `r_π` with a
determiner `b` (`label b = label r_π`, the case `ℬ = {b}` of
`lem:target-rank-circuit`), and the two states it identifies -- `r_π` and `b`
read on G's own piece at the determination support `Z` -- lie in different
boundary-degree fibres (`lem:degree-profile-fibres`).  The separated
coordinates are exactly the ones the quotient identifies, at the quotient's
own support.  Because the paper's determination quotient is admissible
(target-complete), the clause is never inhabited
(`not_sparsePairDEProfileObstructionAt`; closed from G's facts at `[130]`). -/
def SparsePairDEProfileObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  ∃ attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport,
    ∃ determiners : Finset object.PairCoordinate,
      SparsePairDetermination (Baseline := Baseline) (LengthOK := LengthOK)
          activation pairs pair attempt determiners ∧
        ∃ identified ∈ determiners,
          attempt.label identified =
              attempt.label (FiniteObject.DemandActivation.pairCoordinate pair
                ((activation.pairSupport pair).getD ∅)) ∧
            (SupportAtom.retainedPiece object attempt.support
                (sparsePairCoordinateSupport
                  (FiniteObject.DemandActivation.pairCoordinate pair
                    ((activation.pairSupport pair).getD ∅)))).boundaryDegreeProfile ≠
              (SupportAtom.retainedPiece object attempt.support
                (sparsePairCoordinateSupport identified)).boundaryDegreeProfile

/-- On two coordinates a determination identifies, G's responses at the
determination support, in G's own surroundings `G − Z`, agree: the valuation of
the shared label is both. -/
theorem SparsePairDetermination.canonicalResponse_eq_of_label_eq
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {pairs : Finset (Finset (object.Vertex × object.Vertex))}
    {pair : Finset (object.Vertex × object.Vertex)}
    {attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport}
    {determiners : Finset object.PairCoordinate}
    (determination : SparsePairDetermination (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs pair attempt determiners)
    {first second : object.PairCoordinate}
    (firstMem : first ∈ activation.pairFamily pairs)
    (secondMem : second ∈ activation.pairFamily pairs)
    (same : attempt.label first = attempt.label second) :
    Graph.HasCycleWithLength LengthOK
        (ActualContext.actualGlue object attempt.support
          (sparsePairCoordinateSupport first)) =
      Graph.HasCycleWithLength LengthOK
        (ActualContext.actualGlue object attempt.support
          (sparsePairCoordinateSupport second)) := by
  obtain ⟨-, -, -, -, -, -, -, valuation, reads⟩ := determination
  exact (Prod.mk.inj ((reads first firstMem).symm.trans
    ((congrArg valuation same).trans (reads second secondMem)))).2

/-- **`lem:degree-profile-fibres` for a determination of G's pair family**
(tex 6088-6100): two coordinates a determination identifies are read on G's
piece at the determination support in one boundary-degree fibre -- the
profile component of the shared label's value is both profiles. -/
theorem SparsePairDetermination.profile_eq_of_label_eq
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    {activation : object.DemandActivation Coordinate Chord}
    {pairs : Finset (Finset (object.Vertex × object.Vertex))}
    {pair : Finset (object.Vertex × object.Vertex)}
    {attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport}
    {determiners : Finset object.PairCoordinate}
    (determination : SparsePairDetermination (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs pair attempt determiners)
    {first second : object.PairCoordinate}
    (firstMem : first ∈ activation.pairFamily pairs)
    (secondMem : second ∈ activation.pairFamily pairs)
    (same : attempt.label first = attempt.label second) :
    (SupportAtom.retainedPiece object attempt.support
        (sparsePairCoordinateSupport first)).boundaryDegreeProfile =
      (SupportAtom.retainedPiece object attempt.support
        (sparsePairCoordinateSupport second)).boundaryDegreeProfile := by
  obtain ⟨-, -, -, -, -, -, -, valuation, reads⟩ := determination
  exact (Prod.mk.inj ((reads first firstMem).symm.trans
    ((congrArg valuation same).trans (reads second secondMem)))).1

/-- **Clause (d) is empty at every determination** (`def:surplus-blockers` (d)
with `lem:sparse-pair-dependence-exit`, tex 4686-4689): the determination's
quotient reads G's exact response data, so the two states it identifies lie in
one boundary-degree fibre (`profile_eq_of_label_eq`). -/
theorem not_sparsePairDEProfileObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) :
    ¬ SparsePairDEProfileObstructionAt (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs pair := by
  rintro ⟨attempt, determiners, determination, identified, identifiedMem,
    same, different⟩
  have rMem := determination.2.2.1
  have bMem := determination.2.2.2.1 identifiedMem
  exact different (determination.profile_eq_of_label_eq rMem bMem same.symm)

/-- **Clause (e) at a specified pair** (`def:surplus-blockers` (e), tex 2900:
"a target-response coordinate witnessing a target-defective quotient,
target-complete compression, or support-dependence event, in the sense of
`lem:context-universality`, `cor:uncompressible`, `lem:proper-smearing`,
`lem:no-silent-global-smearing`"; tex 4691-4718).  At the same inclusion-minimal
determination of `r_π`, one of the three events of the clause:

* **target-defective quotient**: two of G's own coordinates
  `{r_π} ∪ determiners`, read on G's piece at their canonical support, lie in
  one fibre and are separated by G's own surroundings `G − Z`
  (`ResidualTargetDefect` stated about G, `lem:context-universality`; empty
  at a target-avoiding G);
* **target-complete compression / proper support dependence**: the
  determination support `Z` admits a target-complete proper replacement
  (`ReplacementSupport`, `cor:uncompressible`, `lem:proper-smearing`);
* **whole-graph support dependence**: `Z` is all of G and a strictly smaller
  admissible closed representative meets the baseline with no target cycle
  (`lem:no-silent-global-smearing`, stated about G: `glue X' (G − Z) = X'`). -/
def SparsePairDEResponseObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  ∃ attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object (activation.pairFamily pairs) sparsePairCoordinateSupport,
    ∃ determiners : Finset object.PairCoordinate,
      SparsePairDetermination (Baseline := Baseline) (LengthOK := LengthOK)
          activation pairs pair attempt determiners ∧
        (ResidualTargetDefect (Graph.HasCycleWithLength LengthOK) object
            (@insert _ _ (@Finset.instInsert _ (Classical.decEq _))
              (FiniteObject.DemandActivation.pairCoordinate pair
                ((activation.pairSupport pair).getD ∅))
              determiners) sparsePairCoordinateSupport ∨
          ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK)
            object attempt.support ∨
          ((∀ vertex, vertex ∈ attempt.support) ∧
            ∃ representative : FiniteObject.{u},
              representative.LexicographicallySmaller object ∧
                Baseline representative ∧
                ¬ Graph.HasCycleWithLength LengthOK representative))

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

/-- **Node `[130]`'s test "blocker-free?"** (`prop:sparse-pair-independence-dichotomy`,
tex 4721-4726; `def:canonical-blocker-ledger`, tex 2926-2934): some pair of
`Π` has a nonempty blocker set `𝖡𝗅𝗄(π)` over all six clauses (a)--(f) of
`def:surplus-blockers`, read at the one recorded activation that the blocker
ledger `[134]` and the capacity presentation `[136]` also use.  The pair is
blocked exactly when `π ∈ Π_blk`. -/
def HasSparsePairBlocker
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∃ pair ∈ pairs,
    ((recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
      activation pairs).blockers pair).Nonempty

/-- A clause-(d)/(e) obstruction is a blocker of its pair, so a pair family
with no blocker at all has no clause-(d)/(e) obstruction. -/
theorem hasSparsePairBlocker_of_DE
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (certificate : HasSparsePairDEBlocker
      (Baseline := Baseline) (LengthOK := LengthOK) activation pairs) :
    HasSparsePairBlocker (Baseline := Baseline) (LengthOK := LengthOK)
      activation pairs :=
  recordedSparsePairDEBlocker_nonempty activation pairs certificate

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
