/-!
DEPRECATED: migrated to canonical CT composition strategy
(CT10 -> CT7 -> CT5).
This detached feature executor is retained only as a parity oracle until
its CT-ledger equivalence theorem is kernel-checked.  It must not be
registered or executed by the framework.
-/
import Hypostructure.Graph.Strategy.Official.Features.CanonicalExcessPortActivation
import Hypostructure.Graph.TightVertexSuppression

/-!
# Canonical degree-three port responses

This Graph-owned feature is exactly the reusable content of paper nodes
`[128]--[129]`: it completes the bounded local response attached to every
selected excess port and packages the full active family.  The only numerical
precondition is that the registered deletion threshold is three.  Every
vertex, path, branch, and finite support is then reconstructed from the
graph's own schedules.
-/

namespace Hypostructure.Graph.Strategy.Official.Features.CanonicalDegreeThreePortResponse

open Hypostructure.Graph
open scoped Sym2

universe u v

variable
    {Baseline : FiniteObject.{u} → Prop}
    {profile : DeletionCriticalityProfile Baseline}
    {BranchState : FiniteObject.{u} → Type v}
    {LengthOK : Nat → Prop}
    {ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState)
      (HasCycleWithLength LengthOK)
      (lexicographicProgress Baseline BranchState)}

abbrev Port :=
  CanonicalExcessPortActivation.Port profile ctx.G

/-- Remove the selected centre from the endpoint's canonical neighbour
schedule.  When the threshold is three, this schedule has exactly two entries
and therefore determines the shoulders without a caller choice. -/
def shoulderSchedule
    (port : Port (profile := profile) (ctx := ctx)) :
    List ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  exact (ctx.G.orderedNeighbors port.endpoint).erase port.center

/-- Proof-only certificate that the graph-derived shoulder schedule has its
required two entries.  The entries themselves are projections of the fixed
schedule and cannot be supplied by a caller. -/
structure CanonicalShoulders
    (port : Port (profile := profile) (ctx := ctx)) : Prop where
  private mk ::
  length_eq : (shoulderSchedule port).length = 2

namespace CanonicalShoulders

variable {port : Port (profile := profile) (ctx := ctx)}

def left (shoulders : CanonicalShoulders port) : ctx.G.Vertex :=
  (shoulderSchedule port)[0]'(by
    rw [shoulders.length_eq]
    omega)

def right (shoulders : CanonicalShoulders port) : ctx.G.Vertex :=
  (shoulderSchedule port)[1]'(by
    rw [shoulders.length_eq]
    omega)

theorem left_mem (shoulders : CanonicalShoulders port) :
    shoulders.left ∈ shoulderSchedule port :=
  List.getElem_mem _

theorem right_mem (shoulders : CanonicalShoulders port) :
    shoulders.right ∈ shoulderSchedule port :=
  List.getElem_mem _

theorem schedule_nodup (_shoulders : CanonicalShoulders port) :
    (shoulderSchedule port).Nodup := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  exact (ctx.G.orderedNeighbors_nodup port.endpoint).erase port.center

theorem center_not_mem (_shoulders : CanonicalShoulders port) :
    port.center ∉ shoulderSchedule port := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  exact (ctx.G.orderedNeighbors_nodup port.endpoint).not_mem_erase

theorem center_ne_left (shoulders : CanonicalShoulders port) :
    port.center ≠ shoulders.left := by
  intro equality
  exact shoulders.center_not_mem (equality ▸ shoulders.left_mem)

theorem center_ne_right (shoulders : CanonicalShoulders port) :
    port.center ≠ shoulders.right := by
  intro equality
  exact shoulders.center_not_mem (equality ▸ shoulders.right_mem)

theorem left_ne_right (shoulders : CanonicalShoulders port) :
    shoulders.left ≠ shoulders.right := by
  intro equality
  have injective :=
    List.nodup_iff_injective_getElem.mp shoulders.schedule_nodup
  have indexEquality :
      (⟨0, by rw [shoulders.length_eq]; omega⟩ :
        Fin (shoulderSchedule port).length) =
      ⟨1, by rw [shoulders.length_eq]; omega⟩ :=
    injective equality
  have indexValues := Fin.ext_iff.mp indexEquality
  change (0 : Nat) = 1 at indexValues
  omega

theorem endpoint_left (shoulders : CanonicalShoulders port) :
    ctx.G.graph.Adj port.endpoint shoulders.left := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  apply (ctx.G.mem_orderedNeighbors_iff
    port.endpoint shoulders.left).mp
  exact List.mem_of_mem_erase shoulders.left_mem

theorem endpoint_right (shoulders : CanonicalShoulders port) :
    ctx.G.graph.Adj port.endpoint shoulders.right := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  apply (ctx.G.mem_orderedNeighbors_iff
    port.endpoint shoulders.right).mp
  exact List.mem_of_mem_erase shoulders.right_mem

theorem neighbor_cases (shoulders : CanonicalShoulders port)
    (other : ctx.G.Vertex) (adjacent : ctx.G.graph.Adj port.endpoint other) :
    other = port.center ∨
      other = shoulders.left ∨ other = shoulders.right := by
  by_cases isCenter : other = port.center
  · exact Or.inl isCenter
  · have memberOrdered :
        other ∈ ctx.G.orderedNeighbors port.endpoint :=
      (ctx.G.mem_orderedNeighbors_iff port.endpoint other).mpr adjacent
    have memberShoulder : other ∈ shoulderSchedule port := by
      letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
      exact (List.mem_erase_of_ne isCenter).mpr memberOrdered
    rw [List.mem_iff_getElem] at memberShoulder
    obtain ⟨index, inRange, value⟩ := memberShoulder
    have indexCases : index = 0 ∨ index = 1 := by
      rw [shoulders.length_eq] at inRange
      omega
    rcases indexCases with rfl | rfl
    · exact Or.inr (Or.inl value.symm)
    · exact Or.inr (Or.inr value.symm)

end CanonicalShoulders

/-- The threshold and endpoint-tightness facts force exactly two canonical
shoulders after removing the centre. -/
def deriveShoulders
    (threshold_eq_three : profile.threshold = 3)
    (port : Port (profile := profile) (ctx := ctx))
    (endpointTight : ctx.G.degree port.endpoint = profile.threshold) :
    CanonicalShoulders port := by
  refine ⟨?_⟩
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  unfold shoulderSchedule
  rw [List.length_erase_of_mem
    ((ctx.G.mem_orderedNeighbors_iff
      port.endpoint port.center).mpr port.adjacent.symm)]
  rw [ctx.G.orderedNeighbors_length, endpointTight, threshold_eq_three]

namespace CanonicalPath

open LexicographicPathSelection

theorem mem_pathSchedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (path : graph.Path left right) :
    path ∈ pathSchedule graph left right := by
  classical
  unfold pathSchedule
  rw [List.mem_flatMap]
  refine ⟨path.1.length, List.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.le_of_lt path.2.length_lt)
  · simp

/-- The existing finite path selector is total whenever a path witness exists.
The returned value is exactly the first row of `pathSchedule`; the witness is
used only to prove that the schedule is nonempty. -/
noncomputable def selectOfPath
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (witness : graph.Path left right) :
    SelectedPath graph left right := by
  classical
  have scheduleNonempty :
      pathSchedule graph left right ≠ [] := by
    intro empty
    have member := mem_pathSchedule graph witness
    rw [empty] at member
    simp at member
  have selectedExists :
      ∃ selected, select? graph left right = some selected := by
    unfold select?
    simp only
    split
    next nonempty =>
      exact ⟨_, rfl⟩
    next empty =>
      exact (empty scheduleNonempty).elim
  exact Classical.choose selectedExists

end CanonicalPath

/-- The degree-three data determine a literal tight-vertex suppression
configuration.  The only remaining dichotomy is whether the canonical
shoulder edge is already present. -/
def suppressionConfiguration
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (shoulder_missing :
      ¬ ctx.G.graph.Adj shoulders.left shoulders.right) :
    TightVertexSuppression.Configuration ctx.G where
  vertex := port.endpoint
  center := port.center
  left := shoulders.left
  right := shoulders.right
  vertex_center := port.adjacent.symm
  vertex_left := shoulders.endpoint_left
  vertex_right := shoulders.endpoint_right
  neighbors := shoulders.neighbor_cases
  center_ne_left := shoulders.center_ne_left
  center_ne_right := shoulders.center_ne_right
  left_ne_right := shoulders.left_ne_right
  shoulder_missing := shoulder_missing

/-- The canonical return selector type for one port. -/
abbrev ReturnSelection
    (port : Port (profile := profile) (ctx := ctx)) := by
  letI : FinEnum ctx.G.Vertex := ctx.G.vertices
  letI : Fintype ctx.G.Vertex := by infer_instance
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  letI : DecidableRel
      (CanonicalExcessPortActivation.deletedGraph port).Adj :=
    Classical.decRel _
  exact LexicographicPathSelection.SelectedPath
    (CanonicalExcessPortActivation.deletedGraph port)
    port.endpoint port.center

/-- The first finite scheduled return `R` together with its forced first
shoulder. -/
structure CanonicalReturn
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port) where
  selected : ReturnSelection port
  firstShoulder : by
    letI : FinEnum ctx.G.Vertex := ctx.G.vertices
    letI : Fintype ctx.G.Vertex := by infer_instance
    letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
    letI : DecidableRel
        (CanonicalExcessPortActivation.deletedGraph port).Adj :=
      Classical.decRel _
    exact
      selected.path.1.snd = shoulders.left ∨
        selected.path.1.snd = shoulders.right

private theorem return_not_nil
    (port : Port (profile := profile) (ctx := ctx))
    (path :
      (CanonicalExcessPortActivation.deletedGraph port).Path
        port.endpoint port.center) :
    ¬ path.1.Nil := by
  intro pathNil
  have same : port.endpoint = port.center := pathNil.eq
  exact (ctx.G.graph.ne_of_adj port.adjacent.symm) same

/-- Discard the activation's existential path and reselect the first member of
the graph-owned length-lexicographic schedule. -/
noncomputable def canonicalReturn
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (witness : CanonicalExcessPortActivation.ReturnPath port) :
    CanonicalReturn port shoulders := by
  classical
  letI : FinEnum ctx.G.Vertex := ctx.G.vertices
  letI : Fintype ctx.G.Vertex := by infer_instance
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  letI : DecidableRel
      (CanonicalExcessPortActivation.deletedGraph port).Adj :=
    Classical.decRel _
  let candidate :
      (CanonicalExcessPortActivation.deletedGraph port).Path
        port.endpoint port.center :=
    ⟨witness.walk, witness.simple⟩
  let selected :=
    CanonicalPath.selectOfPath
      (CanonicalExcessPortActivation.deletedGraph port) candidate
  have notNil := return_not_nil port selected.path
  have deletedAdjacent :
      (CanonicalExcessPortActivation.deletedGraph port).Adj
        port.endpoint selected.path.1.snd :=
    selected.path.1.adj_snd notNil
  have sourceAdjacent :
      ctx.G.graph.Adj port.endpoint selected.path.1.snd :=
    (SimpleGraph.deleteEdges_le
      {s(port.center, port.endpoint)}) deletedAdjacent
  have notCenter : selected.path.1.snd ≠ port.center := by
    intro equality
    rw [equality] at deletedAdjacent
    have absent :
        ¬ (CanonicalExcessPortActivation.deletedGraph port).Adj
          port.endpoint port.center := by
      simp [CanonicalExcessPortActivation.deletedGraph]
    exact absent deletedAdjacent
  have shoulderCases :=
    shoulders.neighbor_cases selected.path.1.snd sourceAdjacent
  exact {
    selected := selected
    firstShoulder := by
      rcases shoulderCases with center | left | right
      · exact (notCenter center).elim
      · exact Or.inl left
      · exact Or.inr right
  }

namespace CanonicalAcceptedPath

open LexicographicPathSelection

/-- The finite path schedule restricted to a semantic acceptance predicate. -/
noncomputable def schedule
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    (left right : V) (Accepted : graph.Path left right → Prop) :
    List (graph.Path left right) := by
  classical
  exact (pathSchedule graph left right).filter Accepted

/-- A path pinned definitionally to the first accepted row of the official
finite path schedule. -/
structure Selection
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    (left right : V) (Accepted : graph.Path left right → Prop) where
  path : graph.Path left right
  member : path ∈ pathSchedule graph left right
  accepted : Accepted path
  isHead : ∃ nonempty : schedule graph left right Accepted ≠ [],
    path = (schedule graph left right Accepted).head nonempty

/-- Select the first accepted path; an arbitrary accepted path is consumed
only as a proof that the filtered official schedule is nonempty. -/
noncomputable def selectOfAcceptedPath
    {V : Type u} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj]
    {left right : V} (Accepted : graph.Path left right → Prop)
    (witness : graph.Path left right) (accepted : Accepted witness) :
    Selection graph left right Accepted := by
  classical
  have witnessMember := CanonicalPath.mem_pathSchedule graph witness
  have nonempty : schedule graph left right Accepted ≠ [] := by
    intro empty
    have witnessFiltered : witness ∈ schedule graph left right Accepted := by
      simpa [schedule, accepted] using witnessMember
    rw [empty] at witnessFiltered
    simp at witnessFiltered
  let path := (schedule graph left right Accepted).head nonempty
  have pathFiltered :
      path ∈ schedule graph left right Accepted :=
    List.head_mem nonempty
  have data :
      path ∈ pathSchedule graph left right ∧ Accepted path := by
    simpa [schedule] using pathFiltered
  exact {
    path := path
    member := data.1
    accepted := data.2
    isHead := ⟨nonempty, rfl⟩
  }

end CanonicalAcceptedPath

/-- Literal three-edge cycle through the tight endpoint and its two
shoulders. -/
def triangleWalk
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (shoulder_adjacent :
      ctx.G.graph.Adj shoulders.left shoulders.right) :
    ctx.G.graph.Walk port.endpoint port.endpoint :=
  .cons shoulders.endpoint_left
    (.cons shoulder_adjacent
      (.cons shoulders.endpoint_right.symm .nil))

theorem triangleWalk_isCycle
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (shoulder_adjacent :
      ctx.G.graph.Adj shoulders.left shoulders.right) :
    (triangleWalk port shoulders shoulder_adjacent).IsCycle := by
  have endpoint_ne_left :
      port.endpoint ≠ shoulders.left :=
    ctx.G.graph.ne_of_adj shoulders.endpoint_left
  have endpoint_ne_right :
      port.endpoint ≠ shoulders.right :=
    ctx.G.graph.ne_of_adj shoulders.endpoint_right
  unfold triangleWalk
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · simp [Ne.symm endpoint_ne_left, Ne.symm endpoint_ne_right,
      shoulders.left_ne_right]
  · simp [endpoint_ne_left, endpoint_ne_right, shoulders.left_ne_right]

@[simp]
theorem triangleWalk_length
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (shoulder_adjacent :
      ctx.G.graph.Adj shoulders.left shoulders.right) :
    (triangleWalk port shoulders shoulder_adjacent).length = 3 := by
  simp [triangleWalk]

/-- The triangular branch carries a literal cycle certificate of length three;
the numeral is the semantic degree-three threshold already forced by
`threshold_eq_three`, not a problem-specific target constant. -/
def triangleCertificate
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (shoulder_adjacent :
      ctx.G.graph.Adj shoulders.left shoulders.right) :
    CycleCertificate ctx.G (fun length => length = 3) where
  vertex := port.endpoint
  walk := triangleWalk port shoulders shoulder_adjacent
  isCycle := triangleWalk_isCycle port shoulders shoulder_adjacent
  length_ok := triangleWalk_length port shoulders shoulder_adjacent

/-- Exact finite vertex carrier used by later response/accounting strategies. -/
structure DeclaredSupport (object : FiniteObject.{u}) where
  vertices : Finset object.Vertex

namespace DeclaredSupport

def port
    (selectedPort : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders selectedPort) :
    DeclaredSupport ctx.G := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  exact ⟨{selectedPort.endpoint, shoulders.left, shoulders.right}⟩

@[simp]
theorem port_vertices
    (selectedPort : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders selectedPort) :
    (port selectedPort shoulders).vertices =
      (by
        letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
        exact
          {selectedPort.endpoint, shoulders.left, shoulders.right}) := by
  rfl

def returnPath
    (selectedPort : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders selectedPort)
    (selectedReturn : CanonicalReturn selectedPort shoulders) :
    DeclaredSupport ctx.G := by
  letI : FinEnum ctx.G.Vertex := ctx.G.vertices
  letI : Fintype ctx.G.Vertex := by infer_instance
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  letI : DecidableRel
      (CanonicalExcessPortActivation.deletedGraph selectedPort).Adj :=
    Classical.decRel _
  exact ⟨selectedReturn.selected.path.1.support.toFinset⟩

def triangle
    (selectedPort : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders selectedPort)
    (selectedReturn : CanonicalReturn selectedPort shoulders)
    (shoulder_adjacent :
      ctx.G.graph.Adj shoulders.left shoulders.right) :
    DeclaredSupport ctx.G := by
  letI : FinEnum ctx.G.Vertex := ctx.G.vertices
  letI : Fintype ctx.G.Vertex := by infer_instance
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  letI : DecidableRel
      (CanonicalExcessPortActivation.deletedGraph selectedPort).Adj :=
    Classical.decRel _
  exact ⟨selectedReturn.selected.path.1.support.toFinset ∪
    (triangleWalk selectedPort shoulders shoulder_adjacent).support.toFinset⟩

end DeclaredSupport

/-- Open local data generated when the shoulder edge is absent.  Its
constructor is private: a caller cannot replace the graph-derived
configuration or the canonical return. -/
structure OpenSuppressionRequest
    (port : Port (profile := profile) (ctx := ctx))
    (shoulders : CanonicalShoulders port)
    (selectedReturn : CanonicalReturn port shoulders) where
  private mk ::
  shoulder_missing :
    ¬ ctx.G.graph.Adj shoulders.left shoulders.right

namespace OpenSuppressionRequest

variable
    {port : Port (profile := profile) (ctx := ctx)}
    {shoulders : CanonicalShoulders port}
    {selectedReturn : CanonicalReturn port shoulders}

def configuration
    (request : OpenSuppressionRequest port shoulders selectedReturn) :
    TightVertexSuppression.Configuration ctx.G :=
  suppressionConfiguration port shoulders request.shoulder_missing

/-- The accepted `Q` rows are exactly the paths whose restored cycle length
satisfies the registered target predicate. -/
abbrev QSelection
    (request : OpenSuppressionRequest port shoulders selectedReturn) := by
  let configuration := request.configuration
  letI : FinEnum configuration.deleted.Vertex :=
    configuration.deleted.vertices
  letI : Fintype configuration.deleted.Vertex := by infer_instance
  letI : DecidableEq configuration.deleted.Vertex :=
    configuration.deleted.vertices.decEq
  letI : DecidableRel configuration.deleted.graph.Adj :=
    configuration.deleted.decideAdj
  exact CanonicalAcceptedPath.Selection
    configuration.deleted.graph
    configuration.leftVertex configuration.rightVertex
    (fun path => LengthOK (path.1.length + 1))

/-- Completed open response: minimality produced the suppressed cycle, target
avoidance forced its added edge, reconstruction removed that edge, and the
official schedule reselected the first accepted predecessor path. -/
structure Completion
    (request : OpenSuppressionRequest port shoulders selectedReturn) where
  cycle :
    CycleCertificate request.configuration.suppressed LengthOK
  uses_shoulder :
    s(request.configuration.leftVertex,
      request.configuration.rightVertex) ∈ cycle.walk.edges
  reconstructed :
    TightVertexSuppression.Configuration.ReconstructedPath
      request.configuration cycle
  q : QSelection request

theorem Completion.q_restored_length_ok
    {request : OpenSuppressionRequest port shoulders selectedReturn}
    (completion : Completion request) :
    LengthOK (by
      let configuration := request.configuration
      letI : FinEnum configuration.deleted.Vertex :=
        configuration.deleted.vertices
      letI : Fintype configuration.deleted.Vertex := by infer_instance
      letI : DecidableEq configuration.deleted.Vertex :=
        configuration.deleted.vertices.decEq
      letI : DecidableRel configuration.deleted.graph.Adj :=
        configuration.deleted.decideAdj
      exact completion.q.path.1.length + 1) := by
  let configuration := request.configuration
  letI : FinEnum configuration.deleted.Vertex :=
    configuration.deleted.vertices
  letI : Fintype configuration.deleted.Vertex := by infer_instance
  letI : DecidableEq configuration.deleted.Vertex :=
    configuration.deleted.vertices.decEq
  letI : DecidableRel configuration.deleted.graph.Adj :=
    configuration.deleted.decideAdj
  exact completion.q.accepted

/-- Complete an open request from the target certificate on its strictly
smaller suppressed graph.  All orientation and path choices are internal. -/
noncomputable def complete
    (request : OpenSuppressionRequest port shoulders selectedReturn)
    (cycle :
      CycleCertificate request.configuration.suppressed LengthOK) :
    Completion request := by
  classical
  let configuration := request.configuration
  have uses :=
    configuration.cycle_uses_shoulder ctx.avoids cycle
  let reconstructed :=
    configuration.reconstructPath cycle uses
  let candidate :
      configuration.deleted.graph.Path
        configuration.leftVertex configuration.rightVertex :=
    ⟨reconstructed.path, reconstructed.isPath⟩
  letI : FinEnum configuration.deleted.Vertex :=
    configuration.deleted.vertices
  letI : Fintype configuration.deleted.Vertex := by infer_instance
  letI : DecidableEq configuration.deleted.Vertex :=
    configuration.deleted.vertices.decEq
  letI : DecidableRel configuration.deleted.graph.Adj :=
    configuration.deleted.decideAdj
  let q :=
    CanonicalAcceptedPath.selectOfAcceptedPath
      configuration.deleted.graph
      (fun path => LengthOK (path.1.length + 1))
      candidate reconstructed.restored_length_ok
  exact {
    cycle := cycle
    uses_shoulder := uses
    reconstructed := reconstructed
    q := q
  }

/-- Generic minimality adapter.  The executor supplies the baseline proof for
the graph produced by this official operation; no application supplies a
cycle or chooses a response branch. -/
noncomputable def completeOfBaseline
    (request : OpenSuppressionRequest port shoulders selectedReturn)
    (suppressedBaseline : Baseline request.configuration.suppressed) :
    Completion request := by
  let target :=
    ctx.target_of_smaller
      request.configuration.lexicographicallySmaller
      suppressedBaseline
  exact complete request target.some

end OpenSuppressionRequest

namespace DeclaredSupport

/-- Exact open response carrier `Gamma`: the canonical return carrier united
with the ambient image of the canonical deleted-vertex path `Q`. -/
noncomputable def openResponse
    {port : Port (profile := profile) (ctx := ctx)}
    {shoulders : CanonicalShoulders port}
    {selectedReturn : CanonicalReturn port shoulders}
    (request : OpenSuppressionRequest port shoulders selectedReturn)
    (completion : request.Completion) :
    DeclaredSupport ctx.G := by
  classical
  let configuration := request.configuration
  letI : FinEnum ctx.G.Vertex := ctx.G.vertices
  letI : Fintype ctx.G.Vertex := by infer_instance
  letI : DecidableEq ctx.G.Vertex := ctx.G.vertices.decEq
  letI : DecidableRel
      (CanonicalExcessPortActivation.deletedGraph port).Adj :=
    Classical.decRel _
  letI : FinEnum configuration.deleted.Vertex :=
    configuration.deleted.vertices
  letI : Fintype configuration.deleted.Vertex := by infer_instance
  letI : DecidableEq configuration.deleted.Vertex :=
    configuration.deleted.vertices.decEq
  letI : DecidableRel configuration.deleted.graph.Adj :=
    configuration.deleted.decideAdj
  exact ⟨selectedReturn.selected.path.1.support.toFinset ∪
    completion.q.path.1.support.toFinset.image Subtype.val⟩

end DeclaredSupport

/-- Graph-derived local response before the executor invokes minimality on an
open suppression.  The open constructor contains a complete official request,
not a caller callback or outcome. -/
inductive LocalResponse
    (port : Port (profile := profile) (ctx := ctx)) where
  | bridge
      (obstruction :
        ctx.G.graph.IsBridge s(port.center, port.endpoint))
  | open
      (endpointTight :
        ctx.G.degree port.endpoint = profile.threshold)
      (shoulders : CanonicalShoulders port)
      (selectedReturn : CanonicalReturn port shoulders)
      (request :
        OpenSuppressionRequest port shoulders selectedReturn)
  | triangular
      (endpointTight :
        ctx.G.degree port.endpoint = profile.threshold)
      (shoulders : CanonicalShoulders port)
      (selectedReturn : CanonicalReturn port shoulders)
      (shoulder_adjacent :
        ctx.G.graph.Adj shoulders.left shoulders.right)

/-- Exhaustive local executor.  Bridge/open/triangle is decided from the
literal graph, while both shoulders and the return path come from official
finite schedules. -/
noncomputable def executePort
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3)
    (port : Port (profile := profile) (ctx := ctx)) :
    LocalResponse port := by
  classical
  cases CanonicalExcessPortActivation.activate criticality port with
  | bridge obstruction =>
      exact .bridge obstruction
  | active endpointTight witness =>
      let shoulders :=
        deriveShoulders threshold_eq_three port endpointTight
      let selectedReturn :=
        canonicalReturn port shoulders witness
      by_cases shoulderAdjacent :
          ctx.G.graph.Adj shoulders.left shoulders.right
      · exact .triangular endpointTight shoulders selectedReturn
          shoulderAdjacent
      · exact .open endpointTight shoulders selectedReturn
          ⟨shoulderAdjacent⟩

/-- The exact response carrier in the triangular branch. -/
def LocalResponse.triangularSupport
    {port : Port (profile := profile) (ctx := ctx)}
    (response : LocalResponse port) :
    Option (DeclaredSupport ctx.G) :=
  match response with
  | .triangular _ shoulders selectedReturn shoulderAdjacent =>
      some (DeclaredSupport.triangle port shoulders selectedReturn
        shoulderAdjacent)
  | _ => none

/-- Full response schedule in the exact excess-port order. -/
noncomputable def executeFamily
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3) :
    List (Σ port : Port (profile := profile) (ctx := ctx),
      LocalResponse port) :=
  (ExcessPortExtraction.ports profile ctx.G).map fun port =>
    ⟨port, executePort criticality threshold_eq_three port⟩

/-- The completed local schedule has exactly one row per degree-surplus unit. -/
theorem executeFamily_length
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3) :
    (executeFamily criticality threshold_eq_three).length =
      (DegreeSurplusLedger.derive ctx.G
        (ExcessPortExtraction.surplusBaseline
          (profile := profile) ctx)).total := by
  rw [executeFamily, List.length_map]
  exact ExcessPortExtraction.ports_length_eq_total_surplus ctx

/-- Semantic adapter from the threshold consequence already proved by Graph
to the problem's registered baseline.  For the Universal closed
minimum-degree baseline this is the identity implication. -/
def BaselineFromThreshold
    (profile : DeletionCriticalityProfile Baseline) : Prop :=
  ∀ object : FiniteObject,
    profile.threshold ≤ object.minDegree → Baseline object

/-- Fully completed open response.  The private constructor pins `T` and
`Gamma` to their framework definitions, so neither support can be replaced by
an application. -/
structure CompletedOpenResponse
    (port : Port (profile := profile) (ctx := ctx)) where
  private mk ::
  endpointTight :
    ctx.G.degree port.endpoint = profile.threshold
  shoulders : CanonicalShoulders port
  selectedReturn : CanonicalReturn port shoulders
  request :
    OpenSuppressionRequest port shoulders selectedReturn
  completion : request.Completion
  portSupport : DeclaredSupport ctx.G
  portSupport_eq :
    portSupport = DeclaredSupport.port port shoulders
  responseSupport : DeclaredSupport ctx.G
  responseSupport_eq :
    responseSupport =
      DeclaredSupport.openResponse request completion

/-- Fully completed triangular response, including the literal three-cycle and
the exact finite `T` and `Gamma` carriers. -/
structure CompletedTriangularResponse
    (port : Port (profile := profile) (ctx := ctx)) where
  private mk ::
  endpointTight :
    ctx.G.degree port.endpoint = profile.threshold
  shoulders : CanonicalShoulders port
  selectedReturn : CanonicalReturn port shoulders
  shoulderAdjacent :
    ctx.G.graph.Adj shoulders.left shoulders.right
  triangle :
    CycleCertificate ctx.G (fun length => length = 3)
  triangle_eq :
    triangle = triangleCertificate port shoulders shoulderAdjacent
  portSupport : DeclaredSupport ctx.G
  portSupport_eq :
    portSupport = DeclaredSupport.port port shoulders
  responseSupport : DeclaredSupport ctx.G
  responseSupport_eq :
    responseSupport =
      DeclaredSupport.triangle port shoulders selectedReturn
        shoulderAdjacent

/-- Exhaustive completed response for one canonical excess-port row. -/
inductive CompletedLocalResponse
    (port : Port (profile := profile) (ctx := ctx)) where
  | bridge
      (obstruction :
        ctx.G.graph.IsBridge s(port.center, port.endpoint))
  | open (response : CompletedOpenResponse port)
  | triangular (response : CompletedTriangularResponse port)

/-- Complete one local response.  In the open branch Graph proves the
threshold baseline on the suppressed graph; `baselineFromThreshold` merely
re-expresses that theorem in the problem's registered baseline predicate. -/
noncomputable def completeResponse
    (baselineFromThreshold : BaselineFromThreshold profile)
    {port : Port (profile := profile) (ctx := ctx)}
    (response : LocalResponse port) :
    CompletedLocalResponse port := by
  classical
  cases response with
  | bridge obstruction =>
      exact .bridge obstruction
  | «open» endpointTight shoulders selectedReturn request =>
      let configuration := request.configuration
      have thresholdBaseline :
          profile.threshold ≤ configuration.suppressed.minDegree :=
        configuration.minimumDegree_preserved profile.threshold
          (profile.degreeLowerBound ctx.baseline)
          port.centerHigh
      have suppressedBaseline : Baseline configuration.suppressed :=
        baselineFromThreshold configuration.suppressed thresholdBaseline
      let completion :=
        request.completeOfBaseline suppressedBaseline
      exact .open {
        endpointTight := endpointTight
        shoulders := shoulders
        selectedReturn := selectedReturn
        request := request
        completion := completion
        portSupport := DeclaredSupport.port port shoulders
        portSupport_eq := rfl
        responseSupport :=
          DeclaredSupport.openResponse request completion
        responseSupport_eq := rfl
      }
  | triangular endpointTight shoulders selectedReturn shoulderAdjacent =>
      exact .triangular {
        endpointTight := endpointTight
        shoulders := shoulders
        selectedReturn := selectedReturn
        shoulderAdjacent := shoulderAdjacent
        triangle :=
          triangleCertificate port shoulders shoulderAdjacent
        triangle_eq := rfl
        portSupport := DeclaredSupport.port port shoulders
        portSupport_eq := rfl
        responseSupport :=
          DeclaredSupport.triangle port shoulders selectedReturn
            shoulderAdjacent
        responseSupport_eq := rfl
      }

/-- Complete every row of the canonical excess-port family. -/
private noncomputable def completeFamily
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3)
    (baselineFromThreshold : BaselineFromThreshold profile) :
    List (Σ port : Port (profile := profile) (ctx := ctx),
      CompletedLocalResponse port) :=
  (executeFamily criticality threshold_eq_three).map fun row =>
    ⟨row.1, completeResponse baselineFromThreshold row.2⟩

/-- Framework-owned provenance package for a completed response family.
`rows_eq` pins every completed row to the corresponding row of the canonical
excess-port schedule; in particular an application cannot insert, remove, or
replace a port while retaining this certificate. -/
structure CompletedFamily
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3)
    (baselineFromThreshold : BaselineFromThreshold profile) where
  rows : List (Σ port : Port (profile := profile) (ctx := ctx),
    CompletedLocalResponse port)
  rows_eq :
    rows = (ExcessPortExtraction.ports profile ctx.G).map fun port =>
      ⟨port, completeResponse baselineFromThreshold
        (executePort criticality threshold_eq_three port)⟩

/-- Certified framework-owned view of the completed canonical schedule. -/
noncomputable def completedFamily
    (criticality : DeletionCriticalityCertificate profile ctx)
    (threshold_eq_three : profile.threshold = 3)
    (baselineFromThreshold : BaselineFromThreshold profile) :
    CompletedFamily criticality threshold_eq_three baselineFromThreshold where
  rows := completeFamily criticality threshold_eq_three baselineFromThreshold
  rows_eq := by
    simp only [completeFamily, executeFamily, List.map_map,
      Function.comp_def]

theorem CompletedFamily.port_mem_extracted
    {criticality : DeletionCriticalityCertificate profile ctx}
    {threshold_eq_three : profile.threshold = 3}
    {baselineFromThreshold : BaselineFromThreshold profile}
    (family : CompletedFamily criticality threshold_eq_three
      baselineFromThreshold)
    (row : Σ port : Port (profile := profile) (ctx := ctx),
      CompletedLocalResponse port)
    (member : row ∈ family.rows) :
    row.1 ∈ ExcessPortExtraction.ports profile ctx.G := by
  rw [family.rows_eq] at member
  obtain ⟨port, portMember, equality⟩ := List.mem_map.mp member
  have firstEquality : port = row.1 := by
    exact congrArg Sigma.fst equality
  exact firstEquality ▸ portMember

/-- Node `[129]` cardinality interface: the fully completed family has exactly
one response for each table-derived degree-surplus unit. -/
theorem CompletedFamily.rows_length
    {criticality : DeletionCriticalityCertificate profile ctx}
    {threshold_eq_three : profile.threshold = 3}
    {baselineFromThreshold : BaselineFromThreshold profile}
    (family : CompletedFamily criticality threshold_eq_three
      baselineFromThreshold) :
    family.rows.length =
      (DegreeSurplusLedger.derive ctx.G
        (ExcessPortExtraction.surplusBaseline
          (profile := profile) ctx)).total := by
  rw [family.rows_eq, List.length_map]
  simpa [executeFamily] using
    executeFamily_length criticality threshold_eq_three

end Hypostructure.Graph.Strategy.Official.Features.CanonicalDegreeThreePortResponse
