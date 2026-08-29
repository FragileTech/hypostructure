import Hypostructure.Graph.BlockedClass
import Hypostructure.Graph.WindowLabelCollision
import Hypostructure.Core.Finite.CertifiedTableAggregation

/-!
# The `[18]` label algebra with responses on skeletons (nodes `[170]`--`[172]`)

`lem:scale-additivity` reads, for a graph `H ∈ 𝓑(𝒫)`, a scale `2^j` and a
barrier `(a,b)`, the *`(a,b)`-barrier state of a window `P` at scale `2^j`*: the
triple `(S,A,T)` of labels of `P` and of the two windows reached from it by
outside paths of lengths `a` and `b`, read together with the edge-rooted
Mersenne completion of `P` at that scale.  `def:barrier-overlap-system` fixes
the completion support of that reading, and `lem:blocked-graphs-compress`
encodes `H` as (outside edges, all barrier states), paying
`log₂ W_{a,b} − γ_{a,b}` bits per coordinate instead of `log₂ W_{a,b}`.

This module builds exactly that object and the counting it feeds:

* `WindowLabelCollision.attachmentLabel` -- `app:curv-code`'s label in the
  induced-path order retained by the completion support;
* `CompletionSupport` -- `def:barrier-overlap-system`'s canonical edge-rooted
  completion at a scale, for a packed window `P`: the two *outside* arms of
  lengths `a` and `b`, their first and last window incidences, and the
  completion closing them at the tested scale, which is the edge-rooted
  Mersenne completion *through* `P` (`lem:p13-window-package`: "at each
  remaining scale, the target tester is the corresponding edge-rooted Mersenne
  completion through the window"), so the window segments it uses belong to the
  support and it carries no avoidance constraint;
* `barrierState` -- the `(S,A,T)` triple of the canonical completion, a
  *function* of the labelled skeleton (the manuscript's deterministic
  tie-breaking rule);
* `outsideEdges` and `code` -- the encoding map whose conditional fibres
  `lem:scale-additivity` bounds, one exposure coordinate per window per scale.

The certified table counts present safe/flat triples.  The distinguished
`none` state is retained separately by the strategy's auxiliary state-fibre
bound; it is not added to the paper's `W_{a,b}` or `F_{a,b}` ratio and is never
conflated with an illegal empty label.
No numeral, rate, scale count or density constant occurs in this file.
-/

namespace Hypostructure.Graph.BarrierSystem

open Hypostructure
open scoped BigOperators

universe u v

/-! ## The label algebra on a labelled skeleton -/

variable {n : Nat}

/-- **`def:barrier-overlap-system`'s completion support** at a scale, for a
packed window `P`: "the canonical simple edge-rooted completion used to test its
`(a,b)`-barrier state at scale `2^j`, including the two outside arms, their
first and last window incidences, and every window segment used by the
completion".

The two arms are *outside* paths -- they meet no window interior, and their
endpoints are the window incidences whose labels the barrier state reads.  The
completion is the other half of the definition: by `lem:p13-window-package`
"at each remaining scale, the target tester is the corresponding edge-rooted
Mersenne completion through the window", so it runs through `P` and the window
segments it uses are part of the support.  It therefore carries no avoidance
constraint -- forbidding it the windows would make the tester blind to exactly
the cycles `def:blocked-class` blocks. -/
structure CompletionSupport (order : Nat) (H : LabelledOn n)
    (interiors : Finset (Fin n))
    (window : Finset (Fin n)) (left right scale : Nat) : Type where
  /-- The root window in its induced-path order.  Curvature coordinates are
  positions on this path, never ambient vertex-label order. -/
  presentation : TypeBDirectCycle.Presentation H.toFiniteObject order
  presentation_support : presentation.support = window
  presentationInsideInteriors : presentation.support ⊆ interiors
  /-- The root incidence of the first arm. -/
  source : Fin n
  /-- The incidence the first arm reaches. -/
  middle : Fin n
  /-- The incidence the second arm reaches. -/
  target : Fin n
  /-- The first outside arm, of length `a`. -/
  firstArm : H.graph.Walk source middle
  firstArm_length : firstArm.length = left
  firstArm_path : firstArm.IsPath
  /-- The second outside arm, of length `b`. -/
  secondArm : H.graph.Walk middle target
  secondArm_length : secondArm.length = right
  secondArm_path : secondArm.IsPath
  /-- The composed outside arm is simple; separate simplicity does not exclude
  an intersection between its two pieces. -/
  composedArm_path : (firstArm.append secondArm).IsPath
  /-- The edge-rooted completion closing the two arms at the tested scale. -/
  completion : H.graph.Walk target source
  completion_length : left + right + completion.length = scale
  /-- The two arms are outside paths: they meet no window interior. -/
  armsOutside : ∀ vertex ∈ firstArm.support ++ secondArm.support, vertex ∉ interiors
  /-- The three vertices really are window incidences, so their labels are
  nonempty. -/
  sourceIncident :
    (WindowLabelCollision.attachmentLabel presentation source).Nonempty
  middleIncident :
    (WindowLabelCollision.attachmentLabel presentation middle).Nonempty
  targetIncident :
    (WindowLabelCollision.attachmentLabel presentation target).Nonempty
  /-- The completion is the edge-rooted Mersenne completion *through* the
  window: it uses a window segment of `P`. -/
  completionThroughWindow : ∃ vertex ∈ completion.support, vertex ∈ window

/-- **The `(a,b)`-barrier state of a window at a scale**: the triple `(S,A,T)`
of the labels of the canonical completion support's three window incidences.
It is a function of the labelled skeleton -- the support is chosen by the fixed
deterministic rule.  Absence is retained as `none`; it is not confused with an
illegal empty curvature label. -/
noncomputable def barrierState (order : Nat) (H : LabelledOn n)
    (interiors : Finset (Fin n)) (left right scale : Nat)
    (window : Finset (Fin n)) :
    Option (Graph.WindowCurvature.Label order ×
      Graph.WindowCurvature.Label order ×
        Graph.WindowCurvature.Label order) := by
  classical
  exact
    if support : Nonempty
        (CompletionSupport order H interiors window left right scale) then
      some (WindowLabelCollision.attachmentLabel support.some.presentation
          support.some.source,
        WindowLabelCollision.attachmentLabel support.some.presentation
          support.some.middle,
        WindowLabelCollision.attachmentLabel support.some.presentation
          support.some.target)
    else none

/-- The edges of the skeleton outside the window interiors -- the first half of
`lem:blocked-graphs-compress`'s encoding. -/
noncomputable def outsideEdges (H : LabelledOn n) (interiors : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter fun edge =>
    edge ∈ H.graph.edgeSet ∧ ¬ ∀ vertex ∈ edge, vertex ∈ interiors

/-- The barrier states of one window at one scale: one `(S,A,T)` triple per
certified barrier row. -/
abbrev RowStates (order : Nat) (Row : Type v) : Type v :=
  Row → Option (Graph.WindowCurvature.Label order ×
    Graph.WindowCurvature.Label order × Graph.WindowCurvature.Label order)

/-- The exposure coordinates of `lem:blocked-graphs-compress`: one per window
per selected scale. -/
abbrev Coordinate (windows : Finset (Finset (Fin n))) (scales : Nat) : Type :=
  {window // window ∈ windows} × Fin scales

/-- **The encoding of `lem:blocked-graphs-compress`**: a labelled skeleton is
recorded as its outside edges together with, for every window and every
selected scale, the barrier states of the whole certified barrier list.  The
barrier `(a,b)` of a row is that row's own leg pair, so no barrier is named
here. -/
noncomputable def code (order : Nat) (windows : Finset (Finset (Fin n)))
    (scales : Nat) {Row : Type v} (legs : Row → Nat × Nat) (H : LabelledOn n) :
    Finset (Sym2 (Fin n)) × (Coordinate windows scales → RowStates order Row) :=
  (outsideEdges H (windows.biUnion id),
    fun coordinate row =>
      barrierState order H (windows.biUnion id) (legs row).1 (legs row).2
        (2 ^ (coordinate.2 : Fin scales).1) coordinate.1.1)

/-- **`def:barrier-overlap-system`'s conditional fibre.**  "Fix a separated scale
`2^j`, a barrier `(a,b)`, the edges outside the window interiors, and all barrier
states exposed before `(j,a,b)` in the canonical encoding order": conditional on
exactly that prefix, this is the set of states the coordinate takes on the
class.  `rank` is the canonical encoding order — scale by scale, window by
window. -/
def ConditionalFibre {Class : Type*} {Out : Type*} {Coordinate : Type*} {State : Type*}
    (code : Class → Out × (Coordinate → State)) (rank : Coordinate → Nat)
    (member₀ : Class) (coordinate : Coordinate) : Set State :=
  {state | ∃ member : Class,
    (code member).1 = (code member₀).1 ∧
      (∀ other : Coordinate, rank other < rank coordinate →
        (code member).2 other = (code member₀).2 other) ∧
      (code member).2 coordinate = state}

end Hypostructure.Graph.BarrierSystem
