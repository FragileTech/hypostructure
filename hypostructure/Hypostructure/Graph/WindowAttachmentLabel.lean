import Hypostructure.Graph.InducedPathMaximalPacking
import Hypostructure.Graph.RootedReturn
import Hypostructure.Graph.TargetClosure
import Hypostructure.Graph.TypeBClosure
import Hypostructure.Graph.WindowCurvatureAlgebra

/-!
# Attachment labels of an induced window, and their legality

This file connects the `P₁₃` curvature algebra of
`Graph/WindowCurvatureAlgebra.lean` to the residual's own object.

`original_erdos_64_proof.tex`, *The `P₁₃` curvature algebra*:

> Let `P = v₀v₁⋯v₁₂` be an induced `P₁₃`.  An outside vertex `x` has attachment
> label `S(x) = {i : x vᵢ ∈ E(G)} ⊆ {0, 1, …, 12}`.

`attachmentLabel` is that set, taken against the window embedding the packing
already carries (`InducedPathMaximalPacking.Window`), so a label is a set of
coordinates *of an actual window of the residual's object* and not a free
symbol.

The manuscript's justification of legality is then a construction, and it is
performed here:

> if `x` is adjacent to `vᵢ` and `vⱼ` with `i < j`, then the subpath
> `vᵢ v_{i+1} ⋯ vⱼ` of `P`, which has length `j - i`, together with the two
> edges `x vᵢ` and `x vⱼ` forms a cycle of length `(j - i) + 2`.

`windowSegment` is that subpath, `attachmentCycleCertificate` is that cycle, and
`attachmentLabel_safe` is the consequence: **on a target-avoiding object every
attachment label is legal**, because a non-legal one would exhibit an accepted
dyadic cycle.  The target-avoidance is not restated as a hypothesis of the
theory; it is read from the residual, and `attachmentLabelSafeQuery` is that
read, expressed with `Core.Residual.Query.map` and nothing else.

Nothing is reconstructed: the closing cycle is `Graph.TypeBClosure`'s
`attachmentCertificate`, the target is `Graph.HasCycleWithLength` at the
registered `Core.DyadicLength.PowerOfTwoLength`, and the avoidance record is
`Graph.TargetClosure.AvoidsTarget`.

## What is retrieved

* the window -- `Graph.InducedPathMaximalPacking.Window` at
  `Graph/InducedPathMaximalPacking.lean:19`, and its `support` at `:37`;
* the window-segment construction -- `Graph.InducedPathCold.windowSegment` at
  `Graph/InducedPathCold.lean:1072`;
* the closing cycle -- `Graph.TypeBClosure.attachmentCertificate` at
  `Graph/TypeBClosure.lean:153`;
* the tester -- `Graph.EdgeRootedReturn` at `Graph/RootedReturn.lean:35`,
  `hasCycleWithLength_powerOfTwoLength_iff_hasMersenneCompletion` at `:289` and
  `not_hasMersenneCompletion_of_avoids` at `:317`, whose shift already *is*
  `Core.DyadicLength.MersenneLength` (`shiftedCycleLength_powerOfTwoLength` at
  `:269`).  No tester is defined here;
* target avoidance -- `Graph.TargetClosure.AvoidsTarget` at
  `Graph/TargetClosure.lean:18` (`Core.Closure.TargetAvoidance` at
  `Core/Closure.lean:173`), read with `Core.Residual.Query.map` at
  `Core/Residual/Query.lean:60` following
  `Graph.RootedReturnTargetAlgebra.focusedAvoidanceNotTargetQuery` at
  `Graph/RootedReturn.lean:417`.  It is never a hypothesis of the theory.
-/

namespace Hypostructure.Graph.WindowCurvature

open Hypostructure.Core.DyadicLength

universe u v

/-! ## The subpath of a window between two of its coordinates -/

/-- The ascending segment of the path graph: from coordinate `start` forward by
`steps` steps.

*Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`, which maps a path-graph walk through the
same window embedding; this version retains the exact length and simplicity
that construction discards.
-/
def pathGraphSegment (order start : Nat) (below : start < order) :
    (steps : Nat) → (bound : start + steps < order) →
      (SimpleGraph.pathGraph order).Walk ⟨start, below⟩ ⟨start + steps, bound⟩
  | 0, _ => SimpleGraph.Walk.nil
  | steps + 1, bound =>
      (pathGraphSegment order start below steps (by omega)).concat
        (by rw [SimpleGraph.pathGraph_adj]; exact Or.inl rfl)

/-- *Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`. -/
theorem pathGraphSegment_length (order start : Nat) (below : start < order) :
    ∀ (steps : Nat) (bound : start + steps < order),
      (pathGraphSegment order start below steps bound).length = steps
  | 0, _ => rfl
  | steps + 1, bound => by
      rw [pathGraphSegment, SimpleGraph.Walk.length_concat,
        pathGraphSegment_length order start below steps]

/-- *Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`. -/
theorem pathGraphSegment_support (order start : Nat) (below : start < order) :
    ∀ (steps : Nat) (bound : start + steps < order) (vertex : Fin order),
      vertex ∈ (pathGraphSegment order start below steps bound).support →
        start ≤ vertex.1 ∧ vertex.1 ≤ start + steps
  | 0, _, vertex, member => by
      rw [pathGraphSegment] at member
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at member
      subst member
      exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  | steps + 1, bound, vertex, member => by
      rw [pathGraphSegment, SimpleGraph.Walk.support_concat,
        List.mem_append] at member
      rcases member with inner | last
      · have := pathGraphSegment_support order start below steps _ vertex inner
        omega
      · simp only [List.mem_singleton] at last
        subst last
        exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-- *Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`. -/
theorem pathGraphSegment_isPath (order start : Nat) (below : start < order) :
    ∀ (steps : Nat) (bound : start + steps < order),
      (pathGraphSegment order start below steps bound).IsPath
  | 0, _ => by rw [pathGraphSegment]; exact SimpleGraph.Walk.IsPath.nil
  | steps + 1, bound => by
      rw [SimpleGraph.Walk.isPath_def, pathGraphSegment,
        SimpleGraph.Walk.support_concat]
      refine List.Nodup.append
        ((pathGraphSegment_isPath order start below steps _).support_nodup)
        (by simp) ?_
      intro vertex inner last
      simp only [List.mem_singleton] at last
      subst last
      have bounds := pathGraphSegment_support order start below steps _ _ inner
      have contradiction : start + (steps + 1) ≤ start + steps := bounds.2
      omega

/-- **The manuscript's subpath `vᵢ v_{i+1} ⋯ vⱼ`.**  The segment of an induced
window between two of its coordinates, seen in the ambient object through the
window embedding the packing already carries.

*Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`; consumes
`Graph.InducedPathMaximalPacking.Window` at
`Graph/InducedPathMaximalPacking.lean:19`.
-/
def windowSegment {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {source target : Fin order} (le : source.1 ≤ target.1) :
    object.graph.Walk (window source) (window target) :=
  ((pathGraphSegment order source.1 source.2 (target.1 - source.1)
      (by omega)).map window.toHom).copy rfl
        (congrArg window (Fin.ext
          (show source.1 + (target.1 - source.1) = target.1 by omega)))

/-- The segment has the manuscript's length `j - i`.

*Provenance.* Follows `Graph.TypeBClosure.attachmentCycle_length` at
`Graph/TypeBClosure.lean:109`.
-/
theorem windowSegment_length {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {source target : Fin order} (le : source.1 ≤ target.1) :
    (windowSegment window le).length = target.1 - source.1 := by
  rw [windowSegment, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map,
    pathGraphSegment_length]

/-- The segment is a simple path: the window is an embedding.

*Provenance.* Follows `Graph.InducedPathCold.windowSegment` at
`Graph/InducedPathCold.lean:1072`.
-/
theorem windowSegment_isPath {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {source target : Fin order} (le : source.1 ≤ target.1) :
    (windowSegment window le).IsPath := by
  rw [windowSegment, SimpleGraph.Walk.isPath_copy]
  exact (SimpleGraph.Walk.map_isPath_iff_of_injective
    (f := window.toHom) window.injective).mpr
      (pathGraphSegment_isPath order source.1 source.2 _ _)

/-- Every vertex of the segment is a coordinate of the window.

*Provenance.* Follows `Graph.InducedPathMaximalPacking.support` at
`Graph/InducedPathMaximalPacking.lean:37`.
-/
theorem windowSegment_support {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {source target : Fin order} (le : source.1 ≤ target.1)
    {vertex : object.Vertex}
    (member : vertex ∈ (windowSegment window le).support) :
    ∃ index : Fin order, vertex = window index := by
  rw [windowSegment, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_map, List.mem_map] at member
  obtain ⟨index, _, equal⟩ := member
  exact ⟨index, equal.symm⟩

/-! ## Attachment labels -/

/-- **The manuscript's attachment label** `S(x) = {i : x vᵢ ∈ E(G)}` of an
outside vertex against one induced window of the residual's object.

*Provenance.* Follows `Graph.InducedPathMaximalPacking.support` at
`Graph/InducedPathMaximalPacking.lean:37`, the same `Finset` over `Fin order`
derived from the window.
-/
def attachmentLabel {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    (outsideVertex : object.Vertex) : Label order := by
  letI := object.decideAdj
  exact Finset.univ.filter fun index =>
    object.graph.Adj outsideVertex (window index)

/-- *Provenance.* Follows `Graph.InducedPathMaximalPacking.support` at
`Graph/InducedPathMaximalPacking.lean:37`. -/
theorem mem_attachmentLabel {object : FiniteObject.{u}} {order : Nat}
    {window : InducedPathMaximalPacking.Window object order}
    {outsideVertex : object.Vertex} {index : Fin order} :
    index ∈ attachmentLabel window outsideVertex ↔
      object.graph.Adj outsideVertex (window index) := by
  letI := object.decideAdj
  simp [attachmentLabel, Finset.mem_filter]

/-! ## The closing cycle -/

/-- **The manuscript's closing cycle.**  An outside vertex adjacent to two
coordinates `i < j` of an induced window closes the subpath between them into a
simple cycle of length `(j - i) + 2`.  The cycle itself is
`Graph.TypeBClosure.attachmentCycle`; nothing new is built here.

*Provenance.* Consumes `Graph.TypeBClosure.attachmentCertificate` at
`Graph/TypeBClosure.lean:153`.
-/
def attachmentCycleCertificate {object : FiniteObject.{u}} {order : Nat}
    {LengthOK : Nat → Prop}
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index)
    {source target : Fin order} (le : source.1 ≤ target.1)
    (distinct : source ≠ target)
    (enter : object.graph.Adj outsideVertex (window source))
    (close : object.graph.Adj outsideVertex (window target))
    (accepted : LengthOK (target.1 - source.1 + 2)) :
    CycleCertificate object LengthOK := by
  refine TypeBClosure.attachmentCertificate (segment := windowSegment window le)
    enter close.symm (windowSegment_isPath window le) ?_ ?_ ?_
  · exact fun equal => distinct (window.injective equal)
  · intro member
    obtain ⟨index, equal⟩ := windowSegment_support window le member
    exact outside index equal
  · rwa [windowSegment_length]

/-! ## Legality on a target-avoiding object

Below, the object and its avoidance are the residual's.  `avoids` is exactly the
field of `Graph.TargetClosure.AvoidsTarget` at the registered dyadic target, so
it arrives from the ledger; see `attachmentLabelSafeQuery`. -/

/-- **The barrier state's own cycle.**  A pair of attachments of one outside
vertex sitting at a forbidden difference exhibits an accepted dyadic cycle
routed through the window: the closing cycle of the manuscript's own sentence,
at the registered target.

*Provenance.* Consumes `Graph.TypeBClosure.attachmentCertificate` at
`Graph/TypeBClosure.lean:153` (through `attachmentCycleCertificate` above).
-/
def forbiddenCycleCertificate {object : FiniteObject.{u}} {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index)
    {source target : Fin order}
    (memSource : source ∈ attachmentLabel window outsideVertex)
    (memTarget : target ∈ attachmentLabel window outsideVertex)
    (le : source.1 ≤ target.1)
    (forbidden : ForbiddenGap 0 (Nat.dist source.1 target.1)) :
    CycleCertificate object PowerOfTwoLength := by
  rw [ForbiddenGap, closingLength] at forbidden
  have distinct : source ≠ target := by
    rintro rfl
    rw [Nat.dist_self] at forbidden
    exact absurd forbidden (by decide)
  have accepted : PowerOfTwoLength (target.1 - source.1 + 2) := by
    have equal : 0 + 2 + Nat.dist source.1 target.1 = target.1 - source.1 + 2 := by
      unfold Nat.dist
      omega
    rwa [equal] at forbidden
  exact attachmentCycleCertificate window outside le distinct
    (mem_attachmentLabel.mp memSource) (mem_attachmentLabel.mp memTarget)
    accepted

/-- **The tester of `lem:p13-window-package`, at one window.**

> At each remaining scale, the target tester is the corresponding edge-rooted
> Mersenne completion through the window.  The relations `C_a, C_b, C_{a+b}`
> were defined precisely so that changing the barrier state changes that
> tester.

For the single-vertex barrier state this is exactly the statement below: a
label pair violating `C₀` produces an **edge-rooted Mersenne completion**, the
tester `Graph.RootedReturn` already owns.  Nothing new is defined here -- the
identification of the dyadic cycle target with the Mersenne completion is
`hasCycleWithLength_powerOfTwoLength_iff_hasMersenneCompletion`, and the shift
is `MersenneLength` definitionally.

*Provenance.* Consumes
`Graph.hasCycleWithLength_powerOfTwoLength_iff_hasMersenneCompletion` at
`Graph/RootedReturn.lean:289`, whose shift is
`Core.DyadicLength.MersenneLength` definitionally by
`Graph.shiftedCycleLength_powerOfTwoLength` at `Graph/RootedReturn.lean:269`.
-/
theorem hasMersenneCompletion_of_forbidden {object : FiniteObject.{u}}
    {order : Nat}
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index)
    {source target : Fin order}
    (memSource : source ∈ attachmentLabel window outsideVertex)
    (memTarget : target ∈ attachmentLabel window outsideVertex)
    (le : source.1 ≤ target.1)
    (forbidden : ForbiddenGap 0 (Nat.dist source.1 target.1)) :
    HasEdgeRootedReturn object MersenneLength :=
  (hasCycleWithLength_powerOfTwoLength_iff_hasMersenneCompletion object).mp
    ⟨forbiddenCycleCertificate window outside memSource memTarget le forbidden⟩

/-- One half of the safety argument: a forbidden difference realized by an
ascending pair of attachments closes an accepted cycle, which the residual's
retained avoidance -- read here through the tester's negative answer at every
oriented edge -- forbids.

*Provenance.* Consumes `Graph.not_hasMersenneCompletion_of_avoids` at
`Graph/RootedReturn.lean:317`.
-/
theorem not_forbiddenGap_of_le {object : FiniteObject.{u}} {order : Nat}
    (avoids : ¬ HasCycleWithLength PowerOfTwoLength object)
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index)
    {source target : Fin order}
    (memSource : source ∈ attachmentLabel window outsideVertex)
    (memTarget : target ∈ attachmentLabel window outsideVertex)
    (le : source.1 ≤ target.1) :
    ¬ ForbiddenGap 0 (Nat.dist source.1 target.1) := fun forbidden =>
  not_hasMersenneCompletion_of_avoids object avoids
    (hasMersenneCompletion_of_forbidden window outside memSource memTarget le
      forbidden)

/-- **The bridge to the residual's object.**  On an object that avoids the
registered dyadic cycle target, the attachment label of any outside vertex
against any induced window satisfies the manuscript's safety relation at outside
length zero -- a violating pair would close a power-of-two cycle through the
window, which the residual's retained avoidance forbids.

*Provenance.* Consumes `not_forbiddenGap_of_le` above.
-/
theorem attachmentLabel_safe {object : FiniteObject.{u}} {order : Nat}
    (avoids : ¬ HasCycleWithLength PowerOfTwoLength object)
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index) :
    Safe 0 (attachmentLabel window outsideVertex)
      (attachmentLabel window outsideVertex) := by
  intro source memSource target memTarget forbidden
  rcases Nat.le_total source.1 target.1 with le | le
  · exact not_forbiddenGap_of_le avoids window outside memSource memTarget le
      forbidden
  · refine not_forbiddenGap_of_le avoids window outside memTarget memSource le ?_
    rwa [Nat.dist_comm] at forbidden

/-- **The attachment label of an outside vertex is legal.**  This is the
manuscript's `Labels` membership, stated on the residual's object.  The
nonemptiness side is the manuscript's own scoping of legality ("a *nonempty*
label `S` is legal if …"); the mathematical content is `attachmentLabel_safe`.

*Provenance.* Consumes `attachmentLabel_safe` above and
`WindowCurvature.mem_Labels`.
-/
theorem attachmentLabel_mem_Labels {object : FiniteObject.{u}} {order : Nat}
    (avoids : ¬ HasCycleWithLength PowerOfTwoLength object)
    (window : InducedPathMaximalPacking.Window object order)
    {outsideVertex : object.Vertex}
    (outside : ∀ index : Fin order, outsideVertex ≠ window index)
    (attached : (attachmentLabel window outsideVertex).Nonempty) :
    attachmentLabel window outsideVertex ∈ Labels order :=
  mem_Labels.mpr ⟨attached, attachmentLabel_safe avoids window outside⟩

/-! ## Retrieval

Legality is not a hypothesis of the theory and not a new capability: it is a
transformation of the target-avoidance the residual already carries.  The
transformation is `Core.Residual.Query.map`, so the fact travels on the ledger
and nothing here holds data. -/

/-- Read the legality of every attachment label of the active object off the
residual's retained target avoidance.

*Provenance.* Follows
`Graph.RootedReturnTargetAlgebra.focusedAvoidanceNotTargetQuery` at
`Graph/RootedReturn.lean:417`; consumes `Core.Residual.Query.map` at
`Core/Residual/Query.lean:60` and `Graph.TargetClosure.AvoidsTarget` at
`Graph/TargetClosure.lean:18` (`Core.Closure.TargetAvoidance` at
`Core/Closure.lean:173`).
-/
def attachmentLabelSafeQuery {Stage : Sort v}
    (activeObject : Core.Residual.Query Stage fun _ => FiniteObject.{u})
    (avoidance : Core.Residual.Query Stage fun stage =>
      TargetClosure.AvoidsTarget (HasCycleWithLength PowerOfTwoLength)
        (activeObject stage)) :
    Core.Residual.Query Stage fun stage =>
      ∀ (order : Nat)
        (window : InducedPathMaximalPacking.Window (activeObject stage) order)
        (outsideVertex : (activeObject stage).Vertex),
        (∀ index : Fin order, outsideVertex ≠ window index) →
          Safe 0 (attachmentLabel window outsideVertex)
            (attachmentLabel window outsideVertex) :=
  avoidance.map fun _stage record _order window _outsideVertex outside =>
    attachmentLabel_safe record.avoids window outside

/-- The same read, delivered as `Labels` membership for the outside vertices
that actually attach.

*Provenance.* Follows
`Graph.RootedReturnTargetAlgebra.focusedAvoidanceNotTargetQuery` at
`Graph/RootedReturn.lean:417`; consumes `Core.Residual.Query.map` at
`Core/Residual/Query.lean:60`.
-/
def attachmentLabelLegalQuery {Stage : Sort v}
    (activeObject : Core.Residual.Query Stage fun _ => FiniteObject.{u})
    (avoidance : Core.Residual.Query Stage fun stage =>
      TargetClosure.AvoidsTarget (HasCycleWithLength PowerOfTwoLength)
        (activeObject stage)) :
    Core.Residual.Query Stage fun stage =>
      ∀ (order : Nat)
        (window : InducedPathMaximalPacking.Window (activeObject stage) order)
        (outsideVertex : (activeObject stage).Vertex),
        (∀ index : Fin order, outsideVertex ≠ window index) →
          (attachmentLabel window outsideVertex).Nonempty →
            attachmentLabel window outsideVertex ∈ Labels order :=
  avoidance.map fun _stage record _order window _outsideVertex outside attached =>
    attachmentLabel_mem_Labels record.avoids window outside attached

end Hypostructure.Graph.WindowCurvature
