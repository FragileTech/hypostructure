import Hypostructure.Graph.TypeBDirectCycle
import Hypostructure.Graph.WindowCurvatureAlgebra

/-!
# Label collisions at a shared window

`Graph/WindowCurvatureAlgebra.lean` states the manuscript's safety relation

> `C_s(S, T) = 1` if and only if `s + 2 + |i - j| ∉ Pow` for all `i ∈ S`,
> `j ∈ T`

but nothing in the tree turned a *failure* of that relation into the cycle the
relation is about.  This module is that construction, and nothing else.

The picture is the manuscript's own, one step more general than the legality
picture of `lem:labels`.  Two outside vertices `x` and `y` are joined by a
simple path of length `s` avoiding a packed window `P = p₀p₁⋯`; `x` attaches to
`P` at some coordinate `i` and `y` at some coordinate `j`.  Then

  `x — p_i — P — p_j — y — Q — x`

is a simple cycle, and its length is exactly the manuscript's closing length
`s + 2 + |i − j|`.  When that length is accepted by the target, the object has
an accepted cycle.  At `s = 0` -- one outside vertex, `x = y`, `Q` empty -- this
is the legality derivation of `lem:labels` verbatim: "if `x` is adjacent to `vᵢ`
and `vⱼ` with `i < j`, then the subpath `vᵢ⋯vⱼ` together with the two edges
`x vᵢ` and `x vⱼ` forms a cycle of length `(j − i) + 2`".

## What is stated here and what is retrieved

Stated: the attachment label `S(x)` read at a presented window, the cycle shape
this construction closes, and the collision configuration.

Retrieved, never restated:

* the window presentation and its stretches --
  `Graph.TypeBDirectCycle.Presentation` and `Presentation.exists_stretch` at
  `Graph/TypeBDirectCycle.lean:278,387`;
* the closing length `s + 2 + |i − j|` -- `Graph.WindowCurvature.closingLength`
  at `Graph/WindowCurvatureAlgebra.lean:82`;
* the safety relation `C_s` itself -- `Graph.WindowCurvature.Safe` at
  `Graph/WindowCurvatureAlgebra.lean:139`, identified with the collision below
  by `labelCollision_iff_not_safe`, so the alternative this module states *is*
  failure of the manuscript's relation and not a second copy of it;
* the accepted cycle carrier -- `Graph.CycleCertificate` and
  `Graph.HasCycleWithLength` at `Graph/Target.lean:49,57`.

## The one hypothesis

The construction needs the degenerate closure to be rejected: `s = 0` together
with `i = j` is not two attachments but one, and its closing length is
`closingLength 0 0 = 2`.  The manuscript reads the same condition off its own
target -- "as `1 ≤ j − i ≤ 12`, this length lies in `{3, …, 14}`" -- so the
hypothesis is `¬ LengthOK 2` and it is a statement about the registered target,
never about a graph.

Nothing here mentions a manuscript, a numeral, or a fixed target: the window
order, the packing and the accepted lengths are all parameters.
-/

namespace Hypostructure.Graph.WindowLabelCollision

open Hypostructure

universe u

variable {object : FiniteObject.{u}} {order : Nat} {LengthOK : Nat → Prop}

/-! ## The attachment label -/

/-- **`S(x) = {i : x vᵢ ∈ E(G)}`**, the manuscript's attachment label, read at a
presented window.  The object's own decidable adjacency is what makes it a
`Finset`; no enumeration is prescribed. -/
def attachmentLabel (presentation : TypeBDirectCycle.Presentation object order)
    (outside : object.Vertex) : WindowCurvature.Label order :=
  letI : DecidableRel object.graph.Adj := object.decideAdj
  Finset.univ.filter fun index : Fin order =>
    object.graph.Adj outside (presentation.coordinate index.1)

/-- The label is read back as the attachment it records. -/
theorem mem_attachmentLabel
    {presentation : TypeBDirectCycle.Presentation object order}
    {outside : object.Vertex} {index : Fin order} :
    index ∈ attachmentLabel presentation outside ↔
      object.graph.Adj outside (presentation.coordinate index.1) := by
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp only [attachmentLabel, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## The cycle shape

`attachmentCycle` of `Graph/TypeBDirectCycle.lean` closes a window stretch with
a single outside vertex; this is the same shape with the returning edge replaced
by an outside *path*, which is what the relation `C_s` is stated about.  At
`s = 0` the connector is empty and the two shapes coincide. -/

/-- A walk from a vertex to itself that never repeats one is empty. -/
private theorem length_eq_zero_of_loop {vertex : object.Vertex}
    {walk : object.graph.Walk vertex vertex} (path : walk.IsPath) :
    walk.length = 0 := by
  cases walk with
  | nil => rfl
  | cons adjacency rest =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at path
      exact absurd rest.end_mem_support path.2

/-- `x p_i P p_j y Q x`: a window stretch, the two attachment edges, and the
outside connector that returns. -/
def connectorCycle {stretchSource stretchTarget base pivot : object.Vertex}
    (stretch : object.graph.Walk stretchSource stretchTarget)
    (connector : object.graph.Walk pivot base)
    (enter : object.graph.Adj base stretchSource)
    (close : object.graph.Adj stretchTarget pivot) :
    object.graph.Walk base base :=
  SimpleGraph.Walk.cons enter
    (stretch.append (SimpleGraph.Walk.cons close connector))

/-- The closed walk has length `|stretch| + |connector| + 2`, which is the
manuscript's `s + 2 + |i − j|` once the stretch is the window stretch. -/
theorem connectorCycle_length {stretchSource stretchTarget base pivot :
      object.Vertex}
    (stretch : object.graph.Walk stretchSource stretchTarget)
    (connector : object.graph.Walk pivot base)
    (enter : object.graph.Adj base stretchSource)
    (close : object.graph.Adj stretchTarget pivot) :
    (connectorCycle stretch connector enter close).length
      = stretch.length + connector.length + 2 := by
  rw [connectorCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
  omega

/-- **The closed walk is a simple cycle.**

Both pieces are paths and they are vertex-disjoint, which is what a window
stretch and an outside connector avoiding the window are.  The only degenerate
configuration -- an empty stretch closed by an empty connector -- is excluded by
the length hypothesis, and that is the whole role of `¬ LengthOK 2` downstream. -/
theorem connectorCycle_isCycle {stretchSource stretchTarget base pivot :
      object.Vertex}
    {stretch : object.graph.Walk stretchSource stretchTarget}
    {connector : object.graph.Walk pivot base}
    (enter : object.graph.Adj base stretchSource)
    (close : object.graph.Adj stretchTarget pivot)
    (stretchPath : stretch.IsPath) (connectorPath : connector.IsPath)
    (disjoint : ∀ ⦃z : object.Vertex⦄, z ∈ stretch.support →
      z ∉ connector.support)
    (nondegenerate : 0 < stretch.length + connector.length) :
    (connectorCycle stretch connector enter close).IsCycle := by
  -- The connector's own endpoints are outside the stretch, because they are on
  -- the connector.
  have baseAvoids : base ∉ stretch.support := fun inside =>
    disjoint inside connector.end_mem_support
  have supportEq :
      (stretch.append (SimpleGraph.Walk.cons close connector)).support
        = stretch.support ++ connector.support := by
    rw [SimpleGraph.Walk.support_append]
    simp
  have edgesEq :
      (stretch.append (SimpleGraph.Walk.cons close connector)).edges
        = stretch.edges ++ (s(stretchTarget, pivot) :: connector.edges) := by
    rw [SimpleGraph.Walk.edges_append]
    simp
  rw [connectorCycle, SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def, supportEq]
    refine List.Nodup.append ((SimpleGraph.Walk.isPath_def _).1 stretchPath)
      ((SimpleGraph.Walk.isPath_def _).1 connectorPath) ?_
    intro z left right
    exact disjoint left right
  · rw [edgesEq]
    intro member
    rcases List.mem_append.1 member with inStretch | rest
    · exact baseAvoids
        (SimpleGraph.Walk.fst_mem_support_of_mem_edges stretch inStretch)
    rcases List.mem_cons.1 rest with closingEdge | inConnector
    · rcases Sym2.eq_iff.1 closingEdge with
        ⟨baseIsTarget, -⟩ | ⟨baseIsPivot, sourceIsTarget⟩
      · exact baseAvoids (baseIsTarget ▸ stretch.end_mem_support)
      · -- The one degenerate configuration: both pieces would be loops.
        have connectorLoop : connector.length = 0 := by
          subst baseIsPivot
          exact length_eq_zero_of_loop connectorPath
        have stretchLoop : stretch.length = 0 := by
          subst sourceIsTarget
          exact length_eq_zero_of_loop stretchPath
        omega
    · exact disjoint stretch.start_mem_support
        (SimpleGraph.Walk.snd_mem_support_of_mem_edges connector inConnector)

/-- The closed walk, packaged as a cycle certificate. -/
def connectorCertificate {stretchSource stretchTarget base pivot : object.Vertex}
    {stretch : object.graph.Walk stretchSource stretchTarget}
    {connector : object.graph.Walk pivot base}
    (enter : object.graph.Adj base stretchSource)
    (close : object.graph.Adj stretchTarget pivot)
    (stretchPath : stretch.IsPath) (connectorPath : connector.IsPath)
    (disjoint : ∀ ⦃z : object.Vertex⦄, z ∈ stretch.support →
      z ∉ connector.support)
    (nondegenerate : 0 < stretch.length + connector.length)
    (accepted : LengthOK (stretch.length + connector.length + 2)) :
    CycleCertificate object LengthOK where
  vertex := base
  walk := connectorCycle stretch connector enter close
  isCycle := connectorCycle_isCycle enter close stretchPath connectorPath
    disjoint nondegenerate
  length_ok := by
    rw [connectorCycle_length]
    exact accepted

/-! ## The collision -/

/-- **A shared window violating the legal-label relation `C_s`.**

Two outside vertices attach to one packed window; the simple path joining them
avoids the window; and the closing length their two attachment coordinates
determine is accepted by the target.  `labelCollision_iff_not_safe` is the
statement that this last clause *is* failure of `C_s` at the registered dyadic
target, so nothing here restates the relation.

The connector is a `Walk`, so the `s = 0` case is the single outside vertex of
`lem:labels`: `source = target` and the connector is empty. -/
def LabelCollision (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex)) : Prop :=
  ∃ presentation : TypeBDirectCycle.Presentation object order,
    presentation.support ∈ packing ∧
      ∃ source target : object.Vertex,
        ∃ connector : object.graph.Walk source target,
          connector.IsPath ∧
            (∀ z ∈ connector.support, ∀ t < order,
              z ≠ presentation.coordinate t) ∧
              ∃ sourceIndex ∈ attachmentLabel presentation source,
                ∃ targetIndex ∈ attachmentLabel presentation target,
                  LengthOK (WindowCurvature.closingLength connector.length
                    (Nat.dist sourceIndex.1 targetIndex.1))

/-- No shared window of the packing violates its legal-label relation. -/
def LabelCollisionFree (object : FiniteObject.{u}) (order : Nat)
    (LengthOK : Nat → Prop) (packing : Finset (Finset object.Vertex)) : Prop :=
  ¬ LabelCollision object order LengthOK packing

/-- **The collision clause is exactly `¬ C_s(S, T)`.**

`Graph.WindowCurvature.Safe` is `∀ i ∈ S, ∀ j ∈ T, ¬ ForbiddenGap s |i − j|`,
and `ForbiddenGap` is the registered dyadic target applied to the closing
length.  So the existential clause of `LabelCollision`, read at that target, is
its negation.  This is why the alternative below is the manuscript's own exit
`(3)` and not a surrogate for it. -/
theorem labelCollision_iff_not_safe {shift : Nat}
    {source target : WindowCurvature.Label order} :
    (∃ i ∈ source, ∃ j ∈ target,
        Core.DyadicLength.PowerOfTwoLength
          (WindowCurvature.closingLength shift (Nat.dist i.1 j.1))) ↔
      ¬ WindowCurvature.Safe shift source target := by
  classical
  constructor
  · rintro ⟨i, memI, j, memJ, forbidden⟩ safe
    exact safe i memI j memJ forbidden
  · intro failing
    by_contra missing
    push_neg at missing
    exact failing fun i memI j memJ => missing i memI j memJ

/-- **A label collision at a shared window exhibits an accepted cycle.**

This is the closure the manuscript's exit `(3)` is discharged by: "precisely
failure of the legal `P₁₃` label relation from `lem:labels`; by definition of
the relation, it creates a target event". -/
theorem hasCycleWithLength_of_labelCollision
    {packing : Finset (Finset object.Vertex)}
    (degenerate : ¬ LengthOK 2)
    (collision : LabelCollision object order LengthOK packing) :
    HasCycleWithLength LengthOK object := by
  obtain ⟨presentation, _member, source, target, connector, connectorPath,
    windowFree, sourceIndex, sourceMem, targetIndex, targetMem, accepted⟩ :=
    collision
  have sourceBound : sourceIndex.1 < order := sourceIndex.2
  have targetBound : targetIndex.1 < order := targetIndex.2
  -- The two attachment edges.
  have enter : object.graph.Adj source (presentation.coordinate sourceIndex.1) :=
    mem_attachmentLabel.mp sourceMem
  have exiting :
      object.graph.Adj target (presentation.coordinate targetIndex.1) :=
    mem_attachmentLabel.mp targetMem
  -- The window stretch between the two attachment coordinates.
  obtain ⟨stretch, stretchPath, stretchLength, stretchMember⟩ :=
    TypeBDirectCycle.Presentation.exists_stretch presentation
      (i := sourceIndex.1) (j := targetIndex.1) sourceBound targetBound
  have distEq :
      stretch.length = Nat.dist sourceIndex.1 targetIndex.1 := by
    rw [stretchLength]
    unfold Nat.dist
    omega
  -- The stretch is inside the window and the connector avoids it.
  have disjoint : ∀ ⦃z : object.Vertex⦄, z ∈ stretch.support →
      z ∉ connector.reverse.support := by
    intro z inStretch inConnector
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at inConnector
    obtain ⟨t, _lower, upper, coordinateEq⟩ := stretchMember _ inStretch
    exact windowFree z inConnector t (by omega) coordinateEq
  have reverseLength : connector.reverse.length = connector.length := by
    simp
  -- The degenerate closure is the one the target rejects.
  have nondegenerate :
      0 < stretch.length + connector.reverse.length := by
    by_contra small
    have connectorZero : connector.length = 0 := by omega
    have stretchZero : stretch.length = 0 := by omega
    refine degenerate ?_
    have distZero : Nat.dist sourceIndex.1 targetIndex.1 = 0 := by
      rw [← distEq]; exact stretchZero
    have rewriting :
        WindowCurvature.closingLength connector.length
            (Nat.dist sourceIndex.1 targetIndex.1) = 2 := by
      unfold WindowCurvature.closingLength
      omega
    exact rewriting ▸ accepted
  have acceptedCycle :
      LengthOK (stretch.length + connector.reverse.length + 2) := by
    have lengthEq :
        stretch.length + connector.reverse.length + 2 =
          WindowCurvature.closingLength connector.length
            (Nat.dist sourceIndex.1 targetIndex.1) := by
      rw [reverseLength, distEq]
      unfold WindowCurvature.closingLength
      omega
    rw [lengthEq]
    exact accepted
  exact ⟨connectorCertificate enter exiting.symm stretchPath
    connectorPath.reverse disjoint nondegenerate acceptedCycle⟩

end Hypostructure.Graph.WindowLabelCollision
