import Hypostructure.Core.Strategy.InterfaceReplacement
import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.Progress
import Hypostructure.Graph.SupportComponents

/-!
# Graph specialization of Core interface replacement

Only graph semantics are supplied here.  Execution, predecessor retention,
ledger growth, and the three public Strategy names remain Core-owned.
-/

namespace Hypostructure.Graph.Strategy.InterfaceReplacement

open Hypostructure

universe u v

variable (Baseline : FiniteObject.{u} → Prop)
variable (BranchState : FiniteObject.{u} → Type v)
variable (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)

abbrev P := problem Baseline BranchState

noncomputable def assembly :
    Core.AtomContextAssembly
      (P Baseline BranchState)
      (isomorphismEquivalence Baseline BranchState baselineInvariant) where
  Interface := Boundary.{u}
  Site := ProperBoundariedAtom
  interface := fun _object atom => atom.decomposition.interface
  Atom := BoundaryPiece
  Context := OutsideContext
  compatible := fun _piece _outside => True
  atom := fun _object atom => atom.decomposition.piece
  context := fun _object atom => atom.decomposition.outside
  assemble := fun piece outside => glue piece outside
  extractedCompatible := fun _object _site => trivial
  reconstruct := by
    intro object atom
    exact ⟨atom.decomposition.reconstructionIso⟩

/-- Graph boundary-degree profiles instantiate Core's domain-neutral
interface signature.  The minimum-degree threshold is absent: it is read only
when a concrete compression supplies its baseline certificate. -/
noncomputable def profile
    {T : Core.Target (P Baseline BranchState)}
    (targetInvariant :
      Core.TargetInvariant
        (isomorphismEquivalence Baseline BranchState baselineInvariant)
        T.Predicate) :
    Core.Strategy.InterfaceReplacement.Profile
      (P := P Baseline BranchState) (T := T)
      (lexicographicProgress Baseline BranchState) where
  semantics := isomorphismEquivalence Baseline BranchState baselineInvariant
  targetInvariant := targetInvariant
  assembly := assembly Baseline BranchState baselineInvariant
  Signature := fun boundary =>
    ULift.{u + 1, u} (BoundaryDegreeProfile boundary)
  signature := fun piece => ULift.up piece.boundaryDegreeProfile

noncomputable def assemblyWithPresentation
    (Presentation : Type) (presentation : Presentation) :
    Core.AtomContextAssembly
      (problemWithPresentation Baseline BranchState Presentation presentation)
      (isomorphismEquivalenceWithPresentation
        Baseline BranchState Presentation presentation baselineInvariant) where
  Interface := Boundary.{u}
  Site := ProperBoundariedAtom
  interface := fun _object atom => atom.decomposition.interface
  Atom := BoundaryPiece
  Context := OutsideContext
  compatible := fun _piece _outside => True
  atom := fun _object atom => atom.decomposition.piece
  context := fun _object atom => atom.decomposition.outside
  assemble := fun piece outside => glue piece outside
  extractedCompatible := fun _object _site => trivial
  reconstruct := by
    intro object atom
    exact ⟨atom.decomposition.reconstructionIso⟩

noncomputable def profileWithPresentation
    (Presentation : Type) (presentation : Presentation)
    {T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation)}
    (targetInvariant :
      Core.TargetInvariant
        (isomorphismEquivalenceWithPresentation
          Baseline BranchState Presentation presentation baselineInvariant)
        T.Predicate) :
    Core.Strategy.InterfaceReplacement.Profile
      (P := problemWithPresentation
        Baseline BranchState Presentation presentation)
      (T := T)
      (CanonicalProgress.progress
        (P := problemWithPresentation
          Baseline BranchState Presentation presentation)) where
  semantics :=
    isomorphismEquivalenceWithPresentation
      Baseline BranchState Presentation presentation baselineInvariant
  targetInvariant := targetInvariant
  assembly :=
    assemblyWithPresentation Baseline BranchState baselineInvariant
      Presentation presentation
  Signature := fun boundary =>
    ULift.{u + 1, u} (BoundaryDegreeProfile boundary)
  signature := fun piece => ULift.up piece.boundaryDegreeProfile

end Hypostructure.Graph.Strategy.InterfaceReplacement

namespace Hypostructure.Graph.Strategy.InterfaceReplacement.SupportAtom

open Hypostructure
open Hypostructure.Graph

universe u

variable (object : FiniteObject.{u}) (support : Finset object.Vertex)

/-- The literal cut boundary of a retained connected support. -/
def cutBoundary : Finset object.Vertex := by
  letI : DecidableEq object.Vertex := object.vertices.decEq
  exact support.filter fun vertex =>
    (object.orderedNeighbors vertex).any fun neighbor => neighbor ∉ support

@[simp] theorem mem_cutBoundary_iff (vertex : object.Vertex) :
    vertex ∈ cutBoundary object support ↔
      vertex ∈ support ∧
        ∃ neighbor, object.graph.Adj vertex neighbor ∧ neighbor ∉ support := by
  classical
  simp [cutBoundary, FiniteObject.mem_orderedNeighbors_iff]

/-- Exhaustive scope split for a selected support.  Properness is discovered
by Graph; callers cannot choose whether the support is treated as a proper
atom or as the closed ambient carrier. -/
inductive Scope where
  | proper (vertex : object.Vertex) (outside : vertex ∉ support)
  | closed (covers : ∀ vertex, vertex ∈ support)

noncomputable def classifyScope : Scope object support := by
  classical
  by_cases proper : ∃ vertex, vertex ∉ support
  · let vertex := Classical.choose proper
    exact .proper vertex (Classical.choose_spec proper)
  · exact .closed (by
      intro vertex
      by_contra outside
      exact proper ⟨vertex, outside⟩)

abbrev BoundaryVertex :=
  {vertex : object.Vertex // vertex ∈ cutBoundary object support}

abbrev PieceInternal :=
  {vertex : object.Vertex //
    vertex ∈ support ∧ vertex ∉ cutBoundary object support}

abbrev OutsideInternal := {vertex : object.Vertex // vertex ∉ support}

noncomputable def boundary : Boundary.{u} where
  Vertex := BoundaryVertex object support
  vertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex => vertex ∈ cutBoundary object support

/-- Decode a vertex of the atom side back to the ambient graph.  Both
constructors are already ambient vertices carrying a membership proof, so this
is the first projection and nothing is rebuilt. -/
def pieceDecode :
    (boundary object support).Vertex ⊕ PieceInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

def outsideDecode :
    (boundary object support).Vertex ⊕ OutsideInternal object support →
      object.Vertex
  | .inl vertex => vertex.1
  | .inr vertex => vertex.1

noncomputable def piece : BoundaryPiece (boundary object support) where
  Internal := PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧ vertex ∉ cutBoundary object support
  graph := SimpleGraph.comap (pieceDecode object support) object.graph
  decideAdj := Classical.decRel _

/-- The same support's piece with only the edges `retained` owns.

`piece` and `retainedPiece` share a boundary, an internal type and an internal
enumeration; **only the owned graph varies**.  That is what makes two readings
of one support comparable: `Response.ContextEquivalent` is stated at a single
`Boundary`, so a construction that also moved the boundary could never be
tested against the unrestricted reading.

This is the constructor a carrier restriction needs.  `def:typeA-route8-carriers`
restricts a response state by *retaining* the declared coordinates carried
inside a chosen set and forgetting the rest, while keeping the full boundary
degree profile -- and the boundary profile is preserved here because the
boundary itself is untouched. -/
noncomputable def retainedPiece (retained : Finset object.Vertex) :
    BoundaryPiece (boundary object support) where
  Internal := PieceInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex =>
      vertex ∈ support ∧ vertex ∉ cutBoundary object support
  graph :=
    SimpleGraph.comap (pieceDecode object support) object.graph ⊓
      SimpleGraph.comap (pieceDecode object support)
        (SimpleGraph.fromRel fun left right =>
          left ∈ retained ∧ right ∈ retained)
  decideAdj := Classical.decRel _

noncomputable def outside : OutsideContext (boundary object support) where
  Internal := OutsideInternal object support
  internalVertices := by
    letI : FinEnum object.Vertex := object.vertices
    exact FinEnum.Subtype.finEnum fun vertex => vertex ∉ support
  graph := SimpleGraph.comap (outsideDecode object support) object.graph
  decideAdj := Classical.decRel _

theorem not_adj_pieceInternal_outside
    (inside : PieceInternal object support)
    (outsideVertex : OutsideInternal object support) :
    ¬ object.graph.Adj inside.1 outsideVertex.1 := by
  intro adjacent
  exact inside.2.2 ((mem_cutBoundary_iff object support inside.1).2
    ⟨inside.2.1, outsideVertex.1, adjacent, outsideVertex.2⟩)

private def gluedDecode :
    GluedVertex (piece object support) (outside object support) → object.Vertex
  | .inl vertex => vertex.1
  | .inr (.inl vertex) => vertex.1
  | .inr (.inr vertex) => vertex.1

private noncomputable def gluedEncode :
    object.Vertex → GluedVertex (piece object support) (outside object support) := by
  classical
  intro vertex
  by_cases onBoundary : vertex ∈ cutBoundary object support
  · exact .inl ⟨vertex, onBoundary⟩
  · by_cases inSupport : vertex ∈ support
    · exact .inr (.inl ⟨vertex, inSupport, onBoundary⟩)
    · exact .inr (.inr ⟨vertex, inSupport⟩)

private noncomputable def vertexEquiv :
    GluedVertex (piece object support) (outside object support) ≃ object.Vertex where
  toFun := gluedDecode object support
  invFun := gluedEncode object support
  left_inv := by
    classical
    intro vertex
    rcases vertex with boundaryVertex | internal
    · simp [gluedDecode, gluedEncode, boundaryVertex.2]
    · rcases internal with pieceVertex | outsideVertex
      · simp [gluedDecode, gluedEncode, pieceVertex.2.1, pieceVertex.2.2]
      · have notBoundary : outsideVertex.1 ∉ cutBoundary object support := by
          intro boundaryMember
          exact outsideVertex.2
            ((mem_cutBoundary_iff object support outsideVertex.1).1
              boundaryMember).1
        simp [gluedDecode, gluedEncode, outsideVertex.2, notBoundary]
  right_inv := by
    classical
    intro vertex
    by_cases onBoundary : vertex ∈ cutBoundary object support
    · simp [gluedDecode, gluedEncode, onBoundary]
    · by_cases inSupport : vertex ∈ support
      · simp [gluedDecode, gluedEncode, onBoundary, inSupport]
      · simp [gluedDecode, gluedEncode, onBoundary, inSupport]

noncomputable def decomposition : OwnedDecomposition object where
  interface := boundary object support
  piece := piece object support
  outside := outside object support
  vertexEquiv := vertexEquiv object support
  ownsAdjacency := by
    intro left right
    constructor
    · intro adjacent
      rcases left with left | left
      · rcases right with right | right
        · exact Or.inl ⟨.inl left, .inl right, adjacent, rfl, rfl⟩
        · rcases right with right | right
          · exact Or.inl ⟨.inl left, .inr right, adjacent, rfl, rfl⟩
          · exact Or.inr ⟨.inl left, .inr right, adjacent, rfl, rfl⟩
      · rcases left with left | left
        · rcases right with right | right
          · exact Or.inl ⟨.inr left, .inl right, adjacent, rfl, rfl⟩
          · rcases right with right | right
            · exact Or.inl ⟨.inr left, .inr right, adjacent, rfl, rfl⟩
            · exact False.elim
                (not_adj_pieceInternal_outside object support left right adjacent)
        · rcases right with right | right
          · exact Or.inr ⟨.inr left, .inl right, adjacent, rfl, rfl⟩
          · rcases right with right | right
            · exact False.elim
                (not_adj_pieceInternal_outside object support right left
                  ((object.graph.adj_comm _ _).mp adjacent))
            · exact Or.inr ⟨.inr left, .inr right, adjacent, rfl, rfl⟩
    · rintro (owned | owned)
      · rcases owned with ⟨left', right', adjacent, leftEq, rightEq⟩
        subst left
        subst right
        rcases left' with left' | left' <;>
          rcases right' with right' | right' <;> exact adjacent
      · rcases owned with ⟨left', right', adjacent, leftEq, rightEq⟩
        subst left
        subst right
        rcases left' with left' | left' <;>
          rcases right' with right' | right' <;> exact adjacent

/-- The canonical atom-side piece is exactly the graph induced by its ambient
support.  This is the producer-owned comparison used whenever a later local
move must transport degree or connectedness through the cut interface. -/
noncomputable def pieceInducedIso :
    (piece object support).graph ≃g (object.induce support).graph where
  toEquiv :=
    { toFun
        | .inl boundaryVertex => ⟨boundaryVertex.1,
            ((mem_cutBoundary_iff object support boundaryVertex.1).1
              boundaryVertex.2).1⟩
        | .inr internalVertex => ⟨internalVertex.1, internalVertex.2.1⟩
      invFun := by
        intro supported
        classical
        by_cases onBoundary : supported.1 ∈ cutBoundary object support
        · exact .inl ⟨supported.1, onBoundary⟩
        · exact .inr ⟨supported.1, supported.2, onBoundary⟩
      left_inv := by
        classical
        intro vertex
        rcases vertex with vertex | vertex
        · simp [vertex.2]
        · simp [vertex.2.2]
      right_inv := by
        classical
        intro vertex
        by_cases onBoundary : vertex.1 ∈ cutBoundary object support
        · simp [onBoundary]
        · simp [onBoundary] }
  map_rel_iff' := by
    intro left right
    rcases left with left | left <;>
      rcases right with right | right <;> rfl

private theorem induced_connected
    (connected : Graph.SupportComponents.Connected.ConnectedOn object support) :
    (object.induce support).graph.Connected := by
  rcases connected.1 with ⟨root, rootMember⟩
  letI : Nonempty (object.induce support).Vertex := ⟨⟨root, rootMember⟩⟩
  refine { preconnected := ?_ }
  intro left right
  obtain ⟨path, _isPath, contained⟩ := connected.2 left.2 right.2
  exact ⟨path.induce (support : Set object.Vertex) contained⟩

/-- Convert the exact connected support retained by CT15 into the existing
proper-atom representation.  No support or graph is rebuilt. -/
noncomputable def properAtom
    (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support) : ProperBoundariedAtom object where
  decomposition := decomposition object support
  connected := (pieceInducedIso object support).connected_iff.mpr
    (induced_connected object support connected)
  proper := by
    intro notProper
    rcases proper with ⟨vertex, outsideSupport⟩
    let outsideVertex : OutsideInternal object support := ⟨vertex, outsideSupport⟩
    obtain ⟨preimage, preimageEq⟩ := notProper.1 outsideVertex.1
    rcases preimage with boundaryVertex | internalVertex
    · change boundaryVertex.1 = outsideVertex.1 at preimageEq
      have valEq : boundaryVertex.1 = vertex := preimageEq
      exact outsideSupport (by
        rw [← valEq]
        exact ((mem_cutBoundary_iff object support boundaryVertex.1).1
          boundaryVertex.2).1)
    · change internalVertex.1 = outsideVertex.1 at preimageEq
      have valEq : internalVertex.1 = vertex := preimageEq
      exact outsideSupport (by rw [← valEq]; exact internalVertex.2.1)

end Hypostructure.Graph.Strategy.InterfaceReplacement.SupportAtom

namespace Hypostructure.Graph.Strategy.InterfaceReplacement

open Hypostructure
open Hypostructure.Graph

universe u v

/-- **The hypotheses of `lem:replacement` at G** (tex 6121), stated about G
only.

`X` is G's own piece at the proper connected support `Z` and `Y = G − Z` is
G's own surroundings (`atom.decomposition.outside`, which is
`SupportAtom.outside object support`).  The replacement `X'` is an arbitrary
`∂Z`-boundaried piece — it is **not** a reading of G — and it is required to
have

* (ii) the boundary-degree profile of `X`;
* (iv) together with (ii): `G' = glue X' (G − Z)` meets the baseline, so every
  vertex of `G'`, the interior vertices of `X'` included, has degree at least
  the threshold;
* (v) `G'` is strictly smaller than `G` in the lexicographic order;
* (i)+(iii) `G'` has no target cycle.

The last clause is what `lem:replacement`'s proof derives from (i) and (iii)
("We claim that `G'` has no power-of-two cycle"): a target cycle of `G'` lies in
`Y`, or in `X'`, or crosses `∂Z`; the paper reads each case in `G' = X' ⊕ Y`.
The only context of that argument is `Y = G − Z`, so the hypothesis is stated
there.  (G-only restatement: the former clause, the inclusion of obstruction
profiles against every `∂Z`-boundaried context, quantified over contexts that
are not part of G.) -/
def ReplacementSupport
    (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∃ (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support),
    let atom := SupportAtom.properAtom object support connected proper
    ∃ replacement : BoundaryPiece atom.decomposition.interface,
      replacement.boundaryDegreeProfile =
          atom.decomposition.piece.boundaryDegreeProfile ∧
        Baseline (glue replacement atom.decomposition.outside) ∧
        (glue replacement atom.decomposition.outside).LexicographicallySmaller
          object ∧
        ¬ Target (glue replacement atom.decomposition.outside)

/-- **A nontrivial target-complete compression of G's piece at `Z`**
(`def:target-complete-compression`, tex 6135: "a smaller `T`-boundaried
representative `X'` satisfying the hypotheses of `lem:replacement`"), stated
about G only: exactly the clauses of `ReplacementSupport` — the boundary-degree
profile of G's piece, the baseline and no target cycle in
`glue X' (G − Z)`, and strictly smaller size.  (G-only restatement: the former
last clause compared the two target responses against every `∂Z`-boundaried
context.) -/
def CompressibleSupport
    (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∃ (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support),
    let atom := SupportAtom.properAtom object support connected proper
    ∃ replacement : BoundaryPiece atom.decomposition.interface,
      replacement.boundaryDegreeProfile =
          atom.decomposition.piece.boundaryDegreeProfile ∧
        Baseline (glue replacement atom.decomposition.outside) ∧
        (glue replacement atom.decomposition.outside).LexicographicallySmaller
          object ∧
        ¬ Target (glue replacement atom.decomposition.outside)

/-- A target-complete compression is a replacement in the sense of
`lem:replacement` (`def:target-complete-compression`). -/
theorem replacementSupportOfCompressibleSupport
    (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (compressible : CompressibleSupport Baseline Target object support) :
    ReplacementSupport Baseline Target object support :=
  compressible

/-- At G, compression and replacement are the same hypotheses. -/
theorem compressibleSupport_iff_replacementSupport
    {Baseline Target : FiniteObject.{u} → Prop}
    {object : FiniteObject.{u}} {support : Finset object.Vertex} :
    CompressibleSupport Baseline Target object support ↔
      ReplacementSupport Baseline Target object support :=
  Iff.rfl

/-- **G's own piece at `Z`, glued back into `G − Z`, is `G`**: it carries no
target cycle that `G` avoids. -/
theorem not_target_glue_piece_outside {L : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object) (support : Finset object.Vertex) :
    ¬ HasCycleWithLength L
      (glue (SupportAtom.piece object support) (SupportAtom.outside object support)) :=
  fun cycle => avoids
    ((hasCycleWithLength_iff_of_iso
      (SupportAtom.decomposition object support).reconstructionIso L).mp cycle)

/-- **Target transfer at `G − Z` gives the last replacement clause.**  If a
target cycle of `glue X' (G − Z)` would put one in `glue X (G − Z) ≅ G`, then
`glue X' (G − Z)` has none. -/
theorem not_target_of_transfer {L : Nat → Prop} {object : FiniteObject.{u}}
    (avoids : ¬ HasCycleWithLength L object) {support : Finset object.Vertex}
    {replacement : BoundaryPiece (SupportAtom.boundary object support)}
    (transfer :
      HasCycleWithLength L (glue replacement (SupportAtom.outside object support)) →
        HasCycleWithLength L
          (glue (SupportAtom.piece object support) (SupportAtom.outside object support))) :
    ¬ HasCycleWithLength L (glue replacement (SupportAtom.outside object support)) :=
  fun cycle => not_target_glue_piece_outside avoids support (transfer cycle)

/-- **`lem:replacement`, minimality form.**  `G' = glue X' (G − Z)` is strictly
smaller and meets the baseline, so minimality gives it the target, against the
replacement's last clause. -/
theorem not_replacementSupport_of_minimal {Baseline Target : FiniteObject.{u} → Prop}
    {object : FiniteObject.{u}}
    (minimal : ∀ H : FiniteObject.{u}, H.LexicographicallySmaller object →
      Baseline H → Target H)
    (support : Finset object.Vertex) :
    ¬ ReplacementSupport Baseline Target object support := by
  rintro ⟨_connected, _proper, _replacement, _signatureEq, baseline, smaller,
    noTarget⟩
  exact noTarget (minimal _ smaller baseline)

/-- **`lem:replacement`.**  A selected minimal counterexample admits no
proper-support replacement `G' = glue X' (G − Z)`: `G'` is a strictly smaller
baseline object, so the selection's minimality gives it the target, which the
replacement excludes. -/
theorem not_replacementSupport
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation))
    (_targetInvariant : Core.TargetInvariant
      (isomorphismEquivalenceWithPresentation Baseline BranchState
        Presentation presentation baselineInvariant) T.Predicate)
    (ctx : Core.MinimalCounterexampleContext
      (problemWithPresentation Baseline BranchState Presentation presentation)
      T.Predicate
      (CanonicalProgress.progress
        (P := problemWithPresentation
          Baseline BranchState Presentation presentation)))
    (support : Finset ctx.G.Vertex) :
    ¬ ReplacementSupport Baseline T.Predicate ctx.G support := by
  intro replacementSupport
  rcases replacementSupport with
    ⟨_connected, _proper, replacement, _signatureEq, baseline, smaller, noTarget⟩
  exact noTarget (ctx.target_of_smaller
    (H := glue replacement (SupportAtom.outside ctx.G support)) smaller baseline)

end Hypostructure.Graph.Strategy.InterfaceReplacement
