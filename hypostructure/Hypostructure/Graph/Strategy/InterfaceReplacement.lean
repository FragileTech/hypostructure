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

private noncomputable def pieceInducedIso :
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

/-- Exact proper-support replacement hypothesis of the paper.  The final
clause is the one-way inclusion of obstruction profiles: every outside context
obstructed by the replacement is also obstructed by the source atom. -/
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
        ∀ outside : OutsideContext atom.decomposition.interface,
          Target (glue replacement outside) →
            Target (glue atom.decomposition.piece outside)

/-- Exact mathematical content of a target-complete proper-support
compression.  It mentions only the retained support and the existing Graph
replacement notions; no route, outcome, or target proof is stored. -/
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
        ∀ outside : OutsideContext atom.decomposition.interface,
          (Target (glue replacement outside) ↔
            Target (glue atom.decomposition.piece outside))

/-- A target-complete compression satisfies the weaker, one-way replacement
hypothesis used by the paper's replacement lemma. -/
theorem replacementSupportOfCompressibleSupport
    (Baseline Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (compressible : CompressibleSupport Baseline Target object support) :
    ReplacementSupport Baseline Target object support := by
  rcases compressible with
    ⟨connected, proper, replacement, signatureEq, baseline, smaller,
      contextUniversal⟩
  exact ⟨connected, proper, replacement, signatureEq, baseline, smaller,
    fun outside replacementTarget =>
      (contextUniversal outside).mp replacementTarget⟩

/-- Convert the paper's proper-support replacement data into Core's exact
strict-replacement carrier at the selected minimal counterexample. -/
theorem strictReplacementOfReplacementSupport
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (T : Core.Target (problem Baseline BranchState))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalence Baseline BranchState baselineInvariant) T.Predicate)
    (ctx : Core.MinimalCounterexampleContext
      (problem Baseline BranchState) T.Predicate
      (lexicographicProgress Baseline BranchState))
    (support : Finset ctx.G.Vertex)
    (replacementSupport : ReplacementSupport Baseline T.Predicate ctx.G support) :
    Nonempty (Σ site :
        (profile Baseline BranchState baselineInvariant targetInvariant).assembly.Site
          ctx.G,
      (profile Baseline BranchState baselineInvariant targetInvariant).StrictReplacement
        ctx site) := by
  rcases replacementSupport with
    ⟨connected, proper, replacement, signatureEq, baseline, smaller,
      obstructionLE⟩
  let site := SupportAtom.properAtom ctx.G support connected proper
  let replacement' :
      (profile Baseline BranchState baselineInvariant targetInvariant).assembly.Replacement
        ctx.G site :=
    { atom := replacement
      compatible := trivial }
  exact ⟨⟨site,
    { replacement := replacement'
      signature_eq := congrArg ULift.up signatureEq
      obstruction_le := by
        intro outside _ _ replacementTarget
        exact obstructionLE outside replacementTarget
      baseline := baseline
      smaller := smaller }⟩⟩

/-- Presentation-carrying analogue of
`strictReplacementOfReplacementSupport`. -/
theorem strictReplacementOfReplacementSupportWithPresentation
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalenceWithPresentation Baseline BranchState
        Presentation presentation baselineInvariant) T.Predicate)
    (ctx : Core.MinimalCounterexampleContext
      (problemWithPresentation Baseline BranchState Presentation presentation)
      T.Predicate
      (CanonicalProgress.progress
        (P := problemWithPresentation
          Baseline BranchState Presentation presentation)))
    (support : Finset ctx.G.Vertex)
    (replacementSupport : ReplacementSupport Baseline T.Predicate ctx.G support) :
    Nonempty (Σ site :
        (profileWithPresentation Baseline BranchState baselineInvariant
          Presentation presentation targetInvariant).assembly.Site ctx.G,
      (profileWithPresentation Baseline BranchState baselineInvariant
        Presentation presentation targetInvariant).StrictReplacement ctx site) := by
  rcases replacementSupport with
    ⟨connected, proper, replacement, signatureEq, baseline, smaller,
      obstructionLE⟩
  let site := SupportAtom.properAtom ctx.G support connected proper
  let replacement' :
      (profileWithPresentation Baseline BranchState baselineInvariant
        Presentation presentation targetInvariant).assembly.Replacement ctx.G site :=
    { atom := replacement
      compatible := trivial }
  exact ⟨⟨site,
    { replacement := replacement'
      signature_eq := congrArg ULift.up signatureEq
      obstruction_le := by
        intro outside _ _ replacementTarget
        exact obstructionLE outside replacementTarget
      baseline := baseline
      smaller := smaller }⟩⟩

/-- Baseline-independent form computed at an incoming graph residual.  The
replacement retains minimum degree at least that of the literal source
object, so any threshold already proved for the source specializes to an
ordinary `CompressibleSupport` without a new mathematical input.

The last clause is `def:proper-quotient-representative`: the smaller
representative is a *representative of the ambient object*, not a detached
graph.  The existential over `replacement` would otherwise forget every
relation to `object`, and `cor:uncompressible` -- which speaks about proper
subgraphs of the active object -- could not be applied to it.  The two
components are literally the `vertexEmbedding` and `included` fields of
`Graph.ProperSubgraph`, and `properSubgraphOfIntrinsic` below reads them off
in that shape. -/
def IntrinsicCompressibleSupport
    (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∃ (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support),
    let atom := SupportAtom.properAtom object support connected proper
    ∃ replacement : BoundaryPiece atom.decomposition.interface,
      replacement.boundaryDegreeProfile =
          atom.decomposition.piece.boundaryDegreeProfile ∧
        object.minDegree ≤
          (glue replacement atom.decomposition.outside).minDegree ∧
        (glue replacement atom.decomposition.outside).LexicographicallySmaller
          object ∧
        (∀ outside : OutsideContext atom.decomposition.interface,
          (Target (glue replacement outside) ↔
            Target (glue atom.decomposition.piece outside))) ∧
        ∃ embedding :
            (glue replacement atom.decomposition.outside).Vertex ↪ object.Vertex,
          (glue replacement atom.decomposition.outside).graph.map embedding ≤
            object.graph

/-- Target-free structural frame retained before CT7 compares responses. -/
def IntrinsicCompressionFrameSupport
    (object : FiniteObject.{u}) (support : Finset object.Vertex) : Prop :=
  ∃ (connected : Graph.SupportComponents.Connected.ConnectedOn object support)
    (proper : ∃ vertex, vertex ∉ support),
    let atom := SupportAtom.properAtom object support connected proper
    ∃ replacement : BoundaryPiece atom.decomposition.interface,
      replacement.boundaryDegreeProfile =
          atom.decomposition.piece.boundaryDegreeProfile ∧
        object.minDegree ≤
          (glue replacement atom.decomposition.outside).minDegree ∧
        (glue replacement atom.decomposition.outside).LexicographicallySmaller
          object

/-- Convert the stored target-free graph frame into Core's exact pre-scan
carrier for a presentation-carrying minimum-degree problem. -/
theorem compressionFrameOfIntrinsicWithPresentation
    (threshold : Nat)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant
      (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree))
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalenceWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState Presentation presentation baselineInvariant)
      T.Predicate)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (sourceBaseline : threshold ≤ object.minDegree)
    (frame : IntrinsicCompressionFrameSupport object support) :
    Nonempty (Σ site :
        (profileWithPresentation
          (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
          BranchState baselineInvariant Presentation presentation
          targetInvariant).assembly.Site object,
      (profileWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState baselineInvariant Presentation presentation
        targetInvariant).CompressionFrame object site) := by
  rcases frame with
    ⟨connected, proper, replacement, signatureEq, minimumDegree, smaller⟩
  let site := SupportAtom.properAtom object support connected proper
  let replacement' :
      (profileWithPresentation
        (fun candidate : FiniteObject.{u} => threshold ≤ candidate.minDegree)
        BranchState baselineInvariant Presentation presentation
        targetInvariant).assembly.Replacement object site :=
    { atom := replacement
      compatible := trivial }
  exact ⟨⟨site,
    { replacement := replacement'
      signature_eq := congrArg ULift.up signatureEq
      baseline := sourceBaseline.trans minimumDegree
      smaller := smaller }⟩⟩

/-- Forget only the already-proved target response field of an intrinsic
compression; the exact structural frame is unchanged. -/
theorem intrinsicCompressionFrameOfCompressible
    (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (compressible : IntrinsicCompressibleSupport Target object support) :
    IntrinsicCompressionFrameSupport object support := by
  rcases compressible with
    ⟨connected, proper, replacement, signatureEq, minimumDegree,
      smaller, _contextUniversal, _embedding, _included⟩
  exact ⟨connected, proper, replacement, signatureEq, minimumDegree, smaller⟩

/-- The subgraph reading of one stored intrinsic compression, in the exact
shape `Graph.ProperSubgraph` is indexed by.

All four fields are projections of the retained compression: the glued
replacement is the `value`, its `LexicographicallySmaller` clause is
`decreases`, and the same-interface clause is `vertexEmbedding` together with
`included`.  The retained minimum-degree comparison travels beside it, so a
consumer holding the source's own baseline reads the smaller object's baseline
off this pair without a second graph construction. -/
theorem properSubgraphOfIntrinsic
    (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (intrinsic : IntrinsicCompressibleSupport Target object support) :
    ∃ subgraph : ProperSubgraph object,
      object.minDegree ≤ subgraph.value.minDegree := by
  rcases intrinsic with
    ⟨_connected, _proper, replacement, _signatureEq, minimumDegree,
      smaller, _contextUniversal, embedding, included⟩
  exact ⟨{ value := glue replacement _
           vertexEmbedding := embedding
           included := included
           decreases := smaller }, minimumDegree⟩

/-- Specialize the intrinsic residual-owned compression to an inherited
minimum-degree threshold. -/
theorem compressibleSupportOfIntrinsic
    (Target : FiniteObject.{u} → Prop)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (threshold : Nat) (sourceBaseline : threshold ≤ object.minDegree)
    (intrinsic : IntrinsicCompressibleSupport Target object support) :
    CompressibleSupport (fun candidate => threshold ≤ candidate.minDegree)
      Target object support := by
  rcases intrinsic with
    ⟨connected, proper, replacement, signatureEq, minimumDegree,
      smaller, contextUniversal, _embedding, _included⟩
  exact ⟨connected, proper, replacement, signatureEq,
    sourceBaseline.trans minimumDegree, smaller, contextUniversal⟩

/-- Convert the literal same-interface support data into Core's public
context-free compression carrier.  The dependent site is the proper atom
already determined by the retained support/connectivity/properness witness;
no graph or replacement is reconstructed downstream. -/
theorem compressionCandidateOfCompressibleSupport
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (T : Core.Target (problem Baseline BranchState))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalence Baseline BranchState baselineInvariant) T.Predicate)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (compressible : CompressibleSupport Baseline T.Predicate object support) :
    Nonempty (Σ site :
        (profile Baseline BranchState baselineInvariant targetInvariant).assembly.Site
          object,
      (profile Baseline BranchState baselineInvariant targetInvariant).CompressionCandidate
        object site) := by
  rcases compressible with
    ⟨connected, proper, replacement, signatureEq, baseline, smaller,
      contextUniversal⟩
  let site := SupportAtom.properAtom object support connected proper
  let replacement' :
      (profile Baseline BranchState baselineInvariant targetInvariant).assembly.Replacement
        object site :=
    { atom := replacement
      compatible := trivial }
  exact ⟨⟨site,
    { replacement := replacement'
      complete :=
        { signature_eq := congrArg ULift.up signatureEq
          contextUniversal := by
            intro outside _ _
            exact contextUniversal outside }
      baseline := baseline
      smaller := smaller }⟩⟩

/-- Presentation-carrying analogue of
`compressionCandidateOfCompressibleSupport`.  The fixed presentation changes
only the problem carrier; the retained graph site and replacement data are
identical. -/
theorem compressionCandidateOfCompressibleSupportWithPresentation
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalenceWithPresentation Baseline BranchState
        Presentation presentation baselineInvariant) T.Predicate)
    (object : FiniteObject.{u}) (support : Finset object.Vertex)
    (compressible : CompressibleSupport Baseline T.Predicate object support) :
    Nonempty (Σ site :
        (profileWithPresentation Baseline BranchState baselineInvariant
          Presentation presentation targetInvariant).assembly.Site object,
      (profileWithPresentation Baseline BranchState baselineInvariant
        Presentation presentation targetInvariant).CompressionCandidate
          object site) := by
  rcases compressible with
    ⟨connected, proper, replacement, signatureEq, baseline, smaller,
      contextUniversal⟩
  let site := SupportAtom.properAtom object support connected proper
  let replacement' :
      (profileWithPresentation Baseline BranchState baselineInvariant
        Presentation presentation targetInvariant).assembly.Replacement
          object site :=
    { atom := replacement
      compatible := trivial }
  exact ⟨⟨site,
    { replacement := replacement'
      complete :=
        { signature_eq := congrArg ULift.up signatureEq
          contextUniversal := by
            intro outside _ _
            exact contextUniversal outside }
      baseline := baseline
      smaller := smaller }⟩⟩

/-! ## `lem:replacement` and `cor:uncompressible` at a selected minimal object

Both exclusions below take the selected `MinimalCounterexampleContext` and
nothing else.  The manuscript derives them from minimality alone, and so do
these: `Core.Strategy.InterfaceReplacement.strictReplacementImpossible` reads
only `ctx.avoids` and `ctx.target_of_smaller`, the two components of the
selection.  A row therefore proves them from the selection *fact* of the
canonical ledger, with no closure record, registration, or payload standing
between the fact and its consequence.
-/

/-- **`lem:replacement`.**  A selected minimal counterexample admits no
proper-support replacement satisfying the paper's one-way obstruction
inclusion. -/
theorem not_replacementSupport
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
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
  rcases strictReplacementOfReplacementSupportWithPresentation Baseline
      BranchState baselineInvariant Presentation presentation T targetInvariant
      ctx support replacementSupport with ⟨⟨site, replacement⟩⟩
  exact Core.Strategy.InterfaceReplacement.Profile.strictReplacementImpossible
    (profileWithPresentation Baseline BranchState baselineInvariant
      Presentation presentation targetInvariant) ctx site ⟨replacement⟩

/-- **`cor:uncompressible`.**  No proper atom of a selected minimal
counterexample admits a nontrivial target-complete compression.

A target-complete compression satisfies the weaker one-way hypothesis of
`lem:replacement` (`replacementSupportOfCompressibleSupport`), which the
previous theorem has already excluded. -/
theorem not_compressibleSupport
    (Baseline : FiniteObject.{u} → Prop)
    (BranchState : FiniteObject.{u} → Type v)
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (Presentation : Type) (presentation : Presentation)
    (T : Core.Target
      (problemWithPresentation Baseline BranchState Presentation presentation))
    (targetInvariant : Core.TargetInvariant
      (isomorphismEquivalenceWithPresentation Baseline BranchState
        Presentation presentation baselineInvariant) T.Predicate)
    (ctx : Core.MinimalCounterexampleContext
      (problemWithPresentation Baseline BranchState Presentation presentation)
      T.Predicate
      (CanonicalProgress.progress
        (P := problemWithPresentation
          Baseline BranchState Presentation presentation)))
    (support : Finset ctx.G.Vertex) :
    ¬ CompressibleSupport Baseline T.Predicate ctx.G support := fun compressible =>
  not_replacementSupport Baseline BranchState baselineInvariant Presentation
    presentation T targetInvariant ctx support
    (replacementSupportOfCompressibleSupport Baseline T.Predicate ctx.G support
      compressible)

end Hypostructure.Graph.Strategy.InterfaceReplacement
