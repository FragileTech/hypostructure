import Hypostructure.Graph.Gluing
import Hypostructure.Graph.BoundariedAtom
import Hypostructure.Graph.Response
import Hypostructure.Graph.Target
import Mathlib.SetTheory.Cardinal.Order

/-!
# The canonical realization of a boundaried reading

`def:proper-quotient-representative`, `def:closed-quotient-representative`,
`def:cold-corridor-first-failure` ("the canonical representative determined by
the repeated cold corridor state"), `def:cold-bounded-germ` and
`def:typeA-route8-carriers` all speak of *the* canonical piece realizing a
declared reading at a boundary interface: the same boundary-degree profile,
the same target response against every outside context, internal degrees at
least the baseline, and lexicographically first among such pieces "in the fixed
canonical order on bounded boundaried pieces".

`BoundaryPiece` carries an arbitrary internal vertex type, so it has no
lex-first element by itself.  This module fixes the canonical carrier: a piece
on `Fin k` internal vertices (`CanonicalPiece`), a well-order on canonical
pieces refining internal size (`Precedes`), the transport of an arbitrary piece
to its canonical carrier (`ofPiece`, isomorphic over the interface), and the
operator `canonicalRepresentative` = the `Precedes`-least canonical piece
satisfying a reading.  For the cut-state reading of a piece
(`CutStateReading`) the piece's own transport is a realizer, so the canonical
representative exists, realizes the reading, and precedes every other
realizer; exchanging a piece for its canonical representative inside a gluing
preserves the target response (`glue_swap_target_iff`) and the vertex count
exactly when the internal sizes agree.

Nothing here is specialized to a manuscript: the target and the baseline are
parameters, and no numeral occurs.
-/

namespace Hypostructure.Graph

universe u

/-- The canonical finite carrier of size `k` in universe `u`. -/
abbrev CanonicalCarrier (k : Nat) : Type u := ULift.{u} (Fin k)

instance canonicalCarrierFinEnum (k : Nat) : FinEnum (CanonicalCarrier.{u} k) :=
  FinEnum.ofEquiv (Fin k) Equiv.ulift

/-- A boundaried piece on the canonical carrier of its internal size. -/
structure CanonicalPiece (boundary : Boundary.{u}) where
  size : Nat
  graph : SimpleGraph (boundary.Vertex ⊕ CanonicalCarrier.{u} size)
  decideAdj : DecidableRel graph.Adj

namespace CanonicalPiece

variable {boundary : Boundary.{u}}

/-- The canonical piece read as an ordinary boundary piece. -/
def toPiece (canonical : CanonicalPiece boundary) : BoundaryPiece boundary where
  Internal := CanonicalCarrier canonical.size
  internalVertices := inferInstance
  graph := canonical.graph
  decideAdj := canonical.decideAdj

@[simp] theorem toPiece_internalVertexCount (canonical : CanonicalPiece boundary) :
    canonical.toPiece.internalVertexCount = canonical.size := by
  simp [toPiece, BoundaryPiece.internalVertexCount, FinEnum.card_eq_fintypeCard,
    canonicalCarrierFinEnum]

/-- **The fixed canonical order on bounded boundaried pieces**: internal size
first, then a fixed well-order of the pieces of that size.  Any well-order
serves the manuscript's "lexicographically first"; this one is total and
well-founded, which is all the canonical choice consumes. -/
def Precedes (left right : CanonicalPiece boundary) : Prop :=
  Prod.Lex (fun a b : Nat => a < b) WellOrderingRel (left.size, left) (right.size, right)

theorem precedes_wellFounded : WellFounded (Precedes (boundary := boundary)) := by
  have base : WellFounded
      (Prod.Lex (fun a b : Nat => a < b) (WellOrderingRel (α := CanonicalPiece boundary))) :=
    WellFounded.prod_lex wellFounded_lt WellOrderingRel.isWellOrder.wf
  exact InvImage.wf (fun canonical => (canonical.size, canonical)) base

theorem precedes_irrefl (canonical : CanonicalPiece boundary) :
    ¬ Precedes canonical canonical := fun h => precedes_wellFounded.irrefl.irrefl _ h

/-- Totality: two distinct canonical pieces are comparable. -/
theorem precedes_or_precedes {left right : CanonicalPiece boundary}
    (different : left ≠ right) : Precedes left right ∨ Precedes right left := by
  unfold Precedes
  rcases lt_trichotomy left.size right.size with lt | eq | gt
  · exact Or.inl (Prod.Lex.left _ _ lt)
  · rcases trichotomous_of (WellOrderingRel (α := CanonicalPiece boundary)) left right
      with lr | same | rl
    · exact Or.inl (by rw [eq]; exact Prod.Lex.right _ lr)
    · exact absurd same different
    · exact Or.inr (by rw [eq]; exact Prod.Lex.right _ rl)
  · exact Or.inr (Prod.Lex.left _ _ gt)

theorem size_le_of_precedes {left right : CanonicalPiece boundary}
    (precedes : Precedes left right) : left.size ≤ right.size := by
  unfold Precedes at precedes
  rcases (Prod.lex_iff.1 precedes) with lt | ⟨eq, _⟩
  · exact le_of_lt lt
  · exact le_of_eq eq

/-- **The canonical representative of a reading**: the `Precedes`-least
canonical piece satisfying it. -/
noncomputable def canonicalRepresentative (Reading : CanonicalPiece boundary → Prop)
    (realizable : ∃ canonical, Reading canonical) : CanonicalPiece boundary :=
  precedes_wellFounded.min {canonical | Reading canonical} realizable

theorem canonicalRepresentative_reading (Reading : CanonicalPiece boundary → Prop)
    (realizable : ∃ canonical, Reading canonical) :
    Reading (canonicalRepresentative Reading realizable) :=
  precedes_wellFounded.min_mem {canonical | Reading canonical} realizable

/-- No realizer precedes the canonical representative. -/
theorem not_precedes_canonicalRepresentative (Reading : CanonicalPiece boundary → Prop)
    (realizable : ∃ canonical, Reading canonical) {other : CanonicalPiece boundary}
    (reading : Reading other) :
    ¬ Precedes other (canonicalRepresentative Reading realizable) :=
  precedes_wellFounded.not_lt_min {canonical | Reading canonical} reading

/-- The canonical representative precedes every *other* realizer: this is the
strict decrease the swap of `lem:refined-minimality-swap` uses. -/
theorem canonicalRepresentative_precedes (Reading : CanonicalPiece boundary → Prop)
    (realizable : ∃ canonical, Reading canonical) {other : CanonicalPiece boundary}
    (reading : Reading other) (different : other ≠ canonicalRepresentative Reading realizable) :
    Precedes (canonicalRepresentative Reading realizable) other := by
  rcases precedes_or_precedes different with lt | gt
  · exact absurd lt (not_precedes_canonicalRepresentative Reading realizable reading)
  · exact gt

theorem canonicalRepresentative_size_le (Reading : CanonicalPiece boundary → Prop)
    (realizable : ∃ canonical, Reading canonical) {other : CanonicalPiece boundary}
    (reading : Reading other) :
    (canonicalRepresentative Reading realizable).size ≤ other.size := by
  by_cases same : other = canonicalRepresentative Reading realizable
  · rw [same]
  · exact size_le_of_precedes (canonicalRepresentative_precedes Reading realizable reading same)

end CanonicalPiece

/-! ## Transport of a piece to its canonical carrier -/

namespace BoundaryPiece

variable {boundary : Boundary.{u}}

/-- Relabel the internal vertices of a piece along an equivalence. -/
@[reducible] def transport (piece : BoundaryPiece boundary) {Internal : Type u} [FinEnum Internal]
    (relabel : piece.Internal ≃ Internal) : BoundaryPiece boundary where
  Internal := Internal
  internalVertices := inferInstance
  graph := piece.graph.comap (Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm)
  decideAdj := by
    letI := piece.decideAdj
    exact fun left right => piece.decideAdj _ _

@[simp] theorem transport_adj (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal)
    (left right : boundary.Vertex ⊕ Internal) :
    (piece.transport relabel).graph.Adj left right ↔
      piece.graph.Adj (Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm left)
        (Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm right) :=
  Iff.rfl

/-- The vertex equivalence of the two gluings of a piece and its transport with
one outside context. -/
def transportGlueEquiv (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal)
    (outside : OutsideContext boundary) :
    GluedVertex (piece.transport relabel) outside ≃ GluedVertex piece outside :=
  Equiv.sumCongr (Equiv.refl boundary.Vertex)
    (Equiv.sumCongr relabel.symm (Equiv.refl outside.Internal))

/-- The glued graph of the transport is the pull-back of the glued graph of
the piece along the vertex equivalence. -/
theorem transport_glueGraph_eq (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal)
    (outside : OutsideContext boundary) :
    glueGraph (piece.transport relabel) outside =
      (glueGraph piece outside).comap (piece.transportGlueEquiv relabel outside) := by
  ext left right
  rw [SimpleGraph.comap_adj, glueGraph_adj_iff, glueGraph_adj_iff]
  unfold OwnedAdjacency PieceOwns ContextOwns
  rcases left with left | left | left <;> rcases right with right | right | right <;>
    simp [transportGlueEquiv, pieceEmbedding, contextEmbedding, transport_adj,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Gluing commutes with transport: the two glued graphs are isomorphic. -/
def transportGlueIso (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal)
    (outside : OutsideContext boundary) :
    (glue (piece.transport relabel) outside).Iso (glue piece outside) where
  toEquiv := piece.transportGlueEquiv relabel outside
  map_rel_iff' := by
    intro left right
    change (glueGraph piece outside).Adj _ _ ↔ (glueGraph (piece.transport relabel) outside).Adj _ _
    rw [transport_glueGraph_eq, SimpleGraph.comap_adj]
    exact Iff.rfl

theorem transport_glue_isomorphic (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal)
    (outside : OutsideContext boundary) :
    (glue (piece.transport relabel) outside).Isomorphic (glue piece outside) :=
  ⟨piece.transportGlueIso relabel outside⟩

/-- Transport preserves the boundary-degree profile. -/
theorem transport_boundaryDegreeProfile (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal) :
    (piece.transport relabel).boundaryDegreeProfile = piece.boundaryDegreeProfile := by
  funext vertex
  letI : FinEnum piece.Internal := piece.internalVertices
  simp only [boundaryDegreeProfile, boundaryDegree, FiniteObject.degree, pack]
  letI : Fintype (boundary.Vertex ⊕ piece.Internal) := by
    letI : FinEnum boundary.Vertex := boundary.vertices; infer_instance
  letI : Fintype (boundary.Vertex ⊕ Internal) := by
    letI : FinEnum boundary.Vertex := boundary.vertices; infer_instance
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun vertex' _ => Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm vertex')
    ?_ ?_ ?_
  · intro vertex' member
    simp only [SimpleGraph.mem_neighborFinset] at member ⊢
    simpa [transport_adj, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] using member
  · intro a _ b _ h
    exact (Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm).injective h
  · intro target member
    refine ⟨Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel target, ?_, ?_⟩
    · simp only [SimpleGraph.mem_neighborFinset] at member ⊢
      simpa [transport_adj, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply] using member
    · simp

/-- Transport preserves the internal baseline. -/
theorem transport_internalThresholdBaseline (piece : BoundaryPiece boundary) {Internal : Type u}
    [FinEnum Internal] (relabel : piece.Internal ≃ Internal) (threshold : Nat)
    (baseline : piece.InternalThresholdBaseline threshold) :
    (piece.transport relabel).InternalThresholdBaseline threshold := by
  intro internal
  letI : FinEnum piece.Internal := piece.internalVertices
  have base := baseline (relabel.symm internal)
  simp only [FiniteObject.degree, pack] at base ⊢
  letI instLeft : Fintype (boundary.Vertex ⊕ piece.Internal) := by
    letI : FinEnum boundary.Vertex := boundary.vertices; infer_instance
  letI instRight : Fintype (boundary.Vertex ⊕ Internal) := by
    letI : FinEnum boundary.Vertex := boundary.vertices; infer_instance
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at base ⊢
  refine le_trans base (le_of_eq ?_)
  refine Finset.card_bij (fun vertex' _ => Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel vertex')
    ?_ ?_ ?_
  · intro vertex' member
    simp only [SimpleGraph.mem_neighborFinset] at member ⊢
    simpa [transport_adj, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply] using member
  · intro a _ b _ h
    exact (Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel).injective h
  · intro target member
    refine ⟨Equiv.sumCongr (Equiv.refl boundary.Vertex) relabel.symm target, ?_, ?_⟩
    · simp only [SimpleGraph.mem_neighborFinset] at member ⊢
      simpa [transport_adj, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Equiv.apply_symm_apply] using member
    · simp

/-- The equivalence of a piece's internal carrier with the canonical carrier of
its internal size. -/
noncomputable def canonicalRelabel (piece : BoundaryPiece boundary) :
    piece.Internal ≃ CanonicalCarrier.{u} piece.internalVertexCount :=
  letI : FinEnum piece.Internal := piece.internalVertices
  (FinEnum.equiv (α := piece.Internal)).trans Equiv.ulift.symm

/-- **A piece on its canonical carrier.** -/
noncomputable def toCanonical (piece : BoundaryPiece boundary) : CanonicalPiece boundary where
  size := piece.internalVertexCount
  graph := (piece.transport piece.canonicalRelabel).graph
  decideAdj := (piece.transport piece.canonicalRelabel).decideAdj

theorem toCanonical_toPiece (piece : BoundaryPiece boundary) :
    piece.toCanonical.toPiece = piece.transport piece.canonicalRelabel := rfl

theorem toCanonical_glue_isomorphic (piece : BoundaryPiece boundary)
    (outside : OutsideContext boundary) :
    (glue piece.toCanonical.toPiece outside).Isomorphic (glue piece outside) := by
  rw [toCanonical_toPiece]
  exact piece.transport_glue_isomorphic _ outside

end BoundaryPiece

/-! ## The cut-state reading and its canonical representative -/

namespace CanonicalPiece

variable {boundary : Boundary.{u}}

/-- **The retained cut-state of a piece**, as the manuscript's canonical
representative must realize it: the same boundary-degree profile, the same
target response against every outside context, and — `def:proper-quotient-representative` (d) read at the
gluing — the baseline of every completion is inherited. -/
def CutStateReading (Baseline Target : FiniteObject.{u} → Prop)
    (piece : BoundaryPiece boundary) (canonical : CanonicalPiece boundary) : Prop :=
  canonical.toPiece.boundaryDegreeProfile = piece.boundaryDegreeProfile ∧
    Response.ContextEquivalent Target canonical.toPiece piece ∧
    ∀ outside : OutsideContext boundary,
      Baseline (glue piece outside) → Baseline (glue canonical.toPiece outside)

/-- A piece's own canonical transport realizes its cut-state (target and
baseline being isomorphism-invariant). -/
theorem cutStateReading_toCanonical {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) :
    CutStateReading Baseline Target piece piece.toCanonical := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BoundaryPiece.toCanonical_toPiece]
    exact piece.transport_boundaryDegreeProfile _
  · intro outside
    exact targetInvariant.iff_of_iso (piece.toCanonical_glue_isomorphic outside)
  · intro outside baseline
    exact (baselineInvariant.iff_of_iso (piece.toCanonical_glue_isomorphic outside)).2 baseline

theorem cutStateReading_realizable {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) :
    ∃ canonical, CutStateReading Baseline Target piece canonical :=
  ⟨piece.toCanonical, cutStateReading_toCanonical baselineInvariant targetInvariant piece⟩

/-- **The canonical representative of a piece's cut-state**
(`def:cold-corridor-first-failure`, `def:proper-quotient-representative`). -/
noncomputable def cutStateRepresentative {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) : CanonicalPiece boundary :=
  canonicalRepresentative (CutStateReading Baseline Target piece)
    (cutStateReading_realizable baselineInvariant targetInvariant piece)

theorem cutStateRepresentative_reading {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) :
    CutStateReading Baseline Target piece
      (cutStateRepresentative baselineInvariant targetInvariant piece) :=
  canonicalRepresentative_reading _ _

/-- The representative is at most as large as the piece itself. -/
theorem cutStateRepresentative_size_le {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) :
    (cutStateRepresentative baselineInvariant targetInvariant piece).size ≤
      piece.internalVertexCount :=
  canonicalRepresentative_size_le _ _
    (cutStateReading_toCanonical baselineInvariant targetInvariant piece)

/-- **The swap is neutral for the target**: gluing the representative into any
context has the same target status as gluing the piece. -/
theorem glue_swap_target_iff {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    Target (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside) ↔
      Target (glue piece outside) :=
  (cutStateRepresentative_reading baselineInvariant targetInvariant piece).2.1 outside

/-- The swap inherits the baseline of the completion. -/
theorem glue_swap_baseline {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (baseline : Baseline (glue piece outside)) :
    Baseline (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside) :=
  (cutStateRepresentative_reading baselineInvariant targetInvariant piece).2.2 outside baseline

/-- The swap never increases the vertex count, and strictly decreases it when
the representative is smaller. -/
theorem glue_swap_vertexCount {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary) :
    (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside).vertexCount =
      boundary.vertexCount + (cutStateRepresentative baselineInvariant targetInvariant piece).size +
        outside.internalVertexCount := by
  rw [glue_vertexCount, toPiece_internalVertexCount]

/-- **The canonical-replacement dichotomy of the neutral germ**
(`lem:neutral-germ-symmetry`, nodes `[165]`/`[166]`): either the piece already
is its canonical representative (on the canonical carrier), or the
representative strictly precedes it in the fixed canonical order. -/
theorem toCanonical_eq_or_precedes {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) :
    piece.toCanonical = cutStateRepresentative baselineInvariant targetInvariant piece ∨
      Precedes (cutStateRepresentative baselineInvariant targetInvariant piece) piece.toCanonical := by
  by_cases same : piece.toCanonical = cutStateRepresentative baselineInvariant targetInvariant piece
  · exact Or.inl same
  · exact Or.inr (canonicalRepresentative_precedes _ _
      (cutStateReading_toCanonical baselineInvariant targetInvariant piece) same)

/-- **`lem:refined-minimality-swap`, the size-reducing case.**  If the canonical
representative of a piece is strictly smaller than the piece, then for every
completion the swapped graph has strictly fewer vertices, the same target
status, and the inherited baseline: a strictly smaller counterexample whenever
the completion was one. -/
theorem swap_smaller_counterexample {Baseline Target : FiniteObject.{u} → Prop}
    (baselineInvariant : FiniteObject.IsomorphismInvariant Baseline)
    (targetInvariant : FiniteObject.IsomorphismInvariant Target)
    (piece : BoundaryPiece boundary) (outside : OutsideContext boundary)
    (smaller : (cutStateRepresentative baselineInvariant targetInvariant piece).size <
      piece.internalVertexCount)
    (baseline : Baseline (glue piece outside)) (avoids : ¬ Target (glue piece outside)) :
    (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside).vertexCount <
        (glue piece outside).vertexCount ∧
      Baseline (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside) ∧
      ¬ Target (glue (cutStateRepresentative baselineInvariant targetInvariant piece).toPiece outside) := by
  refine ⟨?_, glue_swap_baseline baselineInvariant targetInvariant piece outside baseline, ?_⟩
  · rw [glue_swap_vertexCount, glue_vertexCount]
    omega
  · intro hit
    exact avoids ((glue_swap_target_iff baselineInvariant targetInvariant piece outside).1 hit)

end CanonicalPiece

end Hypostructure.Graph
