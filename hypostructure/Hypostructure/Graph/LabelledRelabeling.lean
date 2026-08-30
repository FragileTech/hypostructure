import Hypostructure.Graph.LabelledOn
import Hypostructure.Graph.Finite
import Hypostructure.Graph.Isomorphism
import Hypostructure.Graph.BoundaryDemand
import Hypostructure.Graph.RemainderGlue
import Hypostructure.Graph.WindowPacking
import Hypostructure.Core.FiniteRelabelingOrbit
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Relabelling action on canonical labelled graphs

The full permutation group of `Fin n` acts on `LabelledOn n` by transport of
adjacency.  This module exposes the concrete action and its exact
orbit--stabilizer consequences, without mentioning any proof-specific graph
class or entropy threshold.
-/

namespace Hypostructure.Graph.LabelledRelabeling

open Hypostructure.Core

end Hypostructure.Graph.LabelledRelabeling

namespace Hypostructure.Graph

namespace FiniteObject

/-- A graph isomorphism permutes connected components. -/
noncomputable def connectedComponentEquiv {left right : FiniteObject}
    (iso : left.Iso right) :
    left.graph.ConnectedComponent ≃ right.graph.ConnectedComponent where
  toFun := SimpleGraph.ConnectedComponent.map iso.toHom
  invFun := SimpleGraph.ConnectedComponent.map iso.symm.toHom
  left_inv component := by
    rw [SimpleGraph.ConnectedComponent.map_comp]
    exact SimpleGraph.ConnectedComponent.ind (fun vertex => by simp) component
  right_inv component := by
    rw [SimpleGraph.ConnectedComponent.map_comp]
    exact SimpleGraph.ConnectedComponent.ind (fun vertex => by simp) component

/-- The permutation of connected components induced by a graph
self-isomorphism. -/
noncomputable def componentPermutation (object : FiniteObject)
    (iso : object.Iso object) : Equiv.Perm object.graph.ConnectedComponent :=
  connectedComponentEquiv iso

@[simp] theorem componentPermutation_apply_mk (object : FiniteObject)
    (iso : object.Iso object) (vertex : object.Vertex) :
    componentPermutation object iso
        (object.graph.connectedComponentMk vertex) =
      object.graph.connectedComponentMk (iso vertex) := by
  exact SimpleGraph.ConnectedComponent.map_mk iso.toHom vertex

/-- Ambient extensionality for a fixed support and a family of complementary
pieces.  This is the reconstruction step used after component permutation and
all restricted component codes have been shown equal. -/
theorem iso_ext_of_fixedSupport_and_components
    {left right : FiniteObject} (fixed : Finset left.Vertex)
    (components : Finset (Finset left.Vertex))
    (covers : ∀ vertex, vertex ∉ fixed → ∃ component ∈ components,
      vertex ∈ component)
    (first second : left.Iso right)
    (fixedEqual : ∀ vertex ∈ fixed, first vertex = second vertex)
    (componentEqual : ∀ component ∈ components, ∀ vertex ∈ component,
      first vertex = second vertex) :
    first = second := by
  apply RelIso.ext
  intro vertex
  by_cases member : vertex ∈ fixed
  · exact fixedEqual vertex member
  · obtain ⟨component, componentMem, vertexMem⟩ := covers vertex member
    exact componentEqual component componentMem vertex vertexMem

/-- Transport a finite support along a graph isomorphism. -/
noncomputable def transportSupport {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) :
    Finset right.Vertex :=
  support.map iso.toEquiv.toEmbedding

/-- The finite vertex support represented by a connected component. -/
noncomputable def componentSupport (object : FiniteObject)
    (component : object.graph.ConnectedComponent) : Finset object.Vertex := by
  classical
  exact object.vertexFinset.filter (fun vertex => vertex ∈ component.supp)

@[simp] theorem mem_componentSupport_iff (object : FiniteObject)
    (component : object.graph.ConnectedComponent) (vertex : object.Vertex) :
    vertex ∈ componentSupport object component ↔
      object.graph.connectedComponentMk vertex = component := by
  classical
  simp [componentSupport, SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem transport_componentSupport (object : FiniteObject)
    (iso : object.Iso object) (component : object.graph.ConnectedComponent) :
    transportSupport iso (componentSupport object component) =
      componentSupport object (componentPermutation object iso component) := by
  classical
  ext vertex
  constructor
  · intro member
    rcases Finset.mem_map.mp member with ⟨source, sourceMem, rfl⟩
    apply (mem_componentSupport_iff object _ _).2
    change object.graph.connectedComponentMk (iso source) = _
    rw [← componentPermutation_apply_mk]
    exact congrArg (componentPermutation object iso)
      ((mem_componentSupport_iff object component source).1 sourceMem)
  · intro member
    let source := iso.symm vertex
    refine Finset.mem_map.mpr ⟨source, ?_, by simp [source]⟩
    apply (mem_componentSupport_iff object component source).2
    apply (componentPermutation object iso).injective
    simpa [source] using
      (mem_componentSupport_iff object _ vertex).1 member

@[simp] theorem mem_transportSupport_iff {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex)
    (vertex : left.Vertex) :
    iso vertex ∈ transportSupport iso support ↔ vertex ∈ support := by
  classical
  constructor
  · rw [transportSupport, Finset.mem_map]
    rintro ⟨source, sourceMem, equal⟩
    simpa [iso.injective equal] using sourceMem
  · intro member
    exact Finset.mem_map.mpr ⟨vertex, member, rfl⟩

@[simp] theorem card_transportSupport {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) :
    (transportSupport iso support).card = support.card := by
  simp [transportSupport]

/-- An isomorphism restricts to the induced graphs on corresponding supports.
This is the canonical way to cross the distinct subtype vertex types created
by `FiniteObject.induce`. -/
noncomputable def induceIso {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) :
    (left.induce support).Iso (right.induce (transportSupport iso support)) :=
  SimpleGraph.Iso.induce iso (by
    refine ⟨?_, ?_, ?_⟩
    · intro vertex member
      exact (mem_transportSupport_iff iso support vertex).2 member
    · intro leftVertex leftMem rightVertex rightMem equal
      exact iso.injective equal
    · intro rightVertex rightMem
      rcases Finset.mem_map.mp rightMem with ⟨leftVertex, leftMem, equal⟩
      exact ⟨leftVertex, leftMem, equal⟩)

/-- Iterating induced restriction is canonically isomorphic to restricting the
ambient object to the image of the inner support. -/
noncomputable def induceInduceIso (object : FiniteObject)
    (outer : Finset object.Vertex)
    (inner : Finset (object.induce outer).Vertex) :
    ((object.induce outer).induce inner).Iso
      (object.induce (inner.map (object.induceEmbedding outer).toEmbedding)) := by
  let equivalence : ((object.induce outer).induce inner).Vertex ≃
      (object.induce
        (inner.map (object.induceEmbedding outer).toEmbedding)).Vertex :=
    { toFun := fun vertex => ⟨vertex.1.1, Finset.mem_map.mpr
          ⟨vertex.1, vertex.2, rfl⟩⟩
      invFun := fun vertex => ⟨⟨vertex.1, by
          rcases Finset.mem_map.mp vertex.2 with ⟨source, sourceMem, equal⟩
          have underlying : source.1 = vertex.1 := by simpa using equal
          rw [← underlying]
          exact source.property⟩, by
            rcases Finset.mem_map.mp vertex.2 with ⟨source, sourceMem, equal⟩
            have underlying : source.1 = vertex.1 := by simpa using equal
            have sourceEq : source = ⟨vertex.1, by
                rw [← underlying]
                exact source.property⟩ := by
              apply Subtype.ext
              exact underlying
            simpa [sourceEq] using sourceMem⟩
      left_inv := fun vertex => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun vertex => by apply Subtype.ext; rfl }
  refine { toEquiv := equivalence, map_rel_iff' := ?_ }
  intro left right
  rfl

/-- Existence of an induced path is invariant under graph isomorphism. -/
theorem hasInducedPath_iff_iso {left right : FiniteObject}
    (iso : left.Iso right) (order : Nat) :
    HasInducedPath left order ↔ HasInducedPath right order := by
  constructor
  · intro contained
    exact contained.trans ⟨iso.toEmbedding⟩
  · intro contained
    exact contained.trans ⟨iso.symm.toEmbedding⟩

theorem inducesWindow_induce_iff (object : FiniteObject)
    (outer : Finset object.Vertex)
    (inner : Finset (object.induce outer).Vertex) (order : Nat) :
    (object.induce outer).InducesWindow order inner ↔
      object.InducesWindow order
        (inner.map (object.induceEmbedding outer).toEmbedding) := by
  constructor <;> rintro ⟨path, card⟩
  · exact ⟨(hasInducedPath_iff_iso (induceInduceIso object outer inner) order).mp path,
      by simpa using card⟩
  · exact ⟨(hasInducedPath_iff_iso (induceInduceIso object outer inner) order).mpr path,
      by simpa using card⟩

theorem minimumDegreeAtLeast_induce_iff (object : FiniteObject)
    (outer : Finset object.Vertex)
    (inner : Finset (object.induce outer).Vertex) (threshold : Nat) :
    MinimumDegreeAtLeast threshold ((object.induce outer).induce inner) ↔
      MinimumDegreeAtLeast threshold
        (object.induce (inner.map (object.induceEmbedding outer).toEmbedding)) := by
  unfold MinimumDegreeAtLeast
  rw [FiniteObject.minDegree_eq_of_iso (induceInduceIso object outer inner)]

@[simp] theorem internalDegree_vertexFinset (object : FiniteObject)
    (vertex : object.Vertex) :
    object.internalDegree object.vertexFinset vertex = object.degree vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  simp [FiniteObject.internalDegree, FiniteObject.vertexFinset,
    FiniteObject.degree]

@[simp] theorem positiveDeficiency_induce_vertexFinset (object : FiniteObject)
    (support : Finset object.Vertex) (threshold : Nat) :
    (object.induce support).positiveDeficiency
        (object.induce support).vertexFinset threshold =
      object.positiveDeficiency support threshold := by
  classical
  let induced := object.induce support
  letI : Fintype induced.Vertex := @FinEnum.instFintype _ induced.vertices
  unfold positiveDeficiency
  simp_rw [internalDegree_vertexFinset]
  simp_rw [object.degree_induce_eq_internalDegree support]
  exact (Finset.sum_subtype (s := support)
    (p := fun vertex => vertex ∈ support) (by simp)
    (fun vertex : object.Vertex =>
      threshold - object.internalDegree support vertex)).symm

/-- Restrict an isomorphism to one explicit induced support.  In the component
encoder the support is a canonical member set from `SupportComponents`. -/
noncomputable def restrictIso {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) :
    (left.induce support).Iso
      (right.induce (transportSupport iso support)) :=
  induceIso iso support

/-- Restriction of a self-isomorphism from one connected component to the
component selected by its induced component permutation. -/
noncomputable def restrictedComponentIso (object : FiniteObject)
    (iso : object.Iso object) (component : object.graph.ConnectedComponent) :
    (object.induce (componentSupport object component)).Iso
      (object.induce (componentSupport object
        (componentPermutation object iso component))) := by
  let target := componentPermutation object iso component
  let equivalence :
      (object.induce (componentSupport object component)).Vertex ≃
        (object.induce (componentSupport object target)).Vertex :=
    { toFun := fun vertex => ⟨iso vertex.1, by
        apply (mem_componentSupport_iff object target _).2
        change object.graph.connectedComponentMk (iso vertex.1) = target
        rw [← componentPermutation_apply_mk]
        exact congrArg (componentPermutation object iso)
          ((mem_componentSupport_iff object component vertex.1).1 vertex.2)⟩
      invFun := fun vertex => ⟨iso.symm vertex.1, by
        apply (mem_componentSupport_iff object component _).2
        apply (componentPermutation object iso).injective
        simpa [target] using
          (mem_componentSupport_iff object target vertex.1).1 vertex.2⟩
      left_inv := fun vertex => by apply Subtype.ext; simp
      right_inv := fun vertex => by apply Subtype.ext; simp }
  refine { toEquiv := equivalence, map_rel_iff' := ?_ }
  intro left right
  exact iso.map_rel_iff

/-- Target component together with the restricted isomorphism into it.  Keeping
the dependent target and map in one Sigma value avoids eliminating equalities
of quotient-defined connected components in later encoder injectivity proofs. -/
abbrev RestrictedComponentDatum (object : FiniteObject)
    (source : object.graph.ConnectedComponent) :=
  Σ target : object.graph.ConnectedComponent,
    (object.induce (componentSupport object source)).Iso
      (object.induce (componentSupport object target))

noncomputable def restrictedComponentDatum (object : FiniteObject)
    (iso : object.Iso object) (source : object.graph.ConnectedComponent) :
    RestrictedComponentDatum object source :=
  ⟨componentPermutation object iso source,
    restrictedComponentIso object iso source⟩

/-- A deterministic base isomorphism for an inhabited component-pair fibre.
The choice depends only on the two component indices. -/
noncomputable def baseComponentIso (object : FiniteObject)
    (source target : object.graph.ConnectedComponent)
    (inhabited : Nonempty
      ((object.induce (componentSupport object source)).Iso
        (object.induce (componentSupport object target)))) :
    (object.induce (componentSupport object source)).Iso
      (object.induce (componentSupport object target)) :=
  Classical.choice inhabited

noncomputable def normalizeRestrictedComponentDatum (object : FiniteObject)
    (source : object.graph.ConnectedComponent)
    (datum : RestrictedComponentDatum object source) :
    (object.induce (componentSupport object source)).Iso
      (object.induce (componentSupport object source)) :=
  datum.2.trans
    (baseComponentIso object source datum.1 ⟨datum.2⟩).symm

theorem restrictedComponentDatum_eq_of_fst_eq_of_normalize_eq
    (object : FiniteObject) (source : object.graph.ConnectedComponent)
    {first second : RestrictedComponentDatum object source}
    (fstEqual : first.1 = second.1)
    (normalizedEqual : normalizeRestrictedComponentDatum object source first =
      normalizeRestrictedComponentDatum object source second) :
    first = second := by
  rcases first with ⟨firstTarget, firstIso⟩
  rcases second with ⟨secondTarget, secondIso⟩
  dsimp only at fstEqual
  subst secondTarget
  have isoEqual : firstIso = secondIso := by
    apply RelIso.ext
    intro vertex
    have applied := congrArg (fun iso => iso vertex) normalizedEqual
    let base := baseComponentIso object source firstTarget ⟨firstIso⟩
    have recovered := congrArg (fun value => base value) applied
    simpa [normalizeRestrictedComponentDatum, base] using recovered
  exact Sigma.ext rfl (heq_of_eq isoEqual)

theorem restrictedComponentDatum_fst_eq_of_permutation_eq
    (object : FiniteObject) {first second : object.Iso object}
    (permutationEqual : componentPermutation object first =
      componentPermutation object second)
    (source : object.graph.ConnectedComponent) :
    (restrictedComponentDatum object first source).1 =
      (restrictedComponentDatum object second source).1 := by
  exact congrArg (fun permutation => permutation source) permutationEqual

theorem ambient_apply_eq_of_restrictedComponentDatum_eq
    (object : FiniteObject) {first second : object.Iso object}
    (source : object.graph.ConnectedComponent)
    (datumEqual : restrictedComponentDatum object first source =
      restrictedComponentDatum object second source)
    (vertex : object.Vertex)
    (member : vertex ∈ componentSupport object source) :
    first vertex = second vertex := by
  let supported : (object.induce (componentSupport object source)).Vertex :=
    ⟨vertex, member⟩
  have applied := congrArg
    (fun datum : RestrictedComponentDatum object source =>
      (datum.2 supported).1) datumEqual
  simp only [restrictedComponentDatum] at applied
  change first vertex = second vertex at applied
  exact applied

/-- Normalize the restricted component isomorphism by the deterministic base
isomorphism of its source/target fibre.  The result is a self-automorphism of
the source component, so the existing rooted BFS code applies without a
heterogeneous code type. -/
noncomputable def normalizedRestrictedAutomorphism (object : FiniteObject)
    (iso : object.Iso object) (component : object.graph.ConnectedComponent) :
    (object.induce (componentSupport object component)).Iso
      (object.induce (componentSupport object component)) :=
  (restrictedComponentIso object iso component).trans
    (baseComponentIso object component (componentPermutation object iso component)
      ⟨restrictedComponentIso object iso component⟩).symm


@[simp] theorem internalDegree_transport {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex)
    (vertex : left.Vertex) :
    right.internalDegree (transportSupport iso support) (iso vertex) =
      left.internalDegree support vertex := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  classical
  unfold internalDegree
  symm
  apply Finset.card_bij (fun neighbour _ => iso neighbour)
  · intro neighbour neighbourMem
    rw [Finset.mem_inter] at neighbourMem ⊢
    exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).2
      (iso.map_adj_iff.2 ((SimpleGraph.mem_neighborFinset _ _ _).1 neighbourMem.1)),
      (mem_transportSupport_iff iso support neighbour).2 neighbourMem.2⟩
  · intro leftNeighbour _ rightNeighbour _ equal
    exact iso.injective equal
  · intro rightNeighbour rightMem
    rw [Finset.mem_inter] at rightMem
    let leftNeighbour := iso.symm rightNeighbour
    refine ⟨leftNeighbour, ?_, ?_⟩
    · rw [Finset.mem_inter]
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).2
        (iso.map_adj_iff.mp (by simpa [leftNeighbour] using
          (SimpleGraph.mem_neighborFinset _ _ _).1 rightMem.1)),
        (mem_transportSupport_iff iso support leftNeighbour).mp (by
          simpa [leftNeighbour] using rightMem.2)⟩
    · simp [leftNeighbour]

@[simp] theorem positiveDeficiency_transport {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex)
    (threshold : Nat) :
    right.positiveDeficiency (transportSupport iso support) threshold =
      left.positiveDeficiency support threshold := by
  classical
  unfold positiveDeficiency
  symm
  apply Finset.sum_bij (fun vertex _ => iso vertex)
  · intro vertex member
    exact (mem_transportSupport_iff iso support vertex).2 member
  · intro leftVertex _ rightVertex _ equal
    exact iso.injective equal
  · intro rightVertex member
    refine ⟨iso.symm rightVertex,
      (mem_transportSupport_iff iso support _).mp (by simpa using member), by simp⟩
  · intro vertex member
    simp

@[simp] theorem internalEdgeCount_transport {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) :
    right.internalEdgeCount (transportSupport iso support) =
      left.internalEdgeCount support := by
  letI : FinEnum left.Vertex := left.vertices
  letI : DecidableRel left.graph.Adj := left.decideAdj
  letI : FinEnum right.Vertex := right.vertices
  letI : DecidableRel right.graph.Adj := right.decideAdj
  classical
  unfold internalEdgeCount
  symm
  apply Finset.card_bij (fun edge _ => Sym2.map iso edge)
  · intro edge edgeMem
    rw [Finset.mem_filter] at edgeMem ⊢
    constructor
    · rw [SimpleGraph.mem_edgeFinset] at edgeMem ⊢
      induction edge using Sym2.inductionOn with
      | _ a b => exact iso.map_adj_iff.2 edgeMem.1
    · intro vertex vertexMem
      induction edge using Sym2.inductionOn with
      | _ a b =>
        simp only [Sym2.map_mk, Sym2.mem_iff] at vertexMem
        rcases vertexMem with rfl | rfl
        · exact (mem_transportSupport_iff iso support a).2
            (edgeMem.2 a (by simp))
        · exact (mem_transportSupport_iff iso support b).2
            (edgeMem.2 b (by simp))
  · intro first _ second _ equal
    exact Sym2.map.injective iso.injective equal
  · intro edge edgeMem
    refine ⟨Sym2.map iso.symm edge, ?_, ?_⟩
    · rw [Finset.mem_filter] at edgeMem ⊢
      constructor
      · rw [SimpleGraph.mem_edgeFinset] at edgeMem ⊢
        induction edge using Sym2.inductionOn with
        | _ a b => exact iso.map_adj_iff.mp (by simpa using edgeMem.1)
      · intro vertex vertexMem
        induction edge using Sym2.inductionOn with
        | _ a b =>
          simp only [Sym2.map_mk, Sym2.mem_iff] at vertexMem
          rcases vertexMem with rfl | rfl
          · exact (mem_transportSupport_iff iso support _).mp
              (by simpa using edgeMem.2 a (by simp))
          · exact (mem_transportSupport_iff iso support _).mp
              (by simpa using edgeMem.2 b (by simp))
    · induction edge using Sym2.inductionOn with
      | _ a b => simp

/-- Induced-window status is invariant under graph isomorphism, with the
support transported by the same isomorphism. -/
theorem inducesWindow_transport_iff {left right : FiniteObject}
    (iso : left.Iso right) (support : Finset left.Vertex) (order : Nat) :
    right.InducesWindow order (transportSupport iso support) ↔
      left.InducesWindow order support := by
  constructor
  · rintro ⟨window, card⟩
    refine ⟨?_, by simpa using card⟩
    exact window.trans (induceIso iso support).symm.isIndContained
  · rintro ⟨window, card⟩
    refine ⟨?_, by simpa using card⟩
    exact window.trans (induceIso iso support).isIndContained

/-- The assertion that no nonempty induced region has internal minimum degree
at least `threshold` is invariant under relabelling. -/
theorem emptyInternalCore_transport_iff {left right : FiniteObject}
    (iso : left.Iso right) (threshold : Nat) :
    (∀ support : Finset right.Vertex,
      ¬ MinimumDegreeAtLeast threshold (right.induce support)) ↔
    (∀ support : Finset left.Vertex,
      ¬ MinimumDegreeAtLeast threshold (left.induce support)) := by
  constructor
  · intro empty support core
    letI : FinEnum (left.induce support).Vertex := (left.induce support).vertices
    letI : DecidableRel (left.induce support).graph.Adj :=
      (left.induce support).decideAdj
    letI : FinEnum (right.induce (transportSupport iso support)).Vertex :=
      (right.induce (transportSupport iso support)).vertices
    letI : DecidableRel
        (right.induce (transportSupport iso support)).graph.Adj :=
      (right.induce (transportSupport iso support)).decideAdj
    have transported :
        MinimumDegreeAtLeast threshold
          (right.induce (transportSupport iso support)) := by
      unfold MinimumDegreeAtLeast at core ⊢
      simpa only [FiniteObject.minDegree_eq_of_iso (induceIso iso support)]
        using core
    exact empty (transportSupport iso support) transported
  · intro empty support core
    let source := transportSupport iso.symm support
    letI : FinEnum (right.induce support).Vertex := (right.induce support).vertices
    letI : DecidableRel (right.induce support).graph.Adj :=
      (right.induce support).decideAdj
    letI : FinEnum (left.induce source).Vertex := (left.induce source).vertices
    letI : DecidableRel (left.induce source).graph.Adj :=
      (left.induce source).decideAdj
    have sourceCore : MinimumDegreeAtLeast threshold (left.induce source) := by
      unfold MinimumDegreeAtLeast at core ⊢
      simpa only [source,
        FiniteObject.minDegree_eq_of_iso (induceIso iso.symm support)] using core
    exact empty source sourceCore

/-- The action of a graph isomorphism on one neighbour set. -/
noncomputable def neighborIso {left right : FiniteObject}
    (iso : left.Iso right) (vertex : left.Vertex) :
    {neighbor // left.graph.Adj vertex neighbor} ≃
      {neighbor // right.graph.Adj (iso vertex) neighbor} where
  toFun neighbor := ⟨iso neighbor.1, iso.map_adj_iff.2 neighbor.2⟩
  invFun neighbor := ⟨iso.symm neighbor.1, iso.map_adj_iff.mp (by
    simpa using neighbor.2)⟩
  left_inv neighbor := by ext; simp
  right_inv neighbor := by ext; simp

/-- Write a bijection in the canonical finite enumerations of its source and
target.  The result is a permutation of the source index type. -/
noncomputable def equivPermutation {A B : Type*} [Fintype A] [Fintype B]
    (equivValue : A ≃ B) : Equiv.Perm (Fin (Fintype.card A)) :=
  (Fintype.equivFin A).symm.trans
    (equivValue.trans
      ((Fintype.equivFin B).trans (finCongr (Fintype.card_congr equivValue).symm)))

/-- A bijection of a set of size at most three has one of six codes. -/
noncomputable def boundedEquivCode {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (bound : Fintype.card A ≤ 3) : (A ≃ B) → Fin 6 := fun equivValue => by
  exact Fin.castLE (by
      rw [Fintype.card_perm, Fintype.card_fin]
      exact (Nat.factorial_le bound).trans (by decide))
    (Fintype.equivFin (Equiv.Perm (Fin (Fintype.card A)))
      (equivPermutation equivValue))

theorem boundedEquivCode_injective {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (bound : Fintype.card A ≤ 3) :
    Function.Injective (boundedEquivCode (A := A) (B := B) bound) := by
  classical
  intro left right equal
  have permutationEqual : equivPermutation left = equivPermutation right := by
    apply (Fintype.equivFin (Equiv.Perm (Fin (Fintype.card A)))).injective
    exact Fin.castLE_injective _ equal
  apply Equiv.ext
  intro value
  have applied := congrArg
    (fun permutation => permutation (Fintype.equivFin A value)) permutationEqual
  exact (((Fintype.equivFin B).trans
    (finCongr (Fintype.card_congr left).symm)).injective (by
      simpa [equivPermutation] using applied))

theorem boundedEquivCode_transport_neighbor (object : FiniteObject)
    (source : object.Vertex) {leftImage rightImage : object.Vertex}
    (equal : leftImage = rightImage)
    (equivValue :
      {neighbor // object.graph.Adj source neighbor} ≃
        {neighbor // object.graph.Adj rightImage neighbor})
    [Fintype object.Vertex] [DecidableEq object.Vertex]
    [DecidableRel object.graph.Adj]
    (bound : Fintype.card {neighbor // object.graph.Adj source neighbor} ≤ 3) :
    boundedEquivCode bound (equal.symm ▸ equivValue) =
      boundedEquivCode bound equivValue := by
  subst rightImage
  rfl

theorem transport_neighbor_equiv_val (object : FiniteObject)
    (source : object.Vertex) {leftImage rightImage : object.Vertex}
    (equal : leftImage = rightImage)
    (equivValue :
      {neighbor // object.graph.Adj source neighbor} ≃
        {neighbor // object.graph.Adj rightImage neighbor})
    (neighbor : {neighbor // object.graph.Adj source neighbor}) :
    ((equal.symm ▸ equivValue) neighbor).1 = (equivValue neighbor).1 := by
  subst rightImage
  rfl

/-- Root image plus the six-way local neighbour bijection at every vertex.
For a subcubic graph this is the manuscript's breadth-first automorphism
code. -/
noncomputable def rootedAutomorphismCode (object : FiniteObject)
    (root : object.Vertex)
    (subcubic : ∀ vertex, object.degree vertex ≤ 3)
    (automorphism : object.Iso object) :
    object.Vertex × (object.Vertex → Fin 6) :=
  by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  exact ⟨automorphism root, fun vertex =>
    boundedEquivCode (B :=
      {neighbor // object.graph.Adj (automorphism vertex) neighbor})
      (by
        change Fintype.card (object.graph.neighborSet vertex) ≤ 3
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact subcubic vertex)
      (neighborIso automorphism vertex)⟩

/-- Connectedness makes the rooted local code injective: equality propagates
from the root along a walk, one neighbour at a time. -/
theorem rootedAutomorphismCode_injective (object : FiniteObject)
    (root : object.Vertex) (connected : object.graph.Preconnected)
    (subcubic : ∀ vertex, object.degree vertex ≤ 3) :
    Function.Injective (rootedAutomorphismCode object root subcubic) := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableEq object.Vertex := object.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  intro left right codeEqual
  apply RelIso.ext
  intro vertex
  have rootEqual : left root = right root := congrArg Prod.fst codeEqual
  have functionEqual :
      (rootedAutomorphismCode object root subcubic left).2 =
        (rootedAutomorphismCode object root subcubic right).2 :=
    congrArg Prod.snd codeEqual
  have step : ∀ {source target}, object.graph.Adj source target →
      left source = right source → left target = right target := by
    intro source target adjacent imageEqual
    have localCodeEqual := congrFun functionEqual source
    simp only [rootedAutomorphismCode] at localCodeEqual
    change boundedEquivCode _ (neighborIso left source) =
      boundedEquivCode _ (neighborIso right source) at localCodeEqual
    let transported :
        {neighbor // object.graph.Adj source neighbor} ≃
          {neighbor // object.graph.Adj (left source) neighbor} :=
      imageEqual.symm ▸ neighborIso right source
    have sourceBound :
        Fintype.card {neighbor // object.graph.Adj source neighbor} ≤ 3 := by
      change Fintype.card (object.graph.neighborSet source) ≤ 3
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact subcubic source
    have transportedCodeEqual :
        boundedEquivCode sourceBound (neighborIso left source) =
          boundedEquivCode sourceBound transported := by
      calc
        boundedEquivCode sourceBound (neighborIso left source) =
            boundedEquivCode sourceBound (neighborIso right source) := by
          simpa only using localCodeEqual
        _ = boundedEquivCode sourceBound transported :=
          (boundedEquivCode_transport_neighbor object source imageEqual
            (neighborIso right source) sourceBound).symm
    have localIsoEqual : neighborIso left source = transported :=
      boundedEquivCode_injective sourceBound transportedCodeEqual
    have applied := congrArg
      (fun equivValue => (equivValue :
        {neighbor // object.graph.Adj source neighbor} ≃
          {neighbor // object.graph.Adj (left source) neighbor})
        ⟨target, adjacent⟩) localIsoEqual
    have values := congrArg Subtype.val applied
    have transportedValue :
        (transported ⟨target, adjacent⟩).1 = right target := by
      exact transport_neighbor_equiv_val object source imageEqual
        (neighborIso right source) ⟨target, adjacent⟩
    exact values.trans transportedValue
  have along : ∀ {source target} (walk : object.graph.Walk source target),
      left source = right source → left target = right target := by
    intro source target walk
    induction walk with
    | nil => intro equal; exact equal
    | @cons source middle target adjacent tail ih =>
        intro equal
        exact ih (step adjacent equal)
  obtain ⟨walk⟩ := connected root vertex
  exact along walk rootEqual

/-- Component permutation together with one rooted BFS self-code on every
source component, after deterministic base-isomorphism normalization. -/
noncomputable def componentAutomorphismCode (object : FiniteObject)
    (root : ∀ component : object.graph.ConnectedComponent,
      (object.induce (componentSupport object component)).Vertex)
    (_connected : ∀ component,
      (object.induce (componentSupport object component)).graph.Preconnected)
    (subcubic : ∀ component vertex,
      (object.induce (componentSupport object component)).degree vertex ≤ 3)
    (iso : object.Iso object) :
    Equiv.Perm object.graph.ConnectedComponent ×
      (∀ component : object.graph.ConnectedComponent,
        (object.induce (componentSupport object component)).Vertex ×
          ((object.induce (componentSupport object component)).Vertex → Fin 6)) :=
  ⟨componentPermutation object iso, fun component =>
    rootedAutomorphismCode
      (object.induce (componentSupport object component))
      (root component) (subcubic component)
      (normalizedRestrictedAutomorphism object iso component)⟩

theorem normalizedRestrictedAutomorphism_eq_of_componentCode_eq
    (object : FiniteObject)
    (root : ∀ component : object.graph.ConnectedComponent,
      (object.induce (componentSupport object component)).Vertex)
    (connected : ∀ component,
      (object.induce (componentSupport object component)).graph.Preconnected)
    (subcubic : ∀ component vertex,
      (object.induce (componentSupport object component)).degree vertex ≤ 3)
    {first second : object.Iso object}
    (codeEqual : componentAutomorphismCode object root connected subcubic first =
      componentAutomorphismCode object root connected subcubic second)
    (component : object.graph.ConnectedComponent) :
    normalizedRestrictedAutomorphism object first component =
      normalizedRestrictedAutomorphism object second component := by
  have localCodes := congrFun (congrArg Prod.snd codeEqual) component
  exact rootedAutomorphismCode_injective
    (object.induce (componentSupport object component))
    (root component) (connected component) (subcubic component) localCodes

theorem componentAutomorphismCode_injective
    (object : FiniteObject)
    (root : ∀ component : object.graph.ConnectedComponent,
      (object.induce (componentSupport object component)).Vertex)
    (connected : ∀ component,
      (object.induce (componentSupport object component)).graph.Preconnected)
    (subcubic : ∀ component vertex,
      (object.induce (componentSupport object component)).degree vertex ≤ 3) :
    Function.Injective
      (componentAutomorphismCode object root connected subcubic) := by
  intro first second codeEqual
  apply RelIso.ext
  intro vertex
  let component := object.graph.connectedComponentMk vertex
  have member : vertex ∈ componentSupport object component :=
    (mem_componentSupport_iff object component vertex).2 rfl
  have permutationEqual : componentPermutation object first =
      componentPermutation object second := congrArg Prod.fst codeEqual
  have fstEqual := restrictedComponentDatum_fst_eq_of_permutation_eq object
    permutationEqual component
  have normalizedEqual :=
    normalizedRestrictedAutomorphism_eq_of_componentCode_eq object root
      connected subcubic codeEqual component
  have datumEqual : restrictedComponentDatum object first component =
      restrictedComponentDatum object second component := by
    apply restrictedComponentDatum_eq_of_fst_eq_of_normalize_eq object component
      fstEqual
    simpa [normalizeRestrictedComponentDatum, restrictedComponentDatum,
      normalizedRestrictedAutomorphism] using normalizedEqual
  exact ambient_apply_eq_of_restrictedComponentDatum_eq object component
    datumEqual vertex member

@[reducible] noncomputable def componentFintype (object : FiniteObject) :
    Fintype object.graph.ConnectedComponent := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  exact Fintype.ofFinite object.graph.ConnectedComponent

/-- Exact `K!` component-permutation bound with one rooted six-way BFS code
per vertex of each connected subcubic component. -/
theorem card_automorphisms_le_component_factorial_mul_prod
    (object : FiniteObject)
    (root : ∀ component : object.graph.ConnectedComponent,
      (object.induce (componentSupport object component)).Vertex)
    (connected : ∀ component,
      (object.induce (componentSupport object component)).graph.Preconnected)
    (subcubic : ∀ component vertex,
      (object.induce (componentSupport object component)).degree vertex ≤ 3) :
    (letI : Fintype object.graph.ConnectedComponent := componentFintype object
     Nat.card (object.Iso object) ≤
       Nat.factorial (Fintype.card object.graph.ConnectedComponent) *
         ∏ component : object.graph.ConnectedComponent,
           Nat.card
             ((object.induce (componentSupport object component)).Vertex ×
               ((object.induce (componentSupport object component)).Vertex →
                 Fin 6))) := by
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : Fintype object.graph.ConnectedComponent := componentFintype object
  letI : Finite (object.Iso object) := Finite.of_injective
    (fun iso : object.Iso object => fun vertex => iso vertex) (by
      intro left right equal
      apply RelIso.ext
      exact congrFun equal)
  letI (component : object.graph.ConnectedComponent) :
      Fintype (object.induce (componentSupport object component)).Vertex :=
    @FinEnum.instFintype _
      (object.induce (componentSupport object component)).vertices
  letI (component : object.graph.ConnectedComponent) :
      Fintype
        ((object.induce (componentSupport object component)).Vertex ×
          ((object.induce (componentSupport object component)).Vertex → Fin 6)) :=
    Fintype.ofFinite _
  let encode := componentAutomorphismCode object root connected subcubic
  have bound :=
    Hypostructure.Core.FiniteRelabelingOrbit.card_le_factorial_mul_prod_of_component_encoding
      encode (componentAutomorphismCode_injective object root connected subcubic)
  simpa only [Nat.card_eq_fintype_card] using bound

/-- A finite connected subcubic graph has at most `|V|·6^|V|`
automorphisms. -/
theorem card_automorphisms_le_card_mul_six_pow (object : FiniteObject)
    (root : object.Vertex) (connected : object.graph.Preconnected)
    (subcubic : ∀ vertex, object.degree vertex ≤ 3) :
    Nat.card (object.Iso object) ≤
      Nat.card object.Vertex * 6 ^ Nat.card object.Vertex := by
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  letI : Fintype object.Vertex := @FinEnum.instFintype _ object.vertices
  letI : Finite (object.Iso object) := Finite.of_injective
    (fun iso : object.Iso object => fun vertex => iso vertex) (by
      intro left right equal
      apply RelIso.ext
      exact congrFun equal)
  exact
    Hypostructure.Core.FiniteRelabelingOrbit.card_le_card_mul_six_pow_of_rooted_local_encoding
      (rootedAutomorphismCode object root subcubic)
      (rootedAutomorphismCode_injective object root connected subcubic)

/-- The literal induced graph transported to the canonical carrier
`Fin support.card`. -/
noncomputable def labelledInduce (object : FiniteObject)
    (support : Finset object.Vertex) : LabelledOn support.card := by
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  letI : Fintype induced.Vertex := @FinEnum.instFintype _ induced.vertices
  let equivalence : induced.Vertex ≃ Fin support.card :=
    (Fintype.equivFin induced.Vertex).trans
      (finCongr (by
        rw [← object.vertexCount_induce support]
        exact (@FinEnum.card_eq_fintypeCard _ induced.vertices _).symm))
  exact ⟨equivalence.simpleGraph induced.graph⟩

/-- The canonical labelled induced graph retains the literal induced graph up
to the defining relabelling isomorphism. -/
noncomputable def labelledInduceIso (object : FiniteObject)
    (support : Finset object.Vertex) :
    (object.induce support).Iso (labelledInduce object support).toFiniteObject := by
  let induced := object.induce support
  letI : FinEnum induced.Vertex := induced.vertices
  letI : Fintype induced.Vertex := @FinEnum.instFintype _ induced.vertices
  let equivalence : induced.Vertex ≃ Fin support.card :=
    (Fintype.equivFin induced.Vertex).trans
      (finCongr (by
        rw [← object.vertexCount_induce support]
        exact (@FinEnum.card_eq_fintypeCard _ induced.vertices _).symm))
  refine { toEquiv := equivalence, map_rel_iff' := ?_ }
  intro left right
  change (equivalence.simpleGraph induced.graph).Adj
      (equivalence left) (equivalence right) ↔ induced.graph.Adj left right
  simp

@[simp] theorem card_edgeSet_labelledInduce (object : FiniteObject)
    (support : Finset object.Vertex) :
    Nat.card (labelledInduce object support).graph.edgeSet =
      object.internalEdgeCount support := by
  classical
  letI : FinEnum object.Vertex := object.vertices
  letI : DecidableRel object.graph.Adj := object.decideAdj
  let induced := object.induce support
  let embedding := object.induceEmbedding support
  change Nat.card (labelledInduce object support).toFiniteObject.graph.edgeSet = _
  let contained : Set object.graph.edgeSet :=
    {edge | ∀ vertex ∈ edge.1, vertex ∈ support}
  have rangeEq : Set.range embedding.mapEdgeSet = contained := by
    ext edge
    constructor
    · rintro ⟨source, rfl⟩ vertex vertexMem
      change vertex ∈ Sym2.map embedding source.1 at vertexMem
      rcases (Sym2.mem_map.mp vertexMem) with ⟨preimage, _, imageEq⟩
      rw [← imageEq]
      exact preimage.property
    · intro edgeContained
      generalize edgeEq : edge.1 = rawEdge
      induction rawEdge using Sym2.inductionOn with
      | _ left right =>
          have leftIn : left ∈ edge.1 := by
            rw [edgeEq]
            exact (Sym2.mem_iff).2 (Or.inl rfl)
          have rightIn : right ∈ edge.1 := by
            rw [edgeEq]
            exact (Sym2.mem_iff).2 (Or.inr rfl)
          have leftMem : left ∈ support := edgeContained left
            leftIn
          have rightMem : right ∈ support := edgeContained right
            rightIn
          let lifted : Sym2 induced.Vertex :=
            s(⟨left, leftMem⟩, ⟨right, rightMem⟩)
          have liftedEdge : lifted ∈ induced.graph.edgeSet := by
            change object.graph.Adj left right
            apply (SimpleGraph.mem_edgeSet object.graph).1
            rw [← edgeEq]
            exact edge.property
          refine ⟨⟨lifted, liftedEdge⟩, ?_⟩
          apply Subtype.ext
          change s(left, right) = edge.1
          exact edgeEq.symm
  let inducedEquivContained : induced.graph.edgeSet ≃ contained :=
    (Equiv.ofInjective embedding.mapEdgeSet embedding.mapEdgeSet.injective).trans
      (Equiv.setCongr rangeEq)
  let filtered := object.graph.edgeFinset.filter
    fun edge => ∀ vertex ∈ edge, vertex ∈ support
  let containedEquivFiltered : contained ≃ ↑filtered :=
    { toFun := fun edge => ⟨edge.1.1, Finset.mem_filter.mpr
        ⟨(SimpleGraph.mem_edgeFinset).2 edge.1.2, edge.2⟩⟩
      invFun := fun edge => ⟨⟨edge.1,
        (SimpleGraph.mem_edgeFinset).1 (Finset.mem_filter.mp edge.2).1⟩,
        (Finset.mem_filter.mp edge.2).2⟩
      left_inv := fun edge => by rfl
      right_inv := fun edge => by rfl }
  calc
    Nat.card (labelledInduce object support).toFiniteObject.graph.edgeSet =
        Nat.card induced.graph.edgeSet := by
      rw [Nat.card_congr (labelledInduceIso object support).mapEdgeSet]
    _ = Nat.card contained := Nat.card_congr inducedEquivContained
    _ = Nat.card ↑filtered := Nat.card_congr containedEquivFiltered
    _ = filtered.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = object.internalEdgeCount support := rfl

@[simp] theorem positiveDeficiency_labelledInduce (object : FiniteObject)
    (support : Finset object.Vertex) (threshold : Nat) :
    (labelledInduce object support).toFiniteObject.positiveDeficiency
        (labelledInduce object support).toFiniteObject.vertexFinset threshold =
      object.positiveDeficiency support threshold := by
  classical
  let iso := labelledInduceIso object support
  have transported := positiveDeficiency_transport iso
    (object.induce support).vertexFinset threshold
  have fullSupport :
      transportSupport iso (object.induce support).vertexFinset =
        (labelledInduce object support).toFiniteObject.vertexFinset := by
    ext vertex
    simp [transportSupport]
  rw [fullSupport] at transported
  exact transported.trans (positiveDeficiency_induce_vertexFinset object support threshold)

/-- The canonical labelled restriction is a literal member of the remainder
class cut out by the inherited hereditary constraints. -/
theorem labelledInduce_mem_remainderClass (object : FiniteObject)
    (support : Finset object.Vertex) (order threshold : Nat)
    (windowFree : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ object.InducesWindow order inner)
    (coreFree : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ MinimumDegreeAtLeast threshold (object.induce inner)) :
    let labelled := labelledInduce object support
    labelled ∈ Set.range
      (fun candidate : RemainderClass order threshold
          (labelled.toFiniteObject.positiveDeficiency
            labelled.toFiniteObject.vertexFinset threshold)
          (Nat.card labelled.graph.edgeSet) support.card => candidate.val) := by
  classical
  let labelled := labelledInduce object support
  let iso := labelledInduceIso object support
  letI : Fintype (object.induce support).Vertex :=
    @FinEnum.instFintype _ (object.induce support).vertices
  letI : Fintype labelled.toFiniteObject.Vertex := Fin.fintype support.card
  refine ⟨⟨labelled, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro inner window
    let source := transportSupport iso.symm inner
    have sourceWindow : (object.induce support).InducesWindow order source :=
      (inducesWindow_transport_iff iso.symm inner order).2 window
    let ambient := source.map (object.induceEmbedding support).toEmbedding
    apply windowFree ambient
    · intro vertex member
      rcases Finset.mem_map.mp member with ⟨sourceVertex, _, rfl⟩
      exact sourceVertex.property
    · exact (inducesWindow_induce_iff object support source order).1 sourceWindow
  · intro inner core
    let source := transportSupport iso.symm inner
    have sourceCore : MinimumDegreeAtLeast threshold
        ((object.induce support).induce source) := by
      unfold MinimumDegreeAtLeast at core ⊢
      rw [← FiniteObject.minDegree_eq_of_iso (induceIso iso.symm inner)]
      exact core
    let ambient := source.map (object.induceEmbedding support).toEmbedding
    apply coreFree ambient
    · intro vertex member
      rcases Finset.mem_map.mp member with ⟨sourceVertex, _, rfl⟩
      exact sourceVertex.property
    · exact (minimumDegreeAtLeast_induce_iff object support source threshold).1 sourceCore
  · change labelled.toFiniteObject.positiveDeficiency Finset.univ threshold ≤
      labelled.toFiniteObject.positiveDeficiency
        labelled.toFiniteObject.vertexFinset threshold
    have allVertices : labelled.toFiniteObject.vertexFinset = Finset.univ := by
      ext vertex
      simp [FiniteObject.vertexFinset]
    rw [allVertices]

end FiniteObject

end Hypostructure.Graph

namespace Hypostructure.Graph.LabelledRelabeling

open Hypostructure.Core

/-- Transport the labels of a canonical graph by a permutation. -/
def relabel {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) : LabelledOn n :=
  ⟨permutation.simpleGraph graph.graph⟩

/-- Relabelling is the canonical graph isomorphism induced by the same
permutation. -/
def relabelIso {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) :
    graph.toFiniteObject.Iso (relabel permutation graph).toFiniteObject where
  toEquiv := permutation
  map_rel_iff' := by
    intro left right
    change (permutation.simpleGraph graph.graph).Adj
      (permutation left) (permutation right) ↔ graph.graph.Adj left right
    simp

@[simp] theorem relabel_graph {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) :
    (relabel permutation graph).graph = permutation.simpleGraph graph.graph := rfl

@[simp] theorem relabel_adj_iff {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) (left right : Fin n) :
    (relabel permutation graph).graph.Adj (permutation left) (permutation right) ↔
      graph.graph.Adj left right := by
  simp [relabel]

/-- Relabelling bijects the neighbours of a vertex. -/
def neighborEquiv {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) (vertex : Fin n) :
    {neighbor // graph.graph.Adj vertex neighbor} ≃
      {neighbor // (relabel permutation graph).graph.Adj
        (permutation vertex) neighbor} where
  toFun neighbor := ⟨permutation neighbor.1, by simpa using neighbor.2⟩
  invFun neighbor := ⟨permutation.symm neighbor.1, by
    simpa using neighbor.2⟩
  left_inv neighbor := by ext; simp
  right_inv neighbor := by ext; simp

/-- Vertex degree is invariant under relabelling. -/
theorem degree_relabel {n : Nat} (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n) (vertex : Fin n) :
    (relabel permutation graph).toFiniteObject.degree (permutation vertex) =
      graph.toFiniteObject.degree vertex := by
  rw [FiniteObject.degree_eq_ncard_neighborSet,
    FiniteObject.degree_eq_ncard_neighborSet]
  exact Nat.card_congr (neighborEquiv permutation graph vertex).symm

/-- Relabel a finite vertex support with the same permutation as its graph. -/
def relabelSupport {n : Nat} (permutation : Equiv.Perm (Fin n))
    (support : Finset (Fin n)) : Finset (Fin n) :=
  support.map permutation.toEmbedding

@[simp] theorem mem_relabelSupport_iff {n : Nat}
    (permutation : Equiv.Perm (Fin n)) (support : Finset (Fin n))
    (vertex : Fin n) :
    permutation vertex ∈ relabelSupport permutation support ↔ vertex ∈ support := by
  simp [relabelSupport]

@[simp] theorem card_relabelSupport {n : Nat}
    (permutation : Equiv.Perm (Fin n)) (support : Finset (Fin n)) :
    (relabelSupport permutation support).card = support.card := by
  simp [relabelSupport]


instance instMulAction (n : Nat) : MulAction (Equiv.Perm (Fin n)) (LabelledOn n) where
  smul := relabel
  one_smul _graph := rfl
  mul_smul _left _right _graph := rfl

/-- The literal normalized-remainder class is closed under every relabelling
of its inherited finite vertex set. -/
theorem remainderClass_relabel_mem {n order threshold deficiencyCap edgeCount : Nat}
    (permutation : Equiv.Perm (Fin n))
    (graph : LabelledOn n)
    (member : graph ∈
      {candidate : LabelledOn n |
        candidate ∈ Set.range
          (fun candidate : RemainderClass order threshold deficiencyCap edgeCount n =>
            candidate.val)}) :
    permutation • graph ∈
      {candidate : LabelledOn n |
        candidate ∈ Set.range
          (fun candidate : RemainderClass order threshold deficiencyCap edgeCount n =>
            candidate.val)} := by
  classical
  rcases member with ⟨candidate, rfl⟩
  let iso := relabelIso permutation candidate.val
  letI : Fintype candidate.val.toFiniteObject.Vertex := Fin.fintype n
  letI : Fintype (relabel permutation candidate.val).toFiniteObject.Vertex :=
    Fin.fintype n
  refine ⟨⟨relabel permutation candidate.val, ?_⟩, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support window
    let source := FiniteObject.transportSupport iso.symm support
    have sourceWindow : candidate.val.toFiniteObject.InducesWindow order source := by
      simpa [source] using
        (FiniteObject.inducesWindow_transport_iff iso.symm support order).mpr window
    exact candidate.property.1 source sourceWindow
  · exact (FiniteObject.emptyInternalCore_transport_iff iso threshold).2
      candidate.property.2.1
  · have transported :=
      FiniteObject.positiveDeficiency_transport iso
        (Finset.univ : Finset candidate.val.toFiniteObject.Vertex) threshold
    have supportEq : FiniteObject.transportSupport iso
        (Finset.univ : Finset candidate.val.toFiniteObject.Vertex) = Finset.univ := by
      ext vertex
      simp [FiniteObject.transportSupport]
    have equal :
        (relabel permutation candidate.val).toFiniteObject.positiveDeficiency
            Finset.univ threshold =
          candidate.val.toFiniteObject.positiveDeficiency Finset.univ threshold := by
      rw [← supportEq]
      exact transported
    have bound : candidate.val.toFiniteObject.positiveDeficiency
        (Finset.univ : Finset candidate.val.toFiniteObject.Vertex) threshold ≤
          deficiencyCap := by
      exact candidate.property.2.2.1
    exact equal.trans_le bound
  · have equal : Nat.card (relabel permutation candidate.val).graph.edgeSet =
        Nat.card candidate.val.graph.edgeSet := by
      exact (Nat.card_congr iso.mapEdgeSet).symm
    exact equal.trans candidate.property.2.2.2

/-- A relabelling-closed labelled class contains the complete orbit of each of
its members. -/
theorem orbit_subset_of_closed {n : Nat} (accepted : Set (LabelledOn n))
    (closed : ∀ permutation : Equiv.Perm (Fin n), ∀ graph, graph ∈ accepted →
      permutation • graph ∈ accepted)
    {graph : LabelledOn n} (member : graph ∈ accepted) :
    MulAction.orbit (Equiv.Perm (Fin n)) graph ⊆ accepted := by
  rintro relabelled ⟨permutation, rfl⟩
  exact closed permutation graph member

/-- Exact finite orbit lower bound for a concrete relabelling-closed class of
labelled graphs. -/
theorem factorial_le_class_card_mul_stabilizer {n : Nat}
    (accepted : Set (LabelledOn n))
    (closed : ∀ permutation : Equiv.Perm (Fin n), ∀ graph, graph ∈ accepted →
      permutation • graph ∈ accepted)
    {graph : LabelledOn n} (member : graph ∈ accepted) :
    Nat.factorial n ≤
      Nat.card accepted *
        Nat.card (MulAction.stabilizer (Equiv.Perm (Fin n)) graph) := by
  have orbitBound :=
    FiniteRelabelingOrbit.card_group_le_card_mul_card_stabilizer
      graph accepted (orbit_subset_of_closed accepted closed member)
  have groupCard : Nat.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Nat.card_perm, Nat.card_fin]
  rw [groupCard] at orbitBound
  exact orbitBound

/-- Exact finite orbit lower bound for the canonical labelled restriction of
a hereditary normalized remainder. -/
theorem factorial_le_remainderStateCount_mul_stabilizer
    (object : FiniteObject) (support : Finset object.Vertex)
    (order threshold : Nat)
    (windowFree : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ object.InducesWindow order inner)
    (coreFree : ∀ inner : Finset object.Vertex, inner ⊆ support →
      ¬ MinimumDegreeAtLeast threshold (object.induce inner)) :
    let labelled := object.labelledInduce support
    Nat.factorial support.card ≤
      remainderStateCount order threshold
          (labelled.toFiniteObject.positiveDeficiency
            labelled.toFiniteObject.vertexFinset threshold)
          (Nat.card labelled.graph.edgeSet) support.card *
        Nat.card (MulAction.stabilizer
          (Equiv.Perm (Fin support.card)) labelled) := by
  classical
  let labelled := object.labelledInduce support
  let accepted : Set (LabelledOn support.card) :=
    Set.range (fun candidate : RemainderClass order threshold
      (labelled.toFiniteObject.positiveDeficiency
        labelled.toFiniteObject.vertexFinset threshold)
      (Nat.card labelled.graph.edgeSet) support.card => candidate.val)
  have member : labelled ∈ accepted := by
    exact object.labelledInduce_mem_remainderClass support order threshold
      windowFree coreFree
  have orbit := factorial_le_class_card_mul_stabilizer accepted
    (fun permutation graph graphMem =>
      remainderClass_relabel_mem permutation graph graphMem) member
  have acceptedCard : Nat.card accepted =
      remainderStateCount order threshold
        (labelled.toFiniteObject.positiveDeficiency
          labelled.toFiniteObject.vertexFinset threshold)
        (Nat.card labelled.graph.edgeSet) support.card := by
    apply Nat.card_congr
    let injectCandidate := fun candidate : RemainderClass order threshold
        (labelled.toFiniteObject.positiveDeficiency
          labelled.toFiniteObject.vertexFinset threshold)
        (Nat.card labelled.graph.edgeSet) support.card => candidate.val
    exact
      { toFun := fun graph => Classical.choose graph.property
        invFun := fun candidate =>
          ⟨injectCandidate candidate, ⟨candidate, rfl⟩⟩
        left_inv := fun graph => by
          apply Subtype.ext
          exact Classical.choose_spec graph.property
        right_inv := fun candidate => by
          apply Subtype.ext
          exact Classical.choose_spec
            ((⟨injectCandidate candidate, ⟨candidate, rfl⟩⟩ : accepted)).property }
  rw [acceptedCard] at orbit
  simpa only using orbit

/-- Exact fibre lower bound when a state assignment is invariant under a
chosen relabelling group.  Taking the acting group to be the subgroup fixing a
window support pointwise gives the fixed-window form. -/
theorem group_card_le_state_fibre_card_mul_stabilizer
    {n : Nat} {Acting : Type*} [Group Acting]
    [MulAction Acting (LabelledOn n)] [Finite Acting]
    {State : Type*} (state : LabelledOn n → State) (graph : LabelledOn n)
    (invariant : ∀ permutation : Acting,
      state (permutation • graph) = state graph) :
    Nat.card Acting ≤
      Nat.card {candidate | state candidate = state graph} *
        Nat.card (MulAction.stabilizer Acting graph) :=
  FiniteRelabelingOrbit.card_group_le_fibre_card_mul_card_stabilizer
    state graph invariant

/-- The literal group of relabellings fixing a distinguished vertex support
pointwise. -/
abbrev FixedSupportPermutations {n : Nat} (support : Finset (Fin n)) :=
  fixingSubgroup (Equiv.Perm (Fin n)) (support : Set (Fin n))

/-- Relabellings fixing `support` pointwise are exactly the permutations of
its complement. -/
theorem card_fixedSupportPermutations {n : Nat} (support : Finset (Fin n)) :
    Nat.card (FixedSupportPermutations support) =
      Nat.factorial (n - support.card) := by
  classical
  let Complement := {vertex : Fin n // vertex ∉ support}
  have inRange (permutation : FixedSupportPermutations support) :
      permutation.1 ∈
        (Equiv.Perm.ofSubtype :
          Equiv.Perm Complement →* Equiv.Perm (Fin n)).range := by
    rw [Equiv.Perm.mem_range_ofSubtype_iff]
    intro vertex moved
    simp only [Set.mem_setOf_eq]
    intro member
    have fixed :=
      (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).mp permutation.2
        vertex member
    exact (Equiv.Perm.mem_support.mp moved) fixed
  let complementEquiv :
      Equiv.Perm Complement ≃ FixedSupportPermutations support :=
    { toFun := fun permutation =>
        ⟨Equiv.Perm.ofSubtype permutation, by
          rw [mem_fixingSubgroup_iff]
          intro vertex member
          exact Equiv.Perm.ofSubtype_apply_of_not_mem permutation (by
            simpa using member)⟩
      invFun := fun permutation => Classical.choose (inRange permutation)
      left_inv := fun permutation => by
        apply Equiv.Perm.ofSubtype_injective
        exact Classical.choose_spec (inRange
          (⟨Equiv.Perm.ofSubtype permutation, by
            rw [mem_fixingSubgroup_iff]
            intro vertex member
            exact Equiv.Perm.ofSubtype_apply_of_not_mem permutation (by
              simpa using member)⟩ :
              FixedSupportPermutations support))
      right_inv := fun permutation => by
        apply Subtype.ext
        exact Classical.choose_spec (inRange permutation) }
  rw [← Nat.card_congr complementEquiv, Nat.card_perm]
  have complementCard : Nat.card Complement = n - support.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin]
    simp
  rw [complementCard]

/-- Fixed-support specialization of the invariant-fibre orbit bound. -/
theorem fixedSupport_card_le_state_fibre_card_mul_stabilizer
    {n : Nat} (support : Finset (Fin n))
    {State : Type*} (state : LabelledOn n → State) (graph : LabelledOn n)
    (invariant : ∀ permutation : FixedSupportPermutations support,
      state (permutation • graph) = state graph) :
    Nat.card (FixedSupportPermutations support) ≤
      Nat.card {candidate | state candidate = state graph} *
        Nat.card (MulAction.stabilizer
          (FixedSupportPermutations support) graph) :=
  group_card_le_state_fibre_card_mul_stabilizer state graph invariant

end Hypostructure.Graph.LabelledRelabeling
