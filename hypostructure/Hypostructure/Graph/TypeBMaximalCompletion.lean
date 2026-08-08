import Hypostructure.Graph.TypeBCanonicalB2
import Hypostructure.Graph.DecoratedHandoffEnvelope
import Hypostructure.Graph.SupportComponents

/-!
# Component-indexed Type B handoff completion

This module contains the graph-derived part of `lem:typeB-maximal-completion`
that follows B2(a)--(c).  An exit-`(7)` production is not an arbitrary envelope:
it is the concrete separating pair and its two verified connector tails on one
canonical component of the post-ledger core.  Its envelope is therefore built
only by `DecoratedHandoff.envelopeOfSeparation` and has that component as its
core definitionally.

For a finite family of such productions, the canonical connected-component
partition proves that the cores are pairwise disjoint.  Hence the family gives
one `DecoratedHandoff.GroupedEnvelopes`; neither a core assignment nor a
disjointness proof is supplied by a caller.
-/

namespace Hypostructure.Graph.TypeBMaximalCompletion

open Hypostructure.Graph
open Hypostructure.Graph.SupportComponents
open Hypostructure.Graph.DecoratedHandoff

universe u

variable {object : FiniteObject.{u}}
variable {threshold dischargeScale : Nat}
variable {packing : Finset (Finset object.Vertex)}
variable {piece : TypeBRefinedSupport.CanonicalPiece object packing}

noncomputable section

local instance objectVertexDecidableEq : DecidableEq object.Vertex :=
  object.vertices.decEq

/-- One component of the literal post-B2(a)--(c) remaining core. -/
abbrev RemainingComponent
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece) :=
  Connected.Component object ledger.remainingCore

/-- The concrete graph data produced by Type A exit `(7)` on one canonical
post-ledger component.  No envelope or core-equality proof is stored: the
envelope below is computed from this separation by the paper's
`lem:typeA-high-degree-handoff` constructor. -/
structure ComponentExitSeven
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (component : RemainingComponent ledger)
    (LengthOK : Nat -> Prop)
    (HighDegree : object.Vertex -> Prop)
    (Absorbing : object.Vertex -> object.Vertex -> object.Vertex -> Prop) where
  receiver : object.Vertex
  outside : object.Vertex
  separation : Separation object
    (Connected.vertices object ledger.remainingCore component) receiver outside
  armLeft : List object.Vertex
  armRight : List object.Vertex
  armLeftIssued : armLeft.head? = some separation.nextLeft
  armRightIssued : armRight.head? = some separation.nextRight
  armLeftChain : armLeft.IsChain object.graph.Adj
  armRightChain : armRight.IsChain object.graph.Adj
  armLeftNodup : armLeft.Nodup
  armRightNodup : armRight.Nodup
  armLeftLands : ∃ terminal,
    armLeft.getLast? = some terminal ∧
      terminal ∈ Connected.vertices object ledger.remainingCore component
  armRightLands : ∃ terminal,
    armRight.getLast? = some terminal ∧
      terminal ∈ Connected.vertices object ledger.remainingCore component
  armLeftInterior : ∀ vertex, vertex ∈ armLeft →
    vertex ∈ Connected.vertices object ledger.remainingCore component ∨
        vertex = separation.separator ->
      armLeft.getLast? = some vertex
  armRightInterior : ∀ vertex, vertex ∈ armRight →
    vertex ∈ Connected.vertices object ledger.remainingCore component ∨
        vertex = separation.separator ->
      armRight.getLast? = some vertex
  high : HighDegree separation.separator
  denied : ¬ Absorbing separation.separator separation.nextLeft
    separation.nextRight
  deniedSwap : ¬ Absorbing separation.separator separation.nextRight
    separation.nextLeft

namespace ComponentExitSeven

variable {ledger : TypeBRefinedSupport.DisjointLedger object threshold
  dischargeScale piece}
variable {component : RemainingComponent ledger}
variable {LengthOK : Nat -> Prop}
variable {HighDegree : object.Vertex -> Prop}
variable {Absorbing : object.Vertex -> object.Vertex -> object.Vertex -> Prop}

/-- The actual exit-`(7)` envelope.  Its core is not selected separately: it is
the support indexing `production.separation`. -/
noncomputable def envelope
    (production : ComponentExitSeven ledger component LengthOK HighDegree
      Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    Envelope object LengthOK HighDegree Absorbing :=
  envelopeOfSeparation production.separation production.armLeft
    production.armRight production.armLeftIssued production.armRightIssued
    production.armLeftChain production.armRightChain production.armLeftNodup
    production.armRightNodup production.armLeftLands production.armRightLands
    production.armLeftInterior production.armRightInterior production.high
    avoids production.denied production.deniedSwap

/-- The envelope core is exactly the selected canonical component, by
construction rather than by an authored equality. -/
@[simp] theorem envelope_core
    (production : ComponentExitSeven ledger component LengthOK HighDegree
      Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    (production.envelope avoids).core =
      Connected.vertices object ledger.remainingCore component := by
  rfl

/-- Exit `(7)` contributes exactly its surviving separator as a decoration. -/
@[simp] theorem envelope_decorations
    (production : ComponentExitSeven ledger component LengthOK HighDegree
      Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object) :
    (production.envelope avoids).decorations =
      {production.separation.separator} := by
  rfl

/-- The computed envelope is admissible from the inherited branch invariants. -/
theorem envelope_admissible
    {Uncompressible WindowFree : Finset object.Vertex -> Prop}
    (production : ComponentExitSeven ledger component LengthOK HighDegree
      Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (windowFree : WindowFree
      (Connected.vertices object ledger.remainingCore component))
    (uncompressible : ∀ support : Finset object.Vertex,
      Uncompressible support) :
    Admissible object LengthOK Uncompressible WindowFree
      (production.envelope avoids) := by
  apply admissible_of_envelope avoids
  · simpa using windowFree
  · exact uncompressible

end ComponentExitSeven

/-- The finite subtype of canonical components on which exit `(7)` actually
occurred. -/
abbrev SelectedComponent
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (components : Finset (RemainingComponent ledger)) :=
  {component // component ∈ components}

/-- A finite family of actual component-indexed exit-`(7)` productions gives
the manuscript's one grouped decorated-envelope family.  The only supplied
objects are the actual productions.  Cores, decorations, admissibility, and
pairwise disjointness are all derived. -/
noncomputable def groupedOfComponentExitSeven
    {LengthOK : Nat -> Prop}
    {Uncompressible WindowFree : Finset object.Vertex -> Prop}
    {HighDegree : object.Vertex -> Prop}
    {Absorbing : object.Vertex -> object.Vertex -> object.Vertex -> Prop}
    (ledger : TypeBRefinedSupport.DisjointLedger object threshold dischargeScale
      piece)
    (components : Finset (RemainingComponent ledger))
    (production : ∀ component : SelectedComponent ledger components,
      ComponentExitSeven ledger component.1 LengthOK HighDegree Absorbing)
    (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
    (windowFree : ∀ component, component ∈ components →
      WindowFree (Connected.vertices object ledger.remainingCore component))
    (uncompressible : ∀ support : Finset object.Vertex,
      Uncompressible support) :
    GroupedEnvelopes object LengthOK Uncompressible WindowFree HighDegree
      Absorbing (SelectedComponent ledger components) := by
  classical
  refine
    { cores := Finset.univ
      envelope := fun component => (production component).envelope avoids
      admissible := ?_
      decorated := ?_
      pairwiseCoreDisjoint := ?_ }
  · intro component _member
    exact (production component).envelope_admissible avoids
      (windowFree component.1 component.2) uncompressible
  · intro component _member
    refine ⟨(production component).separation.separator, ?_⟩
    simp
  · intro left right _leftMember _rightMember different
    rw [(production left).envelope_core avoids,
      (production right).envelope_core avoids]
    apply Connected.disjoint_vertices object ledger.remainingCore
    intro equal
    exact different (Subtype.ext equal)

namespace Grouped

variable {LengthOK : Nat -> Prop}
variable {Uncompressible WindowFree : Finset object.Vertex -> Prop}
variable {HighDegree : object.Vertex -> Prop}
variable {Absorbing : object.Vertex -> object.Vertex -> object.Vertex -> Prop}
variable (ledger : TypeBRefinedSupport.DisjointLedger object threshold
  dischargeScale piece)
variable (components : Finset (RemainingComponent ledger))
variable (production : ∀ component : SelectedComponent ledger components,
  ComponentExitSeven ledger component.1 LengthOK HighDegree Absorbing)
variable (avoids : ¬ Graph.HasCycleWithLength LengthOK object)
variable (windowFree : ∀ component, component ∈ components →
  WindowFree (Connected.vertices object ledger.remainingCore component))
variable (uncompressible : ∀ support : Finset object.Vertex,
  Uncompressible support)

private noncomputable abbrev grouped :=
  groupedOfComponentExitSeven ledger components production avoids windowFree
    uncompressible

/-- Every grouped core remains definitionally tied to its canonical component. -/
@[simp] theorem envelope_core
    (component : SelectedComponent ledger components) :
    ((grouped ledger components production avoids windowFree uncompressible).envelope
      component).core =
      Connected.vertices object ledger.remainingCore component.1 := by
  exact (production component).envelope_core avoids

/-- Exact centre coverage: the grouped centre set consists of exactly the
surviving separators produced on the selected canonical components. -/
theorem mem_centres_iff (centre : object.Vertex) :
    centre ∈
        (grouped ledger components production avoids windowFree uncompressible).centres
      ↔
    ∃ component : SelectedComponent ledger components,
      centre = (production component).separation.separator := by
  classical
  rw [DecoratedHandoff.GroupedEnvelopes.mem_centres_iff]
  simp [grouped, groupedOfComponentExitSeven]

/-- The exact finite centre set, without an independently authored family. -/
theorem centres_eq :
    (grouped ledger components production avoids windowFree uncompressible).centres =
      Finset.univ.image
        (fun component : SelectedComponent ledger components =>
          (production component).separation.separator) := by
  classical
  ext centre
  rw [mem_centres_iff ledger components production avoids windowFree
    uncompressible]
  constructor
  · rintro ⟨component, equal⟩
    exact Finset.mem_image.mpr ⟨component, Finset.mem_univ component, equal.symm⟩
  · intro member
    obtain ⟨component, _componentMember, equal⟩ := Finset.mem_image.mp member
    exact ⟨component, equal.symm⟩

end Grouped

end

end Hypostructure.Graph.TypeBMaximalCompletion
