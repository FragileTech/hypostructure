import Hypostructure.Graph.TypeBMaximalCompletion

/-!
# Fixture: canonical component-indexed Type B handoff completion

This fixture exercises the generic graph theorem only.  The inputs are actual
exit-`(7)` separations and connector tails; no Strategy fact, history, or
authored envelope assignment is involved.
-/

namespace Hypostructure.Fixtures.TypeBMaximalCompletion

open Hypostructure.Graph
open Hypostructure.Graph.SupportComponents
open Hypostructure.Graph.TypeBMaximalCompletion

universe u

variable {object : FiniteObject.{u}}
variable {threshold dischargeScale : Nat}
variable {packing : Finset (Finset object.Vertex)}
variable {piece : TypeBRefinedSupport.CanonicalPiece object packing}
variable {LengthOK : Nat -> Prop}
variable {Uncompressible WindowFree : Finset object.Vertex -> Prop}
variable {HighDegree : object.Vertex -> Prop}
variable {Absorbing : object.Vertex -> object.Vertex -> object.Vertex -> Prop}

noncomputable section

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

noncomputable def grouped :
    DecoratedHandoff.GroupedEnvelopes object LengthOK Uncompressible WindowFree
      HighDegree Absorbing (SelectedComponent ledger components) :=
  groupedOfComponentExitSeven ledger components production avoids windowFree
    uncompressible

example (component : SelectedComponent ledger components) :
    ((grouped ledger components production avoids windowFree uncompressible).envelope
      component).core =
      Connected.vertices object ledger.remainingCore component.1 :=
  Grouped.envelope_core ledger components production avoids windowFree
    uncompressible component

example (centre : object.Vertex) :
    centre ∈
        (grouped ledger components production avoids windowFree uncompressible).centres
      ↔
    ∃ component : SelectedComponent ledger components,
      centre = (production component).separation.separator :=
  Grouped.mem_centres_iff ledger components production avoids windowFree
    uncompressible centre

example {left right : SelectedComponent ledger components}
    (different : left ≠ right) :
    Disjoint
      ((grouped ledger components production avoids windowFree uncompressible).envelope
        left).core
      ((grouped ledger components production avoids windowFree uncompressible).envelope
        right).core := by
  apply (grouped ledger components production avoids windowFree
    uncompressible).pairwiseCoreDisjoint
  · exact Finset.mem_univ left
  · exact Finset.mem_univ right
  · exact different

end

end Hypostructure.Fixtures.TypeBMaximalCompletion
