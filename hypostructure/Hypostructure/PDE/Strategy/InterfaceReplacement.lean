import Hypostructure.Core.Strategy.InterfaceReplacement
import Hypostructure.PDE.Boundary

/-!
# PDE specialization of Core interface replacement

Represented PDE models supply only decomposition, trace/flux signatures, and
semantic transport.  The executable Strategy family remains in Core and uses
the same public names as Graph.
-/

namespace Hypostructure.PDE.Strategy.InterfaceReplacement

open Hypostructure

universe u uInterface uPiece uOutside uSignature

variable {P : Core.Problem.{u, u}} {T : Core.Target P}

noncomputable def assembly
    (semantics : Core.SemanticEquivalence P)
    (decomposition :
      PDE.Boundary.Decomposition.{u, uInterface, uPiece, uOutside} P)
    (decomposable : ∀ object,
      decomposition.compatible object (decomposition.decompose object).1) :
    Core.AtomContextAssembly P semantics where
  Interface := decomposition.interface.Label
  Site := fun _object => PUnit
  interface := fun object _ => (decomposition.decompose object).1
  Atom := decomposition.Piece
  Context := decomposition.Outside
  compatible := fun _piece _outside => True
  atom := fun object _ => (decomposition.decompose object).2.1
  context := fun object _ => (decomposition.decompose object).2.2
  assemble := fun {interface} piece outside =>
    decomposition.assemble interface piece outside
  extractedCompatible := fun _object _site => trivial
  reconstruct := by
    intro object _site
    have reconstructed := decomposition.reconstruct object (decomposable object)
    rw [reconstructed]

/-- Build the PDE semantic adapter.  `signature` is represented trace, flux,
gauge, or matching data; it is never a DAG argument. -/
noncomputable def profile
    {uMeasure : Level}
    (progress : Core.Progress.{u, u, uMeasure} P)
    (semantics : Core.SemanticEquivalence P)
    (targetInvariant : Core.TargetInvariant semantics T.Predicate)
    (decomposition :
      PDE.Boundary.Decomposition.{u, uInterface, uPiece, uOutside} P)
    (decomposable : ∀ object,
      decomposition.compatible object (decomposition.decompose object).1)
    (Signature : decomposition.interface.Label → Type uSignature)
    (signature : {label : decomposition.interface.Label} →
      decomposition.Piece label → Signature label) :
    Core.Strategy.InterfaceReplacement.Profile
      (P := P) (T := T) progress where
  semantics := semantics
  targetInvariant := targetInvariant
  assembly := assembly semantics decomposition decomposable
  Signature := fun label => Signature label
  signature := fun piece => signature piece

end Hypostructure.PDE.Strategy.InterfaceReplacement
