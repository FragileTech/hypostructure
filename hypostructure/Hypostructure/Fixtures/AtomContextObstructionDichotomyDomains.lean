import Hypostructure.Core.Strategy.Dag
import Hypostructure.Graph.Strategy.AtomContextObstructionDichotomy
import Hypostructure.PDE.Strategy.AtomContextObstructionDichotomy

/-!
# Thin domain-adapter fixture

The fixture checks that Graph and PDE expose their exact decompositions
through the same Core registration without adding an execution layer.
-/

namespace Hypostructure.Fixtures.AtomContextObstructionDichotomyDomains

open Hypostructure
open Hypostructure.Core.Strategy.Dag

universe u v uResidual

namespace Graph

variable
  {Baseline : Hypostructure.Graph.FiniteObject.{u} → Prop}
  {BranchState : Hypostructure.Graph.FiniteObject.{u} → Type v}
  {baselineInvariant :
    Hypostructure.Graph.FiniteObject.IsomorphismInvariant Baseline}
  {Residual : Type uResidual}
  (registration :
    Hypostructure.Graph.Strategy.BoundaryContextObstructionDichotomy.Registration
      Baseline BranchState baselineInvariant Residual)

theorem atom_is_boundary_piece (residual : Residual) :
    (registration.toCore.presentation residual).assembly.atom
        (registration.object residual) (registration.site residual) =
      (registration.site residual).piece :=
  rfl

theorem context_is_outside_context (residual : Residual) :
    (registration.toCore.presentation residual).assembly.context
        (registration.object residual) (registration.site residual) =
      (registration.site residual).outside :=
  rfl

theorem represented_atom_is_boundary_piece (residual : Residual) :
    (registration.toCore.presentation residual).atomRepresented =
      (registration.toCore.presentation residual).assembly.atom
        (registration.object residual) (registration.site residual) :=
  rfl

theorem represented_context_is_outside_context (residual : Residual) :
    (registration.toCore.presentation residual).contextRepresented =
      (registration.toCore.presentation residual).assembly.context
        (registration.object residual) (registration.site residual) :=
  rfl

end Graph

/-! ## Sealed Graph consumer

One sealed Graph consumer that exercises the atom/context split through the
sealed `reduceDag%` frontend using the same Core key
(`Blueprint.atomContextObstructionDichotomy`).  The consumer supplies
mathematics only: a finite graph, an exact boundary decomposition, and a
trivial obstruction law.  No route, ledger entry, query, capability, or
computed execution result is introduced.
-/

namespace Graph

private def trivialBoundary : Hypostructure.Graph.Boundary where
  Vertex := PUnit
  vertices := inferInstance

private def trivialPiece :
    Hypostructure.Graph.BoundaryPiece trivialBoundary where
  Internal := PUnit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := inferInstance

private def trivialOutside :
    Hypostructure.Graph.OutsideContext trivialBoundary where
  Internal := PUnit
  internalVertices := inferInstance
  graph := ⊥
  decideAdj := inferInstance

private noncomputable def trivialGraph : Hypostructure.Graph.FiniteObject :=
  Hypostructure.Graph.glue trivialPiece trivialOutside

private noncomputable def trivialDecomposition :
    Hypostructure.Graph.OwnedDecomposition trivialGraph where
  interface := trivialBoundary
  piece := trivialPiece
  outside := trivialOutside
  vertexEquiv := Equiv.refl _
  ownsAdjacency := by
    intro left right
    change
      (Hypostructure.Graph.glueGraph trivialPiece trivialOutside).Adj
          left right ↔
        Hypostructure.Graph.OwnedAdjacency
          trivialPiece trivialOutside left right
    exact
      Hypostructure.Graph.glueGraph_adj_iff
        trivialPiece trivialOutside left right

private def trivialBaselineInvariant :
    Hypostructure.Graph.FiniteObject.IsomorphismInvariant (fun _ => True) where
  iff_of_iso := by simp

private def graphResidual :
    Core.Strategy.ProblemInput (Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit))
    where
  object := trivialGraph
  baseline := trivial
  branchState := ()

private def graphRegistration :
    Hypostructure.Graph.Strategy.BoundaryContextObstructionDichotomy.Registration
      (fun _ => True) (fun _ => Unit) trivialBaselineInvariant
      (Core.Strategy.ProblemInput (Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit))) where
  object := fun _ => trivialGraph
  site := fun _ => trivialDecomposition
  PieceObstruction := fun _ _ => True
  OutsideObstruction := fun _ _ => False
  pieceDecidable := fun _ => .isTrue trivial
  outsideOfPieceFailure := fun _ absent => absent trivial

private def graphTarget :
    Core.Target (Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit)) where
  Predicate := fun _ => False
  Statement := ∀ _, False
  statement_to_target := by
    intro statement object _
    exact statement object
  target_to_statement := by
    intro closure object
    exact closure object trivial

private def graphDefinition : Core.ProblemDefinition where
  problem := Hypostructure.Graph.problem (fun _ => True) (fun _ => Unit)
  target := graphTarget
  initialState := fun _ => ()
  data := {
    targetDecidable := fun _ => .isFalse id
    atomContextObstructionDichotomies := [
      graphRegistration.toStrategyData
        (metadata := { name := "graph atom--context dichotomy" })
        (pieceMetadata := { name := "graph atom obstruction" })
        (outsideMetadata := { name := "graph context obstruction" })]
  }

instance :
    NeZero graphDefinition.data.atomContextObstructionDichotomies.length :=
  ⟨by simp [graphDefinition]⟩

noncomputable def graphProgram : Program graphDefinition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint graphDefinition.data .authoring)
      |>.atomContextObstructionDichotomy)

noncomputable def graphReduction : ReductionDeclaration :=
  reduceDag% graphDefinition graphProgram

example : graphReduction.report.path =
    [.atomContextObstructionDichotomy 0] :=
  rfl

example : graphReduction.report.statement =
    (∀ (object : Hypostructure.Graph.FiniteObject), False) :=
  rfl

example : graphReduction.report.checksBound = 1 :=
  rfl

example : graphReduction.report.workBound = 1 :=
  rfl

end Graph

namespace PDE

variable
  {P : Core.Problem.{u, u}}
  {semantics : Hypostructure.PDE.RepresentationSemantics P}
  {assembly :
    Hypostructure.PDE.ComponentLocalTailAssembly.{u, u} P semantics}
  {Residual : Type u}
  (registration :
    Hypostructure.PDE.Strategy.LocalTailObstructionDichotomy.Registration
      P semantics assembly Residual)

theorem atom_is_local_term (residual : Residual) :
    (registration.toCore.presentation residual).assembly.atom
        (registration.object residual) (registration.site residual) =
      let source :=
        assembly.interface
          (registration.object residual) (registration.site residual)
      letI := assembly.add source
      (assembly.split
        (registration.object residual) (registration.site residual)).localPart :=
  rfl

theorem context_is_tail (residual : Residual) :
    (registration.toCore.presentation residual).assembly.context
        (registration.object residual) (registration.site residual) =
      let source :=
        assembly.interface
          (registration.object residual) (registration.site residual)
      letI := assembly.add source
      (assembly.split
        (registration.object residual) (registration.site residual)).tailPart :=
  rfl

theorem represented_atom_is_local_term (residual : Residual) :
    (registration.toCore.presentation residual).atomRepresented =
      (registration.toCore.presentation residual).assembly.atom
        (registration.object residual) (registration.site residual) :=
  rfl

theorem represented_context_is_tail (residual : Residual) :
    (registration.toCore.presentation residual).contextRepresented =
      (registration.toCore.presentation residual).assembly.context
        (registration.object residual) (registration.site residual) :=
  rfl

end PDE

/-! ## Sealed PDE consumer

One sealed PDE consumer that exercises the atom/context split through the
sealed `reduceDag%` frontend using the same Core key
(`Blueprint.atomContextObstructionDichotomy`).  The consumer supplies
mathematics only: a represented PDE problem, a component local-tail assembly,
and a trivial obstruction law.  No route, ledger entry, query, capability, or
computed execution result is introduced.
-/

namespace PDE

private abbrev PdeField := Int

private def pdeProblem : Core.Problem where
  Ambient := PdeField
  Baseline := fun _ => True
  BranchState := fun _ => Unit

private def pdeSemantics :
    Hypostructure.PDE.RepresentationSemantics pdeProblem :=
  Hypostructure.PDE.RepresentationSemantics.equality pdeProblem

private def pdeAssembly :
    Hypostructure.PDE.ComponentLocalTailAssembly pdeProblem pdeSemantics where
  Interface := PdeField
  Site := fun _ => Unit
  interface := fun object _ => object
  Carrier := fun _ => PdeField
  add := fun _ => inferInstance
  SameOn := fun _ => (· = ·)
  whole := id
  split := fun object _ =>
    { localPart := object
      tailPart := 0
      exact_reconstruction := by simp }
  rebuild := id
  rebuild_equivalent := by
    intro object _ component agrees
    exact agrees

private def pdeResidual :
    Core.Strategy.ProblemInput pdeProblem where
  object := 0
  baseline := trivial
  branchState := ()

private def pdeRegistration :
    Hypostructure.PDE.Strategy.LocalTailObstructionDichotomy.Registration
      pdeProblem pdeSemantics pdeAssembly
      (Core.Strategy.ProblemInput pdeProblem) where
  presentation := fun residual =>
    { object := residual.object
      site := ()
      LocalObstruction := fun _ => True
      TailObstruction := fun _ => False
      localDecidable := .isTrue trivial
      tailOfLocalFailure := fun absent => absent trivial }

private def pdeTarget : Core.Target pdeProblem where
  Predicate := fun _ => False
  Statement := ∀ _, False
  statement_to_target := by
    intro statement object _
    exact statement object
  target_to_statement := by
    intro closure object
    exact closure object trivial

private def pdeDefinition : Core.ProblemDefinition where
  problem := pdeProblem
  target := pdeTarget
  initialState := fun _ => ()
  data := {
    targetDecidable := fun _ => .isFalse id
    atomContextObstructionDichotomies := [
      pdeRegistration.toStrategyData
        (metadata := { name := "pde atom--context dichotomy" })
        (localMetadata := { name := "pde atom obstruction" })
        (tailMetadata := { name := "pde context obstruction" })]
  }

instance :
    NeZero pdeDefinition.data.atomContextObstructionDichotomies.length :=
  ⟨by simp [pdeDefinition]⟩

noncomputable def pdeProgram : Program pdeDefinition.data :=
  Program.ofBlueprint (
    (Blueprint.root : Blueprint pdeDefinition.data .authoring)
      |>.atomContextObstructionDichotomy)

noncomputable def pdeReduction : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% pdeDefinition pdeProgram

example : pdeReduction.report.path =
    [.atomContextObstructionDichotomy 0] :=
  rfl

example : pdeReduction.report.statement =
    (∀ (field : PdeField), False) :=
  rfl

example : pdeReduction.report.checksBound = 1 :=
  rfl

example : pdeReduction.report.workBound = 1 :=
  rfl

end PDE

#print axioms Graph.atom_is_boundary_piece
#print axioms Graph.context_is_outside_context
#print axioms Graph.represented_atom_is_boundary_piece
#print axioms Graph.represented_context_is_outside_context
#print axioms PDE.atom_is_local_term
#print axioms PDE.context_is_tail
#print axioms PDE.represented_atom_is_local_term
#print axioms PDE.represented_context_is_tail

end Hypostructure.Fixtures.AtomContextObstructionDichotomyDomains
