import Hypostructure.Graph.Strategy.Official

namespace Hypostructure.Fixtures.OfficialGraphCompiler

open Hypostructure
open Hypostructure.Graph
open Hypostructure.Graph.Strategy.Official
open Hypostructure.Core.Strategy.Official

abbrev object : FiniteObject where
  Vertex := Fin 3
  graph := ⊤
  vertices := inferInstance
  decideAdj := inferInstance

def data : Presentation where
  object := object
  target := {
    CycleLengthOK := fun length => length = 3
    cycleLengthDecidable := fun _ => inferInstance
  }

def linearProgram : Program :=
  .invoke ⟨"rooted return"⟩ ⟨.rootedReturn, 0⟩

def declaration : GraphDeclaration where
  data := data
  program := linearProgram

theorem compliant : declaration.Compliant where
  supported := by
    intro ref member
    have equal : ref = ⟨.rootedReturn, 0⟩ := by
      simpa [declaration, GraphDeclaration.ir, Compiler.IR.references,
        Compiler.compile, linearProgram, Program.references] using member
    subst ref
    exact Or.inr (Or.inr rfl)
  shaped := by
    simp [GraphDeclaration.shaped, declaration, GraphDeclaration.ir,
      Compiler.IR.arities, Compiler.compile, linearProgram, Program.arities]

noncomputable def report : GraphReduction declaration :=
  compileGraph declaration compliant

example (proof : GraphTarget declaration)
    (executed : report = .target proof) :
    GraphTarget declaration :=
  compileGraph_target_sound declaration compliant proof executed

/-- A reusable program containing every composition constructor.  Its branch
has exactly the one residual continuation promised by rooted-return. -/
def fullProgram : Program :=
  .join ⟨"join"⟩
    [
      .chain ⟨"chain"⟩
        (.invoke ⟨"first"⟩ ⟨.rootedReturn, 0⟩)
        (.invoke ⟨"second"⟩ ⟨.rootedReturn, 0⟩),
      .branch ⟨"branch"⟩ ⟨.rootedReturn, 0⟩
        [.invoke ⟨"avoidance continuation"⟩ ⟨.rootedReturn, 0⟩]
    ]
    (.invoke ⟨"shared continuation"⟩ ⟨.rootedReturn, 0⟩)

def fullDeclaration : GraphDeclaration where
  data := data
  program := fullProgram

theorem fullCompliant : fullDeclaration.Compliant where
  supported := by
    intro ref member
    simp [fullDeclaration, GraphDeclaration.ir, Compiler.IR.references,
      Compiler.compile, fullProgram, Program.references] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      exact Or.inr (Or.inr rfl)
  shaped := by
    simp [GraphDeclaration.shaped, fullDeclaration, GraphDeclaration.ir,
      Compiler.IR.arities, Compiler.compile, fullProgram, Program.arities]

noncomputable def fullReport : GraphReduction fullDeclaration :=
  compileGraph fullDeclaration fullCompliant

/-- Invalid multi-continuation routing is rejected before execution. -/
def invalidBranchProgram : Program :=
  .branch ⟨"invalid"⟩ ⟨.rootedReturn, 0⟩ [.done, .done]

example :
    (Compiler.compile invalidBranchProgram).arities.all
      (fun entry => entry.2 == 1) = false := by native_decide

#print axioms compileGraph_target_sound

end Hypostructure.Fixtures.OfficialGraphCompiler
