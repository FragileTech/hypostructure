import Hypostructure.PDE.Coordinate
import Hypostructure.Core.Strategy.Dag

namespace HypostructurePDEQuickstart

open Hypostructure
open Hypostructure.PDE

abbrev Index := Fin 5
abbrev Field := Index -> Int

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _field => True
  BranchState := fun _field => Unit

def atlas : LocalAtlas problem where
  Point := Index
  Window := Unit
  contains := fun _point _window => True
  nested := fun _small _large => True
  nested_refl := fun _window => trivial
  nested_trans := fun _first _second => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Field
  restrict := fun field _window => field
  restrictLocal := fun _nested field => field
  restrict_refl := fun _window _field => rfl
  restrict_trans := fun _small _middle _large => rfl
  restrict_global := by
    intro field small large nested
    rfl

def equation : RepresentedEquation problem atlas where
  EquationData := fun _window _field => Unit
  satisfies := fun _data => True
  restrictEquation := fun _nested _field data => data
  restrict_satisfies := fun _nested _field _data valid => valid

def model : LocalModel where
  problem := problem
  atlas := atlas
  equation := equation

def equalitySemantics : RepresentationSemantics problem :=
  RepresentationSemantics.equality problem

def recenter (shift : Index) (field : Field) : Field :=
  fun index => field (index + shift)

def recentering : RecenteringInterface model where
  Shift := Index
  targetWindow := fun _shift window => window
  coordinate := fun shift _window => {
    transform := recenter shift
    transformEquation := fun _data => ()
    preservesEquation := fun _field _valid => trivial
    realize := recenter shift
    realizes := fun _field => rfl
    preservesBaseline := fun _valid => trivial
  }

def path (shift : Index) :
    Core.CoordinatePath (coordinateSystem model) () () :=
  .cons (recentering.coordinate shift ()) .nil

theorem path_formula (shift : Index) (field : Field) (index : Index) :
    (path shift).run field index = field (index + shift) :=
  rfl

def target : Core.Target problem where
  Predicate := fun field : Field => field 0 + 0 = field 0
  Statement := ∀ field : Field, field 0 + 0 = field 0
  statement_to_target := fun statement field _ => statement field
  target_to_statement := fun closure field => closure field trivial

def definition : Core.ProblemDefinition.{0, 0, 0} where
  problem := problem
  target := target
  initialState := fun _ => ()
  data := {
    targetDecidable := fun input => .isTrue (Int.add_zero (input.object 0))
  }

open Core.Strategy.Dag

noncomputable def strategyDag : Program definition.data :=
  Program.ofBlueprint (Blueprint.root.targetOrAvoid)

noncomputable def proofReduction : ReductionDeclaration.{0, 0, 0} :=
  reduceDag% definition strategyDag

noncomputable def certifiedReduction :=
  proofReduction.report.statement

#print axioms path_formula
#check certifiedReduction

end HypostructurePDEQuickstart
