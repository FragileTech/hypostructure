import HypostructureErdos64EG.Official.StructuralProgram

/-!
This module is compiled directly by `make erdos`.  It asks the strict sealed
frontend whether the exact official problem and exact official DAG now close
the target with no surviving residual.  No alternative problem, DAG, closure
witness, or execution callback is accepted here.
-/

namespace HypostructureErdos64EG.Official

open Hypostructure.Core.Strategy.Dag

noncomputable def proofDeclaration : ProblemDeclaration.{1, 0, 0} :=
  ofDag% definition structuralProgram

end HypostructureErdos64EG.Official
