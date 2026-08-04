import HypostructureErdos64EG.AB.StrategyDag

/-!
# Framework-native Type-A/Type-B frontier reduction

The sealed reduction frontend compiles the registered A/B problem and routing
program while retaining every unclosed residual.

`data.targetDecidable` is classical, so no terminal here can be closed by a
target oracle.  Every closed terminal is closed by the registered dichotomy.
-/

namespace HypostructureErdos64EG.AB

open Hypostructure
open Hypostructure.Core.Strategy.Dag

/-! ## The closure test

`ofDag%` carries `program.Closes`: it accepts the declaration only when the
sealed compiler derives **total** execution closure, with no residual
surviving.  It cannot succeed by widening its own statement.  While any
terminal is open this fails, and the failure — with the summary the frontend
emits — is the closure report.  This is the line to watch. -/
noncomputable def abClosure : ProblemDeclaration.{1, 0, 0} :=
  ofDag% definition strategyDag

/-! ## Proof progress

`reduceDag%` retains every surviving residual, so it elaborates whatever
remains open.  It proves nothing about closure — its whole job is to keep the
run exportable while `abClosure` is still failing, so the terminal table below
shows exactly which branches are closed and which residuals survive.

Nothing here depends on `abClosure`.  That separation is deliberate: a
rejected `ofDag%` leaves its declaration as `sorry`, and anything derived from
it would inherit `sorryAx`. -/
noncomputable def abDeclaration : ReductionDeclaration.{1, 0, 0} :=
  reduceDag% definition strategyDag

/-- The current target-or-residual statement.  Not the closure test; see
`abClosure` above. -/
noncomputable def only_type_A_or_B_framework : abDeclaration.Statement :=
  abDeclaration.report.statement

#print axioms only_type_A_or_B_framework

#hypostructure_json "../../build/hypostructure/eg-ab-run.json"
  (reduceDag% definition strategyDag)

end HypostructureErdos64EG.AB
