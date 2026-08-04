import HypostructureErdos64EG.StrategyDag
import HypostructureErdos64EG.AB.Execution

/-!
# Official Erdős--Gyárfás sealed proof

This module executes the exact DAG assembled from framework Strategies against
the official EG64 problem and target.
-/

namespace HypostructureErdos64EG.Official

open Hypostructure
open Hypostructure.Core.Strategy.Dag

/-- The paper-ordered DAG expressed only in Core's executable Strategy API. -/
noncomputable abbrev structuralProgram : Program definition.data :=
  HypostructureErdos64EG.strategyDag

/-- The registered target is definitionally the official EG64 statement,
not a surrogate proposition. -/
example :
    definition.target.Statement =
      HypostructureErdos64EG.officialStatement.{0} :=
  rfl

/-- The sealed unconditional reduction.  Core executes `structuralProgram`
and returns either the official target or its exact accumulated terminal
residual; the application supplies neither outcome nor certification. -/
noncomputable def proofReduction : ReductionDeclaration.{1, 0, 0} :=
  reduceDag% definition structuralProgram

/-- The sealed framework declaration at the current Type-A / Type-B
frontier.  Keeping this alias in the official proof module makes the main EG
build certify the branch endpoint instead of leaving it behind a separate
application entrypoint. -/
noncomputable abbrev abFrontierDeclaration :
    Core.Strategy.Dag.ReductionDeclaration.{1, 0, 0} :=
  HypostructureErdos64EG.AB.abDeclaration

/-- The current official frontier closes exactly through the registered A/B
dichotomy.  Its two terminals are discharged by `closeLeft` and `closeRight`;
the classical target decider supplies no terminal closure. -/
noncomputable def only_type_A_or_B_at_official_frontier :
    abFrontierDeclaration.Statement :=
  abFrontierDeclaration.report.statement

#hypostructure_json "../../build/hypostructure/eg-official-run.json"
  (reduceDag% definition structuralProgram)

end HypostructureErdos64EG.Official
