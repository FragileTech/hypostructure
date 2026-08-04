import Hypostructure.Core.Strategy.Dag

/-!
# Strategy DAG opacity

These elaboration checks pin the application boundary.  The private
compiler (recipes, key resolution, fragments, compiled programs, traces),
the sealed declaration/report internals, and every removed residual-outcome
name are not available to an importing module.  In particular, an author may
place a targetless `autoroute` marker but cannot construct Core's resolved
route record.  The sealed `ofDag%` frontend is the only route resolver and
compiler.
-/

namespace Hypostructure.Fixtures.StrategyDagOpacity

open Hypostructure

/-- error: Unknown identifier `Core.Strategy.Dag.Recipe` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.Recipe

/-- error: Unknown identifier `Core.Strategy.Dag.resolveKey` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.resolveKey

/-- error: Unknown identifier `Core.Strategy.Dag.fragment` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.fragment

/-- error: Unknown identifier `Core.Strategy.Dag.compileFrom` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.compileFrom

/-- error: Unknown identifier `Core.Strategy.Dag.CompileTrace` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.CompileTrace

/-- error: Unknown identifier `Core.Strategy.Dag.refusalRecipe` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.refusalRecipe

/-- error: Unknown identifier `Core.Strategy.Dag.routedRecipe` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.routedRecipe

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ResolvedRoute.mk` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ResolvedRoute.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Program.mk` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.Program.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Program.entry` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.Program.entry

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Program.expand` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.Program.expand

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDescriptor.mk` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDescriptor.mk

/-- error: Unknown identifier `Core.Strategy.Validate.computeRunSummaryData` -/
#guard_msgs (error) in
#check Core.Strategy.Validate.computeRunSummaryData

/-- error: Unknown identifier `Core.Strategy.Validate.emitRunSummary` -/
#guard_msgs (error) in
#check Core.Strategy.Validate.emitRunSummary

/-- error: Unknown identifier `Core.Strategy.Validate.buildRunSummaryJson` -/
#guard_msgs (error) in
#check Core.Strategy.Validate.buildRunSummaryJson

/-- error: Unknown identifier `Core.Strategy.Validate.runSummaryLatexDocument` -/
#guard_msgs (error) in
#check Core.Strategy.Validate.runSummaryLatexDocument

/-- error: Unknown identifier `Core.Strategy.Validate.executiveSummary` -/
#guard_msgs (error) in
#check Core.Strategy.Validate.executiveSummary

/-- error: Unknown constant `Hypostructure.Core.Strategy.HaltingProgram.mk` -/
#guard_msgs (error) in
#check Core.Strategy.HaltingProgram.mk

/-- error: Unknown identifier `Core.Strategy.Dag.UnresolvedKey` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.UnresolvedKey

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.Blueprint.unresolvedIn` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.Blueprint.unresolvedIn

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.ofDag` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.ofDag

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.ofValidated` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.ofValidated

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.statement?` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.statement?

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.closedUnconditionally` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.closedUnconditionally

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.unresolvedKeys` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.unresolvedKeys

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.certified` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.certified

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.mk` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.chain` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.chain

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.compiled` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.compiled

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.run` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.run

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.diagnose` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.diagnose

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.result` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.result

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.TotalResidual` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.TotalResidual

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.CertifiedOutcome` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.CertifiedOutcome

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.unconditional` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.unconditional

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.unconditional_of_isEmpty` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.unconditional_of_isEmpty

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.mk` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.mk

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.proof` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.proof

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.outcome` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.outcome

/-- error: Unknown constant `Hypostructure.Core.Strategy.Dag.ProblemDeclaration.Report.trace` -/
#guard_msgs (error) in
#check Core.Strategy.Dag.ProblemDeclaration.Report.trace

end Hypostructure.Fixtures.StrategyDagOpacity
