import Hypostructure.Core.Response.FiniteTable
import Hypostructure.Core.Residual.Decision

/-!
# Finite response tables: the legacy ledger execution

**Legacy.**  `Core/Response/FiniteTable.lean` holds the finite response-table
mathematics.  This file holds the `Residual.Decision` node that used to execute
it, which reaches the legacy `Core.Residual.Ledger`.

Separated so that the graph response layer -- and through it the spine's row
`[11]`--`[14]` -- can use response tables without importing the legacy stage
stack.  With this split the entry spine's import closure contains no part of
the legacy residual stack at all.
-/

namespace Hypostructure.Core.Response.FiniteTable


section LedgerExecution

variable (system)
  (representatives : Response.Representatives Representative)

/-- Framework-owned finite classification over a schedule queried from the
literal predecessor ledger.  Applications supply the query and response laws;
Core constructs the table and selects the decision constructor. -/
def classificationNode [DecidableEq system.Value]
    {Previous : Sort uPrevious}
    (scheduleQuery : Residual.Query Previous
      (fun _previous => ExactSchedule system.Coordinate)) :
    Residual.Decision.Node Previous
      (fun previous => Distinguishes
        (Table.build system representatives (scheduleQuery previous)))
      (fun previous => Neutrality
        (Table.build system representatives (scheduleQuery previous))) :=
  Residual.Decision.Node.create
    (fun _previous => inferInstance)
    (fun previous absent =>
      (Table.build system representatives
        (scheduleQuery previous)).neutralityOfNotDistinguishes absent)

/-- Execute exact finite response classification while retaining the complete
incoming ledger as the decision stage's literal predecessor. -/
def run [DecidableEq system.Value]
    {Previous : Sort uPrevious}
    (scheduleQuery : Residual.Query Previous
      (fun _previous => ExactSchedule system.Coordinate))
    (previous : Previous) :
    Residual.Decision.Stage
      (fun current => Distinguishes
        (Table.build system representatives (scheduleQuery current)))
      (fun current => Neutrality
        (Table.build system representatives (scheduleQuery current))) :=
  (classificationNode system representatives scheduleQuery).run previous

end LedgerExecution

end Hypostructure.Core.Response.FiniteTable
