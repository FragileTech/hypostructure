import Hypostructure.Graph.Strategy.ColdCorridorRows

/-!
# The cold return corridor has no composite runner

The cold branch is assembled at the proof-specific call site from the literal
incoming `ExactLedger`.  Each paper node is one `Decision.run` or one
`AtomicCT.run`; the framework retains the complete ancestry after every append.

This module deliberately exports no `coldKeys`, `coldBranchClosedKeys`,
`runColdBranchClosed`, or `runCold` wrapper.  The former composite runner
executed mutually exclusive F/G arms sequentially and required a fabricated
`coldTerminalResidual` on entry in order to manufacture a final contradiction.
That is not the branch structure of Figure XI.
-/
