# [144] inherited bridgeless readiness

The literal [144] predecessor ledger contains `K .bridgeless` on the selected graph. The revised `sameTokenBottleneckRoutingRow` uses this existing fact to give `HasReturn` for its forced physical non-skeleton edge. The generic `selectedBottleneckDischarge` caller previously declared every other required `FactKeys.Has` instance but omitted this one.

The only change to `selectedBottleneckDischarge` is `[FactKeys.Has (K .bridgeless) known]` on its same `known` ledger. No witness or assumption is synthesized. The full predecessor in `Assembly.Surplus.Strict.Dependent` supplies the key for all three calls.

Kernel checks: `lake build HypostructureErdos64EG.Assembly.Surplus.Local` and `lake build HypostructureErdos64EG.Assembly.Surplus.Strict.Dependent` both completed successfully. The second build checks the immediate strict caller through its three uses of `selectedBottleneckDischarge`.

This is caller readiness only. The return path remains an owner-local fact until a source-bound `typeBHandoff` `Holds` proposition exports the same extremal envelope and same edge. No [144a] closure or quantitative cap follows from this edit.
