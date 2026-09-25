# [144] window arm: same-root prerequisite (Phase 4.2)

The selected handoff witness contains the certified capacity ledger, one
`token`, one `role`, one `sourceClass`, and a `root` equal to
`CapacityPresentation.tokenRoot token`. In the detailed matching or star
branch of its `HomogeneousBottleneckPatternStatement`, every selected pattern
edge has response support and a `RoutingConfiguration` for each demand in
that edge, with `configuration.path.head? = some root`.

The owner chooses two edges with equal routing labels. Its chosen demand
from each is a member of the corresponding selected edge, so it reads two
configurations from this **same handoff pattern witness**. The matching case
proves `firstConfigurationCanonicalRoot` and
`secondConfigurationCanonicalRoot` before applying the same-root dichotomy;
the star case repeats the corresponding argument. Thus the two path heads
agree at the canonical root of the selected token on `G = selected.object`.

This checks only the same-root prerequisite. The common selected support and
landing premises, parallel-exit elimination, high degree, and source-indexed
publication remain separate. No equality with capacity presentations in
other `Holds` keys is used.

Sources: `ObjectCapacityLedger.lean:623–682`;
`HomogeneousBottleneckRows.lean:1521–1569,2391–2439`;
`SameTokenRoutingGerms.lean:496–540`.
