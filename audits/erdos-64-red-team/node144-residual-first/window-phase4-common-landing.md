# [144] window arm: common-landing prerequisite (Phase 4.2)

The two chosen original pattern edges supply distinct demands `left` and
`right` and declared routing configurations within the **same** selected
capacity presentation. `RoutingConfiguration.lands` puts the first
configuration's last vertex in `capacity.activation.localBuffer left` and
the second's last vertex in `capacity.activation.localBuffer right`.

The routing owner defines `commonSelectedSupport` as the union of those two
local buffers (matching case at line 1654, star case at line 2524). Its
`firstLandsCommon` and `secondLandsCommon` proofs insert each terminal into
the corresponding side of this union, before calling
`parallel_or_firstSeparator_of_same_root` (matching 1713–1733; star
2583–2603). Thus both paths satisfy the theorem's landing premise on one
finite support of `G = selected.object`. No fresh support or cross-key
capacity identification is used.

This checks common landing only. It does not choose the parallel or
separator outcome, eliminate an exit, prove high degree, or publish source
indices in the returned handoff.

Sources: `SameTokenRoutingGerms.lean:229–246,496–540`;
`HomogeneousBottleneckRows.lean:1650–1658,1713–1733,2520–2528,2583–2603`.
