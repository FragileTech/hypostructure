# [144] window arm: one prior structural use

**Object.** `G = selected.object` on the literal window-incidence overload
history. Its incoming key index contains `windowClassOverload`,
`windowIncidenceAudit`, and `homogeneousBottleneckPattern`; the other class
keys are absent. The exact index is pinned in `phase0-evidence.md`.

**Aspect previously used.** The selected role fibre has a same-token matching
or star of size at least the geometric pattern bound, with the registered
same-root routing configurations for demands in that selected pattern.
`windowIncidenceAuditRow` publishes this as `homogeneousBottleneckPattern` on
the same selected graph.

**Use and established conclusion.** `sameTokenBottleneckRoutingRow` reads that
key through `FactInputs.get`, along with the literal active-demand,
capacity, selection, and replacement facts. Its first output is
`bottleneckRouting`: on `G`, the pattern routes to a sparse surplus exit or
a decorated Type B handoff envelope. The row then uses the retained
`active.survives` property to eliminate the sparse-exit arm and publishes
`typeBHandoff`. `sameTokenTypeBFanEntryRow` reads this handoff and appends
`typeBFanEntry`. The [144] Assembly call returns exactly
`[typeBFanEntry, bottleneckRouting, typeBHandoff] ++ known`.

**Unexploited aspect.** The produced envelope has a maximal packing, a core,
and nonempty decorations. The returned `Holds` proposition does not assign
every original pair in the overloaded role fibre to an envelope/centre, and
does not bound how many such pairs one envelope or centre receives. It also
does not assert equality between existential capacity witnesses in distinct
ledger keys. No fixed homogeneous cap, near-cubic estimate, or quantitative
pair-payment conclusion is an output of this use.

**Evidence.** `HomogeneousBottleneckRows.lean:156–275` gives the window
producer; `:593–640,3080–3120` gives the routing and entry manifests and
the sparse-exit elimination. `SpineVocabulary.lean:3961–3995,11702–11731`
gives the exact handoff, routing, and fan-entry propositions.
`Assembly/Surplus/Strict/Dependent.lean:268–285` is the window call site,
and `Assembly/Surplus/Local.lean:333–398` gives the returned ledger index.
