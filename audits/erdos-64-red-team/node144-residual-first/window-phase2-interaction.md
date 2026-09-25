# [144] window arm: unresolved pair-to-envelope interaction (Phase 2)

The object is the selected graph `G = selected.object` on the tagged window-incidence
class-overload history. The source is the literal post-[144] ExactLedger; its
`typeBHandoff` key carries one existential tuple `(active_h, capacity_h,
certified_h, token_h, role_h, pattern_h, packing_h, core_h, envelope_h)` on `G`.
The `homogeneousBottleneckPattern` key was already used by the routing row;
we make no equality claim between its existential witnesses and those of
other returned keys.

## Actual observables on that one handoff witness

1. `pattern_h` is a selected matching or star inside
   `certified_h.ledger.presented.roleFibre token_h role_h`, with at least the
   geometric label bound and same-root routing configurations for both
   demands of every selected pair. Its existence directly contradicts fixed
   homogeneous caps if those caps could be independently proved for `G`.
2. The same certified ledger has the exact blocked/free pair split and the
   token/role partition recorded in `window-phase1-pair-account.md`. These
   account for original unordered demand pairs, not decorated centres or arms.
3. `envelope_h` has a maximal window packing, a core, nonempty decorated
   high-degree centres, a nonempty assigned first-neighbour set at each
   centre, simple arms to the core, and `fanSafe` between distinct assigned
   neighbours at one centre. These are actual graph incidences.

## Unresolved interaction

The pair configurations and envelope arms live on the same graph in one
`typeBHandoff` proposition, but the proposition exposes no function sending
every original pair in `pattern_h` (or every blocked pair in the selected role
fibre) to an assigned centre/first-neighbour/arm of `envelope_h`. It supplies
no injectivity, disjointness, or upper bound on the number of original pairs
that may share one such incidence. The routing proof constructs one envelope
from separated configurations; its published output forgets any indexing by
all selected pairs. The exact question is whether the retained source
configurations and the decorated arms force a bounded multiplicity or an
other graph restriction strong enough to eliminate the positive pattern on
this full window residual. That relation is **not yet proved**. No pair credit
is assigned to the envelope in the existing account.

This is an inventory of an actual higher-order conjunction, not a selected
technique or a cap proof. The positive pattern, not the mere handoff, is what
would contradict a cap established on the full branch.

Sources: `ObjectCapacityLedger.lean:601–682`;
`SpineVocabulary.lean:3944–3995`;
`DecoratedHandoffEnvelope.lean:902–960`;
`HomogeneousBottleneckRows.lean:593–665,808–842,3060–3112`.
