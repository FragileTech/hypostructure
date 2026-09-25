# [144] window arm: select the full route-overlap tension

The live object is the selected graph `G` with the one handoff source tuple
`(capacity_h, certified_h, token_h, role_h, P)` and every declared route
attached to `P`. At every high vertex used by those routes, the retained
normal form restricts adjacent route neighbours; target-return avoidance
also holds on `G`. The current owner uses one same-label pair and returns
one envelope. It does not say how the other routes meet that separator,
other route arms, or each other.

**Selected compatibility question.** Across *all* chosen source routes,
including differently labelled ones, which repeated physical path segments
and high-centre departures can coexist with normal form and return
avoidance? In particular, can a large set of source indices use the same
actual centre/arm incidence without producing a target-relevant return,
or do the retained exclusions force a bound or a located obstruction?
The route paths, their vertex/edge incidences, and the positive source
pattern are tied to one handoff witness on `G`; this question does not
identify the separate window-overload token with `token_h`.

**Prospective effect.** An established bound on the number of original
source pairs per eligible physical incidence, or a located graph
configuration excluded by the retained target facts, would address the
current pair-to-envelope multiplicity gap. This is a prospect only. The
existing normal-form implication on route neighbours does not supply the
bound; it applies conditionally when routes share a high vertex.

**Weakest case.** The source size may be only `Q + 1` for `Q` labels, where
the label count guarantees at least one collision but permits no second
independent collision.
The selected question therefore includes every route with a different
label. Repeating the two-edge pigeonhole step cannot settle it.

**Rival comparison.** Fixing the handoff token's window class would enable
class-specific geometry only after an unproved equality between the
separately quantified source witnesses; it has no present same-witness
payoff. The earlier high-centre fold has an actual smaller graph, but its
target-response transport and original-pair capacity remain unresolved
(`near-cubic-repair/execution.md:300–380`). Full route overlap is the more
direct unresolved relationship with the positive source pattern, because
its observable uses every existing route and the exact original pair
indices. This comparison selects the *structural question*, no method or
construction.

The next stage must catalogue a local mechanism with exact hypotheses and
all outcomes, and reject it if its weakest case merely recreates the
existing two-route envelope or an abstract event count.
