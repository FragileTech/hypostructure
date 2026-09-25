# Phase 4 selection on the [144a] window arm

Select **finite source-terminal congestion counting** for Phase 5 payoff
verification. It acts on the handoff's actual selected surplus-port demands,
not on an arbitrary path system: every demand terminal has degree three and
each such terminal receives at most three distinct demands. The exact output
under review is a bounded source-edge-to-terminal map, the induced distinct
terminal count, and exclusion of the all-root route family.

The weakest source case is a three-edge star. Its four distinct demand
elements cannot all end at the root, since one terminal supports at most
three. Matching has six distinct demands already at three edges. The source
pattern and every original demand remain in the analysis; the matching/star
case is a proof split on the handoff witness, not a replacement for it.

The full-route edge-Menger statement remains a catalogued alternative. Its
route-union linkage does not itself assign paths to distinct source edges,
and its route-union cut is not a cut in `G`. The reviewed terminal count may
later help a linkage analysis, but it does not supply a consumer for either
Menger outcome. The earlier two-edge same-label route already produces an
envelope and cannot be counted as a new move.

Phase 5 must prove the conditional payoff on the **complete** [144a] ledger
and judge whether the terminal bound is an effective structural restriction.
It must not infer bounded centre-arm or envelope multiplicity, homogeneous
caps, a near-cubic estimate, or branch closure. No construction is authorized
by this Phase 4 selection.
