# Phase 5 significance check: terminal count on [144a]

**Before.** The exact [144a] window-arm ledger has a large same-token,
same-role matching or star of original blocked pairs, one decorated Type B
handoff envelope, strict surplus, and all earlier graph restrictions. The
unpaid quantity is the excess number of original blocked pairs relative to
fixed homogeneous token caps. The earlier event account keeps those pair
indices but has no bounded assignment to physical envelope centres or arms.

**After the candidate local count.** On one source pattern `P`, each terminal
receives at most three distinct selected port demands; hence that pattern
has at least `ceil((Q_geom+2)/3)` distinct terminals, including one away
from its root. This is a valid new consequence on the same selected graph.
It does not change the set of original blocked pairs, the token load, or the
capacity of the produced envelope.

**Consumer test.** The terminal bound controls `P → T`. The needed charge
controls original blocked pairs or source events `→` actual centres/arms of
their handoff envelopes. No map or inequality from `T` to such centres/arms
has been proved. Distinct terminals may have routes with the same initial
edge or high first separator; the terminal count alone bounds neither
route-edge use nor envelope multiplicity. Also, the handoff publishes one
envelope for a selected pair of source edges, without assigning the entire
pattern to it. Consequently `3|T|≥Q_geom+2` has no derived comparison with
the strict surplus or the excess token load that would force a cap.

The count eliminates the all-root exception of the *auxiliary* route-union
Menger split. The remaining linkage and `H`-cut outcomes still lack a
branch-conditioned payoff: linkage paths need not index distinct original
pairs, and an `H`-cut is not a `G`-cut. Eliminating an auxiliary exception
without consuming either remaining outcome does not reduce [144a].

**Decision.** Keep the correct terminal-count inference as intermediate
evidence, but **reject this candidate as a productive structural move**.
The first missing inference is a consumer converting its distinct terminals
into a bounded charge on the actual original-pair/envelope account or an
excluded graph configuration. This is a missing proof, not a theorem that no
such consumer exists. The complete [144a] residual remains open, with no
homogeneous cap, near-cubic estimate, or closure added. Return to selecting
an interaction that controls repeated physical route or envelope incidence.
