# Node [20a]: approaches already tried on this residual (operator-supplied context)

Source: the user's binding instruction for this run (relayed by the operator), with
pointers to the scratch analyses that record each attempt. The scratch files are
filed in the run record under `scratch-proved/` (evidence ids `scratch_*`, each
with its sha256). They are Lean-checked analyses of G. They are **not** ledger
facts. This file contributes no mathematics and no fact about G. It lists the
attempt history that a selected structure or move must not repeat. A move that
relies on one of these approaches needs a new ingredient that addresses exactly
why the approach failed.

| # | Approach | Why it did not close (as recorded) | Scratch record |
|---|---|---|---|
| F1 | Local rigidity: length-3 fans and chains at a vertex, window placements and cross-edge gaps, hub C8 | Local consistency: every local configuration forced so far is realizable, so it gives no contradiction by itself | `hubwin/HubWin/Local.lean`; ledger keys `K .threeRouteFan`, `K .threeRouteChain`, `K .windowPositionStubs`, `K .windowAttachmentGap` |
| F2 | Counting-only bounds: degree, dart and edge counts, windows, packing, remainder slack, hub budgets | All of them tighten the same side. The accumulated counting system has a solution at every scale (`accumulated_escape`: `n = 37C²`, `s = 2C`, `k = h = C`, `ν = 1`). That solution is a diagnostic only; it is not a fact about G | `hubwin/HubWin/Escape.lean`, `hubwin/HubWin/Budget.lean`, `hubwin/HubWin/Slack.lean`, `density/Density.lean`, `joint/Joint.lean` |
| F3 | Long paths / cycles in the remainder `R` (GRS-type bounds) | The bound is too weak. Paths and cycles in `R` have at most `6143C + 6142` vertices, which confines `j ≤ 91` for a forced `2^j − 1` path in `R`. No counting relation involves path lengths, so the counting system is unchanged | `grs/Grs/At20a.lean`, `grs/Grs/Generic.lean`, `grs/Grs/Escape.lean` |
| F4 | Menger on a failed 2-linkage ("every forward route meets every backward route ⇒ a separating vertex") | The inference is invalid for general graphs. A failed 2-linkage is not a failed 2-connection (counterexample on `C₄`) | `armB/ArmB/Linkage.lean`, `armB/ArmB/Generic*.lean`, `armB/ArmB/At20a*.lean` |
| F5 | Pairwise window attachment (cross edges and hub pairs between two windows) | Mostly legal. The gap rule excludes few pairs, and every outside label is legal | `windows/Windows.lean`, `windows/LiveCharge.lean`, `hubwin/HubWin/WindowU.lean`; ledger key `K .windowAttachmentGap` |
| F6 | Capacity per-token caps (`load ≤ M₀` for every token) | Separated chord-only pairs charge the earlier port's token, so loads around `σ` are forced (forward degree of a port) | `account/Account/SeparatedCharge.lean`, `account/Account/Singleton.lean`, `account/Account/Witness.lean`, `account/Account/Joint.lean`, `account/Account/Capped.lean` |

One partial result sits in the same scratch files: `hublink/HubLink/Escape.lean` records
that the slot relation refutes the specific `accumulated_escape` point (`escape_killed`).
That is a diagnostic about one feasible point. It is not a closure of the residual.
