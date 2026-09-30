# Structural accounting addendum: `Route8JointBalanceOutcome` — blob structure (keys 9900–9902)

Scope: this addendum accounts the three blob-structure facts 9900-9902 of the generic
`Route8JointBalanceOutcome` (node `[186]`, 146 facts). The other facts of the residual,
including the dominance-irreducibility keys 9975-9980 and the packing-exchange keys
9800-9807 (packing exchange, landing cap, hub-piece mass, net-cap excess, arm-closure
residual), are not accounted in this directory; there is no full Table 1/Table 2 report of
`[186]`. The same three facts are on `Route8QuotientOutcome` (common prefix).

**Defining failure (rate arm).**  `K .route8Rate`: `13|∂R| + 3·slack < 3|R|` at `P₀`
(`δ = 3`, `s = 4`).  With the joint balance `3|R| ≤ 13|∂R| + 3h + O`, the open demand units
`O` are positive.  The uncontrolled term is `R`; facts 9900-9902 name its canonical pieces `X`,
their exits into windows of `P₀`, and the rate term.

## Table 2 — facts 9900-9902

| Fact | Key | Statement (at G) | Coordinates | Certificate |
|---|---|---|---|---|
| 9900 | `route8PieceWindowAttachment` | piece `X`, window `P ∈ P₀` (placement `p`), exits `p i — a`, `b — p i'`: `∀ ℓ ∈ L_X(a,b), ¬pow2(|i−i'| + ℓ + 2)`; every run `[lo,hi] ⊆ L_X(a,b)`: `hi+d+2 < 4 ∨ hi+d+3 < 2(lo+d+2)` | C01, C03, C04, C10, C12, D01 | exclusion, bound |
| 9901 | `route8PieceChainCycle` | `k` distinct pieces, `k` distinct windows joined cyclically by exits: `¬pow2(Σ(ℓᵢ + |jᵢ−j'ᵢ|) + 2k)` for all `ℓᵢ ∈ L_{Xᵢ}(aᵢ,bᵢ)` | C01, C03, C10, C12, C13, D01 | exclusion |
| 9902 | `route8PiecewiseRate` | `|R| = Σ_X|X|`, `|∂R| = Σ_X E(X)`, `3·slack < Σ_X (3|X| − 13E(X))` (general `δ, s`), heavy pieces `13E(X) < 3|X|` nonempty | A10, B01, C10, H02, H03, H08 | identity, bound, witness (a heavy piece of G) |

## Table 1 — coordinates touched

| Code | Property | Contribution |
|---|---|---|
| A10 | Incidence between two regions | `|∂R|` split exactly over the pieces (9902). |
| B01 | Connected-component structure | the canonical pieces carry the rate (9902). |
| C01 | Simple paths and attainable lengths | internal length sets `L_X(a,b)` between exits enter the exclusions and the run bound (9900, 9901). |
| C03 | Cycle-length spectrum | cycles through a piece and one window (9900) or a chain of pieces and windows (9901). |
| C04 | Arithmetic class of lengths | dyadic run bound on shifted runs (9900, `BlobCycles.interval_bound_of_no_pow_two`). |
| C10 | Structure of a packing remainder | pieces of `R` against `P₀` (all three). |
| C12 | Endpoint and attachment constraints | where two exits of one piece may land on one window (9900). |
| C13 | Simultaneous path realizability | disjoint internal paths and window segments close one chain cycle (9901). |
| D01 | Attachment pattern to a fixed motif | exit positions on the placed window (9900, 9901). |
| H02 | Additive or superadditive charge | `3|X| − 13E(X)` is additive over the pieces and sums to the rate excess (9902). |
| H03 | Connected negative support | the heavy pieces (connected, positive rate excess) are nonempty (9902). |
| H08 | Total exceptional mass | `Σ_X (3|X| − 13E(X)) > 3·slack` (9902); with the joint balance `≤ 3h + O`. |

Not used: A07 (2-degeneracy of a piece is automatic for a connected piece with an exit and
all vertices cubic — fact 80 adds nothing), the triangle and toggle lemmas
`BlobCycles.triangles_disjoint`, `toggle_interval` (their bounds are implied by edge counts;
not instantiated at G).

## Remaining gap relevant to the defining failure

C01/B04 at the heavy pieces: the outside routes in `G − X` between the exits of a heavy piece
(`ρ(X) = |X|/E(X) > 13/3`).  9900/9901 use only window segments and chains; a per-piece
bound needs every `a'`–`b'` route length `m` of `G − X` with the sumset `L_X(a,b) + m + 2`.
Joint test with 9900–9902: no contradiction derived; exact remaining proposition in the
register section "Blob structure (route 8)".
