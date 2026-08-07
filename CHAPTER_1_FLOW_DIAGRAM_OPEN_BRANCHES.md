# Chapter 1 flow-diagram branch status

This table compares the eleven proof-dependency diagrams in
`to_formalize/original_erdos_64_proof.tex` with the current Lean strategy
endpoint (`HypostructureErdos64EG.strategyDag`).  The order is the diagram
order, with continuations listed at the node where they first become open.

Here **closed** means that Lean constructs a terminal carrying the framework's
reserved `closed` fact.  A result constructor, theorem, or audit row can be
implemented and still be **open** if it returns an `ExactLedger` without that
closure key.  “Not attached” means that supporting declarations exist, but the
current endpoint does not call them.

| Diagram branch | Lean status | What is closed | What remains open / prevents closure |
|---|---|---|---|
| [1]--[4]: counterexample selection | Closed at the non-counterexample arm; the minimal-counterexample arm continues | The non-counterexample arm [3] is a target terminal | The selected minimal counterexample is intentionally the live input to the rest of the proof; it is not itself a contradiction |
| [5]--[7]: Mersenne return | Closed on [7] | A Mersenne return gives the target power-of-two cycle | The no-return arm continues through the minimal-core reductions [8]--[14] |
| [15]--[18]: induced (P_{13}) packing and local algebra | Closed on [16]; packing and label algebra continue on the other arm | The (P_{13})-free HSS arm [16] is closed by the target theorem | The non-free arm is a live packing/algebra residual; no terminal is expected until the later density and local branches |
| [19]--[20]: non-near-cubic surplus | Mixed continuation | The sparse-surplus block [125]--[144] is invoked for the above arm | The near-cubic arm now enters the attached [145]--[157] cold corridor; Type B bottleneck handoffs remain active outputs for their later consumers |
| [21]--[24]: finite window barrier and density | [21] overflow is closed; the collision/overflow alternative is open | `barrierOverflow` carries `closed`, corresponding to the overflow terminal [23] | `windowPackageCollided` has no closure key, although the diagram presents [23] as terminal; the missing final contradiction/closure is the likely bug |
| [25]--[32]: remainder, curvature rank, and Branch D entry | Rank-drop arm is closed; full-rank arm continues | Branch D reaches closed terminals [37], [39], [42], and [46] | The full-rank residual must pass through the entropy and net-charge branches; it is not a terminal at [32] |
| [33]--[46]: rank-drop Branch D | Closed | The context-defect, proper-atom, proper-support, and whole-graph barrier arms all append `closed` | No remaining open leaf in this panel; failures here would be implementation regressions rather than an intended missing branch |
| [47]--[54]: full-rank entropy split | One arm is closed; the high-entropy package arm is exposed | `entropyCapActive` carries `closed` for the low-entropy cap arm [54] | `entropyPackage` reaches the same mathematical terminal in the paper but has no `closed` key in its Lean index; the final closure is missing on that arm |
| [55]--[64]: large-budget/net-charge split | Several active residuals remain | The entropy-cap and any already-certified incompatible arms are closed | `smallOrderResidual` is an unhandled finite-size residue; `windowJoinPressure` is an active continuation; the Type A [63] and Type B [64] residuals require their later local analyses |
| [63], [86]--[109]: Type A receiver ladder | Mixed: explicit exit closures exist, but handoffs remain open | Exits (1)--(3), (5), and (6) close; route-8 terminal [124] also closes | Exit (4) is a peeling residual, exit (5)'s trace-level arm is open, exit (7) is an open Type B handoff, and the route-8-free arm is an open residual. These are continuations, not contradictions, but they must be consumed by the next block |
| [64], [65]--[85]: Type B fan analysis | Mixed | Direct-cycle arms close; the bridge/branch-kill closed arm is represented where the incompatibility is proved | Certificate-mass, overlap-obstruction-mass, exclusion-residual, and excluded arms remain open. In particular, the excluded arm is explicitly returned open because the caller must apply the appropriate branch-kill contradiction |
| [109]--[124]: route-8 pressure descent | Terminal only on the no-two-carrier route-8 arm | [124] appends the reserved closure key; zero/one-carrier cases route to existing exits | Peeled [102], exit-(4) data, trace-level [104], exit-(7) handoff [108], and the complementary free arm remain active until their consumers are attached |
| [125]--[144]: sparse surplus activation | Mixed | [133] sparse-pair exit and the fixed-cap [138] outcomes are closed locally where `closed` is appended | `nearCubic` now continues into the cold interface; the bottleneck outcomes are Type B handoff data and remain active for later consumers |
| [145]--[157]: hot/cold window interface | Attached continuation | `runCold` commits the ordered corridor facts and `coldBranchClosed` proves the paper’s no-terminal-cold-survivor statement | This is a semantic corridor closure, not the framework’s reserved `closed` contradiction key; the hot route-8/density consumers and Type B handoffs remain downstream work |

## Short bug list

The open branches that most directly indicate missing Lean work are:

1. `windowPackageCollided` at [21]--[23]: add or route the missing closure.
2. `entropyPackage` at [52]--[54]: add the final closure or an explicit continuation to `entropyCapActive`.
3. `smallOrderResidual` at [55]: supply the finite-size argument or a finite exceptional-case closure.
4. `windowJoinPressure` and the Type A/Type B handoffs at [60], [63], and [64]: attach their downstream blocks.
5. The open Type B fan residuals: consume the exclusion and fan-mass outputs with the correct branch-specific contradiction.
6. The remaining hot/density and Type B consumers after the attached cold-corridor block [145]--[157].

This is a topology/status document, not a claim that every mathematical gap
has the same priority.  The authoritative evidence for a branch being closed
is its Lean key index and the presence of the framework closure key; the
manuscript diagram supplies the expected order and terminal behavior.
