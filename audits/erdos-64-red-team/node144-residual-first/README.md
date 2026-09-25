# Node [144]: residual-first structural run

This run starts from the literal post-[144] `ExactLedger` on the selected graph. It keeps the three incoming class histories separate: window-incidence, remainder-surplus, and primitive blocker-support. Each history retains its strict-surplus ancestry, positive homogeneous pattern, `typeBHandoff`, and `typeBFanEntry`. The branch snapshots and complete key indices are in `*-branch.json` and `phase0-evidence.md`.

## Reviewed state

| Incoming arm | Accepted tasks | Productive moves | Open outcome |
| --- | ---: | ---: | --- |
| Window-incidence | 37 | 0 | `window:[144a]-same-token-handoff` |
| Remainder-surplus | 12 | 0 | `remainder:[144a]-same-token-handoff` |
| Primitive blocker-support | 12 | 0 | `primitive:[144a]-same-token-handoff` |

Every accepted task has two independent cited reviews and fresh evidence hashes. The task records, not this summary, are the authoritative review state. Phase 0 pins the exact graph and ledger facts. Phase 1 records the prior use of the pattern and the blocked/free pair account on one certified handoff ledger. Phase 2 identifies the pair/envelope interaction and the two-edge selection made by the routing row. Phase 3 kernel-checks that the retained handoff pattern contradicts fixed homogeneous caps **if those caps are separately established**, and compares pair counting with direct fan geometry.

## Exact obstruction

`SameTokenTypeBHandoffStatement data G → ¬ HomogeneousCapsHold G ...` is checked in `CapCheck.lean`. The source pattern already violates the cap on that graph. The current routing proof uses the pattern's size to select two same-label edges and produces one decorated envelope from their configurations. Its published handoff retains the full pattern and the envelope, but no source-indexed relation from the remaining pattern edges to envelope incidences or bound on repeated use. `FanSafe` is a prohibition on accepted returns, not an actual target cycle. The old near-cubic repair work is an attempt fingerprint, not accepted proof in this run.

The reviewed window-arm trace now distinguishes all two non-centre incidences of each assigned cubic first neighbour. An outside edge enters a component of `G-S` with at least two attachments to the actual envelope support `S`. A positive-length arm only uses a non-centre incidence when its first edge differs from `ha`; the retained handoff permits the exception `[a,h]`. The accepted relative cycle-rank account is

```text
β(G) = β(F) + |E(G[S]) \ E(F)|
       + Σ_C (β(G[C]) + |δ_G(C)| − 1) − (c(F) − 1).
```

Here `F` is the declared core/arm/centre-edge skeleton. The selected graph `G` is connected, but the handoff does not retain connectedness of `F` or its core. Extra edges and exterior components can merge pieces of `F`, and several apparent spare incidences can share a single cost. The paper calls the core connected; the literal returned handoff does not establish that condition. See the three reviewed `window-phase2-*` notes on fan attachments, exterior cuts, and relative cycle rank.

The next mathematical obligation is a graph-level consequence on the **full tagged residual**: a proved map from original source-pair indices to distinct physical edges, exterior components, or other eligible payers, with bounded multiplicity and a calibrated payoff; or a direct forbidden cycle or minimality-valid replacement from the retained fan geometry. The new edge trace has no such map. The ready task queue is empty because structural selection must be revisited; it does not certify closure.

For the union `R` of one declared route for **every** source demand, the reviewed full-route boundary trace gives a connected support `T=V(R)` and the sharper identity `β(G)=β(R)+|E(G[T])\E(R)|+Σ_C(β(G[C])+|δ_G(C)|−1)`. This is an actual cut of `G`; unlike the one-envelope account, it has no component-merger term. It still counts physical edges and components once, while many original source indices may share them.

No [144a] arm is closed. No new Lean owner declaration or manuscript theorem has been installed by this run. The audit proof compiles with exit code zero; the existing node-table and API checks passed before the Phase 2/3 audit work, which changed no proof sources.
