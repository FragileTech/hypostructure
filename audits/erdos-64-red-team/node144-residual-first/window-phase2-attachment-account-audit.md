# [144a] window history: attachment-account audit

**Scope and ancestry.** This account concerns the literal 50-key
post-[144] `ExactLedger` on `G=selected.object` reached by
`[139] yes → [140] windowIncidenceAuditRow → [144]`.
It fixes **one** `typeBHandoff` witness containing its original
same-token matching or star `P`, certified presentation, root,
packing, core, and decorated envelope. The separate existential
`windowClassOverload` and other ledger presentations are not
identified with this witness. Strict surplus and the full selected
graph restrictions remain inherited. The endpoint is still
`False` from this complete ledger; none of the measurements below
is substituted for that endpoint.

| Level | Actual index or physical object | Established account | Unresolved transfer |
| --- | --- | --- | --- |
| Original demand | Source pattern `P` in one certified role fibre | `|P|≥L_geom=Q_geom+1`; the original blocked/free and token/role-fibre partitions remain the published ledger accounts. | Only two selected source edges produce the published envelope. No map from **all** `P` to its fan assignments or to distinct cost units is retained. |
| Declared route | `I_P={(p,d):p∈P,d∈p}`; one simple `r_{p,d}` in `sameTokenRoutingSupport token p` | Every route starts at the same root and ends at `d.2`; `R=⋃r_{p,d}` is connected. `W={(p,e):e∈U_p}` gives `|W|=Σ_p|U_p|=Σ_e n_P(e)`. | Pair supports differ. Shared star demands need not use one route; routes can overlap or coincide physically. |
| Whole-route reuse | Terminal fibres `I_v`, ordered-route classes `Q_v`, incidence multiplicities `ν_v(q)`, pair multiplicities `σ_v(q)` | `|I_P|=Σ_vΣ_{q∈Q_v}ν_v(q)`, `σ_v(q)≤ν_v(q)`. A repeated `q` lies in every pair support of its class, and **only its terminal** is known in every corresponding local buffer. | No effective bound on `ν_v(q)` or on the number of distinct paths follows from this handoff alone. |
| Fan assignment | `A={(h,a):h∈H,a∈K_h}`; `D={(h,a,e):e` incident to `a`, `e≠ha}` | Every assigned `a` is cubic; `|D|=2|A|`. The `K_h` sets need not be disjoint. The physical edge multiplicity `μ(e)` is at most 4 internally and 2 across `δ_G(S)`. | `μ` counts fan assignments, not source pairs. Neither `|A|` nor `|D|` is a payment for `|P|`. |
| Physical fan edge | `B={e:∃(h,a,e)∈D}`; envelope support `S`, skeleton `F` | `B` partitions into `F`, extra internal `I=E(G[S])∖E(F)`, and `δ_G(S)`. `D` partitions with the same edge labels and `Σ_e μ(e)=2|A|`. | `B∩δ_G(S)` and `B∩I` can be empty. A positive arm may begin with `ha`; a length-zero arm lies in the core. The skeleton `F` need not be connected. |
| Source-to-fan incidence | `M=W∩(P×B)`; `P_0={p:U_p∩B=∅}`; physical pair multiplicity `m_P(e)` | `|M|=Σ_p|U_p∩B|=Σ_{e∈B}m_P(e)`. Zero-coverage and repeated-use indices are explicit. | No proof gives `P_0=∅` or a bound on `m_P(e)`. The bound on `μ(e)` does not transfer to `m_P(e)`. |
| Envelope exterior | Components of actual `G-S`; `k_C=|δ_G(C)|`; `q_C=Σ_{e∈δ_G(C)}μ(e)` | Every component attaches and `k_C≥2`; `0≤q_C≤2k_C`; `Σ_Cq_C=|D_∂|`. Source-route visits `V={(p,C):r_{p,d}` visits `C` for some `d∈p}` have their own exact double count. Pair-demand boundary-crossing counts `b(p,d,C)` and edge-use counts `λ_I(e)` have the exact crossing sum and endpoint parity below. | Several fan incidences or source routes may use one component. The second attachment can land at the same assigned neighbour in the allowed degenerate cases. A source visit need not be a fan incidence. |
| Route exterior and rank | `T=V(R)`, `J=E(G[T])∖E(R)`, components of actual `G-T` | Every `e∈B` lies in exactly one envelope-location × route-location cell: `R`, `J`, one boundary `δ_G(C)`, or one component interior. `B∩E(R)` is precisely the physical support of `M`. `β(G)=β(R)+|J|+Σ_C(β(G[C])+k_C−1)`. | `G-S` and `G-T` components are different families. A used route edge is already in `R`; only a distinct `J` edge directly pays one relative-rank unit. Boundary and interior costs are collective. |
| Full cycle trace | Every simple cycle `Z` of `G` | Exactly one category: wholly in `R`, wholly in `G[T]` using `J`, wholly in one `G-T` component, or mixed. A mixed cycle has an exact alternating excursion/`T`-segment length sum. Each cycle retains its fan marker `E(Z)∩B` and per-source-pair marker `a_Z(p)=|U_p∩E(Z)|`. Elementary chord and one-component return spectra retain all path choices and equal-landing cases; all cycle lengths fail `LengthOK` by the inherited `selection`. | Multi-excursion and multi-chord cycles are explicit but no measured profile is forced to have a target length. An inherited target exclusion alone does not bound original pair reuse. |

For clarity, the crossing coordinate in the `G-S` row is
`b(p,d,C)=|E(r_{p,d})∩δ_G(C)|`, while
`λ_I(e)=|{(p,d)∈I_P:e∈E(r_{p,d})}|`. It satisfies

```
Σ_{(p,d)∈I_P} b(p,d,C) = Σ_{e∈δ_G(C)} λ_I(e),
b(p,d,C) ≡ 1_{ρ∈C}+1_{d.2∈C} (mod 2).
```

This counts a shared star demand separately for every source pair.
The cycle marker `a_Z(p)` likewise retains original pair indices;
`E(Z)∩B` records physical fan edges even when no chosen source route
uses them. Neither coordinate identifies a pair with a distinct
boundary edge or cost unit.

Two cycle-rank readings must be kept distinct. For the declared
envelope skeleton `F`, which may have `c(F)>1`, the exact
formula is

```
β(G)=β(F)+|E(G[S])∖E(F)|
     +Σ_{C component of G-S}(β(G[C])+|δ_G(C)|−1)
     −(c(F)−1).
```

The subtraction records component mergers; one cannot charge each
raw attachment term without it. For the connected source-route
union `R`, the route-exterior formula in the table has no such
correction. Its `B∩E(R)` cell can carry arbitrarily many *indexed*
uses without adding a marginal `|J|` unit. The two identities do
not create a source-pair-to-rank map.

**The current exact unanswered interaction** is whether the
pair-specific support intersections, high-centre normal form, and
target-return exclusions constrain repeated source use of one
physical route or force cost-bearing chords/excursions with bounded
multiplicity. This question includes both `P_0` and covered pairs,
matching and star, zero exterior incidence, repeated assignments,
same-component returns, and all cycle-trace categories. The
published handoff supplies no fixed homogeneous cap and no
near-cubic estimate on this arm.

This audit is complete **for the declared attachment coordinates
introduced in Phase 2**: each original incidence, selected route,
fan assignment, physical edge, exterior component, rank term, and
cycle has an explicit index or category, and every missing transfer
is named. It is not a proof that all possible graph invariants have
been examined, nor a proof of an effective restriction or closure.
The next workflow step must select a supported structural tension
and establish a per-outcome payoff before constructing a move.

Sources: `phase0-evidence.md`; accepted
`window-phase1-pair-account.md` and
`window-phase2-fan-attachments.md` through
`window-phase2-all-cycle-trace.md`, including the individually
reviewed source-incidence, rank cross-tab, return-length, and
whole-route reuse records.
