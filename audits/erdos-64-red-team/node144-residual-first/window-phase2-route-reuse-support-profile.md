# [144a] window history: whole-route reuse and support intersections

Fix the literal post-[144] window ledger on `G=selected.object` and
one `typeBHandoff` witness with source matching or star `P`,
token `t`, and common root `ρ`. The routed-pattern statement gives a
configuration separately for each incidence
`I_P={(p,d):p∈P,d∈p}`. Choose one such simple ordered path
`r_{p,d}` for every incidence, inside
`S_p=sameTokenRoutingSupport token p`, ending at `v=d.2`.
Here `localBuffer(d)` abbreviates the handoff activation's
`localBuffer d`.
No equality between choices for repeated demands is assumed.

For every actual terminal vertex `v`, define

```
I_v = {(p,d)∈I_P:d.2=v},
Q_v = {r_{p,d}:(p,d)∈I_v},
C_v(q) = {(p,d)∈I_v:r_{p,d}=q}   (q∈Q_v),
ν_v(q) = |C_v(q)|.
```

Equality in `Q_v` means equality of the **ordered vertex lists**,
rooted at `ρ`, not merely equality of endpoint, support, routing
label, or first edge. The classes `C_v(q)` are disjoint and exhaustive
for `I_v`. Consequently

```
|I_P| = Σ_v |I_v|,
|I_v| = Σ_{q∈Q_v} ν_v(q),
1 ≤ ν_v(q) ≤ |I_v|,
1 ≤ |Q_v| ≤ |I_v|   when I_v≠∅.
```

To keep *source-pair* multiplicity separate from pair-demand
incidence multiplicity, put
`P_v(q)={p∈P:∃d∈p,(p,d)∈C_v(q)}` and
`σ_v(q)=|P_v(q)|`. Then `σ_v(q)≤ν_v(q)`; equality need not
hold if two demands in one pair have terminal `v` and select the same
route. Both indices remain available for a later charge. The
physical route union is exactly
`E(R)=⋃_{v}⋃_{q∈Q_v}E(q)`; repeated incidences do not add physical
edges, and distinct routes can still overlap extensively.

The declared supports impose an exact necessary condition on every
reuse class:

```
V(q) ⊆ ⋂_{(p,d)∈C_v(q)} S_p,
v ∈ ⋂_{(p,d)∈C_v(q)} localBuffer(d).
```

The first inclusion follows from the `inside` field of each selected
configuration. The second follows from its `lands` field and the
retained equality of its final vertex with `d.2=v`. Thus a route
reused by many original incidences must fit all of their
**pair-dependent** supports and all selected endpoint buffers.
The intersections are measured on the one handoff witness; no
nontrivial upper bound on their sizes or on `ν_v(q)` follows from
the retained proposition alone.

For a star, the same centre demand may occur in many distinct source
pairs. Those incidences lie in one `I_v` when they have the same
terminal, but they may occupy one class or many classes because their
`S_p` differ. Distinct demand objects may also share `v`, including
in a matching; terminal equality does not identify their demands or
their buffers. If `|Q_v|=1`, all selected incidences at `v`
reuse one physical route. If `|Q_v|>1`, at least two different
simple `ρ`–`v` routes are present. The present task records this
alternative; it does not charge route diversity to cycle rank or
infer a target cycle from it.

This profile measures every selected route incidence by terminal,
whole-path identity, original source pair, and common support
intersection. It does not prove that either high route diversity or
low route multiplicity must occur. In particular, the large
matching/star size cannot be converted to `|E(R)|`, `β(R)`,
fan-edge coverage, or an envelope cap by replacing `|I_P|` with
`Σ_v|Q_v|` without controlling the `ν_v(q)` fibres.

Sources: complete window ledger in `phase0-evidence.md`; pair-specific
support and routed-pattern quantifiers in `ObjectCapacityLedger.lean`
lines 144–161 and 651–678; routing configuration `inside`,
`lands`, and `nodup` fields in `SameTokenRoutingGerms.lean`
lines 229–246; reviewed `window-phase2-source-incidence.md` and
`window-phase2-route-return-length-profile.md`.
