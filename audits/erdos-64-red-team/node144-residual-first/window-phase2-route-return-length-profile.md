# [144a] window history: elementary return-length profile

Fix the literal post-[144] window ledger on `G=selected.object` and
one `typeBHandoff` witness with source pattern `P` and physical assigned
fan-edge set `B`. For each incidence `(p,d)` with `p∈P,d∈p`, choose
its own declared simple route `r_{p,d}` in the pair-specific support.
Let `R` be the union of these routes and `T=V(R)`. It is connected,
with all routes based at the same token root. Put
`J=E(G[T])∖E(R)`; let `C` range over the actual components of
`G-T`, with `∂_T C=δ_G(C)`. The cut is in `G`, not in the
possibly disconnected handoff skeleton on its different support `S`.

**Chord profile.** For each `e=uv∈J`, let `L_ch(e)` contain
`|Q|+1` for **every** simple `u`–`v` path `Q` in `R`,
where `|Q|` is its number of edges. Connectedness of `R` makes
`L_ch(e)` nonempty. Because `e∉E(R)`, adjoining `e` to any such
`Q` gives a simple cycle of exactly that length in `G`.
The marker `e∈B` or `e∉B` is retained for each chord.

**One-component return profile.** For each `C`, take every ordered
pair of **distinct** boundary edges
`b_1=s_1x_1, b_2=s_2x_2∈∂_T C`, where `s_i∈T,x_i∈C`.
Take every simple `x_1`–`x_2` path `P_C` in `G[C]` and every
simple `s_1`–`s_2` path `Q` in `R`; when the endpoints of either
path coincide, include its trivial length-zero path. Define

```
L_ret(C;b_1,b_2) =
  { |P_C| + 2 + |Q| : P_C and Q range as above }.
```

The paths are internally vertex-disjoint because `V(P_C)⊆C` and
`V(Q)⊆T`. If `s_1=s_2`, simplicity of `G` and `b_1≠b_2`
force `x_1≠x_2`; if `x_1=x_2`, they force
`s_1≠s_2`. Thus `b_1+P_C+b_2+Q` is a simple cycle in every
case, of the displayed length. Actual connectivity of `C` and
`R` makes each `L_ret` nonempty. The retained connectivity and
bridgelessness of `G` give `|∂_T C|≥2`, so every exterior
component has at least one such boundary-edge pair. Each return
keeps the two physical edge markers `b_i∈B` and the markers for
internal `P_C` edges and `Q` edges.

To retain original source indices on each cycle `Z`, put
`U_p=⋃_{d∈p}E(r_{p,d})` and
`a_Z(p)=|U_p∩E(Z)|`. This is an exact per-pair measurement,
including `a_Z(p)=0` and repeated use of the same physical cycle
edge by different `p`. Since `E(R)=⋃_p U_p`, only the `Q`
portion of an elementary return or chord cycle can lie on a chosen
source route. The chord `e`, both boundary edges, and every internal
`P_C` edge have source-pair multiplicity zero **for this selected
route family**. They may still be fan edges in `B`; those independent
markers are retained.

The retained `selection` fact says that `G` has no cycle whose
length satisfies `spineData.LengthOK`. Therefore the two finite
profiles satisfy the exact inherited exclusions

```
L_ch(e) ∩ {ℓ : LengthOK ℓ} = ∅,
L_ret(C;b_1,b_2) ∩ {ℓ : LengthOK ℓ} = ∅.
```

These are consequences of the already retained target avoidance,
not new forbidden-length theorems. In particular no selected value
of either spectrum is assumed to be a power of two.

This profile exhausts chord cycles and the cycles made by **one**
component excursion plus one route path. A simple cycle may visit
several components, alternate among several chords, or lie wholly
inside `R` or a component; those cycles are not claimed to be
classified by these two spectra. The handoff supplies no relation
forcing a target length in the measured spectra and no bound on how
many source pairs can reuse the `Q` segment. Nothing here closes or
quantitatively shrinks [144a].

Sources: full window ledger in `phase0-evidence.md`; reviewed
`window-phase2-source-incidence.md`,
`window-phase2-fan-route-rank-cross-tab.md`, and
`window-phase2-all-route-boundary.md`; target-free `selection`
and `LengthOK` in `SpineVocabulary.lean`.
