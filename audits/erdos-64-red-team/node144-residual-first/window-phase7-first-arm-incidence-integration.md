# [144] integrate the unique own-arm edge

The accepted local rule identifies every `P_a` edge at its first vertex
`a=nextLeft` with its unique first edge; `[a]` has none. In the conditional
case that all physical edges at `a` lie in the exact skeleton `F`, if
`a∉P_b`, the accepted endpoint rule removes every `P_b` edge. The known
centre edge `ha` occupies one incidence. The remaining possible edges at
`a` are now completely localized to `P_a` and `E(G[Y])`, where the
same producer chose `Y={left.2,right.2}`.

There are two exact first-entry cases to prove next. If `a∉Y`, no core edge
can touch `a`, and its own arm can contribute only its first edge. If
`a∈Y`, first-entry at its starting point and nodup should force `P_a=[a]`,
so its own arm contributes none; the induced graph on at most two core
vertices can contribute at most one edge. Thus either case should leave at
most `ha` plus one other edge, contrary to `deg_G(a)=3`. This is a
**mathematical prospect**: the core-edge bound, singleton implication, and
combined cubic contradiction are not yet Lean theorems.

The proposed route splice needs only the resulting `a∈P_b`. That places
`a` after `h` on the original right route, even when it is the first-entry
or final terminal. Replacing its segment from `h` to `a` by the actual edge
`ha` keeps the fixed root, terminal and right support: `a` already occurred
on the right route, and its suffix is unchanged. Nodup of the old right
route should keep the shortened one simple. The new right route agrees
with the left route at `a` after `h`, improving the selected common prefix.
Therefore a separate crossing `b∈P_a` and a cubic-degree use at `b` are not
needed for this particular proposed contradiction. This refinement has
independent mathematical review but still requires the exact Lean route
construction; no proof obligation is silently discharged.

The next atomic proof is `coreEdgeSet {u,v} ⊆ {s(u,v)}` on the actual graph,
including `u=v` and nonadjacent endpoints. A subsequent task must formalize
first-entry singleton behavior, then combine the incidence cases and build
the same-support splice. Constraint: no excluded graph case has yet been
kernel-proved. Compression: none. Quantity: no new account charge or cap.
The current `Holds`, structural move and branch remain open.
