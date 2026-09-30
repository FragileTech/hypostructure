<!-- Operator note: verbatim copy of the user-approved scratch file stage3_required_candidate.md (session scratchpad), added to the Stage 3, 3b and 4 scopes by the user's instruction. It is a candidate for evaluation, not a fact about G and not a required selection. -->

# Stage 3: required candidate tension (the user's joint structure)

Evaluate this candidate at Stage 3 alongside any others. It is required to be considered. It is not required to be selected: judge it by the gate criteria (new structure, real tension on the weakest case, productive payoff, not in known-failed-approaches).

## The combination: every fact below constrains the SAME objects at once

These structures have never been combined in one argument. Earlier threads tested each family on its own, and each collapsed into counting.

1. **Spectral response of the readings** (at [20a]'s pinned witness w = (A,B,Z,O), or at any Spec witness). The facts:
   - the exact port-to-port path-length transfer (`exact_spectrum_one_way`, chain contexts);
   - the refined arm (i) (`spectrumArmOneRefined`): a path π in P from a to b with |π| + |σ| = 2^k, and N lacks length |π|;
   - outside returns τ from b to a with |π| + |τ| ≠ 2^m and |τ| ≠ |σ| (`cubicLabelOutsidePath`, `twoBoundaryOutsideBoth`);
   - O is not realized in G − Z;
   - the private edge, with an interior degree-3 endpoint.

   So the outside spectrum between the ports must avoid the whole set {2^m − |π|}.
2. **Window rigidity**, acting on those same τ. Every τ of length ≥ 12 that avoids windows carries chords, and their spans are pinned (`forced_path_chord`, `closed_path_chord`). When τ does cross windows:
   - the out-stubs are fixed: a cubic interior vertex has exactly one (`windowPositionStubs`);
   - the entry and exit gaps are pinned: |i−i′| + |j−j′| + 2 ∉ 2^ℕ (`windowAttachmentGap`);
   - so the window segments add lengths that are fixed by position.
3. **Hub links in R**, also on those τ. If τ stays inside R:
   - R has no induced P13;
   - bags have at most 6142 vertices;
   - induced hub chains of 13 or more vertices are forbidden (`chain_contra`, `no_rainbow_at20a`, `no_path2`, `no_pathJ`);
   - the link graph is degenerate.

   So a τ inside R is a short route through hubs and bags, with restricted lengths.
4. **Structural obstructions.**
   - `threeRouteFan` and `threeRouteChain` at the hubs τ passes through;
   - the switch paths of length 2^j − 1 at those hubs;
   - Z's position relative to the windows (not inside one window; if Z ⊆ W then there is a cross-window edge at y);
   - the Steiner cut vertices of Z;
   - ≥ 2 active labels in A ∩ B.

## The tension to evaluate
The routes τ available to G between the witness ports have their lengths determined by windows (fixed stubs, gaps, chord spans) and by R (bounded, via hub/bag routes). The spectrum condition forbids exactly the lengths {2^m − |π|} and {|σ|}. At the same time, O's route σ, which is not realized in G, has length 2^k − |π|.

The question: do window rigidity and the R-route constraints together force some τ to hit a forbidden length, or force G to realize O? Either would be a contradiction. It should be decided per region:
- ports on windows versus ports in R;
- |∂Z| = 2 versus ≥ 3;
- arm (i) versus arm (ii).

## For [144a] (U2-shared)
- Region U2-shared has equal port-to-port spectra (`exact_spectrum_iff`).
- The private edges of X_q ∖ X_p lie on hanging parts that meet the seed.
- The same window and hub-route rigidity acts on every route that leaves Z.

Evaluate the analogous combination there.
