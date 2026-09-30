# Existing Stage 1 and Stage 2 material for Node [20a] (verbatim, user-supplied)

Source: the `[20a]` section of the session scratch file `stage12_existing.md` (the user states Stages 1 and 2 are already done; transcribe this material, do not re-derive it). Scratch paths below are relative to the scratch root; the files are filed in the run record under `record/scratch-proved/<same path>` with sha256 (evidence ids `scratch_*`, see `record/scratch-proved/INDEX.md`). The directory `sim/` cited below is empty in the scratch root (no file to cite). The register entry is `prior-use-source-excerpt.md` (2).

## [20a]

### Prior uses (Stage 1): structure already exploited, the move that used it, and its effect
- **The register's [20a] entry.** `audits/erdos-64-red-team/lean-vs-paper-discrepancies.md` → [20a]. It lists 128 facts, and each ported fact names the proving move (contract lemma) and its placement.
- **Moves already tried, and why each failed.** These are prior uses with NO closing effect. Each is Lean-checked, and the scratch file gives the evidence.
  - Counting bounds (`joint/Joint.lean`, `hubwin`, `hublink`). All of them tighten one side. They collapse to the master bound 0.253√n ≲ s < n − C√n.
    - Effect: the minimal order and the first band are closed (8n ≤ 32s + 125s²).
    - The slot relation, made linear, closes few-window hubs-in-R configurations: C√n + 15h < 3s + K·h_R + 584ν + 32σ_W.
  - Local rigidity. The simulation `sim/` found every placement locally consistent. It produced the facts `threeRouteFan`, `threeRouteChain`, `windowPositionStubs` and `windowAttachmentGap`.
  - Density (`density/`). Forced paths only add slack; slack(S) = |S| + ∂S − 6 − σ_S.
  - Windows (`windows/`). Window geometry, the remainder budget, and charge kinds.
  - GRS (`grs/`). R has no induced P13, bags have at most 6142 vertices, and paths in R have at most 6143·h_R + 6142 vertices. There is no h-independent path bound.
  - Capacity accounting (`account/`).
    - Π_free ⊆ Π_tri ∪ Π_cs.
    - The extended charge makes the free side empty and forces an unconditional overload.
    - The caps are missing. Separated pairs, each blocked by a singleton {p}, put load of about σ on a single port.
  - Arm A (`armA/`). The L_geom pattern has exactly four kinds: (a) a vertex w in T∪Γ of ≥ L+1 ports; (b) the same with the returns; (e) target defects; (f,P) a star at p₀ blocked by {p₀}. Only 10 of the 36 roles carry load.
  - Arm B (`armB/`). B1, B2 and B3 are exact.
    - G8 and G12: failed linkage. Menger does not apply (see the C4 counterexample).
    - The demand ends and U: the end-degree facts.
  - K1–K7 and the matrix (`k20a-K*`, `analysis-20a-matrix`, `combine-20a`). Their closures are ported as keys 6700–6718 and the enrichment keys.

### Inventory (Stage 2)
- The full accumulated constraint list, grouped by object, marks each item as ledger or scratch-proved and marks combined facts. It is the list given to the user under "the explicit accumulated list of constraints". The same content is in the register entry plus the scratch files above.
- The fact-by-fact interaction matrix is in `analysis-20a-matrix/matrix.txt`, and the joint inventory in `combine-20a/Combine20a/Joint.lean` (`Joint20aAll`).
- **The dichotomy.** `pairCodeConfiguration` (key 6676) splits [20a] into arm A (the [137]→[143] pattern) and arm B (the pair-code chain, with outcomes B1, B2, B3). Both arms are classified exactly above.

