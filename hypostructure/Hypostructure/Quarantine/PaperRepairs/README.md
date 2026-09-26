# Quarantined paper repairs (reference only)

This folder holds repairs the user ruled out of the proof on 2026-09-26: "no repairs, no
deviations; implement the paper and report its errors". They stay here as a reference.
- No live module may import them.
- They are listed in `hypostructure/quarantine.txt`.
- The live proof represents each paper error as a tagged `PAPER-ERROR` sorry at the node
  where the paper makes the claim.

| File | What it is |
|---|---|
| `Node144Gap.lean` | Lean-checked analysis of the [144] step "target-complete ⇒ compression (c)": the survivor dichotomy (L1′), a target-complete pair adds no exit (L3), the parallel-case positional lemma (L4), and the trie bound (P2). |
| `ColdF4Charge.lean` | Cold (F4) charge: exact characterization of the F4 count for whole-piece registries; the heavy-centre reading with the chain `heavy_handoff_not_subcubic` → the existing loss bound. |
| (pending) `F2PathContext.lean` | The (F2) exclusion analysis, added when that agent reports. |

The repairs reverted from the live tree also belong here:
- the [144a] widening;
- the heavy-centre cold registry;
- F5's [156] G2 closure (commit f8193d4).

They are added by the agent that reverts them.
