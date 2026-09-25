# Node 20 Stage 3b: exact local geometry

Work only with the `Coordinate, family, coordinateSupport, attempt, reduced,
full, identified, defect` tuple from `K .sparseTargetDefectResidual`. Unfold
`defect` once to its own `outside`; do not substitute the ambient complement.
The selected Stage 3 claim is L1–L5 in the accepted
`stage3-opportunity-b358.md` record evidence. Its weakest case is
`rc15_000_r`, symmetric to `rc15_000_f`.

Use the existing local graph facts:

- `glueGraph_adj_iff` identifies each glued adjacency as piece-owned or
  context-owned. `pieceEmbedding` and `contextEmbedding` are injective.
- `SimpleGraph.Walk.transfer` transfers a cycle whose edges all belong to one
  mapped side into that side's mapped graph, preserving edges and length.
- `GluedCycleSides.cycle_pieceLift_or_contextInternal_or_labelDart` classifies
  a glued cycle relative to its piece side.
- `GluedCycleSides.exists_two_labels_of_cycle_sides` supplies two distinct
  boundary labels when a simple cycle visits both interiors.

Prove the missing edge-source alternatives for this *same* positive cycle:
an outside-only cycle contradicts L1; at empty boundary a cycle lies on one
side, hence on the positive piece; when that piece embeds into the selected
target-free graph, a piece-only cycle is excluded too, so the cycle uses both
exclusive edge sources and visits two distinct boundary vertices. Preserve
the piece-local-or-mixed alternative when no realization is given. Do not
assume a code-to-cycle dependency or a numerical payoff.

The only published proof fact belongs under `K .sparseTargetDefectStructure`.
Derive it inside `sparseTargetDefectStructureRow` from `inputs.get` and
`inputs.current`; do not leave a detached theorem that supplies this fact.
The row must retain the incoming residual key and inherited ExactLedger keys.
Avoid environment-wide declaration enumeration or unrelated source searches.
