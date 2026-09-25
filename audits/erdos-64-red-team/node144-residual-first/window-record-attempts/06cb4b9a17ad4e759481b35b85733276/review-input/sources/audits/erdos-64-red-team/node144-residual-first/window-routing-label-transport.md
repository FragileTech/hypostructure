# Routing-label transport on the retained source

Result: **SUBMITTED_RESULT**. The named label equals the owner-local label, coordinate-for-coordinate, on the specified retained domain. This is a mathematical transport proof by unfolding and extensionality; no new Lean theorem was implemented or kernel-checked in this audit.

Fix the complete pinned window residual on `G = selected.object`, and fix one set of witnesses `active_h, capacity_h, certified_h, token_h, role_h, pattern_h` from its single `K.typeBHandoff`. Write `data = spineData`, `δ = data.threshold`, `cubic : δ = 3`, and

```text
H : pattern_h ⊆ certified_h.ledger.presented.roleFibre token_h role_h
hp : pair ∈ pattern_h
hd : demand ∈ pair.
```

Use the owner's local definitions in the supplied excerpt, instantiated with precisely `object = G`, `active = active_h`, `capacity = capacity_h`, `token = token_h`, and `activation = capacity_h.activation`. Denote that instantiation by `routingLabel_old`. For any proof `hc : pair.card = 2`, the precise equality is

```text
sameTokenActualRoutingLabel data G active_h cubic capacity_h certified_h
  token_h role_h pattern_h H pair hp demand hd
  = routingLabel_old pair hc demand.
```

Both sides have type `SameTokenRoutingGerms.RoutingLabel (Fin δ → Fin δ) (WindowCurvature.Label data.windowOrder)`: `data.BoundaryProfile` unfolds to `Fin δ → Fin δ`. The conclusion is under the full retained conjunction; the following proof uses only its indicated projections. No separate class-audit or capacity-token-ledger witness is identified with these witnesses.

**Pair, order, and supports.** From `H hp`, projecting membership through the two filters defining the presented role fibre gives `pair ∈ G.portPairSchedule δ`. As in the named definition, `Finset.mem_powersetCard.mp` gives both `pair ⊆ G.excessPorts δ` and `pair.card = 2`. Put `p = pair.toList.get 0` and `q = pair.toList.get 1`, with their bounds supplied by this cardinality. Both belong to the pair and hence to `G.excessPorts δ`. Both definitions use this identical `pair.toList`, under the same object instances (`G.vertices`, `G.decideAdj`, `G.vertices.decEq`). The different proofs of the two index bounds do not affect `List.get`, by proof irrelevance. In particular there is no pair reversal or relabeling.

For either `u = p` or `u = q`, fix `hu : u ∈ G.excessPorts δ` and write

```text
T_u = (G.surplusPortOfMem hu).support
O_u = G.orderedVertices.filter (fun v => v ∈ T_u).
```

The old `selectedSupport u` reduces to exactly `T_u` by `dif_pos hu`; the membership proof chosen by the old conditional is immaterial by proof irrelevance. `active_h.shoulderPair u hu` supplies two distinct shoulders. The port endpoint is outside its shoulders: membership would imply a loop by `mem_shoulders_iff`. Thus the support, the endpoint inserted into those two shoulders, has cardinality `3 = δ`. This is the same argument in the old `selectedSupport_card` and new `supportCard`.

The fixed vertex enumeration contains every vertex exactly once. Filtering it gives `O_u.toFinset = T_u` and `O_u.Nodup`, so `O_u.length = T_u.card = δ`. For every `i : Fin δ`, therefore, `i.val < O_u.length`. The old outer profile fallback (`u` not an excess port) and old inner profile fallback (index outside this list) are both impossible here. The old empty-support fallback is likewise unreachable.

Let `v_i = O_u.get ⟨i.val, bound⟩`. Both profiles at `i` have precisely the value

```text
⟨(G.induce T_u).degree ⟨v_i, v_i_mem_T_u⟩, degreeBound⟩ : Fin δ.
```

Indeed the degree is strictly less than `(G.induce T_u).vertexCount = T_u.card = δ`, by `degree_lt_vertexCount` and `vertexCount_induce`. The two bound proofs and support-membership proofs may differ syntactically; proof irrelevance identifies them, and `Fin.ext` identifies the results from their identical natural-number values. Function extensionality then gives equality of the whole profile for each of `p,q`. Thus all profile entries are the original actual induced degrees, in the original order.

**The seven coordinates.** Unfolding the two labels now gives these identical entries:

| Coordinate | Common value and equality reason |
| --- | --- |
| Role | `capacity_h.role pair`, literally the same expression. No substitution by another capacity or even by the parameter `role_h` is required. |
| Token subtype | `FiniteObject.CapacityToken.subtype token_h`, on the identical token. |
| Selected endpoint | `if demand = p then 0 else 1 : Fin 2`. The ordered pair is identical. Because the pair has exactly two elements, `hd` ensures that the second case selects `q`. |
| Port statuses | The same pair of tests for two distinct adjacent shoulders of `p` and `q`, giving `.triangular` or `.openPort`. |
| Boundary profiles | The two equal functions just proved, on the ordered supports `O_p,O_q`, with the actual induced degrees at every index. |
| Window positions | `Finset.univ.filter` of indices for which there exist `window ∈ capacity_h.packing` and a `TypeBDirectCycle.Presentation G data.windowOrder` with that support and `presentation.coordinate index.val ∈ capacity_h.sameTokenRoutingSupport token_h pair`. The old `boundedSupport pair` unfolds to that exact support. |
| Blocker flag | `true` exactly when `canonicalBlocker capacity_h.activation pair` is `some (.arithmeticChordSet _)`, and `false` otherwise. The old local `activation` unfolds to `capacity_h.activation`. |

Product congruence using these seven equalities proves the displayed equality. This does not require any equality between `capacity_h.packing` and the separately retained envelope packing `packing_h`.

**Preservation and verification.** No original graph, witness, pattern, pair, selected demand, support, ordering, profile value, packing, core, envelope, or account changes. The named definition restricts evaluation to the actual pattern/member domain on which the old total auxiliary profiles always took their genuine-degree cases; it does not replace that retained domain. No equality is asserted outside this domain. Minimality, exclusions, strict surplus, and all other residual conjuncts remain as retained. No handoff or escape is reconstructed, and no move or branch is declared closed.

All five declared source files were SHA256-checked against `/input/assignment.json` and matched. Verification locators: the owner excerpt's original lines 639–643, 889–961, 967–990, 1230–1246; `SpineVocabulary.lean`'s `Data.BoundaryProfile`, `sameTokenActualRoutingLabel` (3944–4072), and `SameTokenTypeBHandoffStatement`; `ObjectCapacityLedger.lean`'s `presented` and `HomogeneousBottleneckPatternStatement`; `SameTokenRoutingGerms.lean:85–87`; and Phase 0's common-object and retained-account sections. The accepted P6 kernel-check is retained evidence for the definition, not a claim that this new equality was kernel-checked. There is no missing inference for this transport claim.
