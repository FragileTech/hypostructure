# Register section "Hubs, windows and the remainder at G (port-joint)" (verbatim)

Source: `audits/erdos-64-red-team/lean-vs-paper-discrepancies.md` lines 1971-2211 at g-repair-base `4519bdd` (Merge port-joint), plus the port-joint count note (line 2214). Operator note: these 38 keys (idx 7200-7237) are ledger facts of G carried by the `[20a]` residual on g-repair-base from 4519bdd onward (the residual then carries 166 facts). This run was pinned at 7d3186b with the 128-fact residual. The keys are therefore NOT in this run's record facts. They are supplied, by the user's instruction, as Lean-checked ledger facts of G on the current branch, and they may be cited from their statement/contract files (`Graph/Statements/{JointHubs,HubLinks,PairArms}.lean`, `Graph/Contracts/Spine/{JointHubs,HubLinks,PairArms}.lean`, copied at 4519bdd).

## Hubs, windows and the remainder at G (port-joint, 2026-09-28)

**Lean improvement (not routed by the paper).**  The joint analyses (scratch
`joint/Joint.lean`, `windows/Windows.lean`, `windows/LiveCharge.lean`,
`windows/ClauseE.lean`, `density/Density.lean`, `hubwin/HubWin/*`, `grs/Grs/*`)
and the hub-link (scratch `hublink/HubLink/*`, rounds 1-2) and accounting (scratch
`account/Account/*`) analyses are proved in vocabulary-free libraries together with the pair-code arm analyses (scratch `armA/ArmA/*`, `armB/ArmB/*`) and
published as 38 facts of G (idx 7200-7237; 7238-7399 free): 21 on the entry prefix (carried
by every residual), 16 at the top of the strict arm of `[19]` (carried by every
strict-surplus residual), and 1 on the `[20a]` arm.  One `Holds` conjunct and one `get` each at every
return.  No decision is added, moved or removed; no split.  One closure (the first
band at `C_sp`), recorded under "Closed from G's facts"; it excludes orders of the
strict arm without splitting any residual.

- **Library** (`hypostructure/Hypostructure/Graph/`, no EG names, no paper labels):
  - `JointSystem.lean` (any `SimpleGraph`): `comp_bound`, `card_le_degsum_comp`,
    `c4Free_of_noCycle4`, `double_count`, `hub_sum`, `hub_sum_split`,
    `cubic_has_cubic_nbr`, `cubic_hub_nbrs_le_two`, `five_hub_bound`, `LL_supply`,
    `cubicGraph`, `cubic_degsum`, `domComps_card`, `dominate`, `big_hub_bound`,
    `Vmid_card_le`, `X2_sub`, `X2_card`, `t_sum`, `t_upper`, `bonferroni`,
    `high_surplus_bound`, `high_surplus_closure`, `LL_identity`, `hub_mean_at_top`,
    `ll_parity`, `forced_path_uses_LL`, `minimal_order_slice`, `band_closed`,
    `minimal_order_closed`, `first_band_closed`; the propositions `CubicSupply`,
    `LowEdgeParity`, `HubDomination`, `VShapeCaps` with their proofs; the closure
    arithmetic `first_band_of_closure`, `closure_at_window`.
  - `WindowCombination.lean` (any `SimpleGraph`, any window set `W`): `short_walk`,
    `hub_pair_bypass`, `hub_pair_dichotomy`, `block_has_chord`, `chord_cycle`,
    `forced_path_chord`, `chord_count`, `exists_layering`, `layer_bound`,
    `component_card_le`, `remainder_budget`, `window_density`, the capacity arithmetic
    (`capped_window_load`, `capped_spread_pairs`, `cross_region_split`,
    `class_split_G2`, `fits_class_pigeonhole`, `sameHub_cauchy`, `capped_class_load`,
    `pair_deficit_nK`, `pair_deficit_forces_order`, `capped_hub_lower`,
    `capped_single_hub_closed`, `capped_free_hubs`, `late_partition`), `return_short`,
    `attach_no_gap_two`, `attach_le_seven`, `interior_not_in_window`, `seq_crossing`,
    `carrier_position`, `concat_cycle`, `closed_path_chord`,
    `outside_return_dichotomy`, `attach_no_gap_six`, `attach_edge_gap`,
    `component_hub_degree`, `component_single_hub`.
  - `DensityOverload.lean`: `degenerate_internal_sum_le`, `degree_split`,
    `slack_formula`, `density_iff_excess`, `slack_insert`, `single_hub_slack`,
    `single_hub_density_automatic`, `nbhd_matching`, `len3Pairs_card_le`,
    `secondNbhd_card_le`, `secondNbhd_edges_le`, `len3Pairs_le_four_d`,
    `nonadjPairs_card_ge`, `long_pairs_card_ge`.
  - `HubWindow.lean` (Budget, Slack, Lift, WindowU): `intL_formula`, `intL_sigma`,
    `window_LL_exact`, `LL_split`, `hub_budget`, `edge_ends`, `big_hub_mass`,
    `degenerate_internal_sum_le`, `slack`, `hang_one`, `hang_many`, `hanging_bound`,
    `slack_formula`, `list_cycle`, `lift_cycle`, `interval_has_dyadic`,
    `block_ineq`, `window_U`.
  - `RemainderPaths.lean`: `greedy_induced`, `span_induced`, `span_path_bound`,
    `noInducedPath_of_P13`, `long_chord`, `long_cycle`, `path_le_of_circumference`,
    `run_reach`, `run_card`, `bag_path_bound`, `induced_extend`, `induced_of_mindeg`,
    `low_vertex`.
  - `WindowLabelCensus.lean`: `singleton_legal`, `labelsOfSize_one_card`,
    `order_eq_of_sizeDistribution_head` (the registered census fixes the window order
    to `13`).
  - `WindowChargeKinds.lean` (any activation, presentation, packing):
    `canonicalBlocker_ne_sharedDeclared_incidence`,
    `canonicalBlocker_ne_sharedReturn_incidence`, `window_charge_support`,
    `cross_charge_support`, `window_charge_kind`, `window_charge_of_support_edge`,
    `connectedOn_crossing_edge`, `coordinate_spread_window_charge`,
    `separated_of_late_canonical`, `centre_not_mem_support`, `early_of_shared_return`,
    `early_charge`, `sameHub_early`, `sameHub_early_recorded`,
    `window_chord_charge_close`, `recorded_profile_empty`,
    `no_window_charge_of_support_in_R`, `responseObstruction_targetDefect`; the
    propositions `WindowChargeStructure`, `RecordedActivationFacts`,
    `ResponseObstructionsAreTargetDefects` with their proofs.
  - `HubLink/TCount.lean`, `HubLink/Chain.lean`, `HubLink/Rainbow.lean`,
    `HubLink/SlotC8.lean`, `HubLink/SlotCover.lean`, `HubLink/Greedy.lean`,
    `HubLink/Overload.lean` (any `SimpleGraph`): `tsum`, `tc_le_two`, `acount`,
    `codeg_le_one`, `a2_le`, `exception_identity`, `outer_cubic`,
    `linked_of_not_unlinked`, `unlinked_card`, `hub_link_count`, `unlinked_hub_sum`;
    `decode`, `chainSeq_view`, `chain_induced`, `chain_P13`; `extend`, `rainbow5`,
    `part_degenerate`, `strong_rainbow5`, `spart_degenerate`, `degenerate_sum`,
    `strong_path_rainbow`, `mem_part`, `part_subset`; `no_c8`, `tc_one_unique`,
    `ml_pair`, `ml_fibre`, `ll_pair`, `ll_fibre`, `LLset_card`, `A2_one_cubic`,
    `slot_bound`, `slot_relation`, `slot_exact`; `slot_cover`, `slot_classes`;
    `greedy_path`, `greedy_degenerate`; `into_centre_le`.
  - `HubLinkObject.lean` (any `FiniteObject`, any maximal packing of order `13`): bags,
    `LinkVia`, `fibre_card`, `cap`, `chain_contra`, `link_chain_contra`, `no_rainbow`,
    `link_degenerate`, `strong_degenerate`, `link_pairs`, `strong_pairs`, `weak_capacity`,
    `closure_out_edges`, `closure_disjoint`, `closed_reaches_W`, `closed_classes_le`,
    `Lk2`, `LkJ`, `no_path2`, `degenerate2`, `sum2`, `capJ`, `no_pathJ`, `degenerateJ`,
    `sumJ`, the near-window set `Bw` (`Bw_card`), `a2_count`, `ml_count`, `ll_count`,
    `slot_linear_at20a` (stated at any packing), and the bundles `HubLinkStructure`,
    `HubClassCounts`, `SlotRelation`, `ClosedClasses`, `HubTwoHopLinks`, `SlotLinear`,
    `ScalePressure` with their proofs.
  - `CapacityFreeSide/*` (any active family and capacity presentation):
    `nil_mem_lexSublists`, `lexSublists_head`, `mem_lexSublists_of_sublist`,
    `mem_orderedChordSets`, `portT`, `portConfig`, `pairFamily`,
    `chordObstruction_of_separated` (Lean improvement: every separated open pair is
    clause-(f) blocked), `blockers_empty_of_freeSide`, `pair_of_schedule`,
    `free_structure`, `free_triangular_or_centreShoulder`, `mem_chordObstructions_of_cert`,
    `liftWalk` (with `liftWalk_length`, `liftWalk_support`, `liftWalk_edges`,
    `liftWalk_isPath`), `singleton_chordObstruction`, `exists_openWitness_in_declared`,
    `both_singletons_chordObstruction`, `sAt`, `tauAt`, `card_ports_centred`,
    `card_localBuffer_le`; extended accounting: `singleFamily`, `secondConfig`,
    `double_suppression_forced`, `double_suppression_realized`, `centreIncidence_le`,
    `Lambda_eq`, `configSwap`, `CentreShoulderBlocks`, `TriangularBlocks`,
    `triangularBlocks_of_port`, `centreShoulderBlocks_of_ports`, `extended_coverage`,
    `unblocked_structure`, `portToken`, `extCharge`, `extCharge_of_old` (the extension keeps
    every old charge and clauses (a)–(f)), `extCharge_of_none`, `extCharge_mem_tokens`,
    `extLoad`, `extFree`, `extPartition`, `extFree_eq_empty`, `TriPortAt`, `newLoad`,
    `newLoad_le`, `adjEndpoint_le`; canonical chord sets: `lexSublists_first`,
    `head_filter_map`, `chordOrder`, `chordObstructions_head`, `canonicalBlocker_eq_chord`,
    `capacityCharge_of_singleton_chord`, `separated_charge`, `sep_blockers_kind`;
    `PairCount.card_pairs_le`, `PairCount.card_meeting_pairs_le`.
  - `PairArms/*` (any activation, capacity presentation and the canonical pair-code
    objects): arm A `canonicalBlocker_ne_localBuffer`, `chord_head_of_canonical`,
    `eKind_charge_subtype`, `mem_chordOrder_iff`, `first_of_two`, `mem_portT_iff`,
    `chordObstruction_ports`, `fKind_charge_ordered`, `fKind_charge`, `card_support_ge`,
    `canonical_of_charge`, `canonical_ne_profile`, `FKind`, `pair_classification`,
    `hno_of_separated`, `separated_fKind`, `mem_roleFibre_charge`, `liveRoles`; arm B (G1–G13)
    `obstructionCoordinate_support`, `sparseDeclaredSupport_pair`, `specWitness_of_pairDefect`,
    `specWitness_of_obstructionDefect`, `support_eq_union_of_meet`, `cycle_of_disjoint`,
    `serialOfDisjoint`, `realizability_of_disjoint`, `disjointRoutes_trivial_of_fails`,
    `routes_meet_of_same_centre`, `pairObstructionSeparator_spec_of_eq_some`,
    `pairObstructionEnvelope_conditions`, `mem_route_of_route`, `handoff_structure`,
    `pairDefect_of_spec`, `spec_not_both_obstruction`, `serial_lengths_not_accepted`,
    `realizabilityFails_content`, `realizabilityFails_reversed`,
    `realizabilityFails_reversed_high`, `incrementFails_content`,
    `realizabilityFails_routes_meet`, `select_steiner_cut`, `serialOfPiece`,
    `serial_ends_mem`, `noSerial_of_end_outside`, `realizabilityFails_path_meets`,
    `exists_U_path`, `port_end_degree`.
  - `JointObject.lean` (any `FiniteObject` with the cubic baseline and any window
    packing of order `13`): the bridge (`hubs`, `c4Free`, `noC8`, `properTwoLow`,
    `density`, `cubic_nbr`, `degreeSurplus_eq`, `window_degrees`, `jmin`, `jind`,
    `Hset_card_eq`, `sigma_eq`, `avoid_dyadic`, `tight_of_slack`, `dart_identity`,
    `cycleSeq_walk`, `noPow2`, `seq_meets_windows`, `two_le_boundary`), the packing
    theorems (`hubWindowBudget`, `hubBudget_rs`, `windows_LL_sum`, `offPath_identity`,
    `remainderSlack`, `hanging`, `windowU`, `windowU_rs`, `fewWindows`, `vshape`,
    `remainder_noP13`, `bag_card`, `remainder_path_bound`, `remainder_cycle_bound`,
    `remainder_long_cycle`, `remainder_span_bound`), and the object-level fact bundles
    below with their proofs.
- **Statements** `Graph/Statements/JointHubs.lean`, `Graph/Statements/HubLinks.lean`,
  `Graph/Statements/PairArms.lean`; **contracts** `Graph/Contracts/Spine/JointHubs.lean`,
  `Graph/Contracts/Spine/HubLinks.lean`, `Graph/Contracts/Spine/PairArms.lean` (one `<key>_holds` per key; hypotheses are
  ledger facts only: selection, presentation laws, baseline, `[8]`, `lem:bridgeless`,
  `[10]`, the replacement exclusion, `K .surplusAbove`, `K .ceilSqrtAboveScale`,
  `K .canonicalCapacityExplicit`, and the published `K .highSurplusBound`,
  `K .bigHubBound`); **rows** `Graph/Strategy/SpineRows/JointHubs.lean`
  (`remainderGeometryRow`, `densitySlackRow`, `jointHubRow`, `hubWindowRow`,
  `highSurplusOrderRow`, `windowChargeRow`, `hubLinkRow`, `scalePressureRow`,
  `freeSideStructureRow`, `freeSideCountRow`, `freeSideHubsRow`, `extendedChargeRow`, `portEndDegreeRow`, `pairArmARow`, `pairArmBRow`,
  `pairArmBDefectRow`); wired in `Assembly/Entry.lean` and
  `Assembly/Final.lean`.  Registered corollary (presentation identity, not a key):
  `registered_firstBand_excluded`, `registered_pairDeficitCoefficient_pos`,
  `registered_extOverloadedToken`
  (`Assembly/Surplus/RegisteredConstants.lean`).

`H = {d ≠ 3}`, `L = {d = 3}`, `B = {d ≥ 5}`, `σ = 2m − 3n`, `s = n − σ`, `P₀` the
canonical packing (`ν = |P₀|`), `W`, `R` its support and remainder (`r = |R|`),
`h_W, h_R` the hubs in `W`, `R`, `ε` the hub window ends, `I`, `I_W` the cubic vertices
with no cubic neighbour in their own window, `e×` the cross-window edges, `σ_W` the
surplus in `W`, `slack(S) = 4|S| − 6 − 2e(S)`.

| idx | key | fact at G | inputs (`inputs.get`) | placement |
|---:|---|---|---|---|
| 7200 | `cubicNeighbourSupply` | every cubic vertex has a cubic neighbour and `≤ 2` hub neighbours; `|L| ≤ Σ_{v∈L}|N(v) ∩ L| = 2e(L)` | cubicBaseline, minDegreeBaseline, noProperBaseline | entry, after `[9]`/`[10]` (`jointHubRow`) |
| 7201 | `hubCountBound` | `5|H| + σ ≤ 2n` | + slackIndependent | same row |
| 7202 | `lowEdgeParity` | on every walk `p : u → v`, `#LL(p) + [u∈H] + [v∈H] + |p|` is even; odd walks between cubic vertices use an odd number of `L–L` edges | cubicBaseline, minDegreeBaseline, slackIndependent | same row |
| 7203 | `bigHubBound` | a hub dominates `≤ 2` hub-free components of `G[L]` (`≤ 1` if `d ≥ 5`), each such component is dominated; `2|B| + σ ≤ n` | + noProperBaseline | same row |
| 7204 | `bigHubVShapes` | two big hubs share `≤ 12` V-shape middles; `|X₂| ≤ 12(|B|² − |B|)`; `4σ + 93|B| ≤ 2n + 75|B|² + 4|H|` | selection, cubicBaseline (dyadic law), minDegreeBaseline, slackIndependent | same row |
| 7205 | `highSurplusBound` | `24σ + 465|B| ≤ 18n + 375|B|²`; `8n ≤ 32s + 125s²` at `s = n − σ` | + noProperBaseline | same row |
| 7206 | `hubLengthThreePairs` | at a hub `h` with cubic second neighbourhood: `#len3Pairs(h) ≤ 4d_h`, `d_h(d_h − 2) ≤ #(no length-3 path) + 4d_h` | selection, cubicBaseline, minDegreeBaseline, slackIndependent | same row |
| 7207 | `densityExcess` | proper `S`, `|S| ≥ 2`: `2e(S) + 6 ≤ 4|S|`, i.e. `σ_S ≤ |S| + bd S − 6`; `bd S ≥ 2` for nonempty proper `S`; `S ⊇ N[h]` with other vertices cubic: `d_h + 1 ≤ |S|` and slack `≥ |S| − d_h − 1` | cubicBaseline, noProperBaseline (incl. connectivity), bridgeless | entry, after `[8]` (`densitySlackRow`) |
| 7208 | `remainderSlack` | `slack(R) = s + 2ν + 2σ_W − 2e× − 6`; windows `Ws ⊆ P₀` hanging on `K` (all their outside edges into `K`, `K ∪ ⋃Ws ≠ V`): `Σ_{P∈Ws}(2 + 2σ_P) ≤ slack(K)`; with `R ≠ ∅` and `ν ≥ 1` (window density): `2e× + 6 ≤ 28ν` and `σ_W + 6 ≤ e(R, W) + 13ν` | cubicBaseline (`δ = 3`, census ⇒ order 13), minDegreeBaseline, noProperBaseline | same row |
| 7209 | `hubWindowBudget` | `24ν + 2ε + I + 6|H| + σ ≤ 3n + 4h_W`; `2|H| + 3h_R + 2ε + I_W ≤ 2ν + r + s`; `Σ_P #LL(P) + 4h_W = 24ν + 2ε`; `lowDarts − Σ_P #LL(P) = 2ν + 2r + s − 2|H| − 4h_R − 2ε` | cubicBaseline, minDegreeBaseline, noProperBaseline, slackIndependent | entry, after the cubic/hub facts (`hubWindowRow`) |
| 7210 | `windowHubBounds` | `12ν + 31|B| ≤ 2s + 2|H| + 25|B|²`; `23ν + 31|B| ≤ n + 3s + 25|B|²`; `22ν + 93|B| + 6h_R + 4ε + 2I_W ≤ 6s + 75|B|²` | + selection | same row |
| 7211 | `remainderPathBounds` | `R` has no induced `P13`; hub-free `R`-connected sets have `≤ 6142` vertices; an `R`-path through `k` hubs has `≤ 6143k + 6142` vertices (`≤ 6143h_R + 6142`), and so does an `R`-cycle; an `R`-path with `m ≥ 12` edges closes an `R`-cycle of length `L`, `m + 11 ≤ 11L`; span `≤ s` ⇒ `m ≤ 11s`; circumference `L` ⇒ `m ≤ 11(L − 1)`; `R` is `12`-degenerate | selection, cubicBaseline, minDegreeBaseline | entry, after `P₀`'s rigidity row (`remainderGeometryRow`) |
| 7212 | `windowFreeGeometry` | for window-free `S`: short (`≤ 11`) induced walks; chords of long paths open at a hub (`j − i + 1`, `L − (j − i) + 3` not dyadic) or closed by an outside path; one chord per 13 vertices; the outside-return dichotomy; connected window-free `K`: `|K| ≤ 1 + 2047(3 + σ_K)` (`≤ 1 + 2047d_b` with one hub `b`); the hub-pair dichotomy (bypass of length `k ∈ {3,4,5,7,…,11}` avoiding `W ∪ {h}`, or every walk meets `W ∪ {h}`); the carrier position of a connected set | same | same row |
| 7213 | `inducedPathAttachment` | a vertex off an induced `P13` of G has `≤ 7` neighbours on it; every vertex of an induced `P13` has a neighbour off it | selection, cubicBaseline, minDegreeBaseline | same row |
| 7214 | `highSurplusOrder` | `8n ≤ 32(n − C⌈√n⌉ − 1) + 125(n − C⌈√n⌉ − 1)²`; `n > C² + C + 1 + t` for every `t` with `125t² + 24t < 8(C² + C + 1)` (`C = C_sp`) | cubicBaseline, highSurplusBound, bigHubBound, surplusAbove, ceilSqrtAboveScale | strict arm of `[19]`, after the budget row (`highSurplusOrderRow`) |
| 7215 | `windowChargeKinds` | at G's canonical capacity presentation: every pair charged to `𝔗_W` has a coordinate or chord-set canonical blocker; such pairs are fully separated (supports, returns, buffers); a spread connected coordinate support is window-charged; pairs supported in `R` never are; early (vertex) blockers go to vertex tokens; chord-blocked window charges have adjacent chord ends; same-hub pairs are early-blocked; no profile obstruction | canonicalCapacityExplicit | strict arm, after the canonical capacity row (`windowChargeRow`) |
| 7216 | `responseObstructionTargetDefect` | at G's canonical active family, every target-response obstruction is a residual target defect | canonicalCapacityExplicit, selection (minimality), replacementExclusion | same row |
| 7217 | `hubLinkStructure` | no hub chain of `≥ 13` vertices in `R` (induced segments); no rainbow five-path of bag links and no strong `P5` among the hubs of `R`; the link graph on `S_R = H ∩ R` is `18429`-degenerate (`Σ ≤ 36858 h_R`), the strong link graph `3`-degenerate (`Σ ≤ 6 h_R`); a non-strong pair carries `≤ 3·6142` linked vertices | cubicBaseline (census), minDegreeBaseline, slackIndependent | entry, after the hub–window facts (`hubLinkRow`) |
| 7218 | `hubClassCounts` | `|A₀| + |A₁| + |A₂| = |L|`, `|A₁| + 2|A₂| = 3|H| + σ`, `|A₂| ≤ C(|H|, 2)`, `|A₂| + n = |A₀| + 4|H| + σ`, `|U| ≤ 3|A₀|`; per hub `d_h ≤ (|H| − 1) + |N(h) ∩ U| + |N(h) ∩ (A₁ ∖ U)|`; `Σ_H |N(h) ∩ U| = |U|`; `≤ 2d_c` vertices off `N[c]` see `N(c)` | selection, cubicBaseline, minDegreeBaseline, noProperBaseline, slackIndependent | same row |
| 7219 | `slotRelation` | `|A₁| ≤ 3|A₀| + |A₂| + 2(|H|² − |H|) + 2C(|H|, 2)`; `4σ + 21|H| ≤ 3n + 6|H|²`; `4σ + 18|H| ≤ 3n + 6|A₂| + 3|H|²`; `≤ 2` matched-link and `≤ 2` link-link vertices per hub pair | same | same row |
| 7220 | `closedClasses` | edges leaving the closure of a closed bag-link class of hubs of `R` end in `W`; disjoint classes have disjoint closures; with `ν ≥ 1`, a nonempty class reaches `W`; disjoint nonempty classes number `≤ e(R, W)` | cubicBaseline, minDegreeBaseline, noProperBaseline, slackIndependent | same row |
| 7221 | `hubTwoHopLinks` | no seven hubs of `R` joined by common neighbours (the forbid path), `25`-degenerate, `Σ ≤ 50 h_R`; at every centre `c` the two-hop graph: `≤ 6142` partners per bag, no four-hub path, `12286`-degenerate, `Σ_S ≤ 24572|S|` | cubicBaseline, minDegreeBaseline, slackIndependent | same row |
| 7222 | `slotLinear` | `|B_W| ≤ 13ν + 4e(R, W)`; `|A₂ ∖ B_W| ≤ Σ_{S_R} #Lk2`, `|MLall ∖ B_W| ≤ 2P`, `|LLall ∖ B_W| ≤ 2P + 49144P`; `4σ + 15|H| ≤ 3n + K·h_R + 8|B_W|`; `4σ + 15|H| ≤ 3n + K·h_R + 584ν + 32σ_W` (`K = 1811497284`) | selection, cubicBaseline, minDegreeBaseline, noProperBaseline, slackIndependent | same row |
| 7223 | `scalePressure` | `C_sp⌈√n⌉ + 15|H| < 3s + K·h_R + 584ν + 32σ_W`; `11C_sp⌈√n⌉ + 165|H| + 27156|B| < 1785s + 11K·h_R + 21900|B|² + 352σ_W` | + surplusAbove | strict arm, after the high-surplus orders (`scalePressureRow`) |
| 7224 | `freeSideStructure` | at G's canonical capacity presentation: every free pair is two selected ports with disjoint declared supports, disjoint `T`, disjoint returns, distinct centres, ends off the other's return, no target-response and no chord-set obstruction, and one port triangular or one centre in the other's `T` (`Π_free ⊆ Π_tri ∪ Π_cs`) | selection (minimality), minDegreeBaseline, canonicalCapacityExplicit | strict arm, after `windowChargeRow` (`freeSideStructureRow`) |
| 7225 | `freeSideCount` | `|𝒜₀| = σ`, `s(v) = d(v) − δ`, `|Π_free| ≤ τσ + Λ`; G2 with the count; capped arm `c²K + 2M₀(8n + σ − |𝔗|) ≤ 2(τσ + Λ − B)`; for `Δ ≥ max d`: `|Π_free| ≤ σ(τ + 3(Δ − 3))` and (capped, `K ≥ 0`) `n·K ≤ 2σ(τ + 3(Δ − 3))` | cubicBaseline, freeSideStructure, canonicalLedgerDeficit, canonicalFreeExcessOfCapped | strict arm, after the canonical capacity counts (`freeSideCountRow`) |
| 7226 | `freeSideHubs` | `|Π_free| ≤ σ(τ + |H| − 1)` (a hub lies in `T(q)` for at most `|H| − 1` ports, no `C₄`); capped, `K ≥ 0`: `n·K ≤ 2σ(τ + |H| − 1)` | cubicBaseline (`δ = 3`, `L(4)`), selection, slackIndependent, freeSideCount | strict arm, after `freeSideCountRow` (`freeSideHubsRow`) |
| 7227 | `extFreeEmpty` | `Π_free^ext = ∅`: the extended charge `Θ_ext` (clauses (a)–(f) unchanged, then centre–shoulder and triangular pairs to a port token) charges every scheduled pair | cubicBaseline, selection (minimality), minDegreeBaseline, slackIndependent, canonicalCapacityExplicit, pairCountDeficit, canonicalBlockedFreePartition, ceilSqrtAboveScale | strict arm, after `freeSideHubsRow` (`extendedChargeRow`) |
| 7228 | `extLoadSum` | `C(σ, 2) = Σ_{t∈𝔗} load_ext(t)`, `|𝔗| ≤ 8n + σ` | same | same row |
| 7229 | `extOverload` | `c²K + 2M₀(8n + σ − |𝔗|) + 2B ≤ 2Σ_t (load_ext(t) − M₀)` | same | same row |
| 7230 | `extOverloadedToken` | `K > 0` ⇒ some token has `load_ext > M₀` (unconditional at the registered presentation: `registered_extOverloadedToken`) | same | same row |
| 7231 | `newLoadBound` | `newLoad(p) ≤ (|H| − 1) + [p triangular]·σ` for every selected port | same | same row |
| 7232 | `separatedPairs` | a pair with disjoint declared supports and returns has only (e)/(f) blockers; `C(σ, 2) ≤ Σ_v C(d_D(v), 2) + Σ_v C(d_R(v), 2) + |Sep|` | canonicalCapacityExplicit | strict arm, with `freeSideStructureRow` |
| 7233 | `portEndDegree` | every selected port endpoint has degree `δ` | minDegreeBaseline, slackIndependent | entry, after `hubLinkRow` (`portEndDegreeRow`) |
| 7234 | `pairArmAPattern` | arm A of `pairCodeConfiguration` → the canonical homogeneous pattern covers `≥ |𝓜| + 1` ports, every pair charged to the overload token with a canonical blocker of the role's kind, and exactly one of (a) a common shared declared vertex, (b) a common shared return vertex, (e) target responses with `t ∉ I ∪ P`, (f) fully separated singleton chord blockers (a star at `p₀` with `t = P(p₀)`, or a common shoulder `v` with `t = R(v, k)`) | canonicalCapacityExplicit | strict arm, after `freeSideStructureRow` (`pairArmARow`) |
| 7235 | `pairArmARoleAlphabet` | arm A → the canonical overload role lies in the ten live roles (of 36); `M₀`, `C_sp` unchanged | same | same row |
| 7236 | `pairArmB` | arm B → the overlap system exists and G is in (B1), (B2) or (B3); (B1) the `[182]` residual in three exact configurations; (B3) → separator of degree `> 3`, next vertices in `U`, no label collision, envelope escape, Type B fan entry; realizability failure → forward routes in `U` meet backward routes, and the demand-end split; serial system → ends in `U`, centres high, port ends cubic, no accepted route length, the switch at the left port | cubicBaseline, selection, minDegreeBaseline, noProperBaseline, slackIndependent, surplusAbove, highEndpointSwitch | strict arm, after `highEndpointSwitchRow` (`pairArmBRow`) |
| 7237 | `pairArmBDefect` | (B2) the pinned defect of the canonical return system's obstruction coordinates → a second `Spec` witness `w''` on two distinct obstruction coordinates, `|Z''| ≤ |U|`, with the full witness structure | cubicBaseline, selection, minDegreeBaseline, noProperBaseline, tightEndpoint, returnAvoidance, highEndpointSwitch, sparseTargetDefectResidual, specWitnessStructure | `[20a]` arm, after `sparseTargetDefectStructureRow` (`pairArmBDefectRow`) |

**Re-probe (`PathProbe`, 2026-09-29).**  Path counts unchanged at every return (1 at
`[20a]` and the near-cubic target defect, 6 at `[144a]`, 4/2 at `[172a]`, 6/6 at `[182]`,
1170 each at `[186]`, `[348]` and Type B sublinear, 73/11 at the rate failure, 6/4 at the
cold-terminal exclusion, 9/3 at `[153]`, 4/2 at `[162]`, 7/5 at `[54]`, 1 at each Type B
entry subtype); all 21 entry keys are on every probed fact set.  Fact counts after
(before): `[20a]` 166 (128); near-cubic target defect 126 (105); `[144a]` 134–138
(97–101); `[172a]` 121–122 (100–101); `[182]` 122–137 (85–100); `[186]` 148–187 (127–166);
Type B entry 126/129/135/138 (89/92/98/101); Type B sublinear 131–170 (110–149); `[348]`
133–172 (112–151); rate failure 97–101 (76–80); cold-terminal exclusion 114–116 (93–95);
`[153]` 95–96 (74–75); `[162]` 96–97 (75–76); `[54]` 93–98 (72–77).

**Deduplicated (not published; already on the ledger).**
- `LL_identity` (`2e(L) + 6|H| + σ = 3n`) is literally `K .surplusDartIdentity`
  (`sparseLowDartCount = 2e(L)`); `hub_sum` is part of `K .highDegreePairSum`.
- `nonadjPairs_card_ge` (`d(d − 2)` ordered non-adjacent pairs of `N(h)`) is the sum of
  `K .neighbourhoodPairCount`'s per-vertex `d_h − 2` partners; kept as a library lemma.
- `attach_no_gap_two`, `attach_no_gap_six`, `attach_edge_gap` are the legal-label and
  `C₁` rules of `K .windowAttachmentGap`; `cross_pair_cycle` (scratch `Local.lean`) is
  its `crossGap`, and `hub_C8` is `K .threeRouteFan`; `interior_not_in_window` at the
  windows of `P₀` is implied by `K .windowPositionStubs` (published here for every
  induced `P13`, inside `K .inducedPathAttachment`).
- The join identity `e(R, W) + 2e× = 15ν + σ_W` restated inside the scratch
  `closed_classes_le` and `slot_linear_at20a` is `lem:exact-window-join-identity`
  (`K .sparseUpperEnvelope`); `scale_at20a` restates `K .surplusAbove`,
  `K .ceilSqrtAboveScale` and `n ≤ ⌈√n⌉²`; `hub_mean_at_top` is conditional on
  `σ = n − 8` and stays a library lemma.
- The join identity used by `remainderSlack` is `lem:exact-window-join-identity`
  (library `exact_window_join_identity`, also in `K .sparseUpperEnvelope`).

**Not published.**  The numerical escape/feasibility lemmas of the scratch
(`accumulated_escape`, `escape_with_paths`, `AccSystem`) are not facts about G and are
not ported; likewise `escape_killed` (hub-link) is not ported.  All accounting rounds sent to this lane (1-3) are ported.  Arm A: `LiveCharge.lean` and
`ClauseE.lean` there are copies of the windows sources (deduplicated into
`WindowChargeKinds`); `KindA.lean`, `KindE.lean`, `At20aA.lean` were not in the port list.
Arm B: `Linkage.lean` (a statement about `C₄`, not about G) is not ported.  Scratch `Moore.lean` (girth bound) and `Local.lean` are not needed by any
published fact (`Local.lean` duplicates `LocalRigidity`).  The capped-arm lemmas
`capped_single_hub_closed` and `capped_hub_lower` are ported as library arithmetic only:
their G-instantiation needs, respectively, `|Π_free| = 0` from `|H| = 1` and
`Σ_h C(e_h, 2) ≤ M₀(n + σ_R)`, i.e. the link between the canonical capacity's
`freeSide` (its `Eligible` order) and the canonical blocker, and the vertex-token loads
of the early charge; that link is not constructed in this lane.  `remainder_budget` is ported as a library lemma only: its
per-component density hypothesis `σ_K + 6 ≤ |K| + bd K` fails at a singleton component
`K = {v}` of `G[R]` (`σ_K + 6 = d_v + 3 > d_v + 1 = |K| + bd K`, i.e. `slack({v}) = −2`),
so it does not instantiate at G as stated; `window_density` is published (in
`K .remainderSlack`).


- **port-joint count note (2026-09-28).**  Every returned residual (generic, subtype, product) now also carries the 21 entry-prefix keys of "Hubs, windows and the remainder at G" (`K .remainderPathBounds`, `K .windowFreeGeometry`, `K .inducedPathAttachment`, `K .densityExcess`, `K .remainderSlack`, `K .cubicNeighbourSupply`, `K .hubCountBound`, `K .lowEdgeParity`, `K .bigHubBound`, `K .bigHubVShapes`, `K .highSurplusBound`, `K .hubLengthThreePairs`, `K .hubWindowBudget`, `K .windowHubBounds`, `K .hubLinkStructure`, `K .hubClassCounts`, `K .slotRelation`, `K .closedClasses`, `K .hubTwoHopLinks`, `K .slotLinear`, `K .portEndDegree`; +21), and every strict-surplus residual (`[20a]`, `[144a]`, `[182]`, the `[187]` Type B entry) also the 16 strict-arm keys `K .highSurplusOrder`, `K .scalePressure`, `K .windowChargeKinds`, `K .responseObstructionTargetDefect`, `K .freeSideStructure`, `K .separatedPairs`, `K .freeSideCount`, `K .freeSideHubs`, `K .extFreeEmpty`, `K .extLoadSum`, `K .extOverload`, `K .extOverloadedToken`, `K .newLoadBound`, `K .pairArmAPattern`, `K .pairArmARoleAlphabet`, `K .pairArmB` (+37 in all), and `[20a]` also `K .pairArmBDefect` (+38); one `get` per key at every return.  Counts quoted below that predate this note are +21 (+37 on the strict arm, +38 at `[20a]`).
