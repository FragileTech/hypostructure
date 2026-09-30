# Structural accounting: `Node54ResidualOutcome`

> Status (2026-09-30): **Current.** The Lean ledger equals this report's fact list with its second-pass addendum: generic `Node54ResidualOutcome` 92 facts (90 in Table 2 + `stubDeficitIdentity`, `remainderCycleSpectrum`, keys 8550-8551), and the 14 subtype extras of rows 91-104 (subtypes +3/+6/+7/+8/+3). None of today's keys is on this residual. Checked by comparing the keys of this report (Table 2 rows and addenda) with the `Holds` conjuncts of the Lean abbrevs in `Assembly/Residuals.lean` and `Assembly/Residuals/`; the accounting itself was not re-run.

Residual: `Node54ResidualOutcome` (node [54], prop:entropy-high-theta, tex 9921), `Assembly/Residuals.lean` line 5119, with its five subtypes in `Assembly/Residuals/Node54ResidualOutcome.lean`. Worktree `/home/guillem/hs-wt-S54`, branch `g-audit-54`. Read-only: no Lean edited, no build.

## Header

**Defining failure (generic).** At G's fixed maximum packing P0 = `canonicalWindowPacking` (p = |P0|) and its remainder R0 = R(P0), the joint realization inequality RS(R0) * 2^{rate*s*p} * 2^F <= B fails, where B = `skeletonBudget` = C(C(n,2), m) is the number of labelled graphs with G's order and size, RS(R0) = `remainderStates` counts labelled graphs on V(R0) with G's def+(R0), e(R0), |R0|, and F = `forcedObstructionBits` (bounded by c_Omega * r_Omega(R0), r_Omega(R0) = W2(R0) by `curvatureFullRank`). Exactly: `entropyCapActive` gives B < jointPackageDemand * 2^F, and `allColdEntropyResidual` adds `not WindowFamilyRealized P0`, RS*room <= B, room < 2^{rate*s*p} * 2^F, and `not EntropyJointRealization`.

**Defining failure per subtype** (each subtype is the generic residual plus extra facts, all evaluated at the same P0, R0):

- `realizedColdBelow` (3 extras): window package realized (2^{b_P p} <= B) and theta < 1/78 in the exact cold-route-8 form, with the private-carrier rate reading. No size test.
- `realizedBounded` (6 extras): package realized, theta >= 1/78, cold mass bounded, [24]'s density cap, the combined density-order bound, and the size test n < N0 (N0 = 2^235 per register).
- `unrealizedTauHighBounded` (7 extras): package not realized (B < 2^{b_P p}), tau(theta) >= 1/4, theta >= 1/78, cold mass bounded, density cap, combined bound, n < N0.
- `unrealizedRateFailsBounded` (8 extras in the Lean abbrev; its docstring says 6): package not realized, tau < 1/4, private-carrier rate fails, theta >= 1/78, cold mass bounded, density cap, combined bound, n < N0.
- `unrealizedBothRates` (3 extras): package not realized, tau < 1/4, private-carrier rate holds. No size test.

**Fact count.** The generic abbrev `Node54ResidualOutcome` is a conjunction of **90** `Holds` conjuncts (counted by the template script and by reading the abbrev). The task, the Lean docstring header of `Node54ResidualOutcome.lean` and the register all say 64 (docstring of the abbrev says 52); these counts are stale: the abbrev has absorbed the hoisted entry-prefix facts, the cycle-counting, port-local and port-joint facts. All 90 are marked. Extra facts: 14 distinct keys over the five subtypes (91-104 below). Subtype fact totals in Lean: 93, 96, 97, 98, 93.

**Status counts, Table 1 (88 coordinates, generic residual):** x = 37, ~ = 40, gap = 3, n/a = 5, nonG = 3 (total 88).

**Facts by G-status, Table 2 (90 generic + 14 extra = 104 rows):** fully about G: see Table 2 column; nonG facts (whole fact): 11, 12, 15, 67; facts with a nonG clause: 1, 2, 69, 90, 96. Details in section 5.

**Marking conventions used (state once).**

1. `x` requires the fact to be about G, quantitative where the observable is a quantity, and the coordinate to enter (with the other currencies) an inequality of the failing chain: the joint realization inequality, the window-cut/deficiency chain feeding F, the cold-mass/density chain, or, in a subtype, its extra tests. Facts that are proved and quantitative but only sit beside that chain (hub structure, cycle counting, switch families) give `~` with the missing combination named.
2. Mixed facts are split by clause: the G clauses earn marks, the non-G clause is reported as `nonG` and earns none.
3. `Consumed by` is statement-level: the other facts whose statements share the same canonical object or currency in one inequality, or `unconsumed` when no other statement of the residual reads it. It is not a trace of the proof dependencies of the contracts.
4. Table 1 is for the generic residual. Coordinates touched only by subtype extras (I04, D10, and the G08/G09/H03 refinements) are `~` in Table 1 (certified on a sub-object) and are refined in section 4b.
5. `windowPackageBits` is a function of the registered table and n only, and the rate is data, so the package side of the inequality is a function of (n, p) at G; only p, |R0|, e(R0), def+(R0), r_Omega(R0), sigma and m come from G's structure.

## Table 1: structural coordinates (generic residual)

Status legend: `x` accounted, `~` partially accounted, `gap` present at G but unaccounted, `n/a` absent at G (reason), `nonG` only non-G facts touch it. Accounting facts cite Table 2 numbers; numbers >= 91 are the subtype extras of Table 2b.

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 17, 27, 36, 56, 58, 60 ; subtype: 97, 98, 101, 102 | bound (n enters B, /R0/ = n-13p, n^{/R0/}, T(n)) | T01,T12 | order of the 13-window regime: see G08/I04 |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 36, 90 | bound + identity (m enters B = C(C(n,2),m) and room) | T01,T12 | - |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | ~ | 29, 32, 34, 43, 44, 47, 53, 54, 55, 56, 58, 59, 62, 63 | bound/identity on hubs H, big hubs B, classes A_j | T01,T15 | hub and class counts (5/H/+sigma<=2n, slot relations) are proved but never enter the joint-realization inequality; only sigma enters, through T(n) (65) |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | ~ | 3, 55 | bound (delta=3 enters every inequality) | T01 | only the minimum degree is used quantitatively; the maximum degree is bounded only through hub counts (32,43,55) that do not enter the failing inequality |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 27, 32, 43, 44, 47, 56, 58, 59, 60, 62, 63, 65, 66, 74 ; subtype: 95 | identity + bound (sigma<=T(n); dart identity; /H/<=sigma; cold loss charged to sigma) | T01,T13 | - |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | ~ | 6, 42, 46, 58 | bound/exclusion (hubs independent; link degeneracy; two-hop links) | T15,T17 | hub adjacency/distance data is certified inside R0 but not combined with the entropy inequality or with F |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | x | 5, 78, 81 | exclusion (G is its own 3-core; R0 has no baseline subgraph, so every subregion is peelable) | T04,T19 | degeneracy number / explicit peel order not stated (see E08) |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | excluded by: 3 | - | - | no degree-two vertices in G: excluded by minDegreeBaseline (3) |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 81, 83 | identity + bound (W2(R0) counted; delta/X/ <= W2(X)+2def+(X)) | T01,T11 | - |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 25, 26, 79 ; subtype: 92, 93, 94, 104 | bound (e(R0,W) <= 15p + sigma_W; def+ <= e) | T01,T14 | - |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 25, 79, 80, 81, 86 ; subtype: 100, 103 | bound (def+(R0) <= e(R0,W); def+ + 2(order-1)p <= delta*order*p + T(n)) | T01,T13 | - |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | bound (2 beta >= n+2) | T01 | beta enters no inequality with the entropy budget; missing: relation of m-n+1 to B's range and to #cycles (see C07) |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 51, 52 | bound (proper sets: int(S)+6<=4/S/; slack(R0) identity; window density) | T01,T13 | - |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 3, 6, 7, 32, 63, 65 | bound (delta=3, independent high vertices, /H/<=sigma<=T(n), sparse survivor) | T01,T13 | - |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | ~ | 5, 33, 45, 48 | bound/classification (G connected; components of R0 minus hubs <= 6142; closed classes) | T04 | component structure of R0 is bounded but RS(R0) is a count that depends only on /R0/, e(R0), def+(R0), not on components |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | ~ | 24, 51 | exclusion + bound (G bridgeless; >=2 edges leave every proper set) | T04,T08 | edge connectivity beyond 2 and bond structure are not measured; not combined with the entropy budget |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | ~ | 28, 33, 35 | classification (2+2 cut vertices; blocks at cut vertices) | T04 | only local shapes at a single cut vertex; no block-cut tree of G or R0 with counts |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 19 | witness (forced paths after 2-edge deletion; 3-route fan) | T08 | disjoint-path counts between terminals are not quantified (Menger-type bound) |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 26, 28, 39, 41, 76 | bound + identity (e(R0,W); positions d-2/d-1 external; port ends degree delta; exactly 15 stubs per cubic cold window) | T05,T07 | - |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | ~ | 9, 39 | exclusion (boundary-degree fibres) and ordered window placements | T05 | boundaried type of R0 (ordered terminals with degree/incidence) is not stated; RS(R0) uses only (def+, e, /R0/) |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | ~ | 9, 10, 16 | identity + exclusion (G-only restatement: no reading of G separates in G-Z) | T05 | the G-only form is trivially satisfied by construction (10); the response equivalence that r_Omega actually uses is the quotient system of 82, not measured against an explicit G-constructed context (the swap of G at Z) |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | ~ | 16, 23 | identity + exclusion (witness support minimal connected; no clause-(b) witness) | T10 | witnesses are excluded at G, so the locality of a witness is certified only vacuously |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 25, 26, 79, 80, 86 ; subtype: 93, 104 | bound (def+(R0) <= e(R0,W) <= supply; c_Omega chain) | T14,T13 | - |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | ~ | 19, 20, 22, 35, 37, 48, 49, 57, 61 | witness/classification (forced paths; window-free induced walks <= 11; path bounds in R0) | T08 | no quantitative attainable-length set for G or R0 |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | ~ | 4, 24, 35 | exclusion (return lengths avoid shifted accepted set; every edge has a return) | T08 | return-length sets are not measured quantitatively at R0 or its boundary |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | ~ | 1, 4, 18, 21, 30, 31, 34, 36 | exclusion + counts (no accepted-length cycle; star/meeting constraints; #cycles(h) bounds) | T08,T09 | no lower bound on the number/spectrum of cycle lengths of G that interacts with n or B; this is the coordinate a small-order closure would need (see gaps) |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | ~ | 2, 22, 35, 57 | exclusion (dyadic law; residues mod 4; parity of L-L edges) | T09 | arithmetic classes are certified locally (cut vertices, L-L parity) and not combined with n |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | ~ | 20, 30, 31, 37 | exclusion (star, meeting, fan) | T08 | theta structure certified only around a single vertex |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | gap | - (structure shown by 5, 24) | - | T04,T08 | G is connected and bridgeless (5,24), so an open ear decomposition exists; no fact measures ear number/lengths (missing observable: ear lengths of G and of the 2-edge-connected pieces of R0; certificate: decomposition with counts) |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | ~ | 36 | bound (#cycles(G) <= 2^m; double count) | T08,T11 | cycle space dimension (8) and cycle counts (34,36) are separate; no symmetric-difference structure |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 2, 13, 48, 49, 50, 78 | exclusion (window present in G; R0 window-free; P13 attachment <= 7; hereditary closure) | T06,T07 | - |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 13, 14, 17, 26, 47, 52, 53, 54, 68, 70, 88 ; subtype: 91, 99 | bound (p = /P0/, 13p<=n, hub-window budget, window-hub bounds, demand 2^{rate*scales*p}) | T06,T12 | - |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 48, 49, 52, 78 | exclusion + bound (R0 window-free, baseline-free, slack, path bounds) | T06,T04 | - |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | 77 | identity (stubs of cold corridors charged once) | T07 | serial corridor lengths and path increments of the cold corridors are not measured |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 26, 39, 40, 41, 50, 76 | identity + bound (external stubs per window position, attachment gap, ports) | T07 | - |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | ~ | 20, 38, 40 | witness/exclusion (cross-switch, chain 3,3,3, cross-edge gap) | T07,T08 | joint disjointness/simplicity is certified only for small path patterns |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 13, 39, 40, 50, 68, 76 | identity + classification (attachment of outside vertices to windows, legal labels, <=7 contacts, package coordinates) | T07 | - |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | ~ | 39, 40 | classification (window placements; legal labels of outside vertices) | T07,T16 | local types of R0 (radius-two rooted types) are not stated on this ledger; RS(R0) is aggregated |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | ~ | 21, 22, 28, 29, 30, 37, 38, 42, 46, 55, 59, 61 | classification/bound (neighbourhood pairs, fans, hub links) | T07 | none of the neighbourhood counts enters the joint-realization inequality |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | ~ | 29 | bound (G[N(h)] a matching) | T14 | the auxiliary demand/resource incidence graph is not constructed |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 14, 40, 45, 68, 70, 77 ; subtype: 95 | decomposition (P0 disjoint windows, disjoint package coordinates, stubs charged once) | T06,T10 | - |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 23 | identity (minimum connected support of witnesses; closed classes) | T10 | no minimal connected overlap obstruction for the package/remainder glue |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | ~ | 64, 83 | exclusion (label-injective quotients; distinct labelled entries) | T16 | no automorphism/equal-response classification of G or R0 |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 45, 70, 84 | decomposition (canonical P0, hot/cold, surviving family, closed classes) | T16 | hot family is chosen by Classical.choose of a maximal WindowFamilyRealized family (70): canonical only up to that choice |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | ~ | 90 | identity + bound (room identity; RS*room <= B) | T03,T12 | uniqueness of the reconstructed boundaried pieces is not certified; the bound counts glue, it does not inject |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | ~ | - ; subtype: 98, 102 | bound (n < N0 in the bounded subtypes) | T17 | only the bounded subtypes (98,102) bound n, and only by the cutoff; no classification of G as a bounded configuration |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | nonG | nonG: 1 | - | T02 | minimality is stated over strictly smaller graphs (1); G-constructed replacement: minimality restricted to G's own proper subgraphs (5) and to the graphs obtained from G by its own edge deletion/suppression |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 2, 5, 78 | exclusion (no proper subgraph with baseline; R0 subregions; induced subgraphs of G) | T02,T04 | - |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | ~ | 19, 20, 22, 33 | witness (deleting two edges forces a path; vertex deletion components) | T03 | effect of deleting each edge/vertex is certified only for switch patterns |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | ~ | 18 | exclusion (suppression cycles avoid accepted lifted length) | T03 | suppression invariance certified only for open-port suppression |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | nonG | nonG: 11, 12 | - | T03,T18 | facts 11 and 12 exclude a replacement X' that is not a part of G; G-constructed replacement: the swap of G at Z (canonical degree deficit at the boundary of Z), stated on G and G-Z only |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 64, 82 | exclusion (no identification across fibres; label-injective admissible quotients; r_Omega defined by surviving quotients) | T11,T16 | - |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | nonG | nonG: 1 | - | T16 | refinedMinimal tie-break quantifies over smaller graphs (1); G-constructed replacement: the canonical order on G's own equal-size decompositions (P0 choice) |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 78, 81 | exclusion (R0 has no baseline subgraph, hence every subregion has a vertex of degree <= 2) | T19 | no explicit peel sequence and no well-founded measure with a preserved invariant is stated |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | ~ | 1, 10, 16, 23, 66 | exclusion (G avoids the target; no witness of clause (b); sparse exits excluded) | T09,T10 | target defect of G's readings is excluded but no coordinate of it enters the failing inequality |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 81, 82, 83, 85 | identity (W2(R0) tests, exact labelled profile) | T11 | - |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | x | 82, 85, 86, 90 | identity + bound (r_Omega(R0) attained and maximum; = W2) | T11 | - |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | n/a | excluded by: 85 (with 82) | - | T11 | no proper dependence circuit among R0's tests: r_Omega = W2 (85) with attainment (82) gives full survival, so the circuit branch of 84 is empty |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | n/a | excluded by: 85 | - | T11 | no dependence relation at R0 (85), hence no support of dependence |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 68 | decomposition (disjoint package coordinates per window; family card = bits*p) | T10,T12 | - |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | n/a | excluded by: 85 | - | T11 | no dependence relation at R0 (85), hence no cancellation structure |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 84, 85 | classification (full-rank branch: r_Omega = W2) | T11 | - |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 35 | classification (residues at cut vertices) | T09 | periodic response families are certified only at cut vertices; no response family of R0 |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 69, 71, 87, 88, 89, 90 ; subtype: 91, 99 | identity + bound (/Skeleton(n,m)/ = C(C(n,2),m) proved; RS(R0) >= n^{/R0//d}; demand vs B) | T12 | - |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | ~ | 40, 68 ; nonG (no mark): 15, 67 | identity/bound (bits per window >= rate*scales; legal labels of outside vertices) | T12,T17 | the count of legal local states is a registered constant (nonG 15, 67); G-side count of attained states per window is not measured |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 86, 87, 89 | bound (F = forced obstruction bits <= c_Omega r_Omega; eta(R0) >= (1/d) log n) | T12 | - |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | ~ | 87 | bound (aggregate entropy rate of R0) | T12 | largest fibre of the local-type partition of R0 is not exhibited; 87 gives only the aggregate rate |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | x | 88, 89, 90 | bound (window package times remainder states times 2^F versus B) | T12 | - |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | ~ | 64, 68 ; nonG (no mark): 69, 90, 96 | exclusion (label-injective admissible quotients and package coordinates) | T15,T16 | the reconstruction map states -> labelled graphs is present only as the abstract `stateOf` (nonG 69, 90, 96); missing: an explicit map built from G |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 36, 43, 74, 75, 77 ; subtype: 95 | identity + bound (cycle double count; cold loss charged to sigma; stubs charged once) | T15 | - |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | ~ | 2, 65, 72, 73, 80 ; subtype: 96, 97, 98, 101, 102 | bound (T(n) explicit in 65,72,73,80; exact scale count; net-cap slack) | T01,T17 | in the generic residual no fact places n relative to the cutoffs; the bounded subtypes add n < N0 (97,98,101,102) |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 14, 17, 26, 47, 54, 71, 72, 73 ; subtype: 92, 94, 96, 97, 100, 101, 103, 104 | bound (13p<=n, window-hub bounds, cap 2^{rate*scales*/hot/}<=B, cold cap) | T12,T13 | - |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 25, 62, 79, 80, 81, 86 ; subtype: 92, 93, 94, 100, 103, 104 | identity + bound (def+ <= e; dart identity; wedge lower bound; forced cost) | T01,T13 | - |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | x | 81 | bound (delta/X/ <= W2(X)+2def+(X) for every region of R0) | T13 | - |
| H03 | Connected negative support | A connected region with negative charge. | ~ | 52 | bound (proper sets have positive slack; slack(R0) identity) | T13 | no connected negative-charge support is exhibited or excluded for the net-charge of R0 (dense-deficiency comparison appears only in the subtypes 100,103) |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | ~ | 53, 54 | bound/identity (hub-window budget, window-hub bounds) | T13,T14 | transfer rules from suppliers (stubs) to deficits are not stated as a discharge with feasibility check |
| H05 | Load and saturation | Load compared with certified capacity. | x | 26, 71, 72, 79, 80, 86, 89 ; subtype: 93, 96, 104 | bound (window cut capacity vs demand; demand vs skeleton budget) | T13,T14 | - |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | x | 27, 44, 47, 53, 62, 77 | identity (dart identity, slot relations, stubs charged once) | T15 | - |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | ~ | 25, 26, 79 | bound (cut capacity of e(R0,W)) | T14 | no integral flow/matching from def+(R0) into window stubs; missing: internal excess identity e(R0,W) = sigma_R + def+(R0) - exc(R0) |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 65, 73, 74, 75 ; subtype: 92, 93, 95, 103 | bound (sigma<=T(n); cold mass; overlap-bound slack) | T13 | - |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 71, 86, 88, 89, 90 ; subtype: 91, 96, 99 | bound (window package vs remainder states vs forced bits vs B; hot cap) | T12,T13 | - |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | gap | - (structure shown by 14, 68, 88) | - | T19 | the packing P0 is finite and each window is a 13-vertex unit, so a one-window peel of p exists; no fact states the descent (measure p or /R0/, peel step, preserved deficiency/entropy invariant) |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting / reason |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 69 | identity (Skeleton(n,m) is a finite type of cardinality C(C(n,2),m), proved) | T17 | - |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | gap | - (G in Skeleton(n,m), 69) | - | T16 | G's isomorphism class inside Skeleton(n,m) has a canonical orbit (n!//Aut G/ labelled copies); no fact gives a canonical representative or the orbit count (missing: canonical labelling of G and orbit size) |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 89, 90 ; subtype: 91, 99 | identity (strict integer collision B < joint * 2^F; room < 2^{..}2^F) | T17 | - |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | ~ | - ; subtype: 97, 98, 101, 102 | bound (n < N0 on bounded subtypes) | T17 | only 98 and 102, only as n < N0; no exact small-order enumeration or exclusion |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | ~ | 68 ; nonG (no mark): 15, 67 | bound (rate*scales <= bits from the certified table) | T17 | the certificate itself (barrier table, label census) is data (nonG 15, 67); G-side use only via 68 |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | n/a | excluded by: all 104 statements | - | T18 | no Holds statement of the 104 takes an imported theorem as hypothesis (checked: every statement is a Lean-proved proposition about `object` or `data`) |

## Table 2: facts of the generic residual (90) mapped to coordinates

Columns: statement at G in one line; whether it is about G only; coordinates accounted (register codes; `nonG:` lists coordinates touched only through non-G content, which earn no mark); certificate type; what consumes it (statement-level, see convention 3).

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted (dyadic) length; every strictly smaller baseline object has one (sizeMinimal, refinedMinimal). | partly: clause 1 is G; clause 2 quantifies over `smaller : FiniteObject` (other graphs) | C03, E09; nonG: E01, E07 | exclusion (G clause); classification over other graphs (nonG clause) | unconsumed in [54]'s statements; standing hypothesis |
| 2 | `cubicBaseline` | 221 | Presentation laws: delta=3, s=4, 2 not accepted, rate = barrier-table rate; quadrilateral accepted; accepted lengths = dyadic; Type B and surplus presentation slacks (parameter-only); at G: window-free min-degree-3 G and each induced subgraph has an accepted cycle, scale count = log2 n, net-cap slack, label semantics. | partly: components 1-3 are Parameters-only (bookkeeping); component 4 is stated at G and its induced subgraphs | C04, C08, E02, G08 | identity (parameters); exclusion/bound at G (hereditary window-free closure) | 31,36 (delta, s), 68 (rate), 80 |
| 3 | `minDegreeBaseline` | 2850 | Every vertex of G has degree >= delta. | yes | A04, A14 | bound | 81,80,79,26,62,55 |
| 4 | `returnAvoidance` | 1 | At every oriented edge of G the return-length set is disjoint from the shifted accepted set. | yes | C02, C03 | exclusion | unconsumed in [54]'s statements (spine standing invariant) |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has min degree >= delta; G is connected. | yes | A07, B01, E02 | exclusion | 78, 81, 51 |
| 6 | `slackIndependent` | 4 | Vertices of degree > delta are pairwise nonadjacent in G. | yes | A06, A14 | classification | 42,43,46,56,58,63 |
| 7 | `tightEndpoint` | 3 | Every oriented edge of G has an endpoint of degree exactly delta. | yes | A14 | classification | 62,63,6 |
| 8 | `cycleRankConstraint` | 425 | n + 2 <= 2(m + 1 - n): cycle rank beta(G) >= n/2 + 1. | yes | A12 | bound | unconsumed (no partner in the failing inequality) |
| 9 | `degreeProfileFibres` | 2300 | For every region X, admissible rank quotient and two readings of G at its support Z with different boundary-degree profiles: the quotient does not identify them. | yes (readings of G at Z) | B06, B07, E06 | exclusion | 10,82,85 (admissible quotients define r_Omega) |
| 10 | `targetCompleteContextUniversality` | 2301 | Identified readings of G have equal profile and equal power-of-two-cycle response in G's own rest G-Z; and no reading of G at any support closes an accepted cycle in G-Z. | yes (G-only restatement; no outside context) | B07, E06, E09 | identity + exclusion | 9,82,85 |
| 11 | `replacementExclusion` | 223 | No proper support Z of G admits a replacement X' (a boundary-degree-preserving piece with glue X' (G-Z) baseline, smaller than G, no power-of-two cycle). | no: X' is a boundaried piece that is not part of G (witness on another graph, universally excluded) | -nonG: E05 | exclusion (over other pieces) | unconsumed |
| 12 | `uncompressible` | 5 | No proper support Z of G has a strictly smaller target-complete representative X' in G-Z (CompressibleSupport). | no: X' is a smaller representative, not part of G | -nonG: E05 | exclusion (over other pieces) | unconsumed |
| 13 | `windowPresent` | 608 | G contains an induced path on 13 vertices (window). | yes | C08, C09, D01 | witness | 14,68 |
| 14 | `maximalPacking` | 6 | Canonical packing P0 is a maximum, maximal family of disjoint induced windows and is nonempty. | yes | C09, C10, D05, D08, G09 | decomposition | 17,25,26,28,47,53,54,68,70,79-90 (all P0 facts) |
| 15 | `localAlgebra` | 7 | Legal-label census /Labels(13)/ = 399 and size distribution [13,60,122,122,63,17,2] of the window label alphabet. | no: statement about the label alphabet only; the object argument is unused (`_object`) | -nonG: G02, I05 | identity (alphabet census) | 68 (alphabet of package coordinates) |
| 16 | `everyWitnessSpectrumSplit` | 6702 | For every clause-(b) witness triple w of G and X in its pair supports: reading X glued into G-Z has no accepted cycle. | yes (G-only restatement) | B07, B08, E09 | exclusion | 23 |
| 17 | `packingOrderBound` | 6611 | 13 * /P0/ <= n. | yes | A01, C09, G09 | bound | 26,47,53,54,88 |
| 18 | `noSuppressionChordViolation` | 6620 | No open-port suppression cycle of the suppressed graph of G has accepted lifted length walk + used chords. | yes (suppression of G) | C03, E04 | exclusion | unconsumed |
| 19 | `twoSwitchForcedPath` | 6800 | Two-edge switch of G: for u1v1,u2v2 distinct, u1 !~ u2, deg v1,v2 >= delta+1, G-{u1v1,u2v2} has a simple u1-u2 path p with /p/+1 accepted. | yes | B04, C01, E03 | witness | 20,22 |
| 20 | `crossSwitchFamily` | 6802 | Cross switch family: forced u1->u path in G-{u1v,uh'} with accepted closing length; two 2^j-1 paths into distinct neighbours of h' are never h'-free and internally disjoint. | yes | C01, C05, C13, E03 | witness + exclusion | 19,37,38 |
| 21 | `highCentreSplitForced` | 6801 | At every h with deg h > delta, G plus the anti-pairs of N(h) has an accepted cycle avoiding h through an added edge. | yes (G modified by its own anti-pairs) | C03, D03 | witness | 22,29 |
| 22 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch: for nonadjacent neighbours u1,u2 of h with deg h >= delta+2, G-{hu1,hu2} has a path p with /p/+1 accepted, and either p avoids h with /p/+2 not accepted, or splits at h with neither l_i+1 accepted. | yes | C01, C04, D03, E03 | witness + exclusion | 19,21,35 |
| 23 | `specWitnessStructure` | 6677 | At every witness triple whose Z is the canonical support: Z connected, contains A and B, is a minimum connected superset, and w does not satisfy Spec. | yes (G-only restatement) | B08, D06, E09 | identity + exclusion | 16 |
| 24 | `bridgeless` | 226 | Every oriented edge of G has a simple return after its deletion (bridgeless). | yes | B02, C02 | exclusion | 51,35,33 |
| 25 | `remainderDeficiencyBelowCut` | 6663 | def+(R0) <= e(R0,W). | yes | A10, A11, B09, H01, H07 | bound | 79,80,81,86 |
| 26 | `windowCutCapacity` | 6664 | e(R0,W) + 2(order-1)p <= delta*order*p + sigma_W. | yes | A10, B05, B09, C09, C12, G09, H05, H07 | bound | 79,80,86,39 |
| 27 | `primitiveCarrierCount` | 6666 | /U_sp(G)/ = 4n + 2 sigma (primitive carrier count). | yes | A01, A05, H06 | identity | unconsumed in [54]'s statements (route-8 census) |
| 28 | `singleBoundaryShape` | 6627 | Every support S with a single boundary vertex b, a second vertex and an outside vertex has b with exactly 2 neighbours in S and 2 outside. | yes | B03, B05, D03 | classification | unconsumed |
| 29 | `neighbourhoodPairCount` | 6900 | For every vertex h: G[N(h)] is a matching, at least C(d,2)-floor(d/2) nonadjacent pairs, each x in N(h) has >= d-2 nonadjacent partners. | yes | A03, D03, D04 | bound | 30,31,21 |
| 30 | `starCycleConstraint` | 6901 | Star constraint: for every h, distinct neighbours y,z and paths P:x->y, Q:x->z of G-h meeting only at x: /P/+/Q/+2 != 2^k. | yes | C03, C05, D03 | exclusion | 31,37 |
| 31 | `meetingCycleConstraint` | 6902 | Meeting constraint: paths P:x->y, Q:x->z of G-h meeting at t: /P/+/Q/+2 != 2^k + /P1/+/Q1/. | yes | C03, C05 | exclusion | 30,37 |
| 32 | `highDegreePairSum` | 6903 | Pair sums at H = {d != delta}: sigma = sum_H(d-3), 5 sigma <= sum C(d,2), sigma^2+5 sigma/H/+6/H/^2 <= 2/H/ sum C(d,2), 2 sum C(d,2) <= 16 sigma^2, sigma = 0 or some h has sigma <= /H/(d_h-3). | yes | A03, A05, A14 | bound + identity | 43,56,60,62,63 |
| 33 | `vertexDeletionComponents` | 6904 | For every h: G-h is connected, or d_h = 2 #blocks and each component of G-h meeting N(h) holds exactly 2 neighbours. | yes | B01, B03, E03 | classification | 34,35 |
| 34 | `cyclesThroughVertex` | 6905 | C(d_h,2) <= #cycles(h) when G-h connected; else 2 #pairs(h) = d_h and d_h/2 <= #cycles(h). | yes | A03, C03 | bound | 36 |
| 35 | `cutVertexBlockPaths` | 6906 | Block paths at cut vertices: block {a,b}; a->b paths of G-h have /r/+2 != 2^k; returns of ha end by bh; residues 3 and 1 mod 4 at length 2^j-1. | yes | B03, C01, C02, C04, F08 | classification + exclusion | 33 |
| 36 | `cycleDoubleCount` | 6907 | 2 sum_H #cycles(h) <= n #cycles(G); 2 sum_H L_h <= n #cycles(G); #cycles(G) <= 2^m. | yes | A01, A02, C03, C07, G07 | bound | 34 |
| 37 | `threeRouteFan` | 7100 | Length-3 fan at every vertex: paths a p1 p2 b, a q1 q2 c of G-h force p1 = q1, p2 != q2, p2 != c, q2 != b. | yes | C01, C05, D03 | classification | 38,20 |
| 38 | `threeRouteChain` | 7101 | Chain 3,3,3 at every vertex: r1 = p2 and r2 = q1. | yes | C13, D03 | classification | 37 |
| 39 | `windowPositionStubs` | 7102 | Every window of P0 has a placement; interior vertex carries d-2 external neighbours (1 if cubic), end vertex d-1. | yes | B05, B06, C12, D01, D02 | identity | 26,76 |
| 40 | `windowAttachmentGap` | 7103 | Cross-edge gap: /i-i'/+2+/j-j'/ not accepted; at every placed window: outside vertices carry legal labels, adjacent outside vertices C1-safe labels, two windows obey the gap rule, no ladder. | yes | C12, C13, D01, D02, D05, G02 | exclusion + classification | 39,68 |
| 41 | `portEndDegree` | 7233 | Every selected port endpoint of G has degree delta. | yes | B05, C12 | identity | 62 |
| 42 | `hubLinkStructure` | 7217 | Link structure of the hubs of R0 at P0: no long hub chain, no rainbow 5-path, link degeneracy <= 18429, strong <= 3, sums <= 36858 h_R, 6 h_R, weak link capacity 3*6142. | yes | A06, D03 | bound + exclusion | 45,46,47 |
| 43 | `hubClassCounts` | 7218 | Hub classes of cubic vertices: /A0/+/A1/+/A2/ = /L/, /A1/+2/A2/ = 3/H/+sigma, /A2/ <= C(/H/,2), /A2/+n = /A0/+4/H/+sigma, /U/ <= 3/A0/, d_h bounds. | yes | A03, A05, G07 | identity + bound | 44,47,56 |
| 44 | `slotRelation` | 7219 | Slot relation: /A1/ <= 3/A0/+/A2/+2(/H/^2-/H/)+2C(/H/,2); 4 sigma + 21/H/ <= 3n. | yes | A03, A05, H06 | bound | 43,47 |
| 45 | `closedClasses` | 7220 | Closed bag-link classes of the hubs of R0: closures do not leak, disjoint closed sets have disjoint closures, each meets a window-remainder incidence. | yes | B01, D05, D08 | classification | 42,46 |
| 46 | `hubTwoHopLinks` | 7221 | Two-hop links between hubs of R0: no 6-path of Lk2, degeneracy <= 25, sum <= 50 h_R; per-centre caps 6142, 12286, 24572. | yes | A06, D03 | bound + exclusion | 42,47 |
| 47 | `slotLinear` | 7222 | Slot relation linear in h_R: /B_W/ <= 13 nu + 4 e(R,W); 4 sigma + 15/H/ <= 3n + K h_R + 584 nu + 32 sigma_W, K = 1811497284. | yes | A03, A05, C09, G09, H06 | bound | 44,53,54 |
| 48 | `remainderPathBounds` | 7211 | Paths and cycles inside R0: no induced P13, components of R0 minus hubs <= 6142, path length <= 6143 h_R + 6142, cycle length <= 6143 h_R + 6142. | yes | B01, C01, C08, C10 | bound | 49,78 |
| 49 | `windowFreeGeometry` | 7212 | Window-free geometry of P0: shortest induced walks in window-free sets have length <= 11; hub cycle lengths in {3,4,5,7,...,11}. | yes | C01, C08, C10 | bound | 48,78 |
| 50 | `inducedPathAttachment` | 7213 | Induced P13s of G: every outside vertex has <= 7 neighbours on it; each of its vertices has a neighbour off it. | yes | C08, C12, D01 | bound | 39,40 |
| 51 | `densityExcess` | 7207 | Density: proper sets S span int(S)+6 <= 4/S/ edges (equivalently surplus(S) <= /S/+bd(S)-6); >= 2 edges leave every nonempty proper set; single-hub slack. | yes | A13, B02 | bound | 52,53,54 |
| 52 | `remainderSlack` | 7208 | Remainder slack of P0: slack(R0) = (n-sigma)+2p+2 sigma_W - cross(W)-6; hanging windows slack; cross(W)+6 <= 28p; sigma_W+6 <= e(R,W)+13p. | yes | A13, C10, C09, H03 | identity + bound | 51,53,54 |
| 53 | `hubWindowBudget` | 7209 | Hub-window budget at P0: 24p+2 hubEnds+isoCubic+6/H/+sigma <= 3n+4 hubs_W; 2/H/+3 hubs_R+... <= 2p+/R0/+(n-sigma); window LL sum and dart identity. | yes | A03, C09, H04, H06 | identity + bound | 47,54,62 |
| 54 | `windowHubBounds` | 7210 | Windows of P0 against big hubs: for s = n-sigma, 12p+31/B/ <= 2s+2/H/+25/B/^2; 23p+31/B/ <= n+3s+25/B/^2; 22p+93/B/+... <= 6s+75/B/^2. | yes | A03, C09, G09, H04 | bound | 53,58 |
| 55 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; /L/ <= 2e(L). | yes | A03, A04, D03 | bound | 56 |
| 56 | `hubCountBound` | 7201 | 5/H/ + sigma <= 2n. | yes | A01, A03, A05 | bound | 43,58 |
| 57 | `lowEdgeParity` | 7202 | Parity of L-L edges on walks: #LL + [u in H] + [v in H] + /p/ even. | yes | C01, C04 | identity | unconsumed |
| 58 | `bigHubBound` | 7203 | Hub domination and 2/B/ + sigma <= n. | yes | A01, A03, A05, A06 | bound | 54,59 |
| 59 | `bigHubVShapes` | 7204 | V-shape caps: <= 12 middles per pair of big hubs; 4 sigma + 93/B/ <= 2n + 75/B/^2 + 4/H/. | yes | A03, A05, D03 | bound | 58,60 |
| 60 | `highSurplusBound` | 7205 | 24 sigma + 465/B/ <= 18n + 375/B/^2; 8n <= 32 s + 125 s^2 at s = n-sigma. | yes | A01, A05 | bound | 54,59 |
| 61 | `hubLengthThreePairs` | 7206 | Length-3 pairs at the hubs of G. | yes | C01, D03 | classification | unconsumed |
| 62 | `surplusDartIdentity` | 6607 | sigma + 2 delta /H/ + lowDarts = delta n. | yes | A05, A03, H01, H06 | identity | 44,47,53,63 |
| 63 | `highDegreeCountBound` | 6608 | /H/ <= sigma. | yes | A03, A05, A14 | bound | 62,74 |
| 64 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible declared quotient of G is label-injective on its family. | yes | D07, E06, G06 | exclusion | 68,82,85 |
| 65 | `surplusAtOrBelow` | 9 | sigma(G) <= T(n) (near-cubic spine). | yes | A05, A14, G08, H08 | bound | 74,75,80,86 |
| 66 | `sparseSurplusSurvivor` | 119 | G survives the five sparse-surplus exits (SurvivesSparseExits on the declared family). | yes | A05, E09 | exclusion | unconsumed |
| 67 | `barrierEnumeration` | 211 | Certified finite barrier enumeration read from the registered (1,1) row: safe/flat/obstructed counts and log2(safe/flat) identity. | no: takes only `data`; no object argument, nothing constructed from G | -nonG: G02, I05 | certificate (data table) | 68 (rate) |
| 68 | `windowPackageSeparated` | 35 | Window-package coordinates of P0: each window has `bits` disjoint coordinates, /family/ = bits*p, rate*scales <= bits, label-injective under functional admissible quotients (also jointly with the spine family). | yes (coordinates are G's declared window coordinates; rate is registered data) | C09, D01, D05, F05, G02, G06, I05 | decomposition + bound | 88,71,91 |
| 69 | `skeletonDominates` | 206 | /Skeleton(n,m)/ = skeletonBudget = C(C(n,2),m); every stateOf : Skeleton -> State has /range/ <= that budget. | partly: clause 1 is a number determined by G's (n,m); clause 2 quantifies over abstract state maps on the class of labelled graphs | G01, I01; nonG: G06 | identity (clause 1); bound over abstract maps (clause 2) | 71,89,90 |
| 70 | `hotColdPartition` | 200 | IsHotColdWindowPartition(P0, canonicalHot, canonicalCold). | yes (subfamilies of G's P0; hot is defined by Classical.choose of a maximal `WindowFamilyRealized` family, see caveat) | C09, D05, D08 | decomposition | 71,72,73-77 |
| 71 | `barrierCap` | 10 | 2^(rate*scales*/hot/) <= skeletonBudget. | yes | G01, G09, H05, H09 | bound | 72,73 |
| 72 | `coldHotEntropyCap` | 215 | coldWindowBitRate*/hot/ <= (L+1)(delta n + T(n)). | yes | G08, G09, H05 | bound | 73 |
| 73 | `coldMass` | 216 | coldWindowBitRate*p <= coldWindowBitRate*C + (L+1)(delta n + T(n)) (cold mass). | yes | G08, G09, H08 | bound | 74,75 |
| 74 | `coldAmbientCubic` | 217 | C <= /cubic cold/ + sigma and sigma <= T(n). | yes | A05, G07, H08 | bound | 75,63,65 |
| 75 | `coldStubExcess` | 218 | perWindow*C <= perWindow*/cubic cold/ + perWindow*sigma. | yes | G07, H08 | bound | 74,77 |
| 76 | `coldAmbientCubicStubExcess` | 180 | Every ambient-cubic cold window has exactly coldExternalStubCount external stubs. | yes | B05, C12, D01 | identity | 77,26,39 |
| 77 | `coldSelectedBranchExcess` | 179 | selected stubs = 9*/cubic cold/ and each selected stub is charged to exactly one cold window. | yes | C11, D05, G07, H06 | identity + injection | 75,76 |
| 78 | `remainderNormalized` | 13 | Every subregion of R0 carries no window and no baseline subgraph. | yes | A07, C08, C10, E02, E08 | exclusion | 81,48,49 |
| 79 | `boundaryDemand` | 14 | def+(R0) <= e(R0,W) <= (delta*order - 2(order-1))p + sigma_W. | yes | A10, A11, B09, H01, H05, H07 | bound | 80,81,26 |
| 80 | `stubSupply` | 15 | def+(R0) + 2(order-1)p <= delta*order*p + T(n). | yes | A11, B09, G08, H01, H05 | bound | 81,86 |
| 81 | `wedgeSupply` | 16 | For every X within R0: delta/X/ <= W2(X) + 2 def+(X); and for R0 itself with the P0 chain. | yes | A07, A09, A11, F01, H01, H02, E08 | bound | 86,85 |
| 82 | `curvatureTargetRank` | 18 | Some surviving subfamily of curvature tests of R0 has size r_Omega(R0) and bounds every surviving subfamily. | yes | E06, F01, F02 | witness + bound | 85,86 |
| 83 | `exactResponseProfile` | 207 | /remainderCurvatureTests(R0)/ = W2(R0) (exact labelled profile). | yes | A09, D07, F01 | identity | 85 |
| 84 | `targetRankCircuit` | 210 | Canonical surviving family: every test outside it has a proper finite target-dependence; absence of dependences is full survival. | yes | D08, F07 | classification | 85 |
| 85 | `curvatureFullRank` | 20 | r_Omega(R0) = W2(R0). | yes | F01, F02, F07 | identity | 86,90 |
| 86 | `forcedCurvatureCost` | 37 | c_Omega(delta/R0/ + 4(order-1)p) <= c_Omega r_Omega(R0) + 2 c_Omega(delta*order*p + T(n)). | yes | A11, B09, F02, G03, H01, H05, H09 | bound | 90 (F <= c_Omega r_Omega), 89 |
| 87 | `remainderEntropyHigh` | 38 | RS(R0) >= n^{/R0//d}: the remainder state count is at least the high-entropy rate. | yes (RS counts labelled graphs on V(R0) with G's def+, e(R0), /R0/; a number) | G01, G03, G04 | bound | 88,89 |
| 88 | `entropyPackageDemand` | 40 | (2^{rate*scales*p})^d * n^{/R0/} <= jointPackageDemand^d. | yes | C09, G01, G05, H09 | bound | 89,90 |
| 89 | `entropyCapActive` | 41 | skeletonBudget < jointPackageDemand * 2^F (eq:entropy-cap active). | yes | G01, G03, G05, H05, H09, I03 | bound (strict overflow) | 90 |
| 90 | `allColdEntropyResidual` | 3205 | Conjunction at P0,R0: not WindowFamilyRealized; RS*room <= B; room = C(C(n,2)-C(/R0/,2), m-e(R0)); F <= c_Omega r_Omega; room < 2^{rate*scales*p} 2^F; B < joint*2^F; not EntropyJointRealization. | partly: conjunct 1 negates an existence over abstract state maps on the class of labelled graphs; conjuncts 2-7 are numbers determined by G | A02, D09, F02, G01, G05, H09, I03; nonG: G06 | identity + exclusion + bound | the residual itself |

### Table 2b: per-subtype extra facts (rows 91-104)

| # | Key | idx | Subtype(s) | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|---|
| 91 | `windowPackageRealized` | 228 | realizedColdBelow, realizedBounded | 2^(bits*p) <= skeletonBudget (window package of P0 fits the skeleton class). | yes | C09, G01, H09, I03 | bound | 97 (cap side), 92 |
| 92 | `coldRoute8Below` | 212 | realizedColdBelow | (delta*s+1)(stubs*p + T(n)) + delta*F*s*T(n) < delta(n - order*p): theta < 1/78 in exact form. | yes | A10, G09, H01, H08 | bound | 93 (route-8 carrier rate) |
| 93 | `route8Rate` | 264 | realizedColdBelow, unrealizedBothRates | (delta*s+1)/dR/ + delta*slack < delta*/R0/ (tau < 3/13 with slack). | yes | A10, B09, H01, H05, H08 | bound | unconsumed in [54]'s statements (route-8 carrier lemmas) |
| 94 | `coldRoute8AtOrAbove` | 213 | realizedBounded, unrealizedTauHighBounded, unrealizedRateFailsBounded | not (coldRoute8Below): (delta*s+1)(stubs*p+T(n)) + delta*F*s*T(n) >= delta(n-order*p). | yes | A10, G09, H01 | bound (lower bound delta*n <= A*p + D*T(n)) | 97,101 |
| 95 | `coldMassBounded` | 225 | realizedBounded, unrealizedTauHighBounded, unrealizedRateFailsBounded | perWindow*C <= (perWindow + (delta+1)*overlapBound)*sigma: cold mass within the two slacks. | yes | A05, D05, G07, H08 | bound | 96 |
| 96 | `densityCap` | 12 | realizedBounded, unrealizedTauHighBounded, unrealizedRateFailsBounded | 2*rate*scales*p <= (L+1)(delta n + T(n)) + densitySlack*rate*scales*T(n), and for all State, stateOf: joint-fit implication into skeletonBudget^d. | partly: conjunct 2 quantifies over abstract state maps on the class of labelled graphs | G08, G09, H05, H09; nonG: G06 | bound | 97,101 (via [24] cap) |
| 97 | `realizedDensityOrder` | 6600 | realizedBounded | DensityOrderBound(A,D,r,0,delta,n,log2 n,T(n)): 2 r L (delta n) <= A((L+1)(delta n+T)) + L T (A*0 + 2 r D). | yes | A01, G08, G09, I04 | bound (combined) | 98 |
| 98 | `realizedOrderSmall` | 6602 | realizedBounded | not SufficientlyLargeForDensityOrder: not (A < 2r and 0 < delta and cutoff <= n). The first two conjuncts are registered constants; the residual content is n < N0. | yes | A01, D10, G08, I04 | bound (order)  | unconsumed |
| 99 | `windowPackageUnrealized` | 229 | unrealizedTauHighBounded, unrealizedRateFailsBounded, unrealizedBothRates | skeletonBudget < 2^(bits*p) (strict). | yes (numeric in G's n, m, p) | C09, G01, H09, I03 | bound (strict) | unconsumed in [54]'s statements |
| 100 | `denseDeficiencyAtOrAbove` | 231 | unrealizedTauHighBounded | not denseDeficiencyBelow: s(delta*order*p + spineScale*ceilSqrt n) >= s*2(order-1)p + (n - order*p): tau >= 1/4 up to T(n). | yes | A11, G09, H01 | bound | unconsumed |
| 101 | `boundedDensityOrder` | 6603 | unrealizedTauHighBounded, unrealizedRateFailsBounded | DensityOrderBound(A,D,r,densitySlack*r,...): as 97 with slack S = densitySlack*rate. | yes | A01, G08, G09, I04 | bound (combined) | 102 |
| 102 | `boundedOrderSmall` | 6605 | unrealizedTauHighBounded, unrealizedRateFailsBounded | not SufficientlyLargeForDensityOrder with S = densitySlack*rate: n < N0 = max(2^235, (...)^2). | yes | A01, D10, G08, I04 | bound (order) | unconsumed |
| 103 | `denseDeficiencyBelow` | 230 | unrealizedRateFailsBounded, unrealizedBothRates | s(delta*order*p + spineScale*ceilSqrt n) < s*2(order-1)p + (n - order*p): 4 def+(R) < /R/ up to T(n) (tau < 1/4). | yes | A11, G09, H01, H08 | bound | unconsumed |
| 104 | `route8RateFails` | 265 | unrealizedRateFailsBounded | not Rate: (delta*s+1)/dR/ + delta*slack >= delta*/R0/. | yes | A10, B09, G09, H01, H05 | bound (lower bound on e(R0,W)) | unconsumed |

Subtype ledgers (generic 1-90 plus): `realizedColdBelow` = {91,92,93}; `realizedBounded` = {91,94,95,96,97,98}; `unrealizedTauHighBounded` = {99,100,94,95,96,101,102}; `unrealizedRateFailsBounded` = {99,103,104,94,95,96,101,102}; `unrealizedBothRates` = {99,103,93}. (Read from the five `abbrev`s.)

**Bookkeeping rows.** None of the 104 rows is pure routing: every row accounts for at least one coordinate or is listed as nonG in section 5. Parameter-only components of row 2 (Cubic/TypeB/Surplus presentation) are bookkeeping and earn nothing.

## 4. Gaps ranked (joint check)

Ranking key: number of existing facts (generic rows plus subtype extras) whose statements share a currency with the missing observable, i.e. would enter one inequality with it once measured. Every `gap` and every `~` whose missing accounting is a new observable appears; coordinates that are `~` only because a fact is proved but unconsumed are folded into the entry that would consume it.

**1. G08 / I04 / D10: exact small-order regime (n vs N0 and the net-cap threshold)** (22 facts)
- Present at G: Subtypes 98/102 assert n < N0 with p >= 1 windows, delta*n <= A*p + D*T(n) (94), 13p <= n (17), 5|H|+sigma <= 2n (56), 2|B|+sigma <= n (58), 8n <= 32s+125s^2 (60): G has a definite order below the cutoff; no fact bounds n from below.
- Missing observable and certificate: Observable: a lower bound n >= f(structure of G) (cycle rank, degrees, hub counts, packing) to be compared with N0; or an explicit finite list. Certificate: bound (T13) or finite exact certificate (T17).
- Technique: T13, T17
- Combines with existing facts: generic 7, 17, 47, 51, 52, 53, 54, 56, 58, 60, 62, 65, 69, 71, 72, 73, 80; subtype 94, 97, 98, 101, 102.

**2. C03 (with C04, C01, C05, C13): cycle-length spectrum of G and of R0** (21 facts)
- Present at G: G has no cycle of length 2^k (1) yet has cycles through every vertex (34, 36), forced paths with accepted closing length (19-22), so its length spectrum is a nonempty, constrained set at G.
- Missing observable and certificate: Observable: the set of cycle lengths of G (and of the 2-connected pieces of R0), as a quantitative statement (e.g. a cycle of length in [l, 2l) not a power of two whenever n and the cycle rank exceed an explicit function). Certificate: bound (decomposition into ears/paths with length increments).
- Technique: T08, T09
- Combines with existing facts: generic 1, 4, 18, 19, 20, 21, 22, 30, 31, 34, 35, 36, 37, 38, 57, 60, 61; subtype 97, 98, 101, 102.

**3. H07 / H04 / A10: flow-cut and internal-excess identity for def+(R0) against the window stubs** (18 facts)
- Present at G: def+(R0) <= e(R0,W) (25) and e(R0,W) <= 15p + sigma_W (26) are certified; the rate tests (93, 104, 92, 94) bound e(R0,W) from below and 103/100 bound def+(R0) against |R0|. The exact relation e(R0,W) = sigma_R + def+(R0) - exc(R0) with exc(R0) = sum over R0 of max(0, deg_R0 - 3) is not on the ledger.
- Missing observable and certificate: Observable: exc(R0) and an integral assignment of def+(R0) to distinct window stubs. Certificate: identity plus flow/matching bound.
- Technique: T14, T13
- Combines with existing facts: generic 25, 26, 27, 44, 47, 53, 54, 62, 79, 80, 81, 86; subtype 92, 93, 94, 100, 103, 104.

**4. G06 (with D09, I02): an explicit reconstruction map built from G** (12 facts)
- Present at G: `not WindowFamilyRealized` (90) and the cap clauses (69, 96) are stated over an abstract `stateOf : Skeleton(n,m) -> State`; G itself and its labelled skeleton class are present, but the map is not constructed from G.
- Missing observable and certificate: Observable: a map from (window label bits, R0 state, forced bits) into G's own labelled skeleton class defined from G's canonical objects (P0, R0, canonical labelling), with injectivity. Certificate: replacement (injection) and its range count.
- Technique: T15, T16
- Combines with existing facts: generic 64, 68, 69, 70, 71, 87, 88, 89, 90; subtype 91, 96, 99.

**5. H10 finite demand descent on p** (10 facts)
- Present at G: P0 is a finite family of 13-vertex windows (14) and the demand is 2^{rate*s*p} (88).
- Missing observable and certificate: Observable: a one-window peel with a preserved invariant. Certificate: descent.
- Technique: T19
- Combines with existing facts: generic 14, 17, 68, 71, 72, 73, 88, 89; subtype 91, 99.

**6. B06 / D02 / G04: boundaried type and local types of R0** (9 facts)
- Present at G: RS(R0) (87, 88, 90) depends on (def+, e(R0), |R0|) only; windows have placements and labels (39, 40); R0 has a boundary of e(R0,W) incidences (26).
- Missing observable and certificate: Observable: the boundaried type classes of R0 (ordered terminals, degrees) and the largest fibre. Certificate: count (G02/G04).
- Technique: T05, T12, T16
- Combines with existing facts: generic 26, 39, 40, 83, 87, 88, 89, 90, 64.

**7. A12 / C07: cycle space of G and R0** (8 facts)
- Present at G: beta(G) >= n/2+1 (8), cycle counts (34, 36), m in B and in room (69, 90): the cycle space has dimension m-n+1 at G.
- Missing observable and certificate: Observable: cycle-space basis/ranges of G and R0 and their symmetric-difference closure counts. Certificate: identity (dimension, #cycles) combined with B.
- Technique: T08, T11
- Combines with existing facts: generic 8, 34, 36, 51, 52, 60, 69, 90.

**8. H03 connected negative support** (7 facts)
- Present at G: slack of proper sets (51, 52) and the deficiency chain (79, 80, 86) are certified.
- Missing observable and certificate: Observable: a connected support of R0 with negative net charge, or its exclusion. Certificate: obstruction/exclusion.
- Technique: T13
- Combines with existing facts: generic 51, 52, 79, 80, 86; subtype 100, 103.

**9. C06 ear structure** (6 facts)
- Present at G: G connected and bridgeless (5, 24).
- Missing observable and certificate: Observable: an ear decomposition with ear lengths. Certificate: decomposition.
- Technique: T04, T08
- Combines with existing facts: generic 5, 24, 33, 35, 8, 51.

**10. I02 canonical representative / orbit of G in Skeleton(n,m)** (6 facts)
- Present at G: G sits in Skeleton(n,m) (69).
- Missing observable and certificate: Observable: canonical labelling and orbit size n!/|Aut(G)|. Certificate: identity.
- Technique: T16
- Combines with existing facts: generic 14, 45, 69, 70, 84, 90.

### 4b. Relevance to the subtypes

**Bounded-order subtypes (n < N0: `realizedBounded`, `unrealizedTauHighBounded`, `unrealizedRateFailsBounded`).** Coordinates certified in these subtypes: A01 (n enters 97/101), G08 and I04 (98/102 give n < N0, an exact cutoff `max(2^235, (scale+1)^2)`), D10 (bounded configuration, only as an order bound). Note on 98/102: the statement is `not SufficientlyLargeForDensityOrder`, i.e. `not (A < 2r and 0 < delta and cutoff <= n)`; the first two conjuncts are registered constants, so `n < N0` follows only once those constants are evaluated (they are not a `Holds` fact of this ledger). What is unmeasured for a graph of order below N0: ranked gaps 1 (lower bound on n, G08/I04), 2 (length spectrum, C03/C04), 3 (flow-cut for def+) and 5 (cycle space); they combine with 7, 17, 47, 53, 54, 56, 58, 60, 62 and 97/98 or 101/102. For the realized arm the cap side is exact (no slack); for the [24] arms it is `densityCap` (96) with slack densitySlack*rate*scales*T(n), and its second conjunct is a nonG clause.

**Rate/density failure subtypes.** `unrealizedRateFailsBounded` (104 with 103) and `unrealizedTauHighBounded` (100), `realizedColdBelow`/`unrealizedBothRates` (92/93, 103). The certified content is a pair of opposite bounds on the same G-objects: 26 gives e(R0,W) <= 15p + sigma_W (upper); 104 gives (delta*s+1)e(R0,W) + delta*slack >= delta|R0| (lower, since supply.card = boundaryIncidence); 25 gives def+(R0) <= e(R0,W); 103 gives 4 def+ < |R0| up to T(n); 100 the reverse. Missing: ranked gap 3 (exc(R0) identity and an assignment of def+ to stubs) and ranked gap 8 (net-charge support, H03), and for the [146] test the coefficients A = 234, D = 109 of `densityOrderPackingCoeff/SurplusCoeff` are registered arithmetic of `coldExternalStubCount`, not facts about G's stubs beyond 39/76. For the two unbounded-size subtypes (`realizedColdBelow`, `unrealizedBothRates`) no size test exists at all: G08 stays `~` and I04 is not certified on them.

## 5. Non-G facts

| Fact | Non-G object | G-constructed replacement (the missing accounting) |
|---|---|---|
| 11 `replacementExclusion` | the replacement piece X' (a boundaried graph that is not part of G), excluded by `not exists` | The swap of G at Z and its canonical degree deficit: statement on G and G-Z only (e.g. G's own reading at Z has boundary-degree profile equal to the profile of the canonical smaller piece constructed from G at Z); coordinate E05 |
| 12 `uncompressible` | smaller target-complete representative X' in G-Z | same swap; E05 |
| 15 `localAlgebra` | the window label alphabet (census 399, size distribution); the object argument is `_object` and unused | Count of legal labels attained at G's placed windows (from 40 and 68) matched to the census; coordinates G02, I05 |
| 67 `barrierEnumeration` | only `data` (registered table); nothing constructed from G | Same as 15: G-side bits per window (68) tied to the table rate |
| 1 `selection` (clause 2) | every strictly smaller baseline graph (`sizeMinimal`, `refinedMinimal`) | Minimality restricted to G's own proper subgraphs and G's own reductions (5 plus the canonical order on G's decompositions); E01, E07 |
| 2 `cubicBaseline` (components 1-3) | Parameters-only laws (no object) | none needed: constants; the G component (4) stays accounted |
| 69 `skeletonDominates` (clause 2) | arbitrary `State`, `stateOf` on the class of labelled graphs | Explicit map built from G (gap 4); clause 1 (the count) is a number determined by G's (n, m) and is kept |
| 90 `allColdEntropyResidual` (conjunct 1) | `not WindowFamilyRealized` = no `stateOf` exists on the labelled class | same; conjuncts 2-7 are G numbers and are kept |
| 96 `densityCap` (conjunct 2) | `forall State stateOf` over the labelled class | same; conjunct 1 (the linear cap) is kept |

**Caveat, not counted as nonG.** The hot family used by 70-77 is `Classical.choose` of a maximal `WindowFamilyRealized` family, so the cold facts are about a subfamily of G's P0 that is selected through the abstract predicate of 90. The numbers (|hot|, |cold|) are G's and the facts are kept; the choice is canonical only up to that predicate.

## 6. Cross-check results

1. **Every coordinate code in Table 2 (and 2b) has status x or ~ in Table 1 and lists that fact: PASS.** Checked by script: no gap, n/a or nonG coordinate appears in the coordinates column; the coordinates of Table 2 rows were used to generate the `Accounting facts` column of Table 1, so each row is cited by construction. The nonG coordinates (E01, E05, E07) appear only under `nonG:`.
2. **Every x or ~ in Table 1 cites at least one Table-2 row: PASS.** Two `~` rows (I04, D10) are supported only by subtype extras (97, 98, 101, 102 and 98, 102); they are `~` for exactly that reason (certified on a sub-object) and each row names the extras.
3. **Every Table-2 row accounts for at least one coordinate or is labelled bookkeeping: PASS.** Rows 11, 12, 15, 67 account only nonG coordinates (they earn no mark); they are listed in section 5, not as bookkeeping.
4. **No fact counted twice for the same demand in different currencies: PASS with two notes.** 25, 79 and 80 all state def+(R0) against the boundary (the chain `def+ <= e(R,W) <= ...` in 79 contains 25 and 26); they are one demand in one currency (boundary incidences) and are cited jointly, not summed. 86 restates 81 with c_Omega and 85; F is counted once. 91 (2^{b_P p} <= B) and 71 (hot cap) and 99 (the negation of 91) are different families/branches; 91 and 99 never occur together.

**Outside the register.** (i) The realization predicate `WindowFamilyRealized` (existence of a state map into the labelled class) and the hot/cold retention it defines: it is a property of a code against the class, mapped here to G06/G01 only through its numeric consequences. (ii) Registered arithmetic constants (A = 234, D = 109, K = 1811497284, N0): data facts, not structure of G.

## Discrepancies found while reading (not structural)

- Fact counts: abbrev docstring says 52 common facts, file header and register say 64, the abbrev conjunction has 90.
- `unrealizedRateFailsBounded` docstring says 6 extra facts; the abbrev has 8 (99, 103, 104, 94, 95, 96, 101, 102). `unrealizedTauHighBounded` docstring says 52+7; actual 90+7.
- `realizedOrderSmall` / `boundedOrderSmall` are `not SufficientlyLargeForDensityOrder`, a three-way disjunction (margin A < 2r, 0 < delta, cutoff <= n negated); the register reads them as n < N0.

## After (g-audit-54)

No fact was added to the ledger; the status counts of Table 1 are unchanged (x 37 / ~ 40 / gap 3 / n/a 5 / nonG 3).  G08/I04/D10 stay `~`: the cutoff behind facts 98/102 is now `max(2^176, (13096·C_sp + 2)^2)` (bounded arm: same formula with the `[24]` coefficient), `Graph.densityOrderCutoff` with the log floor `⌊3A/(2(2r−A))⌋ + 1` and the scale `⌊3·coef·C/((2r−A)·δ)⌋ + 1`, and `Assembly/Residuals/Node54Order.lean` reads 98/102 as `n < N₀` at `spineData`.  Gap 1 (a lower bound on `n`) is unchanged: no G fact bounds `n` below.

## After, second pass (keys 8550-8551)

Added facts 105 `stubDeficitIdentity` (8550) and 106 `remainderCycleSpectrum` (8551) to the generic residual.  Coordinates moved: A10 (incidence between two regions: `e(R0,W)` identity with `exc`, `def+`, `sigma_R`), A11 (boundary degree deficit: deficit units assigned to stubs), A05 (excess above the baseline: `exc(R0)`), H03/H04/H07 partially (flow-cut identity with a canonical integral assignment; still no connected negative support), C03 (accepted-length cycles excluded in `G[R0]`; quantitative spectrum still absent), D09 (handshake fixes `e(G[R0])`).  Unchanged: gap 1 (no lower bound on n beyond `13 <= n`), C06, H10, I02.  Minimality (`selection` clause 2, `replacementExclusion`, `uncompressible`) is legitimate and is not nonG; E01/E05/E07 are `x`, not `nonG`.  Facts 69 `skeletonDominates` clause 2 and 96 `densityCap` clause 2 (class quantification): 96's clause 2 is removed (counting lemma, no fact of G); 90's conjunct 1 is restated in aggregate form.
