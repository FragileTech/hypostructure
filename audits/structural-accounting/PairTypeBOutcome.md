# Structural accounting: `PairTypeBOutcome`

> Coverage: the generic `PairTypeBOutcome` has 132 facts, all accounted here (Table 2 rows and the sections at the end). The root returns two subtypes, `independentSystem` (+2) and `dependentSystem` (+11), whose extras are listed in "Arm keys and subtype-only keys". The increment arm is empty at G, so rows 124-127 (`pairSerialDemandSystem`, `pairSystemNoEarlyOutcome`, `pairIncrementCovered`, `pairIncrementEarlyOutcome`) and the arm-A rows (`pairArmAPattern`, `pairArmARoleAlphabet`) are not facts of the returned subtypes. Fact list compared with the `Holds` conjuncts of the Lean abbrevs in `Assembly/Residuals.lean` and `Assembly/Residuals/`.

Node `[187]` ([179]/[180] Type B entry), `Assembly/Residuals.lean` abbrev `PairTypeBOutcome` (thm:main (vi)). Worktree `/home/guillem/hs-wt-SPTB`, branch `g-audit-pairTypeB`. Read-only analysis; no Lean edited, no build run.

**Defining failure.** At G's canonical objects the free-pair entropy count fails (fact 110: `2^(|spine|+|R_Pi|) > skeletonBudget(G)`), giving the canonical first failed extension (112), the minimal connected overlap obstruction (119) and its two demands d_p, d_q with returns (120). The [179]/[180] coverage test yields an early outcome (123) with the two alternatives `targetCycle` (excluded by selection, fact 1) and `typeB`, so the surviving alternative is `PairObstructionHandoff` (Statements/CanonicalPairHandoff.lean): two routes of maximal common prefix inside U = the overlap support of the minimal obstruction, first separator h with deg h > 3 and two entry arms into the core {d_p,d_q}, envelope escaping at P0. That is `TypeBFanEntryStatement` (122) on its `[179]/[180]` lane (Statements/TypeBLanes.lean), i.e. G enters node [65] Type B at `canonicalPairObstructionSupport`. Every later judgement is relative to (U, d_p, d_q, h, P0, the canonical capacity charge).

**Table 2:** 127 rows (122 common conjuncts, the system arm key 123, and the increment-arm keys 124-127, which are empty at G, see Coverage), and rows 128-138 in the sections "Handoff facts" at the end.

**Status counts (Table 1, 88 coordinates, rows 1-138):** `x` = 58, `~` = 17, `gap` = 7, `n/a` = 1, `nonG` = 5 (H03, H07, B06, G03 and H10 are `~` by rows 128-135; see the sections at the end).

**Headline findings** (details in the sections below):

1. *nonG facts on the path*: 1 (minimality clause), 2/15 (registered-parameter tables), 9, 10 (conjunct 1), 11, 12, 63 (abstract quotients / arbitrary replacement piece X'), 81 (existential AttemptedQuotient), 100 (clauses (c),(d)), 109 (existentially chosen Coordinate type and family), 126 (PairSerialArithmetic free data). The early outcomes 123 and 127 name only objects of G (constructors `targetCycle`, `typeB` and `typeB`).
2. *Increment arm is empty at G*: `PairIncrementEarlyOutcome serial` has the single constructor `typeB`, which maps onto the `typeB` constructor of `PairSystemEarlyOutcome serial.returns`, and `canonicalPairDemandReturns = some serial.returns` (`canonicalPairDemandReturns_of_serial`); so facts 124 and 127 contradict each other at G (`not_pairIncrementEarly_of_noEarly`, `Contracts/Spine/PairHandoffSupport.lean`).
3. *Facts 66 and 67 are vacuous on every ledger path* reaching this residual: their hypothesis contains `DependentPairFamilyStatement`, contradicted on the independent paths by `independentPairFamily` (same canonical activation) and, on the dependent paths, contains `BlockedPairEntropySandwichStatement`, contradicted by `blockedPairCountFails`.
4. *Top gap* by number of facts it would combine with: H07 flow-cut support of the capacity charge (22), H03 connected negative support at the Type B lane (21), B06 boundaried type of the obstruction support U (16).

## Table 1 - Structural coordinates (same for every residual)

Status legend: `x` accounted - `~` partially accounted - `gap` present at G but unaccounted - `n/a` absent at G (reason given) - `nonG` accounted only through an object outside G (does not count). Fact numbers refer to Table 2. `nonG-touch` lists Table-2 rows that touch the coordinate only through an object outside G; they never earn a mark.





### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 16, 79, 84, 85 | bound: n >= C^2+C+1+t, C_sp+1 <= ceil(sqrt n), w∣P0∣ <= n | T01 | none for this residual |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 8, 64, 83, 86, 105, 111, 115 | identity 2m = 3n+sigma; m+2 <= 2n; skeleton exponent m-e3 <= sigma/2+1 | T01 T12 | none for this residual |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 3, 31, 40, 42, 43, 54, 55, 61, 65 | degree classes L, H, B; dart identity; class counts A0,A1,A2 | T01 T15 | none for this residual |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 3, 78, 87, 102 | delta >= 3; ∣H∣ >= 1; suppressed graph delta >= 3; max-degree Delta bound in free count | T01 | none for this residual |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 26, 31, 42, 55, 59, 61, 62, 64, 74, 83, 88, 93, 105, 106 | sigma = sum (d-3); sigma > threshold(n); 2m = 3n+sigma; ∣excessPorts∣ = sigma | T01 T13 T15 | none for this residual |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 7, 41, 45, 53, 54, 57, 58, 65, 87, 122 | high vertices pairwise nonadjacent, hub links bounded, domination, V-shapes, no rainbow 5-chain | T02 T03 T07 | none for this residual |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | ~ | ~: 47 | every nonempty X in the remainder R has a vertex with <= 12 neighbours in X (12-degeneracy of R only) | T04 | G itself and the obstruction support U: no peeling order / core number; needs core number of G[U] and G (certificate: peeling order), T04/T19 |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | - | excluded by fact 3 | - | absent at G: delta(G) >= 3 (fact 3) leaves no degree-two vertex, hence no degree-two chain; suppression of tight vertices is E04 |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 28, 60 | wedge supply at every vertex: >= C(d,2) - floor(d/2) nonadjacent neighbour pairs; length-3 pair bounds | T01 T07 T15 | none for this residual |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 25, 44, 46, 51, 52, 90, 111; ~: 80 | window/remainder incidence identities and caps (cut capacity, slot linear, budgets) | T01 T14 T15 | attachment geometry of the crossing edges at the obstruction support U is not counted (see B06) |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 24, 38, 50, 101 | deficiency of R <= boundary incidence; window stub counts; density boundary >= 2 | T01 T05 T13 | boundary degree deficit of the obstruction support U and of the Type B core (see B06/H03) |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | ~: 8 | n+2 <= 2(m+1-n) only | T01 | never entered with the pair-code currency; cycle-space dimension of G[U] not measured (needs rank identity for U, T01/T11) |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 50, 51, 86, 111 | hereditary slack: every proper S has sum internal degrees + 6 <= 4∣S∣; m+2 <= 2n; slackG(R) identity | T01 T02 T12 | none for this residual |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 31, 55, 62, 88 | ∣H∣ <= sigma; 5∣hubs∣+sigma <= 2n; sigma <= ∣H∣(n-∣H∣-3); hub count bounds | T01 T12 T13 | none for this residual |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | x | 5, 32, 44, 48, 57 | G connected; components of G-h; components of R and window-free regions; closed classes | T04 T13 | none for this residual |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 23 | G bridgeless (every edge contraction has a return) | T02 T04 | none for this residual |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 27, 32, 34 | G-h shape at every vertex, cut-vertex block structure, single-boundary supports | T04 T05 | separator structure of the first separator h of the obstruction routes (deg h > 3) inside U is only asserted in 68/123, not decomposed into blocks |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | ~: 36 | only pair-of-routes fragments (star/meeting constraints, ThreeRouteFan) on disjoint route pairs | T08 | maximum number of internally disjoint d_p-d_q connections inside U (Menger certificate, T04/T14) is not measured |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 24, 25, 27, 50 | boundary incidences of R, single-vertex boundary shape, window stubs, density boundary | T01 T05 | none for this residual, except the obstruction support U (B06) |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | gap | - | none | - | boundaried type of G[U] for the obstruction support U = union of X_pi over the minimal family: ordered terminals dU, their degrees and the crossing-edge incidence to G-U (identity/bound); technique T05. Present at G: U is a connected support (fact 119) and the objects `SupportAtom.decomposition object U` exist |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10; nonG-touch: 9, 11 | G-form context equivalence: every reading glued into G-Z has no accepted cycle, so any two readings agree (10 conj 2) | T05 T16 | arbitrary-context version (9, 10 conj 1, 11) is nonG; G-constructed form is the swap/actualGlue of G at Z |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 22, 68, 112, 119, 122, 123 | canonical connected supports: the canonical support of two declared coordinates (22), response support of the failed pair (112), overlap support U (119), Type B support (122) | T05 T10 | size/boundary bound for U not stated |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 25, 108, 120 | sigma demands with canonical returns (108), the two demands d_p,d_q with l_ret (120), window cut capacity (25) | T14 T15 | none for this residual |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 18, 19, 21, 29, 34, 36, 47, 48, 56, 60, 68, 82, 103, 107, 125 | forced paths of accepted restored length (18-21, 82), open-port witnesses (103, 107), 3-path structure (36, 37), remainder reach bounds (47, 48), serial pieces (125) | T04 T07 T08 | none for this residual |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 23, 120 | edge-rooted returns: returnAvoidance, bridgeless, canonical returns of the demands | T03 T08 | none for this residual |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 4, 47, 100; ~: 20, 33 | G has no accepted cycle; augmented/glued graphs have none; remainder cycle length bounds | T08 T09 | none for this residual |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 2, 17, 29, 30, 34, 56, 104; ~: 126 | dyadic accepted set; star/meeting/block arithmetic, LL-edge parity, suppression length shift | T08 T09 | none for this residual |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 19, 29, 30, 34 | star and meeting constraints, cross-switch pairs, cut-vertex blocks | T08 T09 | none for this residual |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | gap | - | none | - | ear structure of G[U] (or of the connector) relative to a base cycle through d_p,d_q: forward/backward ConnectorRoutes are paths attached at their ends (120, 125) but no ear decomposition is recorded; certificate: ear decomposition with lengths, T04/T08 |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | gap | - | none | - | cycle-space interaction at the first separator h: the cycles closed by the two arms and the core edge (theta at h) and their symmetric difference; certificate: binary incidence relation, T08/T11. Present at G: h has degree > 3 with two entry arms (68, 123) |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 2, 13, 47, 48, 49 | G has an induced window path (13); remainder has no induced P13 (47); induced 12-path attachment bounds (49); imported HSS law (2) | T06 T07 T18 | none for this residual |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 13, 14, 16 | maximal window packing P0 with ∣P0∣ = nu and w∣P0∣ <= n | T06 T12 | none for this residual |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 24, 44, 47, 48 | remainder R after P0: path/reach/degeneracy bounds, closed classes, slack, deficiency | T04 T06 T07 | none for this residual |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | ~: 68, 121, 125, 126 | only conditional/partial: serial system exists on the increment arm (125, contradicted by 127 with 124); coverage (121, 126); bounded-increment claim (68 part v) | T08 T09 | serial corridor with base lengths and increments on the system arm (the arm that actually reaches Type B) is not recorded; needs canonical serial system at G independent of the arm |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 36, 37, 39, 49, 103, 104, 107; ~: 77 | attachment constraints: ThreeRoute facts, window attachment rules, induced-path attachment, open-port witnesses, suppression cycles | T07 T08 | none for this residual |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | x | 29, 30, 37, 39, 68, 123, 125; ~: 121 | star/meeting constraints, three-route chain, window cross gaps, maximal-common-prefix routes in U (123), serial realization (125) | T07 T10 T15 | none for this residual |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 38, 39, 49, 101, 107 | window attachment labels, window stubs, induced path attachment, suppression neighbourhood pattern, port shoulder data | T07 T17 | none for this residual |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 38, 80, 106 | window position types, charge kinds, port types (center, tight end, 2 shoulders) | T07 T16 T17 | none for this residual |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 20, 21, 28, 33, 36, 37, 40, 58, 60, 68, 82, 106, 108, 122, 123; ~: 73, 77 | high-degree neighbourhoods: pair counts, cycles through h, route fans, switches, ports, V-shapes, separator with two next vertices and deg > 3 (68, 123), Type B centres (122) | T03 T07 T15 | none for this residual |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | ~ | ~: 95 | existence of an overloaded token with a role-homogeneous matching or star of size >= L_geom (95), conditional on freeCount <= B | T07 T14 T15 | proved but consumed only by vacuous 66/67; the pattern-to-graph lift is not used in this residual |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 39, 41, 45, 75, 77, 117, 118, 119 | hub-link overlap, separated pairs, free-side pair supports, pair-overlap system, factorization, minimal obstruction overlap | T10 T11 T15 | higher-order (triple) overlap of the supports in the minimal family is not measured |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | x | 68, 119, 123; ~: 99 | canonical minimal connected overlap obstruction: inclusion-minimal family, overlapping pair, connected support (119, 68) | T10 T16 | no size bound on the obstruction family (register caveat: minimality gives no size bound) |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | gap | - | none | - | role-swap symmetry of the two demands (d_p,d_q) and the two entry arms (a,b) of the first separator: the handoff conditions and SameTokenEscape are symmetric but ordered leftDemand/rightDemand is fixed; certificate: canonical swap/orbit reduction, T16. Present at G: 68, 123 |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 89, 122, 123 | canonical packing P0, canonical capacity, canonical support choices, canonical Type B support | T04 T16 | none for this residual |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | gap | - | none | - | gluing realizability of G[U] with G-U: uniqueness/injectivity of the reconstruction from (G[U], G-U, boundary identification) at the obstruction support (certificate: injective reconstruction, T05/T15/T16). Present at G: decomposition object U |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | ~ | ~: 65 | existence: a vertex of degree >= 5 or two of degree 4 (65) | T07 | fixed-size marked configuration is only an existence claim; no exact closure/surviving list |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | nonG | nonG-touch: 1 | none | - | G-constructed form: proper subgraph exclusion (E02) and canonical swap of G at Z with its degree deficit (not a ledger fact); minimality clause of 1 quantifies over other graphs |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5; nonG-touch: 11, 100 | no proper subgraph has delta >= 3; G connected | T02 T03 | none for this residual |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 7, 18, 19, 21, 82 | tight endpoint of every edge; forced-path switches; high-endpoint switch | T02 T03 | none for this residual |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | x | 17, 100, 101, 102, 103, 104, 107 | safe suppression: chord-length shift excluded, min degree kept, open-port witnesses, critical cycle expansion | T03 T05 T08 | none for this residual |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | nonG | nonG-touch: 11, 12, 100 | none for G (only 11, 12, 100 c/d) | - | G-constructed form: swap(G,Z,X) as a subgraph of G with swapDeficit (first vertex of degree < 3 when no proper subgraph has delta >= 3) at every proper connected support Z, including Z = U |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | ~ | ~: 113; nonG-touch: 9, 10, 63, 81, 109 | canonical mixed-family quotient dichotomy (113, conditional) only; abstract quotients 9, 10 conj 1, 63, 81 are nonG | T05 T11 T16 | existence of the canonical mixed quotient at G, and its label-injectivity or explicit defect, is not decided; Label/Value types are free |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | nonG | nonG-touch: 1 | none | - | refinedMinimal tie-break sits inside 1 (quantifies over other graphs); G-constructed form: the canonical choice order on pair schedule / supports |
| E08 | Peelability | A removable unit preserving the residual invariant. | gap | - | none | - | peelable unit: last pair of the failed prefix; 112 shows every shorter prefix still fits (realizedThrough) but no fact peels the last pair and preserves the response invariant; certificate: shorter ledger + monotone measure, T19 |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 81, 100 | no target defect at G: response obstructions (81), survivor clause (b) (100) | T05 T07 T08 | none for this residual |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 28, 33, 91, 108, 112; ~: 109 | supply of tests: neighbour pairs (28), C(sigma,2) scheduled pairs (91), sigma active demands (108), first-failure ordering (112) | T07 T08 T15 | spine family (109) is an unconstructed existential; needs the actual wedge family W2(R) of G (remainderCurvatureTests) |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | nonG | nonG-touch: 63, 109 | none for G (63, 9, 10 conj 1, 109 are abstract-quotient facts) | - | G-constructed form: rank of G's actual remainder wedge family (internalWedgeFamily of R, card = W2(R)) or of the canonical mixed family |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | x | 119; ~: 117 | inclusion-minimal family with no realizing order (119); failed prefix (117) | T10 T11 | circuit is minimal for the counting model, geometric locality only via U |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | x | 75, 117, 119 | geometric support of the dependence: U = union of response supports (119), supports in separated pairs (75) | T05 T10 T11 | none for this residual |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 75, 77 | disjoint declared/return supports of separated and free-side pairs (75, 77) | T05 T10 T11 | none for this residual |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | gap | - | none | - | composite response relation among the failed family (cancellation) and its repair support; certificate: repair network inside U, T08/T10/T11. Present at G: 117, 119 |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | ~ | ~: 113; nonG-touch: 63 | conditional dichotomy at G's canonical mixed quotient (113) only | T10 T11 T12 | dichotomy is conditional on the quotient's existence; needs unconditional rank-vs-loss decision at G's pair family |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | ~: 125, 126 | serial corridor increments and periodic arm only on the increment path (125, 126) | T09 T16 | periodic response of the obstruction on the system arm; arithmetic data is free (modulus, smear) |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 35, 109, 110, 114, 115, 116 | global counts: cycles <= 2^m, skeletonBudget = ∣Skeleton(n,m)∣, cubic baseline budget, exponent m-e3 | T12 | none for this residual |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 39, 92, 93; ~: 15 | label alphabet 399 (15) enters M0 = Cap_hom(routingLabelBound) in 92, 93 and the window attachment classification (39) | T07 T12 T17 | none for this residual |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | gap | - | none | - | conditional information of the failed pair coordinate given its exposed prefix: log2 ∣conditionalFibre∣ / ∣fibreValues∣ in the overlap system; certificate: additive cost or detected correlation, T11/T12. Present at G: fibreValues/refinedFibre are fields of 117 but no fact measures them |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | ~ | ~: 72, 95 | existence of an overloaded token (72) and homogeneous role pattern (95) | T12 | dominant fibre is existence-only, consumed only by vacuous 66/67 |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | x | 110, 115, 116, 118; ~: 99 | product-code factorization (118), free-pair count failure (110), incremental skeleton room (115), domination of states (116) | T10 T11 T12 | none for this residual |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | ~ | ~: 109, 114, 116 | skeleton class count domination (116) and cubic baseline budget (114); injection from realizations to skeletons is not stated | T05 T15 | injective map (baseline realization -> skeleton) at G as a stated fact |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 26, 35, 52, 61, 69, 70, 71, 73, 74, 75, 78, 90, 91; ~: 80 | dart identity, token count, blocked/free partition, extended loads, double counts, hub-window budgets | T14 T15 | none for this residual |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 59, 76, 79, 84, 85 | explicit thresholds: n > C^2+C+1+t, C_sp+1 <= ceil(sqrt n), 8n <= 32s+125s^2, scale pressure | T12 T17 | none for this residual |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 16; ~: 14 | w∣P0∣ <= n (packing density cap) | T06 T12 | none for this residual |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 24, 25, 42, 43, 46, 51, 52, 53, 58, 59, 61, 76, 83, 105; ~: 57 | deficiency-surplus identities: 2m = 3n+sigma, dart identity, cut capacity, slack, hub budgets, slot relations | T01 T13 | none for this residual |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | x | 51 | superadditive charge over disjoint windows: sum (2+2 sigma(P)) <= slack(K) (51) | T04 T13 | additivity over the windows only; not over the supports of the obstruction family |
| H03 | Connected negative support | A connected region with negative charge. | ~ | ~: 128, 129, 130 | net charge of the Type B support (Y,H) = ({d_p.2,d_q.2},{h}): 1<=|Y|<=2, (delta-1)|Y| <= def+(Y) <= delta|Y|, sigma(Y)=0, omega(H)=d(h)-delta>=1, and envelope.NegativeCharge or omega(H)<def+(Y) i.e. d(h)<3delta | T13 | the negative-charge arm is not derived (only the exact dichotomy); certificate `TypeBBridgeDeficitBoundAt` at the pair-obstruction lane and the connected negative region are not built |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | ~ | ~: 69, 73 | port-wise newLoad bounds (73) and empty extended free side (69); no transfer rule | T13 T15 | transfer rules from suppliers (surplus of H) to the deficits at U; certificate: nonnegative charge or overloaded receiver |
| H05 | Load and saturation | Load compared with certified capacity. | x | 26, 70, 71, 72, 73, 78, 90, 92, 95, 96; ~: 89 | primitive carrier supply, token count, extended loads, overload (71, 72), capped form (96) | T13 T14 T15 | none for this residual |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | x | 69, 70, 91, 106, 108 | blocked/free partition, empty extended free side, C(sigma,2) = sum extLoad, sigma ports, active demands | T14 T15 | none for this residual |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | gap | - | none | - | integral flow / Hall violator in the pair -> token network of the canonical charge (eligibility from blockers): cut form of the overload; certificate: flow or deficient cut lifting to graph incidences, T14/T10. Present at G: canonical charge (89, 90, 91) and loads (70-73) |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 31, 62 | sum (d-3) = sigma over the exceptional family H, ∣H∣ <= sigma, pair sums | T13 T15 | none for this residual |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 71, 74, 76, 78, 92, 93, 94, 96, 97, 98, 109, 110, 112, 115 | pair-code count failure vs skeleton budget (110, 112, 115), capacity deficit (92, 93, 96, 71, 78, 74, 76), paper budget (97, 98) | T01 T12 T13 | none for this residual |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | gap | - | none | - | well-founded measure on the pair schedule (∣Pi∣ - index of the first failure) with one-unit peel steps preserving interface response; certificate: strict descent to empty/classified state, T14/T19. Present at G: 112 (indexed prefix), 91 (C(sigma,2) demands) |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 39 | finite alphabets: Labels(w) (399), window position types, blocker kinds, token kinds | T07 T17 | none for this residual |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | gap | - | none | - | canonical representative of a window placement (q vs reversed q) and of labels: 38, 39 quantify over all placements; certificate: orbit representatives, T16/T17 |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 94, 98, 112 | exact integer first failure 2^(∣F∣+index) <= B < 2^(∣F∣+index+1); certification iff freeCount <= B; parity/LL exactness | T15 T17 | none for this residual |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | x | 79, 84, 85 | explicit order thresholds n > C^2+C+1+t (79, 84, 85) entering 59, 76 | T17 | none for this residual |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | nonG | nonG-touch: 2, 15 | none for G (2, 15 are registered-parameter tables) | - | G-constructed form: alphabet size of the labels realised at G's windows (fact 39 lands in the table); the census itself is a Lean-checked constant |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | x | 2 | HSS closure law at G and at every induced G[S]: baseline and window-free implies accepted cycle (2) | T18 | none for this residual |

## Table 2 - Facts of the residual -> structural coordinates

Coordinate marks: plain = accounted at G (`x`-level); `~` = partial; `!` = touched only through a non-G object (nonG; never earns a mark). `bookkeeping` rows account for no coordinate, with the reason given.

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted length (LengthOK) AND every smaller baseline object (lex order and refined order) has one | partly: first conjunct yes; minimality clause quantifies over every smaller FiniteObject (other graphs): nonG | C03 E01! E07! | exclusion | 123 constructor targetCycle; 100(a); 4; pairChain_outcome |
| 2 | `cubicBaseline` | 221 | Registered presentation laws: delta=3, s=4, not LengthOK 2, LengthOK 4, LengthOK <-> 2^k (k>=2), window census, rate/scale inequalities, routingLabelBound=∣RoutingLabel∣; plus the HSS law at G and at every induced G[S] (baseline and window-free implies accepted cycle) | mixed: numeric/label constants are registered parameters, not a graph fact (nonG); HSS-law clauses are about G and G[S] | C04 C08 I06 I05! | classification (exact accepted set, imported theorem) | 13 (non-windowfreeness of G), 29, 30, 34, 56, 92/93 (M0 from routingLabelBound) |
| 3 | `minDegreeBaseline` | 2850 | delta(G) >= 3: every vertex has degree at least 3 | yes | A04 A03 | bound | 5, 7, 54, 101, 102, 106 |
| 4 | `returnAvoidance` | 1 | For every dart of G the return-length set is disjoint from the shifted accepted set | yes | C02 C03 | exclusion | 18-21, 82, 107 |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has minimum degree >= 3, and G is connected | yes | E02 B01 | exclusion | 101, 102, 103; G-form of replacement (swap at Z has a vertex of degree < 3) |
| 6 | `slackIndependent` | 4 | Vertices of degree > 3 are pairwise nonadjacent | yes | A06 | exclusion | 7, 31, 41, 45, 54-57, 65 |
| 7 | `tightEndpoint` | 3 | Every edge of G has an endpoint of degree exactly 3 | yes | E03 A06 | exclusion | 61, 82, 101, 102, 106 |
| 8 | `cycleRankConstraint` | 425 | n + 2 <= 2(m + 1 - n): cycle rank bound | yes | A12~ A02 | bound | unconsumed (equivalent to a lower bound on m; not entered with any other currency) |
| 9 | `degreeProfileFibres` | 2300 | For every region, every admissible CurvatureQuotient (free Label/Value/label/value fields; properRepresentative field carries a ReplacementSupport; closedRepresentative an arbitrary smaller graph) and every two readings: different boundary-degree profiles are not identified | no: quantifies over abstract quotients whose data nothing constructs from G | E06! B07! | exclusion (nonG) | 10, 63, 113 (G-canonical quotient) |
| 10 | `targetCompleteContextUniversality` | 2301 | (1) every CurvatureQuotient that identifies two readings gives equal profiles and equal target response in actualGlue; (2) for all Z, X subsets of V(G): actualGlue G Z X (a subgraph of G) has no accepted cycle | mixed: (2) yes; (1) no (forall quotient, free data) | B07 E06! | exclusion | no row of this residual reads it |
| 11 | `replacementExclusion` | 223 | For every proper connected support Z and every arbitrary boundaried piece X' (BoundaryPiece, not a reading of G): NOT (profile(X') = profile(G[Z]) and delta(glue X' (G-Z))>=3 and glue X' (G-Z) smaller and no accepted cycle) | no: the statement is about the graph glue X' (G-Z), which is not part of G | E05! E02! B07! | exclusion (nonG) | 63, 80/81, 109 (row inputs); 12 duplicates it |
| 12 | `uncompressible` | 5 | For every support Z: NOT CompressibleSupport (definitionally the same clauses as ReplacementSupport; Iff.rfl) | no: same arbitrary X' | E05! | exclusion (nonG); duplicate of 11 | none beyond 11 |
| 13 | `windowPresent` | 608 | G contains an induced path on windowOrder vertices | yes | C08 C09 | witness | 14, 47, 48, 49; HSS non-freeness |
| 14 | `maximalPacking` | 6 | Canonical window packing P0 is a maximal packing (0<nu, ∣P0∣=nu, IsWindowPacking, every induced window meets a member) | yes | C09 C10 D08 G09~ | decomposition | 16, 24, 25, 44, 46-53, 111 |
| 15 | `localAlgebra` | 7 | ∣Labels(windowOrder)∣ = 399 and sizeDistribution.take 7 = [13,60,122,122,63,17,2] (object argument unused) | no: registered-parameter table, independent of G | I05! G02~ | identity (finite table) | 39 uses the alphabet; 92/93 via routingLabelBound |
| 16 | `packingOrderBound` | 6611 | windowOrder * ∣P0∣ <= n | yes | C09 G09 A01 | bound | 25, 46, 52, 53, 76, 111 |
| 17 | `noSuppressionChordViolation` | 6620 | For every compatible tight-vertex suppression family of G and every accepted-cycle certificate of the suppressed graph: walk length + ∣used chords∣ is not accepted | yes (suppressed graph is built from G's own configurations) | E04 C04 | exclusion | 100(e), 104 |
| 18 | `twoSwitchForcedPath` | 6800 | For disjoint edges u1v1, u2v2, u1 not adjacent u2, deg v1,v2 >= 4: G minus the two edges has a path u1->u2 of length p with p+1 accepted | yes | C01 E03 | witness | 82, 20, 21 |
| 19 | `crossSwitchFamily` | 6802 | Cross-switch family at (u1,v,h'): forced path of accepted restored length, and no two disjoint paths of length 2^j-1 to two neighbours of h' | yes | C01 C05 E03 | witness + exclusion | 82, 21 |
| 20 | `highCentreSplitForced` | 6801 | For every vertex h of degree > 3: G plus the anti-pairs of N(h) has an accepted cycle avoiding h through an added edge | yes (derived graph built from G at h) | D03 C03~ | witness | 21, 82, 58 |
| 21 | `sameVertexSwitchForcedPath` | 6803 | For h of degree >= 5 and nonadjacent neighbours u1,u2: G-{hu1,hu2} has a path with accepted restored length, and either h off it with p+2 not accepted or a split of it into two non-accepted parts | yes | C01 D03 E03 | witness / dichotomy | 82, 60 |
| 22 | `declaredPairSupportStructure` | 6677 | For every two declared sparse coordinates A, B of G, Z = select?(A ∪ B) is connected in G, contains A and B, and is a minimum connected set of G containing A ∪ B | yes | B08 | decomposition | 117, 119 (connected supports) |
| 23 | `bridgeless` | 226 | Every edge contraction of G has a return (no bridge) | yes | B02 C02 | exclusion | 5, 27, 32, 34 |
| 24 | `remainderDeficiencyBelowCut` | 6663 | Positive degree deficiency of the remainder R = G - windows is <= its boundary incidence | yes | A11 B05 C10 H01 | bound | 25, 50, 51, 46 |
| 25 | `windowCutCapacity` | 6664 | boundaryIncidence(R) + 2(w-1)∣P0∣ <= 3 w ∣P0∣ + sigma(windowSupport) | yes | A10 H01 B05 B09 | bound | 24, 46, 51, 52, 111 |
| 26 | `primitiveCarrierCount` | 6666 | ∣primitiveCarrier∣ = 4n + 2 sigma | yes | G07 H05 A05 | identity | 90, 89 |
| 27 | `singleBoundaryShape` | 6627 | For every support S with cut boundary {b} and z in S, z != b, outside vertex present: b has exactly 2 neighbours in S and 2 outside | yes | B03 B05 | decomposition | 32, 34 |
| 28 | `neighbourhoodPairCount` | 6900 | For every h: G[N(h)] is a matching; >= C(d,2) - floor(d/2) nonadjacent neighbour pairs; each neighbour has >= d-2 nonadjacent partners | yes | A09 D03 F01 | bound | 29, 30, 33, 35, 60 |
| 29 | `starCycleConstraint` | 6901 | Star constraint: paths P,Q in G-h from x to distinct neighbours y,z of h meeting only at x have ∣P∣+∣Q∣+2 != 2^k (k>=2) | yes | C05 C04 C13 C01 | exclusion | 34, 68, 123 (route arithmetic) |
| 30 | `meetingCycleConstraint` | 6902 | Meeting constraint: ∣P∣+∣Q∣+2 != 2^k + ∣P1∣ + ∣Q1∣ for the meeting-point prefixes | yes | C05 C04 C13 | exclusion | 29, 34, 68 |
| 31 | `highDegreePairSum` | 6903 | sigma = sum over H of (d_h-3); 5 sigma <= sum C(d_h,2); Cauchy-Schwarz form; 2 sum C(d_h,2) <= 16 sigma^2; heavy centre sigma <= ∣H∣(d_h-3) | yes | A05 A03 A14 H08 | identity + bound | 61, 62, 88, 55, 59 |
| 32 | `vertexDeletionComponents` | 6904 | For every vertex h: G-h connected, or d_h = 2 #blocks(h) and every neighbour component holds exactly two neighbours of h | yes | B03 B01 | classification | 34, 33, 35 |
| 33 | `cyclesThroughVertex` | 6905 | Cycles through h: >= C(d_h,2) if G-h connected, else d_h/2 | yes | F01 D03 C03~ | bound (cycle count) | 35 |
| 34 | `cutVertexBlockPaths` | 6906 | At a cut vertex h with block {a,b}: a-b paths avoid 2^k-2; returns are a...b h; residues 3 mod 4; cross-block sums 1 mod 4 with opposite parities | yes | B03 C04 C05 C01 | classification + exclusion | 29, 30 |
| 35 | `cycleDoubleCount` | 6907 | 2 sum_H cycles(h) <= n * cycles(G); same with lower bounds L_h; cycles(G) <= 2^m | yes | G07 G01 | bound (double count) | 33 |
| 36 | `threeRouteFan` | 7100 | ThreeRouteFan: for h with neighbours a,b,c (b!=c) and 3-paths a->b, a->c avoiding h: same first interior vertex, distinct second, p2 != c, q2 != b | yes | D03 C12 C01 B04~ | exclusion / forced structure | 37, 41 |
| 37 | `threeRouteChain` | 7101 | ThreeRouteChain: chain of 3-paths a-b-c-d through neighbours of h forces r1=p2, r2=q1 | yes | D03 C12 C13 | forced structure | 36, 41 |
| 38 | `windowPositionStubs` | 7102 | Each P0 window: placement exists; interior positions have external neighbours = degree - 2 (exactly 1 if cubic); end positions ext + 1 = degree | yes | A11 D01 D02 | identity | 39, 25, 90 |
| 39 | `windowAttachmentGap` | 7103 | CrossGap and window attachment rules: attachLabel in Labels(order); adjacent outside vertices have Safe labels; no forbidden gap between distinct windows; consecutive positions not both linked | yes | D01 C12 C13 D05 I01 G02 | exclusion + classification | 80, 38, 44 |
| 40 | `portEndDegree` | 7233 | Every excess port (h,c) has d(c) = 3 (tight port end) | yes | D03 A03 | identity | 106, 73, 77 |
| 41 | `hubLinkStructure` | 7217 | HubLinkStructure at P0: no long hub-link chain, no rainbow 5-path, bounded parts (<= 18429, <= 3), sums <= 36858 hubsR, 6 hubsR | yes | A06 D05 | bound | 45, 43, 46 |
| 42 | `hubClassCounts` | 7218 | Hub class counts: ∣A0∣+∣A1∣+∣A2∣ = ∣L∣; ∣A1∣+2∣A2∣ = 3∣H∣ + sigma; ∣A2∣ <= C(∣H∣,2); ∣U∣ <= 3∣A0∣; degree bound; two-hop count <= 2d | yes | A03 A05 H01 | identity + bound | 43, 46, 61 |
| 43 | `slotRelation` | 7219 | Slot relation: ∣A1∣ <= 3∣A0∣+∣A2∣+..., 4 sigma + 21∣H∣ <= 3n + 6∣H∣^2, lateral counts <= 2 | yes | A03 H01 | bound | 42, 46, 76 |
| 44 | `closedClasses` | 7220 | ClosedClasses: closures of closed sets are disjoint, meet a window-remainder incidence; number of disjoint closed classes <= window-remainder incidences | yes | B01 A10 C10 | decomposition + bound | 46 |
| 45 | `hubTwoHopLinks` | 7221 | Two-hop hub links: no 6-path in the F2 structure, parts <= 25, sum <= 50 hubsR, per-centre bounds | yes | A06 D05 | bound | 41, 46 |
| 46 | `slotLinear` | 7222 | SlotLinear: ∣Bw∣ <= 13∣P0∣ + 4∣window-remainder incidences∣; 4 sigma + 15∣H∣ <= 3n + K hubsR + 584∣P0∣ + 32 sigma(W) | yes | H01 A10 | bound | 25, 51, 76 |
| 47 | `remainderPathBounds` | 7211 | Remainder path bounds: no induced P13 in R, reach sets <= 6142, path/cycle length bounds in hubsR, every nonempty X in R has a vertex with <= 12 neighbours in X | yes | C10 C01 C08 A07~ C03 | bound | 48, 76 |
| 48 | `windowFreeGeometry` | 7212 | Window-free geometry: in G minus windows, reach implies induced path of length <= 11; hub-cycle structure; component size <= 1+(3+sum(d-3))(2^11-1) | yes | C10 C01 B01 C08 | bound + classification | 47 |
| 49 | `inducedPathAttachment` | 7213 | Every induced 12-path g: each outside vertex meets <= 7 of its vertices; each g_i has an outside neighbour | yes | C08 C12 D01 | bound | 48, 13 |
| 50 | `densityExcess` | 7207 | Density excess: every proper S (∣S∣>=2): sum internal degrees + 6 <= 4∣S∣; sum(d-3) <= ∣S∣ + boundary - 6; boundary >= 2; hub-star closure | yes | A13 A11 B05 | bound (hereditary) | 51, 86, 111 |
| 51 | `remainderSlack` | 7208 | Remainder slack identity slack(R) = n - sigma + 2∣P0∣ + 2 sigma(W) - cross(W) - 6; additive over windows: sum(2+2 sigma(P)) <= slack(K); cross+6 <= 28∣P0∣ | yes | H01 H02 A13 A10 | identity + bound | 25, 46, 52 |
| 52 | `hubWindowBudget` | 7209 | Hub-window budget: 24∣P0∣ + 2 hubEnds + isoCubic + 6∣hubs∣ + sigma <= 3n + 4 hubsW; dart-count identities | yes | H01 G07 A10 | identity + bound | 25, 51, 53 |
| 53 | `windowHubBounds` | 7210 | For every split sigma + s = n: 12∣P0∣ + 31∣B∣ <= 2s + 2∣hubs∣ + 25∣B∣^2 and two more bounds | yes | H01 A06 | bound | 52, 59, 76 |
| 54 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; ∣L∣ <= 2 e(L) | yes | A03 A06 | bound | 55, 57, 42 |
| 55 | `hubCountBound` | 7201 | 5∣hubs∣ + sigma <= 2n | yes | A05 A14 A03 | bound | 54, 57, 61 |
| 56 | `lowEdgeParity` | 7202 | Parity of low-low edges on every walk; an odd walk between cubic vertices uses an odd number of LL edges | yes | C04 C01 | identity | 29, 34 |
| 57 | `bigHubBound` | 7203 | Hub domination of cubic components (each hub dominates <= 2, <= 1 if deg >= 5); 2∣B∣ + sigma <= n | yes | A06 B01 H01~ | bound | 58, 53 |
| 58 | `bigHubVShapes` | 7204 | V-shape caps (<= 12 middles per pair in B); 4 sigma + 93∣B∣ <= 2n + 75∣B∣^2 + 4∣hubs∣ | yes | D03 H01 A06 | bound | 53, 59 |
| 59 | `highSurplusBound` | 7205 | 24 sigma + 465∣B∣ <= 18n + 375∣B∣^2; for every split sigma + s = n: 8n <= 32 s + 125 s^2 | yes | H01 A05 G08 | bound | 79, 76, 53 |
| 60 | `hubLengthThreePairs` | 7206 | For h of degree > 3 with cubic second neighbourhood: #length-3 pairs <= 4d and d(d-2) <= #nonadjacent pairs without a 3-path + 4d | yes | D03 C01 A09 | bound | 28, 36 |
| 61 | `surplusDartIdentity` | 6607 | sigma + 2*3*∣H∣ + #low darts = 3n (dart identity) | yes | A05 H01 G07 A03 | identity | 31, 62, 83 |
| 62 | `highDegreeCountBound` | 6608 | ∣H∣ <= sigma (number of high-degree vertices) | yes | A14 A05 H08 | bound | 88, 55, 31 |
| 63 | `admissibleQuotientsLabelInjective` | 6626 | For every admissible DeclaredQuotient of any declared family (free Label/Value/label/value; properRepresentative carries ReplacementSupport; closedRepresentative arbitrary smaller graph): label is injective on the family | no: abstract quotient data not constructed from G | F02! E06! F07! | exclusion (nonG) | 109 (BaselineSpineFamilySpec first conjunct), 113 |
| 64 | `surplusAbove` | 8 | surplusThreshold(n) < sigma(G) | yes | A05 A02 | bound | 79, 84, 85, 59, 95 |
| 65 | `highSurplusConfiguration` | 6703 | G has a vertex of degree >= 5 or two distinct vertices of degree 4 | yes | A06 A03 D10~ | existence (classification) | 82, 18-21 |
| 66 | `pairArmAPattern` | 7234 | Conditional: IF dependent pair family AND blocked-pair entropy sandwich AND homogeneous pattern schema AND sparse overload schema AND NOT homogeneous caps THEN explicit capacity, token, role, pattern with blocker-kind case split | yes in content; VACUOUS on every ledger path (hypothesis contradicts independentPairFamily, or the dependent-path fact blockedPairCountFails) | bookkeeping | bookkeeping (vacuous implication at G) | none |
| 67 | `pairArmARoleAlphabet` | 7235 | Conditional (same hypothesis as 66): canonical overload token/role is a live role | yes in content; vacuous like 66 | bookkeeping | bookkeeping (vacuous implication at G) | none |
| 68 | `pairArmB` | 7236 | PairArmB: (i) first failure + (factorization residual or handoff+TypeB) implies overlap system and (not CF or returns with no defect or handoff+TypeB); (ii),(iv) vacuous given 121; (iii) for every canonical returns with a handoff: TypeBFanEntry, SurplusAbove, routes/split/envelope exist, deg(separator) > 3, no label collision at P0, a != b, separator and both next vertices in U, SameTokenEscape; (v) canonical serial system: demands in U, deg d_p > 3, deg d_q = 3, all serial cycle lengths not accepted | yes | D03 C13 B08 D06 C01 C11~ | classification + decomposition | 122, 123 (the handoff certificate at G) |
| 69 | `extFreeEmpty` | 7227 | Extended free side Pi_free^ext of the canonical capacity charge is empty (every scheduled pair extended-charged) | yes | H06 G07 H04~ | identity | 70, 71, 74, 78, 91 |
| 70 | `extLoadSum` | 7228 | C(sigma,2) = sum over tokens of extLoad; ∣tokens∣ <= 8n + sigma | yes | G07 H05 H06 | identity + bound | 71, 72, 69 |
| 71 | `extOverload` | 7229 | K*ceil(sqrt n)^2 + 2 M0 (8n+sigma-∣T∣) + 2B <= 2 sum_t (extLoad(t) - M0) | yes | H05 H09 G07 | bound (overload) | 72, 92 |
| 72 | `extOverloadedToken` | 7230 | If K > 0 there is a token with extLoad > M0 | yes | H05 G04~ | witness (saturated token) | 95 (same currency, different charge) |
| 73 | `newLoadBound` | 7231 | For every excess port p: newLoad(p) <= (∣H∣-1) + [triangular port]*sigma | yes | G07 H05 H04~ D03~ | bound | 74, 78 |
| 74 | `freeSideHubs` | 7226 | ∣Pi_free∣ <= sigma(tau + ∣H∣ - 1); in the capped arm n*K <= 2 sigma(tau+∣H∣-1) | yes | H09 G07 A05 | bound | 73, 78, 92 |
| 75 | `separatedPairs` | 7232 | Separated pairs: pairs with disjoint declared/return supports carry only target-response or chord blockers; C(sigma,2) <= sum_v C(#decl at v,2) + sum_v C(#ret at v,2) + #separated | yes | F05 D05 G07 F04 | bound + decomposition | 77, 117, 118 |
| 76 | `scalePressure` | 7223 | ScalePressure at C=spineScale, q=ceil(sqrt n): C q + 15∣H∣ < 3(n - sigma) + K hubsR + 584∣P0∣ + 32 sigma(W), and the s-split form | yes | H09 H01 G08 | bound | 59, 79, 46 |
| 77 | `freeSideStructure` | 7224 | Every free-side pair has two ports p!=q with disjoint declared, port and return supports, distinct centres, no DE response obstruction, no chord obstruction, and one of chord adjacency / p1 in portT(q) | yes | F05 D05 C12~ D03~ | decomposition | 75, 118 |
| 78 | `freeSideCount` | 7225 | freeCount <= tau*sigma + sum of local buffers (also <= sigma(tau + 3(Delta-3)) for every max-degree bound Delta); ledger inequality; capped form | yes | H09 A04 G07 H05 | bound | 74, 92, 96 |
| 79 | `highSurplusOrder` | 7214 | 8n <= 32(n - C ceil(sqrt n) - 1) + 125(...)^2 and n > C^2 + C + 1 + t for every t with 125t^2+24t < 8(C^2+C+1) | yes | A01 G08 I04 | bound | 59, 84, 85, 64 |
| 80 | `windowChargeKinds` | 7215 | Canonical capacity is explicit; every window/cross-window charged pair has a coordinate or chord blocker, is fully separated, boundaryWindow-charged if its support meets R and W; recorded activation facts | yes | D02 A10~ G07~ | classification | 39, 89, 90 |
| 81 | `responseObstructionTargetDefect` | 7216 | Every DE response obstruction of the schedule comes with an AttemptedQuotient, a SparsePairDetermination and a ResidualTargetDefect (empty at avoiding G, so no response obstruction exists) | mixed: exclusion content G-only; the existential AttemptedQuotient carries free data (nonG) | E09 E06! | exclusion | 77, 80 |
| 82 | `highEndpointSwitch` | 6704 | For high h and cubic neighbour c: h has degree >= 5 with a path c->u in G-{hc,hu} of accepted restored length, or another high h2 with such a path | yes | C01 E03 D03 | witness / dichotomy | 65, 18-21 |
| 83 | `edgeSurplusIdentity` | 6606 | 2m = 3n + sigma | yes | A02 A05 H01 | identity | 61, 86, 105, 90 |
| 84 | `ceilSqrtAboveScale` | 6612 | C_sp + 1 <= ceil(sqrt n) | yes | A01 G08 I04 | bound | 79, 71, 92 |
| 85 | `orderAboveScaleSquare` | 6613 | C_sp (C_sp + 1) + 9 <= n | yes | A01 G08 I04 | bound | 79 |
| 86 | `sixVertexExtremalEnvelope` | 6614 | m + 4 <= 2n (six-vertex extremal envelope) | yes | A02 A13 | bound | 50, 111 |
| 87 | `highDegreePositive` | 6609 | ∣H∣ >= 1 | yes | A04 A06 | bound | 62, 88 |
| 88 | `highDegreeSurplusCapacity` | 6610 | sigma <= ∣H∣(n - ∣H∣ - 3) | yes | A05 A14 | bound | 62, 31 |
| 89 | `canonicalCapacityExplicit` | 6665 | The canonical capacity presentation equals the explicit one (recorded blocker activation on the P0 packing) | yes | D08 H05~ | identity (canonical object) | 90-98 |
| 90 | `canonicalTokenCount` | 6667 | ∣T∣ + 2(w-1)∣P0∣ = 4n + 3 sigma + 3 w ∣P0∣ | yes | G07 H05 A10 | identity | 92, 95 |
| 91 | `canonicalBlockedFreePartition` | 6668 | ∣blocked∣ + freeCount = C(sigma,2) | yes | G07 H06 F01 | identity (partition) | 92, 93, 69 |
| 92 | `canonicalLedgerDeficit` | 6669 | K ceil(sqrt n)^2 + 2 M0 (8n+sigma-∣T∣) <= 2(free - B) + 2(∣blocked∣ - M0∣T∣) | yes | H09 H05 G02 | bound | 93, 94, 96 |
| 93 | `pairCountDeficit` | 6670 | K ceil(sqrt n)^2 + 2 M0 (8n+sigma) <= 2(C(sigma,2) - B) | yes | H09 G02 A05 | bound | 92 |
| 94 | `canonicalCertificationCriterion` | 6671 | Certified capacity data exists iff freeCount <= B | yes | H09 I03 | identity (iff) | 95, 98 |
| 95 | `canonicalOverloadOfFits` | 6674 | If freeCount <= B: deficit inequality and an overloaded token with a role-homogeneous matching or star of size >= L_geom | yes | D04~ H05 G04~ | witness | 66, 67 (vacuous) |
| 96 | `canonicalFreeExcessOfCapped` | 6675 | If all loads <= M0: K ceil(sqrt n)^2 + 2 M0 (8n+sigma-∣T∣) <= 2(free - B) | yes | H05 H09 | bound | 92, 78 |
| 97 | `paperBudgetBound` | 6672 | paperBudget(∣spine family∣) <= B | yes | H09 | bound | 98 |
| 98 | `paperBudgetCertifies` | 6673 | freeCount <= paperBudget implies certified capacity data | yes | H09 I03 | implication (criterion) | 94 |
| 99 | `pairCodeConfiguration` | 6676 | (dependent pair family and sandwich and pattern schema and overload schema and not caps) OR (first failure exists and (uncovered residual OR handoff with TypeB entry)) | yes | D06~ G05~ | classification | 68, 112, 122; on all four ledger paths the left disjunct is false |
| 100 | `sparseSurplusSurvivor` | 119 | G survives the five sparse surplus exits of its declared family: no accepted cycle (a), no target defect (b), no compression with arbitrary X' (c), no delocalization by an arbitrary smaller graph (d), no suppression-chord violation (e) | mixed: (a),(b),(e) G-only; (c),(d) quantify over pieces/graphs outside G (nonG) | E09 E04 C03 E05! E02! | exclusion | same-token bottleneck routing rows (`SameTokenBottleneckRouting`, `SameTokenPair`) |
| 101 | `openPortSuppression` | 435 | Every compatible tight-vertex suppression family at high centres: local structure, disjointness, injective chords, capacity iff, deleted vertices, suppressed adjacency = G adjacency + chords | yes | E04 D01 A11 | decomposition | 102, 104, 17 |
| 102 | `openPortSuppressionSafe` | 436 | Compatible family with capacity: suppressed graph has minimum degree >= 3 | yes | E04 A04 | bound | 101, 104 |
| 103 | `singleOpenPortSuppressionWitness` | 437 | For every tight configuration with high centre: an OpenPortWitness (simple path between shoulders avoiding the port end, restored length accepted) | yes | C01 E04 C12 | witness | 107, 104 |
| 104 | `suppressedFamilyCriticalCycle` | 438 | For every capacity-compatible family: suppressed graph has a chord-using accepted cycle and every such cycle expands to a non-accepted length walk+∣chords∣ | yes | E04 C04 C12 | exclusion | 17, 100(e) |
| 105 | `sparseSlackSurplus` | 109 | 2m = 3n + sigma (same identity as 83) | yes | A02 A05 H01 | identity; duplicate of 83 | none beyond 83 |
| 106 | `activeSurplusFamily` | 110 | ∣excessPorts∣ = sigma; each port (h,x): d(h) > 3, d(x) = 3, exactly 2 shoulders | yes | D03 A05 H06 D02 | identity + classification | 107, 108, 40 |
| 107 | `sparsePortActivation` | 111 | Each port with shoulders (l,r): PortReturn exists; open port gives OpenPortWitness path; adjacent shoulders give a triangle | yes | C01 C12 D01 E04 | witness | 108, 103 |
| 108 | `activeSurplusDemands` | 120 | ActiveSurplusDemands: sigma active demands, each with shoulder pair and canonical return / suppression path / triangle data | yes | F01 B09 H06 D03 | decomposition | 109, 112, 120 |
| 109 | `baselineSpineDemand` | 112 | Exists a canonical baseline spine family: an existentially chosen Coordinate type, finite family and supports such that every functional DeclaredQuotient is label-injective, a BaselineCodeRealization exists, budget <= 2^(∣family∣ + spineDeficit), spineDeficit <= S n | mixed: family is Classical.choose over an abstract Coordinate type (nothing constructs it from G); the quotient clause is nonG | F01~ G01 H09 G06~ F02! E06! | existence + bound | 110, 112, 115 |
| 110 | `freePairCountFails` | 1600 | NOT (2^(∣spine∣ + ∣R_Pi∣) <= skeletonBudget(G)): the free-pair entropy count fails | yes | H09 G01 G05 | obstruction (count failure) | 112, 99 |
| 111 | `sparseUpperEnvelope` | 129 | m + 2 <= 2n and ∣window-remainder∣ + 2(w-1)∣P0∣ + ∣cross∣ = 3 w ∣P0∣ + sigma(W) | yes | A13 A10 A02 | bound + identity | 50, 86, 25 |
| 112 | `pairOverlapFirstFailure` | 357 | Canonical first failed extension exists: index, pair, 2^(∣F∣+len) <= B for len <= index, NOT 2^(∣F∣+index+1) <= B, connected response support | yes | H09 I03 B08 F01 | obstruction (first failure) | 117, 119 |
| 113 | `mixedSparseSpineDependence` | 203 | IF the canonical mixed-family declared quotient exists (functional, not label-injective) THEN a declared sparse exit or a DE blocker exists | yes (canonical chosen quotient) but its Label/Value types are free | E06~ F07~ | dichotomy (conditional) | 118; 63, 9 (nonG counterparts) |
| 114 | `exactCubicBaselineBudget` | 204 | cubicBaselineBudget <= (2n)^e3 and (n-1)^e3 <= budget * (2(delta+1))^e3 | yes (function of n, delta) | G01 G06~ | bound | 115, 116 |
| 115 | `incrementalSkeletonRoom` | 205 | skeletonBudget <= cubicBaselineBudget * n^(m - e3) and 2(m - e3) <= sigma + 2 | yes (function of n, m) | G01 G05 H09 A02 | bound | 110, 116 |
| 116 | `skeletonDominates` | 206 | ∣Skeleton(n,m)∣ = skeletonBudget and every map from skeletons into a State type has range <= skeletonBudget | class-level: depends only on G's (n,m); universal over abstract State types | G01 G06~ G05 | bound | 110, 112 |
| 117 | `pairOverlapSystem` | 401 | Canonical pair-overlap system: first failure, connected response supports per pair, ranking, failed family (rank < index+1) with no realizing order in the skeleton-response model | yes | D05 F04 F03~ | decomposition | 118, 119 |
| 118 | `pairConditionalFactorization` | 412 | Canonical overlap system satisfies ConditionalFactorization (product-code and componentwise concatenation) | yes | G05 D05 | identity (product code) | 119 |
| 119 | `pairFailureOverlap` | 402 | Canonical PairFailureOverlap: factorization, inclusion-minimal obstruction family, overlapping pair, connected overlap support | yes | D06 F03 F04 B08 D05 | decomposition (minimal obstruction) | 120, 123 |
| 120 | `pairDemandReturns` | 405 | Canonical demand returns: two distinct active demands d_p,d_q of the failed pair, their canonical return paths, l_ret = max of their lengths | yes | B09 C02 | decomposition | 123, 125 |
| 121 | `pairSystemRealizability` | 414 | Canonical returns exist and Nonempty (PairSystemRealizabilityOutcome): early outcome or serial system | yes | C13~ C11~ | classification (coverage) | 123-127 |
| 122 | `typeBFanEntry` | 270 | Type B fan entry: a lane support with nonempty high centres, OR surplus above and a same-token handoff / a pair-obstruction handoff at the canonical returns at canonicalPairObstructionSupport | yes | D03 A06 B08 D08 | classification (entry) | node [65]; derived from 123 by typeBFanEntry_of_pairObstructionHandoff |
| 123 | `pairSystemEarlyOutcome` | 415 | Nonempty PairSystemEarlyOutcome at canonical returns: targetCycle (accepted cycle) or typeB (PairObstructionHandoff: routes of maximal common prefix inside U, first separator h, envelope with core {d_p,d_q}, escape) | yes | D03 C13 B08 D06 D08 | classification (exclusion of targetCycle, surviving typeB) | typeBFanEntry (122); pairObstructionHandoff_of_pairSystemEarlyOutcome |
| 124 | `pairSystemNoEarlyOutcome` | 1606 | At canonical returns NOT Nonempty (PairSystemEarlyOutcome): serial arm of [179] | yes (literal negation of 123) | bookkeeping | bookkeeping (branch negation); contradicted by 127 | 125 |
| 125 | `pairSerialDemandSystem` | 416 | Canonical serial demand system: cells, interfaces, G-paths per length, internal disjointness, closing length = backward route + 2, bounded increments, every choice realizes an actual cycle of G | yes | C11~ C13 C01 F08~ | decomposition (serial corridor) | 126, 127; arithmetic then contradicts 1 |
| 126 | `pairIncrementCovered` | 417 | Canonical serial system has Nonempty (PairIncrementOutcome): full-modulus arithmetic input (free base, modulus, smear, frequent set) OR early outcome | mixed: early constructor G-only; arithmetic constructor carries data fields (modulus, smear, base, frequent) nothing constructs from G | C04~ F08~ C11~ | classification (coverage) | 127 |
| 127 | `pairIncrementEarlyOutcome` | 418 | Canonical serial system has Nonempty (PairIncrementEarlyOutcome): typeB, the handoff at serial.returns | yes | bookkeeping | bookkeeping: its constructor typeB is the typeB constructor of 123 (same returns), unit rule | end of increment arm |
## Arm keys and subtype-only keys

The two subtypes in `Assembly/Residuals/PairTypeBOutcome.lean` (`independentSystem`, `dependentSystem`) are the generic residual plus extra keys. Their extras are listed here because they fix which alternatives of facts 66/67/99 are live. They are not among the 127 rows.

| Subtype | Extra keys | Statement at G | About G only? |
|---|---|---|---|
| independentSystem | `independentPairFamily` | exists canonical activation with NO blocked pair (not HasSparsePairBlocker) on the full schedule | yes |
| independent* | `freePairCodeUnrealized` | at the canonical activation, spine family and baseline realization: no blocker on codeSchedule, |codeSchedule| = C(sigma,2), NOT 2^(|spine|+|Pi|) <= skeletonBudget, Pi nonempty | yes |
| dependent* | `dependentPairFamily` | same activation, some scheduled pair has a blocker (Pi_blk nonempty) | yes |
| dependent* | `pairDegreeProfileFibres` | for every AttemptedQuotient of the pair family and SparsePairDetermination: identified coordinates lie in one boundary-degree fibre | no: forall AttemptedQuotient (free label data, ReplacementSupport field) |
| dependent* | `pairNoProfileObstruction`, `pairNoResponseObstruction` | no scheduled pair has a type-(d) / type-(e) obstruction at the canonical activation | yes (type (e) uses attempted quotients only through its definition) |
| dependent* | `blockedPairNoExit` | not (DeclaredSparseSurplusExit): none of exits (a)-(e) | mixed: as fact 100 ((c),(d) nonG) |
| dependent* | `canonicalBlockerRoute`, `canonicalPairLedger`, `capacityTokenLedger` | survivor and a blocked pair with canonical blocker; blocked/unblocked partition identities; canonical capacity and its ledger spec | yes (survivor part mixed) |
| dependent* | `blockedPairEntropySetup`, `blockedPairCountFails`, `blockedPairCodeUnrealized` | |codeSchedule| = C(sigma,2); NOT 2^(|spine| + |free side|) <= skeletonBudget; free side nonempty | yes |
| *System | arm key 123 | as Table 2 | see rows |

## Gaps ranked

Rank = number of Table-2 facts already on the residual that would enter an inequality, identity or decision with the coordinate once it is measured. Ties are broken by nearness to the defining failure (the pair-code count and the obstruction handoff). `~` coordinates are ranked below with the same measure.

| Rank | Coordinate | Present at G because | Missing observable and certificate | Technique | Existing facts it would combine with (count) |
|---|---|---|---|---|---|
| 1 | H07 Flow-cut structural support | the canonical charge (89) with load counts (70-73) and partition (91). | integral flow (or Hall violator / deficient cut) in the pair -> token network of the canonical capacity charge at G: demands = the C(sigma,2) scheduled pairs, supports = tokens of the carrier (∣T∣ = 4n+3sigma+3w∣P0∣-2(w-1)∣P0∣), eligibility from the recorded blockers. Certificate: a flow saturating all demands, or a cut whose deficiency lifts to a set of graph incidences (equivalently the overloaded token of 72/95 as the violating side). | T14 (T10 for the cut) | 26, 69, 70, 71, 72, 73, 74, 75, 77, 78, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 106, 108 (22) |
| 2 | H03 Connected negative support | 122 fixes (Y,H) with high H; 123 fixes the envelope. | net charge (deficit - surplus + order, i.e. the linear form of H01) of the Type B support (Y,H) = canonicalPairObstructionSupport, with Y the core {d_p,d_q} extended by the envelope and H the assigned high centres. Certificate: `TypeBBridgeDeficitBoundAt` for this lane, i.e. a connected region with negative charge or a bound sigma(H) >= deficit(Y). | T13 with T04/T10 | 16, 24, 25, 31, 46, 50, 51, 52, 53, 59, 61, 62, 64, 68, 79, 83, 88, 111, 119, 122, 123 (21) |
| 3 | B06 Boundaried graph type | U is a connected support (119) containing d_p.2, d_q.1 and the separator (68, 123); `SupportAtom.decomposition object U` exists. | boundaried type of G[U] for U = overlapSupport(family): ordered boundary terminals of U, their degrees inside U, the crossing-edge incidence to G - U (identity/bound ∣bdry U∣, deficit(U)). Certificate: identity on boundary size and degree profile, composable with the contexts of 10 (only G - U). | T05 (T16) | 10, 22, 24, 25, 27, 38, 50, 68, 81, 101, 112, 117, 119, 120, 122, 123 (16) |
| 4 | G03 Conditional information of local tests | 110 and 112 give only the joint count failure. | log2 of the conditional fibre sizes of the failed pair coordinate given its exposed prefix (`conditionalFibre`, `fibreValues`, `refinedFibre` are fields/defs of the overlap system 117 but no fact states a count). Certificate: additive cost or detected correlation making the failure of 110 a statement about the last coordinate. | T12 (T11) | 93, 97, 98, 109, 110, 112, 114, 115, 116, 117, 118, 119 (12) |
| 5 | H10 Finite demand descent | 112 (indexed prefix with realizedThrough), 91 (C(sigma,2) demands). | well-founded measure on the pair schedule (∣Pi∣ minus the first-failure index of 112) with one-unit peel steps that keep the response invariant; termination at the classified state 'obstruction handoff'. Certificate: strict descent lemma per removed pair. | T19 (T14) | 91, 93, 99, 106, 108, 110, 112, 115, 117, 119, 120, 125 (12) |
| 6 | D09 Gluing realizability | decomposition/reconstruction objects exist (ActualContext.actualGlue_hom) but no ledger fact. | uniqueness/injectivity of the reconstruction of G from (G[U], G-U, boundary identification) at the obstruction support U, and compatibility of the swapped readings. Certificate: injective reconstruction, as required before the local counts 114-116 are multiplied. | T05/T15/T16 | 10, 22, 109, 112, 114, 115, 116, 117, 118, 119, 123 (11) |
| 7 | C07 Cycle-space interaction | h has degree > 3 and two arms (68, 123). | binary incidence vectors of the cycles closed by the two entry arms at the first separator h (theta with the core edge / connector) and their symmetric difference. Certificate: a cancellation relation or support decomposition. | T08/T11 | 20, 21, 29, 30, 33, 34, 35, 56, 68, 123, 125 (11) |
| 8 | D07 Symmetry and equal response | 119, 123 fix an ordered (leftDemand, rightDemand) and (nextFirst, nextSecond); the handoff conditions (SameTokenHandoffConditions) are symmetric in the two arms | role-swap of the two demands (d_p,d_q) and of the two next vertices (a,b) of the separator; certificate: canonical swap/orbit reduction, so that leftDemand/rightDemand ordering does not create two cases. | T16 (T09) | 36, 37, 68, 75, 77, 119, 120, 123, 125 (9) |
| 9 | E08 Peelability | 112: realizedThrough gives that every shorter prefix of the failed family still fits the budget | removable unit: last pair of the failed prefix; certificate: shorter ledger and terminating descent (companion of H10). | T19 | 91, 99, 108, 110, 112, 115, 117, 119 (8) |
| 10 | C06 Ear structure | 120, 125: ConnectorRoutes forward/backward are paths attached to the connector at their ends | ear decomposition of the connector / G[U] relative to a base cycle through d_p, d_q; forward/backward ConnectorRoutes (120, 125) are the ears' candidates. | T04/T08 | 23, 34, 68, 103, 107, 120, 123, 125 (8) |
| 11 | F06 Cancellation and repair structure | 117, 119: the failed family has no realizing order, i.e. a composite response relation exists | composite response relation among the failed family and its repair support inside U. | T10/T11 | 75, 77, 81, 113, 117, 118, 119 (7) |
| 12 | I02 Isomorphism and canonical representative | 38, 39 quantify over every placement q of a window, and the two reversed placements give the same window | canonical representative of a window placement (q vs reversed q) and of labels; 38, 39 quantify over every placement. | T16/T17 | 14, 38, 39, 80, 114, 116 (6) |

Ranking of the `~` coordinates by the same measure: B04 (8: 19, 23, 29, 30, 36, 37, 68, 123), A07 (8: 5, 31, 47, 50, 55, 57, 62, 88), D10 (8: 6, 7, 18, 19, 20, 21, 65, 82), D04 (7: 70, 71, 72, 73, 92, 95, 96), C11 (6: 68, 120, 121, 123, 125, 126), H04 (6: 69, 71, 73, 74, 78, 92), G06 (6: 109, 110, 112, 114, 115, 116), E06 (5: 10, 81, 100, 109, 113), F07 (5: 109, 110, 113, 117, 119), A12 (5: 8, 50, 83, 86, 111), G04 (5: 70, 71, 72, 92, 95), F08 (4: 112, 120, 125, 126).

Ties: H10 and G03 combine with 12 facts; D09 and C07 with 11; D07 with 9. H10 and G03 are ranked above D09 because they act on the count failure of 110/112 that defines the residual, while D09 acts on the local counts 114-116; D09 is ranked above C07 because those local counts enter the count failure of 110.

What the top of the ranking says for a closure attempt: the residual's arithmetic (facts 69-98) is a demand-supply system over pairs and tokens with no flow/cut certificate (H07), and the strict-surplus lane it exits into (122) is not given a charge (H03). The structure that connects them is the boundaried type of U (B06), which is also what the arbitrary-context facts 9-12 and 63 try, and fail, to say about G.

## Non-G facts

Each fact that uses an object outside G, the object, and the G-constructed replacement (the missing accounting).

| Fact | Non-G object | What is G-only inside it | G-constructed replacement |
|---|---|---|---|
| 1 selection | minimality clause: `forall smaller : FiniteObject` (lex order and refined order) - other graphs | not (HasCycleWithLength) at G | proper-subgraph exclusion (5) and the canonical swap of G at Z (subgraph of G, `ActualContext.swap`, `swapDeficit`) |
| 2 cubicBaseline, 15 localAlgebra | registered parameters and finite label table (not a graph fact); 15 ignores its object | HSS law at G and G[S] (2) | alphabet realised at G's windows: fact 39 lands in the table; add the count of labels attained at P0's windows |
| 9 degreeProfileFibres | forall CurvatureQuotient: free Label/Value/label/value; `properRepresentative` carries ReplacementSupport (arbitrary piece), `closedRepresentative` an arbitrary smaller graph | none | boundary-degree fibres of G's own readings at U (`readingProfile`, ResidualProfileSeparation at G's pair family); canonical mixed quotient (113) |
| 10 targetCompleteContextUniversality (conjunct 1) | forall quotient (as 9) | conjunct 2: actualGlue G Z X (subgraph of G) has no accepted cycle | conjunct 2 already is the G-form (`actualGlue_agree`) |
| 11 replacementExclusion, 12 uncompressible | arbitrary `BoundaryPiece` X' and the graph `glue X' (G-Z)` (a graph that is not part of G); 12 is `Iff.rfl` to 11 | none | swap of G at Z: for every proper connected Z with no proper baseline subgraph (5), the swap has a vertex of degree < 3 (`swapDeficit_isSome_of_noProper`); this is what should replace `repl support replacement` in `pairChain_outcome` |
| 63 admissibleQuotientsLabelInjective | forall DeclaredQuotient (free data, ReplacementSupport, arbitrary smaller graph) | none | rank of G's actual wedge family of R (`remainderCurvatureTests`, card W2(R)) or of the canonical mixed family (113) |
| 81 responseObstructionTargetDefect | existential `AttemptedQuotient` (free label data) | exclusion of every response obstruction (via empty ResidualTargetDefect) | state directly: no DE response obstruction at G (already available as `pairNoResponseObstruction` on dependent paths) |
| 100 sparseSurplusSurvivor | clause (c) `compression` (arbitrary X' via ReplacementSupport) and clause (d) `delocalization` (arbitrary smaller `representative : FiniteObject`) | clauses (a), (b), (e) | swap of G at Z as for 11; for (d) the closed case Z = V(G) is minimality (1) |
| 109 baselineSpineDemand | `Coordinate : Type u`, `family`, `coordinateSupport` chosen by `Classical.choose`; forall DeclaredQuotient; a spine family is only constrained by its cardinality inequality | skeleton budget inequalities | the actual wedge/curvature family of G (`internalWedgeFamily` of R, card W2(R)) with its realization |
| 126 pairIncrementCovered | arithmetic constructor: `PairSerialArithmetic` fields `base`, `modulus`, `smear`, `frequent`, `increment`, `wide`, `criterion`, `spanning` - free numbers constrained only by memberships in `serial.lengths`/`offsets` and an order condition on 2 mod modulus, nothing constructs them from G | early constructor (G-only), serial system (125) | the modulus/increment of G's own corridor: the actual set of piece lengths of the canonical serial system (125) and its spectrum; only needed if the increment arm were live (it is contradicted, finding 2) |
| 116 skeletonDominates (borderline) | class-level count of Skeleton(n,m) and forall State type: depends only on G's n and m, not on a witness on another graph; kept as G-parameter count | - | no replacement needed; note that G01 counts a class by definition |

Definitions checked on the path for free data fields (nothing constructs them from G): `CurvatureQuotient`/`DeclaredQuotient` (Label, Value, label, value), `AttemptedQuotient`, `ReplacementSupport`/`CompressibleSupport` (the piece X' is an arbitrary `BoundaryPiece`), `SparseSurplusExit` (compression, delocalization), `DeclaredCoordinateFamily` (Coordinate type), `PairSerialArithmetic` (base, modulus, smear, frequent), `PairOverlapFirstFailure` (Coordinate type and baseline family, but they are fixed by `canonicalBaselineSpineFamily`). Checked and found G-constructed: `PairDemandReturns` (all data derived from the failed pair), `PairSerialDemandSystem` (G-walks; `lengths` are constrained by the realized cycles), `PairObstructionRoutes/Separator/Envelope` (canonicalChoice over G's overlap support), `ActiveSurplusDemands` (Prop about G), `actualGlue` (subgraph of G).

## Structural findings from reading the statements

1. **Increment arm contradiction (124 with 127).** `PairIncrementEarlyOutcome serial` has the single constructor `typeB`, whose field `PairObstructionHandoff ... serial.returns` is the field of the `typeB` constructor of `PairSystemEarlyOutcome serial.returns`. `canonicalPairSerialSystem` is defined with `system.returns = returns`, so `canonicalPairDemandReturns = some serial.returns`. Hence 127 implies `Nonempty (PairSystemEarlyOutcome returns)`, the negation of which is 124. The subtypes `independentIncrement` and `dependentIncrement` are therefore inconsistent as stated; the [179] serial arm and the [180] periodic arm are not disjoint routings of the paper. (Not machine-checked; no build was run.)
2. **Vacuity of 66 and 67.** As stated in the header; they add no certificate on any of the four paths.
3. **Fact 99** has its left disjunct false on all four paths, so on this residual it reduces to `PairOverlapFirstFailure` and (uncovered residual or handoff with Type B entry), which are 112 and 122/123.
4. **The early outcomes name only objects of G.** `PairSystemEarlyOutcome` has the constructors `targetCycle` and `typeB`, and `PairIncrementEarlyOutcome` the constructor `typeB`. `pairObstructionHandoff_of_pairSystemEarlyOutcome` excludes `targetCycle` by selection (fact 1), G-side; `pairSystemEarlyTypeBEntryRow` requires no replacement exclusion.
5. **Two charges of the same demands.** 91 (basic canonical charge, blocked + free) and 69/70 (extended charge Theta_ext, Pi_free^ext empty) partition the same C(sigma,2) pair demands under different charges; they must not be added (unit rule).

## Cross-check results

1. Every coordinate code in Table 2 (plain or `~`) has status `x` or `~` in Table 1 and lists the fact: **PASS**. Coordinates touched only with `!` are `nonG` in Table 1 unless a G-only fact also touches them (then the nonG row is listed in the `nonG-touch` note).
2. Every `x` or `~` in Table 1 cites at least one Table-2 row: **PASS**.
3. Every Table-2 row accounts for at least one coordinate or is labelled `bookkeeping`: **PASS**. Bookkeeping rows: [66, 67, 124, 127] (66, 67 vacuous implications; 124 branch negation; 127 constructor subset of 123). Rows that touch coordinates only through nonG marks (they account for no coordinate but are not bookkeeping): [9, 11, 12, 63].
4. Unit rule (no fact counted twice for the same demand in different currencies): **PASS with notes**. Identical-content duplicates are listed once in effect: 12 duplicates 11 (both nonG), 105 duplicates 83 (A02/A05/H01 already `x` without 105), 127 is a subset of 123 (bookkeeping). The pair-deficit inequality is stated at several presentations (71, 74, 78, 92, 93, 96): one demand in one currency (pairs against certified token capacity), cited for H05 and H09 as two observables of one inequality, not two payments. 69/70 and 91 are two charges of the same demands (finding 5): they are not summed anywhere on this residual.

Counts check: Table 1 has 88 rows (x 58, ~ 12, gap 12, n/a 1, nonG 5); Table 2 has 127 rows.

## Outside the register

None forced. Two observables sit at the edge of the register and were mapped to the nearest row, with the caveat stated in the Table-1 row: (1) canonical-choice functionality (`canonicalPairDemandReturns` is `Option`-valued, so 'the same returns' in 124/127 is an equality of options) mapped to D08; (2) class-level entropy counts of the labelled skeleton class at G's (n,m) mapped to G01.

## Technique register (reference)

| Code | Technique | Standard move |
|---|---|---|
| T01 | Direct invariant calculation | Apply degree sums, incidence identities, or rank identities. |
| T02 | Extremal selection | Choose a smallest counterexample and exploit strict descent. |
| T03 | Local graph modification | Delete, suppress, split, glue, or replace a local piece. |
| T04 | Core and connectivity decomposition | Peel low-degree vertices or decompose into components, blocks, cuts, and ears. |
| T05 | Boundary-interface analysis | Mark terminals, record boundary data, and compare outside contexts. |
| T06 | Maximal packing | Pack disjoint witnesses and study the excluded remainder. |
| T07 | Local configuration analysis | Classify bounded neighborhoods, attachments, fans, and paths. |
| T08 | Path–cycle and cycle-space analysis | Root cycles, combine paths, add ears, or take symmetric differences. |
| T09 | Arithmetic of lengths | Use parity, congruences, sumsets, intervals, or periodicity. |
| T10 | Uncrossing and minimal obstruction | Choose a minimal failure and uncross its intersecting supports. |
| T11 | Linear-algebraic rank | Encode local tests as coordinates and extract a basis or circuit. |
| T12 | Counting and information | Use labelled enumeration, pigeonhole, conditional counting, or entropy. |
| T13 | Potential and discharging | Define charge, redistribute it locally, and isolate overload or negative support. |
| T14 | Demand–supply and flow | Use an incidence network, matching, alternating paths, or flow–cut. |
| T15 | Double counting and injection | Partition contributions, control multiplicity, or reconstruct injectively. |
| T16 | Symmetry and canonicalization | Choose canonical representatives and break equal-size ties. |
| T17 | Finite exact certification | Enumerate a finite state space and retain a checkable certificate. |
| T18 | External structural theorem | Invoke a fixed classification or exclusion theorem with exact hypotheses. |
| T19 | Peeling and finite descent | Remove one certified unit while preserving a decreasing invariant. |


## Handoff facts (rows 128-130) and the closed increment arm

1. *The `[180]` increment arm is empty at G (Lean improvement: `[180]`'s periodic alternatives are empty after `[179]`'s no-early arm).* Facts 124, 125, 126 and 127 (`pairSystemNoEarlyOutcome`, `pairSerialDemandSystem`, `pairIncrementCovered`, `pairIncrementEarlyOutcome`) are on no returned residual: `K .pairIncrementEarlyOutcome` is incompatible with `K .pairSystemNoEarlyOutcome` (`not_pairIncrementEarly_of_noEarly`). The root returns the subtypes `independentSystem` and `dependentSystem` only; the fact 126 nonG item (free fields of `PairSerialArithmetic`) is not on the residual. The generic residual ends with fact 123 as a plain conjunct (`pairSystemEarlyOutcome`, no disjunction).
2. *G facts (Table 2 rows 128-130), published with `K .typeBFanEntry` by the `[179]` early row:*

| # | Key | idx | Statement at G | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 128 | `pairHandoffSupport` | 8350 | canonical support of the obstruction handoff is (Y,H) = ({d_p.2,d_q.2},{h}), h the canonical first separator; H nonempty and high; Y and H lie in the overlap support U | yes | B06~ D07~ H03~ | decomposition | 129, 130 (and the Type B lane test) |
| 129 | `pairHandoffCharge` | 8351 | core ends are cubic port ends (sigma(Y)=0), Y and H disjoint, omega(H)=d(h)-delta >= 1 | yes | A05 A11 H03~ | identity, bound | 130 |
| 130 | `pairHandoffNetCharge` | 8352 | 1<=|Y|<=2; (delta-1)|Y| <= def+(Y) <= delta|Y|; envelope negative charge, or omega(H) < def+(Y) so d(h) < 3 delta | yes | H03~ A11 | bound (exact dichotomy) | Type B lane certificate cap (not routed) |

3. *The obstruction is an aggregate count, not a class member.* `RealizingOrder` (the obstruction of facts 117-119, and `not ConditionalFactorization`) is stated in the aggregate form the counting consumes: the number of realized (baseline word, prefix) signatures of G's labelled (n,m) class doubles at every level (`N_{|F|} = 2^{|F|} N_0`); a failure is the numerical inequality `N_{|F|} < 2^{|F|} N_0` about G's class count. The derivation of the obstruction from the first failed extension (fact 112) goes `|Baseline| 2^{|F|} <= N_{|F|} <= |Skeleton|` directly (`Contracts/SurplusPair/PairOverlap.lean`).

**Table 1 contribution of rows 128-130.** H03 `~` (facts 128-130). A11/B06 have a partial contribution (128-130) and their `~`/`gap` marks from Table 1 (the boundaried type of G[U] is not built). The aggregate signature counts N_k are the definition of `RealizingOrder`; G03 (conditional information) is `~` by row 133 (below).

**nonG items.** 1 (minimality: legitimate by the current rule), 2/15, 9, 10 (conjunct 1), 11, 12, 63, 81, 100 (c),(d), 109 remain; they are shared with other residuals (entry prefix, sparse-exit survivor). 124-127 are on the empty increment arm.


### Handoff facts at the hub h (rows 131-135)

Keys 8353-8357, published by `pairHandoffFactsRow` after the early row (statements `Statements/PairHandoffFacts.lean`, contracts `Contracts/Spine/PairHandoffFacts.lean`; each choice is the `canonicalChoice` of its spec or fixed by G's data):

| # | Key | Statement at G | Coordinates | Certificate |
|---|---|---|---|---|
| 131 | `pairHandoffHubCharge` (8353) | every pair of the obstruction family has an extended charge in the canonical capacity's tokens (integral flow); if the pair-deficit coefficient is positive the canonical overloaded token and its charged pair set are a Hall violator (`load > M0`) | H07~ H03~ | flow, cut |
| 132 | `pairHandoffBoundaryType` (8354) | boundary vertices of U, `e(U,G-U)` as their deficit sum, `e(U,G-U) + sum_U d_U = delta|U| + sigma(U)`, `sigma(U) >= 1`, and the response of every reading of U glued into `G - U` has no accepted cycle | B06~ A11 A10 | decomposition, identity |
| 133 | `pairHandoffCriticalCoordinate` (8355) | for every exposure order of the obstruction family some level has `N_{k+1} < 2 N_k` (uses the level bound `N_{k+1} <= 2 N_k`) | G03~ | bound |
| 134 | `pairObstructionDescent` (8356) | `2 <= |U-family| <= |Pi|`, the family is not realizing, every one-step peel is realizing | H10~ | descent measure |
| 135 | `pairHandoffHubForces` (8357) | at the canonical first separator h: vertex split forced, same-vertex switch, endpoint switch at cubic neighbours, length-3 fan and chain 3,3,3 | D07~ C06~ C07~ | classification |

Facts `pairArmAPattern`, `pairArmARoleAlphabet` are not facts of this residual (vacuous on both returned paths).


### Rows 131 and 133 at the handoff

Row 131 `pairHandoffHubCharge` (8353): each pair of the obstruction family is charged to the port token of one of its own ports (high centre); `h` has `d(h) - delta` port tokens; the pairs of the family charged at `h` are at most `sum over h's ports of newLoadBound`. Coordinates: H07~ (flow-cut restricted to h's tokens; no global Hall-violator token), H03~.
Row 133 `pairHandoffCriticalCoordinate` (8355): every coordinate of the obstruction is critical (deficit exactly at it in the order exposing it last); canonical members with `h`, `nextFirst`, `nextSecond` in their supports exist. Coordinates: G03~ (fibre-size count at the coordinate h decides), H10~.


### Rows 136-138

Row 136 `pairHandoffDemandEnds` (8358): endpoints of the ports of 𝒰's pairs lie in their response supports and in U; cubic; centres high. Coordinates: B06~ D07~.
Row 137 `pairHandoffHubBalance` (8359): conjunction of rows 128-130 (8352), 131 (8353), 135 (8357) with the combined bound (negative charge, or d(h) < 3 delta, fewer than 2 delta tokens, load at most (2 delta - 1)((|H|-1)+sigma)). Coordinates: H03~ H07~ A05.
Row 138 `pairHandoffFibreAtG` (8360): G's own member of the class has all responses negative; for the canonical member pi_h whose support contains h, in the order exposing it last, G's fibre has 1 or 2 extensions. Coordinates: G03~ E06~ (repetition at G).
