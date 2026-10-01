# Structural accounting: `Node144aOutcome`

> Coverage: partial. The generic `Node144aOutcome` has 135 facts; this report accounts 130. Not accounted: the generic keys `sameTokenWalkWindows`, `sameTokenWalkExchange`, `sameTokenW0Escape`, `sameTokenCrossingCount`, `sameTokenHubCount` (9850-9854), and, among the subtype extras of the three `*Fails` subtypes (+18/+19/+20), `sameTokenPathInteractions`, `sameTokenLadderCount` (8106-8107), `sameTokenWalkAttachment` (9990), `sameTokenSeparatorExcluded` (9991) and `sameTokenTriArmEmpty` (9855: the sub-arm W ∧ Tri ∧ EndEdgesFree is empty at G). The Table 1 status counts do not include these keys. Fact list compared with the `Holds` conjuncts of the Lean abbrevs in `Assembly/Residuals.lean` and `Assembly/Residuals/`.

**Branch/worktree:** `/home/guillem/hs-wt-S144a`. Read-only; no Lean edited, nothing built.

**Defining failure.** The entry test "pair unresolved" (`SameTokenPatternPairUnresolvedStatement`, `Graph/Statements/SurplusPairRouting.lean`) is `profile(X_p at Z) != profile(X_q at Z)` OR `HasCycle(actualGlue G Z X_p) <-> HasCycle(actualGlue G Z X_q)`, at the canonical routing pair `r_p != r_q` and `Z = select?(X_p u X_q)`. `actualGlue G Z X` is a subgraph of G (`actualGlue_hom`) and G has no accepted cycle, so both sides of the iff are false: the second disjunct is true for every pair at G, and [144a] is reached through a trivially true disjunct. The paper's replacement (swap the interior of one port's piece for the other's inside `Z`, equal interior size, then compare the canonical degree deficit) is not constructed at G. What exists is (i) `SameTokenSwapExact` (130: deletion of the private edges of the swap), (ii) the strictly smaller transplant `G - D`, `D = int(Z) \ Y`, with its exact conditions and canonical deficit vertex (R5: 140 `sameTokenTransplantSize` idx 8000, 141 `sameTokenTransplantDeficit` idx 8001).

**Scope and fact count.** 130 facts are in the generic `Node144aOutcome` conjunction (rows 1-130; the abbrev and the template script give 130). Rows 131-141 are the extras of the three handoff-fails subtypes (`windowFails`, `remainderFails`, `primitiveFails`): the five class facts (`windowClassOverload`, `windowClassAbsent`, `remainderClassOverload`, `remainderClassAbsent`, `primitiveClassOverload`) and the six fails facts (`typeBHandoffFails`, `sameTokenPatternUnresolved`, `sameTokenReadingsNotReplacement`, `sameTokenPairPartition`, `sameTokenTransplantSize`, `sameTokenTransplantDeficit`). Total analysed: 141. Handoff subtypes' `typeBHandoff` and `typeBFanEntry` are out of scope.

**Status counts (88 coordinates):** x = 68, ~ = 15, gap = 3, n/a = 1, nonG = 1. Rows 142-147 are the six keys 8100-8105; they account F06, B07, D07, E07 (`x`).

**Families of the common facts (rows 1-130):** entry/baseline 1-8 (`selection` ... `cycleRankConstraint`); quotient/replacement 9-12; windows and packing 13-17; switches and forced paths 18-21; pair supports and cut capacity 22-26; cycle counting 27-34; local rigidity 35-38; hubs, links, remainder and joint bounds 39-59; surplus identities and orders 60-64, 78, 82-87; pair arms 65-67; extended charge and free side 68-77; window charge 79-81; canonical capacity and certification 88-98; suppression 99-103; sparse survivor chain 104-123; bridgeless, normal form, routing 124-130.

**Non-G marks (Table 2, column 5):** 17, 20, 101, 103 (and the G/Q clause of 100). Everything else, including every `actualGlue` fact (a subgraph of G) and the transplant (`G - D`), is a fact about G.

**Note on the unit rule.** 82 (`edgeSurplusIdentity`), 104 (`sparseSlackSurplus`) state the same identity 2m = 3n + sigma; it is counted once for A02/A05/H01.

Status legend: `x` accounted · `~` partially accounted · `gap` present at G but unaccounted · `n/a` absent at G (reason required) · `nonG` accounted only through an object outside G (does not count).

## Table 1 — Structural coordinates (same for every residual)

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 16, 84, 89, 140 | identity/bound n vs nu, scale, transplant int(X')=int(Z) | T01 T12 | - |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 49, 82, 85, 104, 117 | identity 2m=3n+sigma; m+2<=2n; m+4<=2n; density excess | T01 | 81: 82 and 104 are one identity, counted once |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 3, 6, 7, 41, 53, 64 | degree >=3; degree>3 vertices independent; tight endpoint; hub classes | T01 T07 | - |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 3, 7, 18, 39, 130, 141 | delta>=3; endpoint degree 3; kept degree <3 at canonical v (141); w with degree <=2 in swap (130) | T01 | - |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 30, 42, 45, 54, 56, 58, 60, 61, 63, 64, 82, 86, 87, 104, 105 | sigma=sum(d-3) with identities, /H/<=sigma, slot and pair-sum inequalities | T01 T13 | - |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 40, 44, 52, 54, 56, 57, 59, 72, 86, 87, 125 | high vertices pairwise nonadjacent; 2-hop and length-3 links; hub bounds | T07 T13 | - |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | ~ | 5, 117 | only the top core: no proper subgraph has min degree 3 (5) and m+2<=2n (117) | T04 | Core/peeling of G-D for the transplants (D = int(Z)\Y): the 3-core of G-D and its peeling order are unmeasured, although 141 exhibits the first deficient vertex; needed certificate: decomposition (peeling sequence of G-D). |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | - | excluded by 3: every vertex of G has degree >=3, so G has no degree-2 vertex and no degree-2 chain | T04 | Not applicable at G; degree <=2 vertices of G-D appear only in the subgraph G-D (see A07) |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 27, 30 | nonadjacent neighbour pairs of every vertex; pair sums; length-3 pairs; separated pairs | T01 T12 | - |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 23, 24, 37, 53, 117, 139 | crossing counts e(R,W), window/remainder incidences, reading counts at bdry(Z) | T01 T05 | - |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 23, 139, 140, 141 | def+(R)<=e(R,W); reading count +1 <= deg at each boundary vertex; kept degree of the canonical deficit vertex | T05 T13 | - |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | 2 beta(G) >= n+2 (8) | T01 | Proved but never combined: no fact of [144a] enters 8 with another currency; cycle rank of G[Z] and of G-D not measured |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 8, 49, 50, 85, 117 | linear slack of m in n at G (8,49,50,85,117) | T01 T13 | - |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 54, 56, 61, 64 | exceptional set H bounded: /H/<=sigma, 5/H/+sigma<=2n, 2/B/+sigma<=n; case (deg>=5 or two deg 4) | T01 T13 | - |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | ~ | 5, 31, 129, 139 | G connected; Z, X_p, X_q connected; G-h components (5,31,129,139) | T04 | Components of G-Z and of G-D (the rest and the removed set of the transplant) are not stated; certificate: decomposition of G-Z and of D |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 49, 124 | bridgeless; two-edge cut of every nonempty proper set (contains Z) | T04 T01 | - |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 26, 31, 32, 33, 139 | cut vertices/blocks: G-h decomposition, block paths, 2+2 single-boundary shape, U2 boundary cut vertices of Z | T04 T05 | - |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 140 | linkage inclusion (140): internally disjoint bdry-to-bdry linkages of the transplant are realized in G[Z] | T05 T08 | Menger number between boundary vertices of Z in G[Z] and in G-Z; certificate: bound on disjoint boundary paths, needed to compare Xp-linkages with Xq-linkages |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 26, 139, 140 | boundary of Z: cut boundary, reading counts c_X(b), transplant boundary conditions | T05 | - |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | x | 9, 11, 111, 112, 137, 138, 139, 140 | boundary-degree profile fibres (9,111); profile of the two readings at Z (137,138,139); profile iff no boundary neighbour in D (140) | T05 | - |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10, 62, 113, 137, 139, 140, 144 | G-only response of a reading (constant, 142); response of the swapped object: every accepted cycle of glue(S)(G-Z) uses a vertex of int(Z) n Q\P as itself and as its copy (swap_cycle_double_use, in 144); linkage inclusion gives target-free glue | T05 T16 | - |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 22, 129 | minimum connected support Z of X_p u X_q; connected supports of pattern pairs | T10 | - |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 37, 140, 141 | demand 3 at each kept vertex vs supply of neighbours outside D (140 (ii), 141); window stubs | T05 T14 | - |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 18, 19, 21, 33, 44, 46, 55, 59, 81, 102, 106 | forced simple paths of prescribed accepted length after switches; two-hop and block paths; open-port and return witnesses | T08 | - |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 106, 124, 147 | return lengths disjoint from shifted accepted set at every dart; return path R_p; bridgeless | T08 | - |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 10, 32, 34, 46 | no accepted cycle in G or in any actualGlue; cycle counts and double count | T08 T12 | - |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 4, 18, 19, 21, 28, 29, 33, 38, 55, 102 | accepted length = 2^k-1: switch closures, star/meeting constraints, parity, residues mod 4 | T09 | - |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 19, 28, 29, 35 | theta-type configurations: star and meeting constraints, cross-switch pair, length-3 fan | T08 | - |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | ~ | 147 | the port paths R_p (shortest, induced in G-cx) and Q_p as supports of the seed cover; each interior cubic vertex has exactly one stub; same-path chords have unaccepted span (147) | T08 | Attachment of the stubs only at path ends (an ear decomposition over the base G[X]) is not stated; the stub structure is |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | gap | - | Present at G: the two ports p,q have distinct return cycles (106, 126) with E(R_p) != E(R_q) (137: r_p != r_q); no fact measures their symmetric difference. | T08 | Observable: binary incidence vectors of the return cycles of p and q in the cycle space of G[Z]; certificate: identity for the symmetric difference and its length parity (with 55). |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 47, 48, 147 | induced P13 present; window-free remainder; attachments | T07 | - |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 16, 45, 52 | packing number nu with 13 nu <= n, packing inequalities and hub/window bounds | T06 T01 | - |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 23, 46, 47, 50 | remainder R of P0: deficiency, path bounds, window-free geometry, slack | T06 | - |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | 36, 67 | chain 3,3,3 at every vertex (36); Arm B serial system (67) | T08 | Serial corridor of the pattern pair p,q (base length and increments between the two return corridors) is not stated at the canonical routing |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 37, 38, 48, 102, 106 | allowed contacts of window endpoints/interiors; cross-edge gap; open-port witness avoids the port vertex | T07 | - |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | x | 19, 29, 35, 36, 67, 140 | joint disjointness/endpoint compatibility: cross-switch, meeting paths, linkage inclusion of the transplant, Arm B realizability | T08 | - |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 37, 38, 48, 106 | attachment of outside vertices/paths to windows; triangular port triangle | T07 | - |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 13, 26, 125 | induced P13 type, 2+2 cut vertex shape, heavy neighbourhood normal form | T07 | - |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 21, 27, 28, 35, 36, 39, 40, 41, 53, 57, 65, 81, 100, 105, 107, 122, 125, 126, 128 | centres with typed neighbours, ports, fans, stars, matchings inside N(h) | T07 | - |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | x | 65, 94, 126 | role-homogeneous matching or star of size L_geom in the overloaded role fibre | T14 T12 | - |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 14, 38, 40, 43, 65, 76, 139 | overlap of X_p and X_q at bdry(Z) (U2-free/shared); ladders; free-pair support overlaps | T10 T07 | - |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 67, 139 | Z is the minimum connected set containing X_p u X_q (22,139); canonical first failure of the pair overlap system (67) | T10 | No minimal connected obstruction is exhibited for the pair p,q: certificate (obstruction) that the swap fails on the smallest connected family is missing |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 65, 100, 126, 130, 139, 144 | order-fixed equal-count contact bijection orderEquiv (k-th in G.orderedVertices to k-th) with the attachment identity of the swap copy at each boundary vertex (144) | T16 | - |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 22, 43, 79, 88, 98, 115, 129, 131, 132, 133, 134, 135, 137, 139 | canonical selections: select?(seed), Z=select?(Xp u Xq), canonical capacity, canonical blocker, overload class, canonical vertex | T16 | - |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | x | 67, 138, 140 | glue of transplant = G-D (cycle transfer), retained-reading glue conditions, Arm B forward/backward routes | T05 | - |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 64, 141 | fixed-size marked configuration: canonical deficit vertex v; deg>=5 or two deg-4 vertices | T07 | - |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1, 11 | G minimal counterexample (selection); replacement exclusion | T02 | - |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5, 140 | no proper subgraph has min degree 3; transplant smaller than Z contradicts minimality (size equality) | T02 | - |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 7, 18, 19, 21, 81, 124, 130, 140, 141 | effect of deleting edges/vertices: switches, bridgeless, tight endpoint, private-edge deletion, D-deletion with its degree conditions | T03 | - |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | nonG | - | Only 17, 101, 103 and the G/Q clause of 100 speak of safe suppression, and they are statements about the suppressed graph G/Q, which is not part of G. | T03 | G-constructed replacement: the degree of each vertex of G/Q as a closed formula in G (deg_G minus deleted neighbours plus chord ends), i.e. the inequality centerLoad(c) <= deg(c) - 3 already proved in 100 as a statement about G, with the accepted-cycle exclusion stated as a path in G-{deleted vertices} |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 130, 138, 140 | no replacement of Z exists (11,12); none among retained readings (138); transplant satisfies the four conditions exactly and cannot be smaller (140); swap dichotomy (130) | T03 T02 | - |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 62, 111 | quotients: no identification across fibres; label-injective quotients; pair determination fibres | T05 T12 | - |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | x | 11, 138, 143, 144, 145 | descent on the neutral move: a valid swap is not lexicographically smaller than G (fewer vertices, or equal vertices and fewer edges), |int Z n P| <= |int Z n Q|, both valid give equality (145, 146); readings dropping an edge are lexicographically smaller and lose the baseline (144) | T16 | - |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 141 | one canonical peel candidate v of G-D (141) | T19 | Iterated peeling of D from G until the 3-core (removal of v, recomputation of kept degrees); certificate: peeling sequence preserving the invariant |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 67, 80, 98, 99, 112, 113, 114, 128, 141 | target/response defect: none at scheduled pairs (112,113), classified obstruction outcomes (67,80,98), deficit vertex of the transplant (141) | T05 | - |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 27, 74, 105, 107, 116 | supply of tests: nonadjacent pairs, C(sigma,2) scheduled pairs, active family, ports | T07 T11 | - |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | ~ | 110, 116 | existence of a blocked pair (110) and exact counts /Pi_blk/+/Pi_free/ (116) | T11 | Rank of the response vectors of the pair family (or maximum independent subfamily) is not measured; certificate: bound |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | ~ | 115 | canonical blocker min_prec Blk(pi) of a blocked pair (115) | T11 T10 | Inclusion-minimal dependent subfamily for the same-token pair p,q (not the order-minimal blocker); certificate: obstruction (circuit) |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | x | 74, 76, 80, 129 | geometric support of dependence: declared supports, returns, T; supports X_p, X_q; response obstructions | T10 | - |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 74, 76 | separation of testers by disjoint declared supports and returns (74,76) | T05 T10 | - |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | x | 142, 143, 144, 145 | replacement: the rerouted swap S(G,Z;P,Q) built at G (fresh copy of the interior of Q in place of the interior of P, order-fixed contact bijection); conditions (i)-(iv) exact; canonical exceptional vertex swapDeficit; linkage double-use witness; size relation | T03 T13 | - |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 94, 95, 110, 114 | dichotomy free vs blocked: /Pi_free/ <= B, or overload with role-homogeneous pattern (94,95,65,126,128) | T11 T12 | - |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 33 | residues 3 and 1 mod 4 at lengths 2^j-1 for block paths (33) | T09 | Periodic response of the return family of p,q under additive increments (e.g. lengths of R_p and R_q shifted by the swap) is not measured |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 34, 108, 109, 119, 120 | labelled-class counts: #cycles<=2^m, code 2^(/spine/+/free/) <= skeleton budget | T12 | - |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 15, 25, 41, 57, 66, 89, 118 | legal states: 399 labels, ten roles, hub classes, token supply /T_cap/ | T12 | - |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 108, 109, 119, 120 | conditional information of local tests: entropy sandwich, spine deficit, setup | T12 | - |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | x | 65, 66, 94, 121, 122, 126, 127, 131, 132, 133, 134, 135 | dominant type: overloaded role fibre, class partition W/R/prim, caps | T12 | - |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | ~ | 109, 120 | joint count 2^(/spine/+/free/) vs skeleton budget (120), negation (109) | T12 | Joint state count of the pair (r_p, r_q) at Z compared with the product of conditional counts is not stated; certificate: bound |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | x | 62, 120 | injective reconstruction: label-injective quotients, code realized among labelled skeletons | T15 T12 | - |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 25, 34, 60, 68, 69, 74, 77, 89, 90, 116, 118, 121 | double-counting: token/pair ledgers, dart identity, partition of C(sigma,2) | T15 | - |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 58, 63, 75, 78, 83, 84 | asymptotic/finite thresholds: C+1<=ceil sqrt n, scale pressure, high-surplus order | T17 | - |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 16 | 13 nu <= n and window-density inequalities in the slot relation | T06 T12 | - |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 23, 24, 42, 45, 58, 60, 70, 75, 77, 82, 91, 92, 117, 141 | deficiency-surplus balances: def+<=e, slot relation, deficits G2/G3, kept-degree deficit | T13 | - |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | ~ | 79, 116 | window structure of the canonical charge; charge single-valued (79,116) | T13 | Additivity of the charge over the overlap of the two supports X_p, X_q at Z is not stated |
| H03 | Connected negative support | A connected region with negative charge. | gap | - | Present at G: Z is connected (139), Z contains the canonical deficit vertex v when D != empty (141), and the overload D_all>0 (123) is a positive coupled excess; the net charge of a connected support has no sign fact. | T13 | Observable: net charge (deficit minus surplus, in the units of 91/92) of the connected region Z and of D; certificate: bound giving a negative connected support, or its exclusion |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | x | 68, 79 | discharge completes: extended charge leaves no free pair; recorded activation facts | T13 T14 | - |
| H05 | Load and saturation | Load compared with certified capacity. | x | 24, 51, 52, 65, 69, 70, 71, 72, 73, 77, 91, 94, 95, 118, 122, 123, 127 | load vs certified capacity: extended loads, new loads, caps M0, cut capacity | T13 | - |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | x | 68, 90, 107, 116, 121 | payment of deficits by distinct resources: blocked/free partition, canonical incidence ledger, extended charge | T14 T15 | - |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | gap | - | Present at G: demands (scheduled pairs, C(sigma,2)) and supports (tokens, incidences at bdry(Z)) form a bipartite demand-support network (116,118,121); only an assignment/count is stated, no flow value or cut. | T14 | Observable: integral flow in the demand-support network of the pair (p,q) into Z's boundary incidences; certificate: identity (max-flow = min-cut) or an obstruction cut |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 30, 69 | total exceptional mass: sums of C(d,2), extended loads, free-side count | T13 | - |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 51, 70, 73, 77, 91, 92, 93, 95, 96, 97, 108, 123 | competition of budgets: required tests vs token supply and certified budget (G2, G3, criterion) | T13 T12 | - |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 140 | well-founded measure internalVertexCount with size equality from minimality (140) | T19 | One-unit peel steps and the descent of the measure along the swap are not stated |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 2, 15, 38, 66 | finite label set, ten roles, deg>=5 or two deg-4 configuration | T17 | - |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | x | 115, 141 | canonical representatives: select?, min_prec, first deficient vertex in G's order | T16 | - |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 19, 28, 93 | exact collisions 2^k: star/meeting constraints, cross switch, certification iff | T01 T17 | - |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | x | 78, 84 | excluded small orders: n>C^2+C+1+t, C(C+1)+9<=n | T17 | - |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | ~ | 2, 15 | registered barrier table and 399-label census enter as facts (2,15) | T17 | Input schema, generator and verifier of the barrier table are not part of these facts |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | x | 2, 85 | p13-free law (HSS) at G and induced subgraphs; ex(6,C4)=7 | T18 | - |

## Table 2 — Facts of the residual → structural coordinates

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted length and no strictly smaller baseline object avoids the target (SelectionMinimality). | yes (extremality of G; smaller objects enter only through the order on G) | E01 C03 | exclusion + minimality | every later fact (baseline/minimality hypothesis); 138, 140 (size equality) |
| 2 | `cubicBaseline` | 221 | Presentation laws at G and its induced subgraphs: threshold 3, dyadic LengthOK, p13-free law (HSS), label census 399, barrier-table rows = legal labels. | yes (laws stated at G and G[S]) | I06 I01 I05 | classification (imported law + finite table) | 13, 14, 15, 38 |
| 3 | `minDegreeBaseline` | 2850 | Every vertex of G has degree >= 3. | yes | A04 A03 | bound | 5, 7, 18, 19, 21, 141 (kept-degree test), 130 |
| 4 | `returnAvoidance` | 1 | For every dart, the return-length set is disjoint from the shifted accepted set. | yes | C02 C04 | exclusion | 106, 28, 29, 33, 18-21 |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has min degree >= 3; G is connected. | yes | E02 B01 A07 | exclusion | 117, 140 (transplant is a subgraph), 141 |
| 6 | `slackIndependent` | 4 | Vertices of degree > 3 are pairwise nonadjacent. | yes | A06 A03 | exclusion | 7, 30, 54, 56 |
| 7 | `tightEndpoint` | 3 | Every dart has an endpoint of degree exactly 3 (tight endpoint). | yes | A03 A04 E03 | identity | 6, 81, 105, 106, 117 |
| 8 | `cycleRankConstraint` | 425 | 2*beta(G) >= n+2 with beta = m-n+1. | yes | A12 A13 | bound | unconsumed by another fact at [144a] (returned only) |
| 9 | `degreeProfileFibres` | 2300 | Readings of G at Z in different boundary-degree fibres are not identified by any admissible rank quotient of G. | yes | E06 B06 | exclusion | 10, 111, 137 (first disjunct) |
| 10 | `targetCompleteContextUniversality` | 2301 | Identified readings of G share their profile and their response in G-Z; no reading of G at any Z closes an accepted cycle in G-Z (G-only form). | yes (actualGlue is a subgraph of G, Lean actualGlue_hom) | E06 B07 C03 | exclusion | 137 (second disjunct is this fact for X=Xp,Xq), 139 |
| 11 | `replacementExclusion` | 223 | No proper connected support Z of G has a replacement X' (boundary profile kept, glue has baseline, smaller than G, no target). | yes (universally quantified over candidate pieces X'; no X' asserted; content is minimality of G) | E05 E01 B06 E07 | exclusion | 12, 138, 140 (used by size equality) |
| 12 | `uncompressible` | 5 | No proper support Z of G has a strictly smaller compressing representative X' in G-Z. | yes (same remark as 11) | E05 | exclusion | 138, 140 |
| 13 | `windowPresent` | 608 | G has an induced path of the registered window order (13). | yes | C08 D02 | witness | 14, 47, 48 |
| 14 | `maximalPacking` | 6 | Canonical packing P0 is a nonempty maximum, maximal family of vertex-disjoint induced windows. | yes | C09 C10 D05 | decomposition | 16, 23, 24, 37, 45-52, 117, 140 (int(Z) vs windows unstated) |
| 15 | `localAlgebra` | 7 | Legal-label census: /Labels 13/ = 399 with size distribution [13,60,122,122,63,17,2,...]. | yes | G02 I01 I05 | classification | 38, 37, 2 |
| 16 | `packingOrderBound` | 6611 | 13 * nu(P0) <= n. | yes | C09 G09 A01 | bound | 24, 45, 52, 89, 117 |
| 17 | `noSuppressionChordViolation` | 6620 | Every cycle of a compatible open-port suppression G/Q has non-accepted lifted length /walk/+/chords/. | no: cycles of the suppressed graph G/Q (a derived graph, not part of G) | - (nonG: none earned) | exclusion | nonG; consumed by 103 (mixed), exit (e) |
| 18 | `twoSwitchForcedPath` | 6800 | Two-edge switch of G forces a simple path u1-u2 in G-{u1v1,u2v2} with /p/+1 accepted (deg v1,v2 >= 4). | yes | E03 C01 C04 A04 | witness | 19, 81, 21, 130 (deletion of private edges) |
| 19 | `crossSwitchFamily` | 6802 | Cross-vertex switch family: forced paths u1->u in G-{u1v,uh'}; two such paths of length 2^j-1 are never both h'-free and internally disjoint. | yes | E03 C01 C13 C04 C05 I03 | witness + exclusion | 28, 29, 35, 81 |
| 20 | `highCentreSplitForced` | 6801 | At every vertex h of degree > 3, G ∪ M_h (all nonadjacent pairs of N(h) added as edges) has an accepted cycle avoiding h and using an added edge. | no: G ∪ M_h is a supergraph with added edges, not a subgraph of G | - (nonG: none earned) | witness | nonG; 21 (G-form for the switch) |
| 21 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch at h (deg >= 5) forces a path u1-u2 in G-{hu1,hu2} splitting exactly by h. | yes | E03 C01 C04 D03 | witness + decomposition | 81, 28, 33 |
| 22 | `declaredPairSupportStructure` | 6677 | For every two declared sparse coordinates A, B of G and Z = select?(A u B) (the canonical support): Z is connected in G, contains A and B, and is a minimum connected set of G containing A u B. | yes | B08 D08 | decomposition | 129, 137, 139 (same Z = select?(X_p u X_q)) |
| 23 | `remainderDeficiencyBelowCut` | 6663 | def+(R) <= e(R,W) at P0 (R remainder, W window part). | yes | A11 A10 H01 C10 | bound | 24, 117, 42 |
| 24 | `windowCutCapacity` | 6664 | Window cut capacity: e(R,W) + 2(order-1)p <= delta*order*p + sigma_W. | yes | A10 H01 H05 | bound | 23, 117, 45 |
| 25 | `primitiveCarrierCount` | 6666 | /U_sp(G)/ = 4n + 2 sigma (primitive carrier). | yes | G07 G02 | identity | 89, 118 |
| 26 | `singleBoundaryShape` | 6627 | Single-boundary supports have exactly two neighbours of the boundary vertex inside and two outside (2+2 cut vertex). | yes | B03 B05 D02 | classification | 139 (U2-free needs cut vertices of Z) |
| 27 | `neighbourhoodPairCount` | 6900 | For every vertex h, G[N(h)] is a matching and N(h) has >= C(d,2)-floor(d/2) nonadjacent pairs. | yes | D03 A09 F01 | bound | 28-34 |
| 28 | `starCycleConstraint` | 6901 | Star constraint: paths x->y, x->z of G-h meeting only at x have /P/+/Q/+2 != 2^k. | yes | C05 C04 D03 I03 | exclusion | 29, 35, 19 |
| 29 | `meetingCycleConstraint` | 6902 | Meeting constraint: /P/+/Q/+2 != 2^k + /P1/+/Q1/ for meeting paths of G-h. | yes | C05 C04 C13 | exclusion | 28, 35 |
| 30 | `highDegreePairSum` | 6903 | Pair sums at high vertices: 5 sigma <= sum C(d_h,2), quadratic inequalities, 2 sum C(d,2) <= 16 sigma^2. | yes | A05 A09 H08 | bound | 34, 58, 42 |
| 31 | `vertexDeletionComponents` | 6904 | G-h is connected, or d_h is even with pairs of neighbours per block. | yes | B01 B03 | decomposition | 32, 33 |
| 32 | `cyclesThroughVertex` | 6905 | C(d,2) <= #cycles(h) (G-h connected) or d/2 <= #cycles(h). | yes | C03 B03 | bound | 34 |
| 33 | `cutVertexBlockPaths` | 6906 | Block paths at cut vertices: /r/+2 != 2^k, residues 3 and 1 mod 4 at length 2^j-1. | yes | B03 C01 C04 F08 | exclusion | 31 |
| 34 | `cycleDoubleCount` | 6907 | 2 sum_H #cycles(h) <= n #cycles(G), #cycles(G) <= 2^m. | yes | G07 G01 C03 | bound | 32, 30 |
| 35 | `threeRouteFan` | 7100 | Length-3 fan at every h: two length-3 routes from a neighbour force p1=q1. | yes | D03 C05 C13 | exclusion | 36, 38 |
| 36 | `threeRouteChain` | 7101 | Chain 3,3,3 at every h forces r1=p2, r2=q1. | yes | D03 C11 C13 | exclusion | 35, 67 |
| 37 | `windowPositionStubs` | 7102 | Each window of P0 has a placement; interior vertices carry d-2 external neighbours, end vertices d-1. | yes | D01 C12 A10 B09 | decomposition | 38, 48, 47 |
| 38 | `windowAttachmentGap` | 7103 | Cross-edge gap for placed disjoint paths; outside vertices carry legal labels; no two windows form a ladder. | yes | C12 D01 D05 C04 I01 | exclusion | 48, 52, 15 |
| 39 | `portEndDegree` | 7233 | Every selected port endpoint x(p) has degree 3. | yes | A04 D03 | identity | 105, 106, 72 |
| 40 | `hubLinkStructure` | 7217 | Link structure of the hubs of R at P0. | yes | D03 A06 D05 | classification | 41-45 |
| 41 | `hubClassCounts` | 7218 | Hub classes of the cubic vertices of G. | yes | A03 G02 D03 | classification | 42, 45 |
| 42 | `slotRelation` | 7219 | Slot relation 4 sigma + 21/H/ <= 3n + 6/H/^2. | yes | H01 A05 | bound | 45, 23 |
| 43 | `closedClasses` | 7220 | Closed bag-link classes of the hubs of R at P0. | yes | D08 D05 | classification | 44, 45 |
| 44 | `hubTwoHopLinks` | 7221 | Two-hop links between hubs of R at P0. | yes | A06 C01 | classification | 45 |
| 45 | `slotLinear` | 7222 | Slot relation linear in h_R: 4 sigma + 15/H/ <= 3n + K h_R + 584 nu + 32 sigma_W. | yes | H01 A05 C09 | bound | 75 (scale pressure) |
| 46 | `remainderPathBounds` | 7211 | Path and cycle bounds inside the remainder R of P0. | yes | C10 C01 C03 | bound | 47, 50, 52 |
| 47 | `windowFreeGeometry` | 7212 | Window-free geometry of P0 (R has no induced window). | yes | C10 C08 | classification | 46, 48 |
| 48 | `inducedPathAttachment` | 7213 | Attachments to induced P13s of G. | yes | D01 C08 C12 | classification | 38, 47, 37 |
| 49 | `densityExcess` | 7207 | Density in excess form; two-edge cut of every nonempty proper set; single-hub slack. | yes | A02 A13 B02 | bound | 50, 117 |
| 50 | `remainderSlack` | 7208 | Remainder slack of P0 and its hanging windows. | yes | C10 A13 | bound | 46, 51 |
| 51 | `hubWindowBudget` | 7209 | Hub-window budget at P0. | yes | H09 H05 | bound | 52, 45 |
| 52 | `windowHubBounds` | 7210 | Windows of P0 against big hubs. | yes | A06 C09 H05 | bound | 51, 45 |
| 53 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; /L/ <= 2e(L). | yes | A03 D03 A10 | bound | 54, 55, 56 |
| 54 | `hubCountBound` | 7201 | 5/H/ + sigma <= 2n. | yes | A05 A06 A14 | bound | 56, 58 |
| 55 | `lowEdgeParity` | 7202 | Parity of L-L edges on walks between cubic vertices. | yes | C04 C01 | identity | 56 |
| 56 | `bigHubBound` | 7203 | Hub domination and 2/B/ + sigma <= n. | yes | A06 A05 A14 | bound | 57, 58 |
| 57 | `bigHubVShapes` | 7204 | V-shape caps: <= 12 middles per pair of big hubs; 4 sigma + 93/B/ <= 2n + 75/B/^2 + 4/H/. | yes | D03 G02 A06 | bound | 58 |
| 58 | `highSurplusBound` | 7205 | 24 sigma + 465/B/ <= 18n + 375/B/^2 and 8n <= 32s + 125 s^2 (s = n - sigma). | yes | A05 H01 G08 | bound | 78 |
| 59 | `hubLengthThreePairs` | 7206 | Length-3 pairs at the hubs of G. | yes | A06 C01 | classification | 35, 44 |
| 60 | `surplusDartIdentity` | 6607 | Dart identity: sigma + 6/H/ + lowDarts = 3n. | yes | A05 G07 H01 | identity | 61, 82, 104 |
| 61 | `highDegreeCountBound` | 6608 | /H/ <= sigma. | yes | A05 A14 | bound | 86, 87 |
| 62 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible quotient of G is label-injective on its family. | yes | E06 G06 B07 | identity | 9, 120 (code), 111 |
| 63 | `surplusAbove` | 8 | Degree surplus exceeds the registered scale threshold. | yes | A05 G08 | bound | 75, 78, 83 |
| 64 | `highSurplusConfiguration` | 6703 | G has a vertex of degree >= 5 or two distinct vertices of degree 4. | yes | A03 A05 D10 A14 | classification | 81 |
| 65 | `pairArmAPattern` | 7234 | Arm A kind structure of the canonical homogeneous pattern (role, token, blocker kind, star/matching data). | yes | D03 D04 D07 G04 H05 D05 | classification | 98, 126 |
| 66 | `pairArmARoleAlphabet` | 7235 | Arm A: the canonical overload role is one of ten live roles. | yes | G02 G04 I01 | classification | 65, 98 |
| 67 | `pairArmB` | 7236 | Arm B outcomes: pair overlap system exists; (B1) [182] residual, (B3) obstruction handoff with canonical separator/envelope/escape; realizability failure gives split demands. | yes | E09 C13 C11 D09 D06 | classification | 98 |
| 68 | `extFreeEmpty` | 7227 | The extended charge leaves no pair free: Pi_free^ext is empty. | yes | H04 H06 G07 | identity | 69, 70, 71 |
| 69 | `extLoadSum` | 7228 | C(sigma,2) = sum_t load_ext(t), /T/ <= 8n + sigma. | yes | H05 G07 H08 | identity | 70, 71 |
| 70 | `extOverload` | 7229 | c^2 K + 2 M0 (8n+sigma-/T/) + 2B <= 2 sum (load_ext(t) - M0). | yes | H05 H01 H09 | bound | 71, 91 |
| 71 | `extOverloadedToken` | 7230 | When K > 0, some token has load_ext > M0. | yes | H05 | witness (existence) | 72, 94 |
| 72 | `newLoadBound` | 7231 | newLoad(p) <= (/H/-1) + [p triangular] sigma for every selected port. | yes | H05 A06 | bound | 73, 77 |
| 73 | `freeSideHubs` | 7226 | /Pi_free/ <= sigma(tau + /H/ - 1); n K <= 2 sigma(tau+/H/-1) in the capped arm. | yes | H09 H05 | bound | 77, 95 |
| 74 | `separatedPairs` | 7232 | Separated pairs (disjoint declared supports and returns) have only target-response or chord blockers; C(sigma,2) <= sum C(d_D,2) + sum C(d_R,2) + /Sep/. | yes | F05 F01 G07 F04 | bound | 76, 77 |
| 75 | `scalePressure` | 7223 | Scale pressure: C q + 15/H/ < 3s + K h_R + 584 nu + 32 sigma_W (q = ceil sqrt n). | yes | H01 G08 | bound | 78 |
| 76 | `freeSideStructure` | 7224 | Every free pair is two ports with disjoint declared supports, T, returns, distinct centres, no obstruction, and one triangular port or one centre in the other's T. | yes | F04 F05 D05 | decomposition | 77 |
| 77 | `freeSideCount` | 7225 | /Pi_free/ <= tau sigma + Lambda; capped-arm form of G2; bounds in Delta. | yes | H09 H05 H01 G07 | bound | 73, 95 |
| 78 | `highSurplusOrder` | 7214 | 8n <= 32 s + 125 s^2 at s = n - C ceil sqrt n - 1; every t with 125t^2+24t < 8(C^2+C+1) has n > C^2+C+1+t. | yes | G08 I04 | bound | 83, 84 |
| 79 | `windowChargeKinds` | 7215 | Window structure of the canonical charge and recorded activation facts (early-blocked same-hub pairs, no profile obstruction). | yes | H02 H04 D08 | decomposition | 68, 80 |
| 80 | `responseObstructionTargetDefect` | 7216 | Every target-response obstruction of G is a residual target defect. | yes | E09 F04 | classification | 112, 113 |
| 81 | `highEndpointSwitch` | 6704 | Switch at every high/baseline edge hc: forced path by same-vertex or two-edge switch. | yes | E03 C01 D03 | witness | 18-21 |
| 82 | `edgeSurplusIdentity` | 6606 | 2m = 3n + sigma. | yes | A02 A05 H01 | identity | 85, 91, 104 (same identity, counted once) |
| 83 | `ceilSqrtAboveScale` | 6612 | C + 1 <= ceil sqrt n. | yes | G08 | bound | 84, 75 |
| 84 | `orderAboveScaleSquare` | 6613 | C(C+1) + 9 <= n. | yes | A01 G08 I04 | bound | 78 |
| 85 | `sixVertexExtremalEnvelope` | 6614 | m + 4 <= 2n (from ex(6, C4) = 7). | yes | A02 A13 I06 | bound | 117 (m+2<=2n weaker) |
| 86 | `highDegreePositive` | 6609 | 1 <= /H/. | yes | A05 A06 | bound | 87 |
| 87 | `highDegreeSurplusCapacity` | 6610 | sigma <= /H/ (n - /H/ - 3). | yes | A05 A06 | bound | 61 |
| 88 | `canonicalCapacityExplicit` | 6665 | G's canonical capacity presentation is the explicit one (recorded activation on P0). | yes | D08 | identity | 89-97, 118 |
| 89 | `canonicalTokenCount` | 6667 | /T_cap/ + 2(order-1) nu = 4n + 3 sigma + 3 order nu. | yes | G02 G07 A01 | identity | 91, 25 |
| 90 | `canonicalBlockedFreePartition` | 6668 | /Pi_blk/ + /Pi_free/ = C(sigma,2) at the canonical ledger. | yes | G07 H06 | identity | 91, 116 |
| 91 | `canonicalLedgerDeficit` | 6669 | Deficit G2: c^2 K + 2 M0 (8n+sigma-/T/) <= 2(/Pi_free/-B) + 2(/Pi_blk/ - M0/T/). | yes | H01 H09 H05 | bound | 94, 95, 92 |
| 92 | `pairCountDeficit` | 6670 | Pair-count deficit G3: c^2 K + 2 M0 (8n+sigma) <= 2(C(sigma,2) - B). | yes | H01 H09 | bound | 91 |
| 93 | `canonicalCertificationCriterion` | 6671 | Certified ledger exists iff /Pi_free/ <= B. | yes | H09 I03 | identity (iff) | 94, 95, 97 |
| 94 | `canonicalOverloadOfFits` | 6674 | If /Pi_free/ <= B: blocked side overloaded and some token has load > M0 with an L_geom role-homogeneous matching or star. | yes | H05 D04 G04 F07 | bound + witness | 126, 123 |
| 95 | `canonicalFreeExcessOfCapped` | 6675 | If every token load <= M0: free side exceeds B. | yes | H05 H09 F07 | bound | 93, 77 |
| 96 | `paperBudgetBound` | 6672 | E_paper <= B at the canonical spine family. | yes | H09 | bound | 97 |
| 97 | `paperBudgetCertifies` | 6673 | /Pi_free/ <= E_paper certifies the canonical certified ledger. | yes | H09 | bound | 93 |
| 98 | `pairCodeConfiguration` | 6676 | Where G sits in the pair-code chain: [137]->[143] configuration, or canonical first failure ([182] residual), or obstruction handoff with Type B fan entry. | yes | E09 D08 | classification | 128 (routing) |
| 99 | `sparseSurplusSurvivor` | 119 | G survives the five sparse surplus exits (DeclaredSparseSurvivor). | yes | E09 | exclusion | not_spec_of_survivor; 128, 115 |
| 100 | `openPortSuppression` | 435 | Open-port suppression: for every compatible family of G, its vertex/left/right/centre configuration, disjointness, injectivity, CenterCapacity <-> centerLoad <= deg - 3, and the adjacency of G/Q. | mixed: the configuration and capacity clauses are about G; the last clause (adjacency of the suppressed graph G/Q) is not | D03 D07 | classification |  101, 103 |
| 101 | `openPortSuppressionSafe` | 436 | For every compatible family with capacity, every vertex of G/Q has degree >= 3. | no: degrees of the suppressed graph G/Q | - (nonG: none earned) | bound | nonG |
| 102 | `singleOpenPortSuppressionWitness` | 437 | Every high-centre configuration has an open-port witness path in G avoiding the port vertex with restored length 2^j-1. | yes | C01 C04 C12 | witness | 106 |
| 103 | `suppressedFamilyCriticalCycle` | 438 | Every compatible family with capacity has an accepted cycle of G/Q using a chord; every accepted cycle of G/Q expands to a simple cycle of G with non-accepted length. | mixed: first conjunct and the hypothesis cycle are in G/Q; the expanded cycle is in G | - (nonG: none earned) | exclusion | nonG (G/Q part) |
| 104 | `sparseSlackSurplus` | 109 | 2m = 3n + sigma (duplicate of 82 under the [126] publication). | yes | A02 A05 | identity | 105; duplicate of 82, not counted twice for H01 |
| 105 | `activeSurplusFamily` | 110 | /P_exc/ = sigma; each selected port has centre degree > 3, endpoint degree 3 and exactly 2 shoulders. | yes | A05 D03 F01 | decomposition | 106, 107 |
| 106 | `sparsePortActivation` | 111 | Each selected port carries a return path R_p; open ports a suppression witness in G-x(p); triangular ports a triangle. | yes | C02 C01 D01 C12 | witness | 107, 129, 76 |
| 107 | `activeSurplusDemands` | 120 | The active surplus family: sigma members each with canonical return. | yes | F01 H06 D03 | decomposition | 110, 116 |
| 108 | `baselineSpineDemand` | 112 | Canonical baseline spine family exists with its spec (cubic baseline budget B0(n), room, deficit E_spine). | yes | G03 G01 H09 | identity | 119, 120, 96 |
| 109 | `freePairCountFails` | 1600 | The free-pair entropy sandwich fails (negation). | yes | G03 G01 G05 | exclusion | 128 (routing), 94 |
| 110 | `dependentPairFamily` | 201 | Some pair of the schedule has a nonempty blocker set at the canonical activation. | yes | F07 F02 | witness (existence) | 115, 65, 98 |
| 111 | `pairDegreeProfileFibres` | 2902 | Determination certificates of scheduled pairs identify only coordinates in one boundary-degree fibre. | yes | E06 B06 | exclusion | 9, 112 |
| 112 | `pairNoProfileObstruction` | 2904 | No scheduled pair has a type-(d) profile obstruction. | yes | E09 B06 | exclusion | 110, 80 |
| 113 | `pairNoResponseObstruction` | 2901 | No scheduled pair has a type-(e) response obstruction. | yes | E09 B07 | exclusion | 110, 80 |
| 114 | `blockedPairNoExit` | 1602 | No sparse surplus exit settles the dependence. | yes | E09 F07 | exclusion | 128, 115 |
| 115 | `canonicalBlockerRoute` | 144 | Blocked pair with canonical blocker min_prec Blk(pi) at the canonical activation. | yes | D08 F03 I02 | identity | 116, 126 |
| 116 | `canonicalPairLedger` | 113 | /Pi/ = C(sigma,2); Pi_blk and Pi_free exhaust it; /Pi_blk/ = sum mu(B); a blocked pair exists. | yes | G07 F01 H06 F02 H02 | identity | 90, 121 |
| 117 | `sparseUpperEnvelope` | 129 | m + 2 <= 2n; window/remainder incidence identity at P0. | yes | A02 A13 A10 H01 A07 | bound + identity | 85, 24 |
| 118 | `capacityTokenLedger` | 114 | Capacity-token ledger: /T_cap/ accounting identities at the canonical presentation. | yes | G02 G07 H05 | identity | 121, 89 |
| 119 | `blockedPairEntropySetup` | 356 | Blocked-pair entropy setup: canonical capacity, spine family, /schedule/ = C(sigma,2). | yes | G01 G03 | identity | 120 |
| 120 | `blockedPairEntropySandwich` | 242 | 2^(/spine/ + /free side/) <= skeleton budget at G. | yes | G01 G03 G05 G06 | bound | 109, 65, 98 |
| 121 | `roleFibrePartition` | 115 | Exact partition of C(sigma,2) into Pi_free and class/token/role fibres; caps by Cap_hom(L) S_C. | yes | G04 G07 H06 | decomposition | 122, 123 |
| 122 | `fibrePressure` | 116 | High-load display C(s,2) <= E + L_max/T_cap/; a role fibre carries a Q_st-th of the load and contains a matching or star. | yes | G04 H05 D03 | bound | 123, 126 |
| 123 | `sparsePressureOverload` | 128 | Coupled excess D_all at the geometric caps is positive at the canonical certified ledger. | yes | H05 H09 | bound | 65, 98, 126 |
| 124 | `bridgeless` | 226 | Every edge of G lies on a cycle (bridgeless). | yes | B02 C02 E03 | exclusion | 4, 49 |
| 125 | `highCentreNormalForm` | 72 | Every high centre has cubic neighbours, a matching in N(h), and no common neighbour outside {h} for a nonadjacent pair. | yes | D03 D02 A06 | classification | 21, 81 |
| 126 | `homogeneousBottleneckPattern` | 141 | Canonical role-homogeneous same-token L_geom-matching or star at the overloading token, with declared same-root connector configuration. | yes | D03 D04 D07 G04 | classification | 128, 127, 129, 65 |
| 127 | `homogeneousCapsFail` | 601 | Homogeneous caps fail at the canonical ledger. | yes | H05 G04 | exclusion | 128 |
| 128 | `bottleneckRouting` | 142 | The canonical pattern routes to a sparse surplus exit, to the same-token Type B handoff, or to the unresolved pair. | yes | D03 E09 | classification (three-way disjunction) | 137, 136, 99 |
| 129 | `sameTokenPatternSupports` | 6804 | Routing exists; each pattern pair p,q has declared support X = select?(seed), connected, with two distinct vertices. | yes | B08 D08 B01 F04 | decomposition | 137-141 |
| 130 | `sameTokenPatternSwap` | 6805 | The swap of ret_q by ret_p and of ret_p by ret_q in G is G itself (every G-edge of G[Y] lies in G[X]) or loses the baseline at a tight endpoint of a private edge. | yes | E03 E05 A04 D07 | decomposition (exact dichotomy) | unconsumed at [144a] (returned only); needs combination with 141 |
| 131 | `windowClassOverload` | 130 | The canonical overload token lies in T_W. | yes | G04 D08 | classification | subtype selection; 128-137 for windowFails |
| 132 | `windowClassAbsent` | 131 | The canonical overload token lies outside T_W. | yes | G04 D08 | classification | subtype selection |
| 133 | `remainderClassOverload` | 132 | The canonical overload token lies in T_R. | yes | G04 D08 | classification | subtype selection |
| 134 | `remainderClassAbsent` | 133 | The canonical overload token lies outside T_R. | yes | G04 D08 | classification | subtype selection |
| 135 | `primitiveClassOverload` | 1603 | The canonical overload token lies in T_prim. | yes | G04 D08 | classification | subtype selection |
| 136 | `typeBHandoffFails` | 1801 | Exact complement of the same-token Type B handoff of G. | yes (negation of 128's second disjunct) | - (bookkeeping) | bookkeeping: pure branch tag; the complement carries no observable of its own, its content is 128 with the disjunct removed | 137 |
| 137 | `sameTokenPatternUnresolved` | 1802 | ENTRY TEST. Routing exists, r_p != r_q, Z = select?(X_p u X_q); boundary-degree profiles of the two readings at Z differ, OR glue(G-Z, X_p) and glue(G-Z, X_q) have the same cycle status. | yes (actualGlue is a subgraph of G) | B06 B07 D08 | classification (disjunction); second disjunct true for every pair at a target-avoiding G | 138, 139, 140, 141 (all at the same Z) |
| 138 | `sameTokenReadingsNotReplacement` | 2905 | At Z, no retained reading of G[Z] (any vertex subset) keeps the profile of G[Z], has the baseline in the glue, and is lexicographically smaller than G. | yes (retainedPiece/outside glue = subgraph of G) | E05 E07 B06 D09 | exclusion | 140 (transplant is not a reading), 137 |
| 139 | `sameTokenPairPartition` | 6806 | Exact partition at Z: X_p,X_q subset Z, Z connected; (U1) a separating boundary count at some b in bdry(Z), or (U2) equal counts with the G-only agreement in G-Z, free or shared; the one-sided region is empty. | yes | B05 B06 B03 B07 D05 D06 D08 D07 A10 A11 B01 | decomposition | 137, 140 (equal-count bijection contactEquiv unused as fact) |
| 140 | `sameTokenTransplantSize` | 8000 | Transplant of X_q (and of X_p) into Z: int(X') <= int(Z), linkage-included, profile iff no boundary vertex has a neighbour in D = int(Z)-Y, baseline iff kept degrees >= 3, and baseline+linkage force int(X') = int(Z). | yes (transplant = G-D, a subgraph) | E02 E03 E05 A01 A11 B04 B05 B06 B07 B09 C13 D09 H10 | replacement (exact conditions) + size equality | 141, 138, 11 |
| 141 | `sameTokenTransplantDeficit` | 8001 | The transplants of X_q and of X_p are exact: D empty with no deficit, or the canonical vertex v (first in G's order) lies in Z \ D, has a neighbour in D, and keeps fewer than 3 neighbours outside D. | yes | A04 A11 B09 E03 E08 E09 H01 D10 I02 | decomposition + obstruction (canonical deficit vertex) | 140; unconsumed by any inequality (returned only) |
| 142 | `sameTokenUnresolvedDecided` | 8100 | At the pinned Z: r_p != r_q; both readings actualGlue(Z,X_p), actualGlue(Z,X_q) are target-free and agree in G-Z; the arm "equal profiles and separated by G-Z" is empty. | yes (actualGlue is a subgraph of G) | B07 E06 B06 | exclusion | 137 (decides its test), 143, 144 |
| 143 | `sameTokenReadingsExact` | 8101 | Each edge restriction actualGlue(Z,Y) drops no edge of G[Z] with an interior end (it is G) or drops one, is lexicographically smaller than G and fails the baseline. | yes | E05 E02 B04 A04 E07 | replacement (exact) + minimality | 138 (special case), 144 |
| 144 | `sameTokenSwap` | 8102 | Rerouted swap P->Q at G, both directions: |int S|+|int Z n P| = |int Z|+|int Z n Q|; profile of G[Z] iff n_Q(b)=n_P(b) at every b in bdry(Z), with the copy attachments equal to the order-bijection images of the P-neighbours; baseline iff no vertex of G is deficient in any of four roles; linkage inclusion or a linkage using a vertex and its copy (and it holds when int Z n Q subset P); valid => |int Z n P| <= |int Z n Q| and not lexicographically smaller than G; every accepted cycle of the glued swap uses a vertex and its copy. | yes (S built from G, no other graph; linkages are subgraphs of the swap) | F06 B07 D07 E07 E05 E02 A01 A04 B04 B05 B06 C13 D09 | replacement (exact conditions) + size relation + descent + response | 146 |
| 145 | `sameTokenSwapExact` | 8103 | Each swap is valid (no deficient vertex, linkage-included, size inequality), or the canonical exceptional vertex swapDeficit lies in Z and is deficient in a role, or a linkage uses a vertex and its copy; both valid => |int Z n X_p| = |int Z n X_q|. | yes | F06 E03 E07 A04 A11 B09 E08 | decomposition + obstruction (canonical deficit vertex) + equality | returned only |
| 146 | `sameTokenU2FreeWhole` | 8104 | Neither support meets bdry(Z) and both glued transplants keep the baseline => X_p = X_q = Z, bdry(Z) empty, Z = V(G), every vertex outside a pair seed is a cut vertex of G. | yes | B01 B02 B04 E05 D06 | decomposition + exclusion | returned only |
| 147 | `sameTokenSeedCover` | 8105 | Each pair seed is at most 2 delta vertices and the supports of two canonical port paths (a triangular port: shortest return in G-cx, induced; an open port: suppression path), each with unaccepted-span chords and one stub per interior cubic vertex; with every degree-3 vertex in both seeds, the cubic vertices lie in 4 paths + 4 delta vertices and 3n <= 5(|T|+|P1|+|P2|). | yes | C01 C02 C06 C08 A03 A11 | decomposition + identity + bound | 147 (whole-graph arm), returned only |

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

## Gaps ranked (joint check)

Ranking = number of existing facts that would be combined with the coordinate once it is measured. `gap` rows first, then the `~` rows.

1. **F06 Cancellation and repair structure (the swap)**. Present at G: the pair (p,q) is blocked (115), homogeneous with equal labels (126), and unresolved at Z (137) only through the vacuous disjunct; 130 and 140-141 build only edge deletions and the smaller transplant. Missing observable and certificate: canonical swap graph S(G,Z) (interior of X_p replaced by the interior of X_q inside Z, equal interior size) and its canonical degree-deficit vertex, or a target cycle of S(G,Z) mapped into G; certificate: replacement. Technique: T03 local graph modification (+T13 for the deficit). Existing facts it combines with (27): 3, 4, 7, 9, 10, 11, 12, 18, 19, 21, 62, 65, 81, 106, 110, 111, 115, 123, 126, 128, 129, 130, 137, 138, 139, 140, 141.
2. **H03 Connected negative support**. Present at G: Z is connected (139), contains the canonical deficit vertex when D is nonempty (141), and the canonical excess D_all is positive (123); no sign fact for a connected support. Missing observable and certificate: signed net charge of the connected region Z (and of D) in the units of 91/92; certificate: bound. Technique: T13 potential and discharging. Existing facts it combines with (18): 23, 24, 42, 45, 58, 70, 75, 82, 91, 92, 94, 95, 117, 123, 129, 139, 140, 141.
3. **H07 Flow-cut support**. Present at G: the pair schedule (C(sigma,2) demands), the tokens and incidences at bdry(Z) form a bipartite demand-support network (116, 118, 121); only counts and assignments are stated. Missing observable and certificate: integral flow of the pair demands into the incidences at bdry(Z) with a cut; certificate: identity or obstruction. Technique: T14 demand-supply and flow. Existing facts it combines with (16): 23, 24, 25, 68, 69, 74, 76, 77, 89, 90, 107, 116, 118, 121, 139, 140.
4. **C07 Cycle-space interaction of the two returns**. Present at G: the ports p and q have distinct return cycles (106, 126; r_p != r_q by 137); their symmetric difference is not measured. Missing observable and certificate: incidence vectors of the return cycles of p and q and their symmetric difference with its length; certificate: identity. Technique: T08 path-cycle and cycle-space analysis. Existing facts it combines with (16): 4, 18, 19, 21, 28, 29, 33, 35, 36, 55, 81, 102, 106, 126, 129, 137.
5. **C06 Ear structure of returns and private edges**. Present at G: return paths R_p, R_q (106) and the private-edge set of the swap (130) are attached to G[X]; the attachment only at their ends is not stated. Missing observable and certificate: ear decomposition of R_p, R_q and of E(G[Y])\E(G[X]) over G[X]; certificate: decomposition. Technique: T08. Existing facts it combines with (11): 14, 37, 38, 47, 48, 102, 106, 129, 130, 139, 140.

`~` rows, ranked by combined facts:

6. **B07 Response of the swapped piece**: missing response of the piece-for-piece swap (see F06); technique T05; combines with 8 facts: 9, 10, 62, 113, 137, 138, 139, 140.
7. **E08 / A07 Peelability and core of G-D**: missing peeling sequence of D from G to the 3-core; technique T19 / T04; combines with 6 facts: 3, 5, 7, 117, 140, 141.
8. **D07 Equal-response identification of the two readings**: missing explicit bijection of the equal-count contacts (contactEquiv) as a ledger fact; technique T16; combines with 5 facts: 126, 130, 137, 139, 140.
9. **B01 Components of G-Z and G-D**: missing components of the rest; technique T04; combines with 5 facts: 5, 129, 139, 140, 141.
10. **E07 Descent on equal-size alternatives**: missing lexicographic comparison of the swapped object with G; technique T16; combines with 4 facts: 11, 138, 140, 130.

Other `~` rows (A12, B04, C11, D06, F02, F03, F08, G05, H02, H10, I05) have their missing accounting stated in Table 1. Reading of the ranking: F06 is the swap the paper needs; it is the only gap whose absence is exactly the defining failure, and it sits at the top of the count too (27 facts, including the whole switch/return family 18-21, 106, and the exclusions 9-12, 138, 140).

## Non-G facts

| # | Key | Non-G object | G-constructed replacement |
|---|---|---|---|
| 17 | `noSuppressionChordViolation` | cycles of the suppressed graph G/Q | For each compatible family, state the lifted length `|walk|+|chords|` of every G-cycle through the restored ports directly in G (the expansion), as a path statement in G minus the deleted vertices |
| 20 | `highCentreSplitForced` | supergraph G u M_h with added edges | The G-form: for nonadjacent neighbours u1,u2 of h, a path u1-u2 in G-h with |p|+2 accepted (a path in G, cycle closed through h); 21 already gives the same-vertex switch version at deg >= 5 |
| 100 (last clause only) | `openPortSuppression` | adjacency of G/Q | Drop the G/Q adjacency clause; the configuration and capacity clauses (G) are kept and earn D03, D07 |
| 101 | `openPortSuppressionSafe` | degrees of G/Q | The closed formula deg_{G/Q}(v) = deg_G(v) - (deleted neighbours) + (chord ends at v) as an identity over G-degrees, which yields the >= 3 bound from centerLoad <= deg - 3 (already in 100) |
| 103 | `suppressedFamilyCriticalCycle` | the accepted cycle of G/Q (first conjunct and hypothesis of the second) | Its expansion, the simple cycle of G with one extra edge per used chord and non-accepted length, stated without the G/Q cycle |

Borderline cases kept as facts about G, with the reason: 1 `selection` and 11-12 quantify over smaller objects / candidate pieces X', but assert no witness on them (they are extremality and exclusion statements about G); 137-141 use `actualGlue`, the retained pieces and the transplant, all of which are subgraphs of G (`actualGlue_hom`, `Transplant`: glue = G - D).

## Outside the register

- **Swap object as a piece-for-piece replacement.** Observable: the graph S(G,Z) obtained from G by replacing the interior of Z by an isomorphic copy of the interior of X_q (respectively X_p) on the same boundary labels. It fits F06/E05 but has no coordinate of its own beyond them; recorded here to prevent it being forced into a row.

## Cross-check results

1. Every coordinate code in Table 2 has status x or ~ in Table 1 and lists the fact: **pass** (generated by inversion; no Table-2 code sits on a gap, n/a or nonG row).
2. Every x or ~ in Table 1 cites at least one Table-2 row: **pass** (81 rows, each derived from Table 2, none empty).
3. Every Table-2 row accounts for at least one coordinate or is bookkeeping: **pass with the flagged rows** 136 (bookkeeping: branch tag, complement of the handoff) and the four nonG rows 17, 20, 101, 103, which by the G-only rule account for no coordinate (their replacements are in the Non-G section).
4. No fact counted twice for the same demand in different currencies: **pass with one merge**: 82 and 104 state one identity (2m=3n+sigma) and count once. 91, 92, 94, 95 are different inequalities of the same ledger (G2, G3 and two implications) and are each listed once per coordinate; 140 (size equality) and 5 (no proper baseline subgraph) both feed E02 as different demands (minimality of G versus of the transplant).

Caveats on marks. (a) Global facts about G (A-group, G-group) are accepted at G; boundary/support coordinates (B, D06-D07, E05-E09) require the certificate at Z, X_p, X_q. (b) "Combined" is read inside the residual: through a shared statement, ledger identity or the routing decision 128/137; the leaf [144a] itself has no closing inequality. (c) Rows 140/141 were marked from the Lean statements `SameTokenTransplantAt` / `SameTokenTransplantExactAt`.

## Swap and reading facts (rows 142-147)

- **Accounted (`x`).** F06 (the rerouted swap `swapPiece`, facts 144-145), B07 (response of the swapped object: every accepted cycle uses a vertex and its copy, fact 144), D07 (order-fixed equal-count contact bijection `orderEquiv` and the copy-attachment identity, fact 144), E07 (descent: a valid swap is not lexicographically smaller than G, equal interior sizes when both swaps are valid, facts 144-145). Fact 142 records that the entry test is decided at G; fact 143 that every edge-restricted reading is G or loses the baseline; fact 146 is R5's unimplemented boundary-free argument.
- **`gap`: H03, H07, C07** (C06 is `~` by fact 147, the port paths and their stubs). They are present at G (Table 1) but the `[144a]` test does not consume them: the pair test consumes swap validity (profile, degrees, linkage, size, descent), which is measured. They enter only through the token-flow and return-cycle currencies of the parent routing (facts 23-25, 102, 106), not through the unresolved pair.
- **`~`.** B01 (components of G-Z and G-D), E08/A07 (iterated peeling of D), A12, B04, C11, D06, F02, F03, F08, G05, H02, H10, I05: as in the table above.
- **Closure test (explicit).** The swap facts, the reading facts and 146 were combined with the partition arms: U2-free with both transplants valid is `X_p = X_q = Z = V(G)` (there the swaps are the identity, so no contradiction is derived from them); U1 and U2-shared give contact counts `c_Y(b)` that include `dZ`-neighbours, while the swap profile identity counts interior neighbours only, so neither refutes it. No arm closes; the remaining proposition is `K .sameTokenSwapExact` at the two swaps, with the boundary-free arm reduced to "both pair supports are all of V(G)".
- **Non-G facts 17, 20, 100 (last clause), 101, 103** are on the shared entry prefix (suppressed graph `G/Q`, supergraph `G ∪ M_h`); they are not on the `[144a]`-specific path and are not touched here.
