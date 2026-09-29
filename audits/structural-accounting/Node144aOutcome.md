# Structural accounting: `Node144aOutcome`

**Branch/worktree:** `/home/guillem/hs-wt-S144a` (head b3225d1, R5 keys 8000/8001 present). Read-only; no Lean edited, nothing built.

**Defining failure.** The entry test "pair unresolved" (`SameTokenPatternPairUnresolvedStatement`, `Graph/Statements/SurplusPairRouting.lean`) is `profile(X_p at Z) != profile(X_q at Z)` OR `HasCycle(actualGlue G Z X_p) <-> HasCycle(actualGlue G Z X_q)`, at the canonical routing pair `r_p != r_q` and `Z = select?(X_p u X_q)`. `actualGlue G Z X` is a subgraph of G (`actualGlue_hom`) and G has no accepted cycle, so both sides of the iff are false: the second disjunct is true for every pair at G, and [144a] is reached through a trivially true disjunct. The paper's replacement (swap the interior of one port's piece for the other's inside `Z`, equal interior size, then compare the canonical degree deficit) is not constructed at G. What exists is (i) `SameTokenSwapExact` (131: deletion of the private edges of the swap), (ii) the strictly smaller transplant `G - D`, `D = int(Z) \ Y`, with its exact conditions and canonical deficit vertex (R5: 141 `sameTokenTransplantSize` idx 8000, 142 `sameTokenTransplantDeficit` idx 8001).

**Scope and fact count.** 131 facts are in the generic `Node144aOutcome` conjunction (rows 1-131; the docstrings that say 87 or 94 common facts are stale, the abbrev and the template script give 131). Rows 132-142 are the extras of the three handoff-fails subtypes (`windowFails`, `remainderFails`, `primitiveFails`): the five class facts (`windowClassOverload`, `windowClassAbsent`, `remainderClassOverload`, `remainderClassAbsent`, `primitiveClassOverload`) and the six fails facts (`typeBHandoffFails`, `sameTokenPatternUnresolved`, `sameTokenReadingsNotReplacement`, `sameTokenPairPartition`, `sameTokenTransplantSize`, `sameTokenTransplantDeficit`). Total analysed: 142. Handoff subtypes' `typeBHandoff` and `typeBFanEntry` are out of scope.

**Status counts (88 coordinates), after G audit S144a:** x = 68, ~ = 15, gap = 3, n/a = 1, nonG = 1 (before: x = 64, ~ = 17, gap = 5, n/a = 1, nonG = 1). Rows 143-148 are the six S144a keys 8100-8105; F06 gap to x, B07, D07, E07 from ~ to x.

**Families of the common facts (rows 1-131):** entry/baseline 1-8 (`selection` ... `cycleRankConstraint`); quotient/replacement 9-12; windows and packing 13-18; switches and forced paths 19-22; witnesses and cut capacity 23-27; cycle counting 28-35; local rigidity 36-39; hubs, links, remainder and joint bounds 40-60; surplus identities and orders 61-65, 79, 83-88; pair arms 66-68; extended charge and free side 69-78; window charge 80-82; canonical capacity and certification 89-99; suppression 100-104; sparse survivor chain 105-124; bridgeless, normal form, routing 125-131.

**Non-G marks (Table 2, column 5):** 18, 21, 102, 104 (and the G/Q clause of 101). Everything else, including every `actualGlue` fact (a subgraph of G) and the transplant (`G - D`), is a fact about G.

**Note on the unit rule.** 83 (`edgeSurplusIdentity`), 105 (`sparseSlackSurplus`) state the same identity 2m = 3n + sigma; it is counted once for A02/A05/H01.

Status legend: `x` accounted · `~` partially accounted · `gap` present at G but unaccounted · `n/a` absent at G (reason required) · `nonG` accounted only through an object outside G (does not count).

## Table 1 — Structural coordinates (same for every residual)

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 17, 85, 90, 141 | identity/bound n vs nu, scale, transplant int(X')=int(Z) | T01 T12 | - |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 50, 83, 86, 105, 118 | identity 2m=3n+sigma; m+2<=2n; m+4<=2n; density excess | T01 | 82: 83 and 105 are one identity, counted once |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 3, 6, 7, 42, 54, 65 | degree >=3; degree>3 vertices independent; tight endpoint; hub classes | T01 T07 | - |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 3, 7, 19, 40, 131, 142 | delta>=3; endpoint degree 3; kept degree <3 at canonical v (142); w with degree <=2 in swap (131) | T01 | - |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 31, 43, 46, 55, 57, 59, 61, 62, 64, 65, 83, 87, 88, 105, 106 | sigma=sum(d-3) with identities, /H/<=sigma, slot and pair-sum inequalities | T01 T13 | - |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 41, 45, 53, 55, 57, 58, 60, 73, 87, 88, 126 | high vertices pairwise nonadjacent; 2-hop and length-3 links; hub bounds | T07 T13 | - |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | ~ | 5, 118 | only the top core: no proper subgraph has min degree 3 (5) and m+2<=2n (118) | T04 | Core/peeling of G-D for the transplants (D = int(Z)\Y): the 3-core of G-D and its peeling order are unmeasured, although 142 exhibits the first deficient vertex; needed certificate: decomposition (peeling sequence of G-D). |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | - | excluded by 3: every vertex of G has degree >=3, so G has no degree-2 vertex and no degree-2 chain | T04 | Not applicable at G; degree <=2 vertices of G-D appear only in the subgraph G-D (see A07) |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 28, 31 | nonadjacent neighbour pairs of every vertex; pair sums; length-3 pairs; separated pairs | T01 T12 | - |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 24, 25, 38, 54, 118, 140 | crossing counts e(R,W), window/remainder incidences, reading counts at bdry(Z) | T01 T05 | - |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 24, 140, 141, 142 | def+(R)<=e(R,W); reading count +1 <= deg at each boundary vertex; kept degree of the canonical deficit vertex | T05 T13 | - |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | 2 beta(G) >= n+2 (8) | T01 | Proved but never combined: no fact of [144a] enters 8 with another currency; cycle rank of G[Z] and of G-D not measured |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 8, 50, 51, 86, 118 | linear slack of m in n at G (8,50,51,86,118) | T01 T13 | - |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 55, 57, 62, 65 | exceptional set H bounded: /H/<=sigma, 5/H/+sigma<=2n, 2/B/+sigma<=n; case (deg>=5 or two deg 4) | T01 T13 | - |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | ~ | 5, 32, 130, 140 | G connected; Z, X_p, X_q connected; G-h components (5,32,130,140) | T04 | Components of G-Z and of G-D (the rest and the removed set of the transplant) are not stated; certificate: decomposition of G-Z and of D |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 50, 125 | bridgeless; two-edge cut of every nonempty proper set (contains Z) | T04 T01 | - |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 27, 32, 33, 34, 140 | cut vertices/blocks: G-h decomposition, block paths, 2+2 single-boundary shape, U2 boundary cut vertices of Z | T04 T05 | - |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 141 | linkage inclusion (141): internally disjoint bdry-to-bdry linkages of the transplant are realized in G[Z] | T05 T08 | Menger number between boundary vertices of Z in G[Z] and in G-Z; certificate: bound on disjoint boundary paths, needed to compare Xp-linkages with Xq-linkages |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 27, 140, 141 | boundary of Z: cut boundary, reading counts c_X(b), transplant boundary conditions | T05 | - |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | x | 9, 11, 112, 113, 138, 139, 140, 141 | boundary-degree profile fibres (9,112); profile of the two readings at Z (138,139,140); profile iff no boundary neighbour in D (141) | T05 | - |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10, 16, 63, 114, 138, 140, 141, 145 | G-only response of a reading (constant, 143); response of the swapped object: every accepted cycle of glue(S)(G-Z) uses a vertex of int(Z) n Q\P as itself and as its copy (swap_cycle_double_use, in 145); linkage inclusion gives target-free glue | T05 T16 | - |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 23, 130 | minimum connected support Z of X_p u X_q; connected supports of pattern pairs | T10 | - |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 38, 141, 142 | demand 3 at each kept vertex vs supply of neighbours outside D (141 (ii), 142); window stubs | T05 T14 | - |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 19, 20, 22, 34, 45, 47, 56, 60, 82, 103, 107 | forced simple paths of prescribed accepted length after switches; two-hop and block paths; open-port and return witnesses | T08 | - |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 107, 125, 148 | return lengths disjoint from shifted accepted set at every dart; return path R_p; bridgeless | T08 | - |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 10, 16, 33, 35, 47 | no accepted cycle in G, in any actualGlue, at clause-(b) witnesses; cycle counts and double count | T08 T12 | - |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 4, 19, 20, 22, 29, 30, 34, 39, 56, 103 | accepted length = 2^k-1: switch closures, star/meeting constraints, parity, residues mod 4 | T09 | - |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 20, 29, 30, 36 | theta-type configurations: star and meeting constraints, cross-switch pair, length-3 fan | T08 | - |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | ~ | 148 | the port paths R_p (shortest, induced in G-cx) and Q_p as supports of the seed cover; each interior cubic vertex has exactly one stub; same-path chords have unaccepted span (148) | T08 | Attachment of the stubs only at path ends (an ear decomposition over the base G[X]) is not stated; the stub structure is |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | gap | - | Present at G: the two ports p,q have distinct return cycles (107, 127) with E(R_p) != E(R_q) (138: r_p != r_q); no fact measures their symmetric difference. | T08 | Observable: binary incidence vectors of the return cycles of p and q in the cycle space of G[Z]; certificate: identity for the symmetric difference and its length parity (with 56). |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 48, 49, 148 | induced P13 present; window-free remainder; attachments | T07 | - |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 17, 46, 53 | packing number nu with 13 nu <= n, packing inequalities and hub/window bounds | T06 T01 | - |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 24, 47, 48, 51 | remainder R of P0: deficiency, path bounds, window-free geometry, slack | T06 | - |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | 37, 68 | chain 3,3,3 at every vertex (37); Arm B serial system (68) | T08 | Serial corridor of the pattern pair p,q (base length and increments between the two return corridors) is not stated at the canonical routing |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 38, 39, 49, 103, 107 | allowed contacts of window endpoints/interiors; cross-edge gap; open-port witness avoids the port vertex | T07 | - |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | x | 20, 30, 36, 37, 68, 141 | joint disjointness/endpoint compatibility: cross-switch, meeting paths, linkage inclusion of the transplant, Arm B realizability | T08 | - |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 38, 39, 49, 107 | attachment of outside vertices/paths to windows; triangular port triangle | T07 | - |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 13, 27, 126 | induced P13 type, 2+2 cut vertex shape, heavy neighbourhood normal form | T07 | - |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 22, 28, 29, 36, 37, 40, 41, 42, 54, 58, 66, 82, 101, 106, 108, 123, 126, 127, 129 | centres with typed neighbours, ports, fans, stars, matchings inside N(h) | T07 | - |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | x | 66, 95, 127 | role-homogeneous matching or star of size L_geom in the overloaded role fibre | T14 T12 | - |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 14, 39, 41, 44, 66, 77, 140 | overlap of X_p and X_q at bdry(Z) (U2-free/shared); ladders; free-pair support overlaps | T10 T07 | - |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 68, 140 | Z is the minimum connected set containing X_p u X_q (23,140); canonical first failure of the pair overlap system (68) | T10 | No minimal connected obstruction is exhibited for the pair p,q: certificate (obstruction) that the swap fails on the smallest connected family is missing |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 66, 101, 127, 131, 140, 145 | order-fixed equal-count contact bijection orderEquiv (k-th in G.orderedVertices to k-th) with the attachment identity of the swap copy at each boundary vertex (145) | T16 | - |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 23, 44, 80, 89, 99, 116, 130, 132, 133, 134, 135, 136, 138, 140 | canonical selections: select?(seed), Z=select?(Xp u Xq), canonical capacity, canonical blocker, overload class, canonical vertex | T16 | - |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | x | 68, 139, 141 | glue of transplant = G-D (cycle transfer), retained-reading glue conditions, Arm B forward/backward routes | T05 | - |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 65, 142 | fixed-size marked configuration: canonical deficit vertex v; deg>=5 or two deg-4 vertices | T07 | - |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1, 11 | G minimal counterexample (selection); replacement exclusion | T02 | - |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5, 141 | no proper subgraph has min degree 3; transplant smaller than Z contradicts minimality (size equality) | T02 | - |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 7, 19, 20, 22, 82, 125, 131, 141, 142 | effect of deleting edges/vertices: switches, bridgeless, tight endpoint, private-edge deletion, D-deletion with its degree conditions | T03 | - |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | nonG | - | Only 18, 102, 104 and the G/Q clause of 101 speak of safe suppression, and they are statements about the suppressed graph G/Q, which is not part of G. | T03 | G-constructed replacement: the degree of each vertex of G/Q as a closed formula in G (deg_G minus deleted neighbours plus chord ends), i.e. the inequality centerLoad(c) <= deg(c) - 3 already proved in 101 as a statement about G, with the accepted-cycle exclusion stated as a path in G-{deleted vertices} |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 131, 139, 141 | no replacement of Z exists (11,12); none among retained readings (139); transplant satisfies the four conditions exactly and cannot be smaller (141); swap dichotomy (131) | T03 T02 | - |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 63, 112 | quotients: no identification across fibres; label-injective quotients; pair determination fibres | T05 T12 | - |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | x | 11, 139, 144, 145, 146 | descent on the neutral move: a valid swap is not lexicographically smaller than G (fewer vertices, or equal vertices and fewer edges), |int Z n P| <= |int Z n Q|, both valid give equality (145, 146); readings dropping an edge are lexicographically smaller and lose the baseline (144) | T16 | - |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 142 | one canonical peel candidate v of G-D (142) | T19 | Iterated peeling of D from G until the 3-core (removal of v, recomputation of kept degrees); certificate: peeling sequence preserving the invariant |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 16, 23, 68, 81, 99, 100, 113, 114, 115, 129, 142 | target/response defect: none at witnesses (16,113,114), classified obstruction outcomes (68,81,99), deficit vertex of the transplant (142) | T05 | - |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 28, 75, 106, 108, 117 | supply of tests: nonadjacent pairs, C(sigma,2) scheduled pairs, active family, ports | T07 T11 | - |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | ~ | 111, 117 | existence of a blocked pair (111) and exact counts /Pi_blk/+/Pi_free/ (117) | T11 | Rank of the response vectors of the pair family (or maximum independent subfamily) is not measured; certificate: bound |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | ~ | 116 | canonical blocker min_prec Blk(pi) of a blocked pair (116) | T11 T10 | Inclusion-minimal dependent subfamily for the same-token pair p,q (not the order-minimal blocker); certificate: obstruction (circuit) |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | x | 75, 77, 81, 130 | geometric support of dependence: declared supports, returns, T; supports X_p, X_q; response obstructions | T10 | - |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 75, 77 | separation of testers by disjoint declared supports and returns (75,77) | T05 T10 | - |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | x | 143, 144, 145, 146 | replacement: the rerouted swap S(G,Z;P,Q) built at G (fresh copy of the interior of Q in place of the interior of P, order-fixed contact bijection); conditions (i)-(iv) exact; canonical exceptional vertex swapDeficit; linkage double-use witness; size relation | T03 T13 | - |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 95, 96, 111, 115 | dichotomy free vs blocked: /Pi_free/ <= B, or overload with role-homogeneous pattern (95,96,66,127,129) | T11 T12 | - |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 34 | residues 3 and 1 mod 4 at lengths 2^j-1 for block paths (34) | T09 | Periodic response of the return family of p,q under additive increments (e.g. lengths of R_p and R_q shifted by the swap) is not measured |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 35, 109, 110, 120, 121 | labelled-class counts: #cycles<=2^m, code 2^(/spine/+/free/) <= skeleton budget | T12 | - |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 15, 26, 42, 58, 67, 90, 119 | legal states: 399 labels, ten roles, hub classes, token supply /T_cap/ | T12 | - |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 109, 110, 120, 121 | conditional information of local tests: entropy sandwich, spine deficit, setup | T12 | - |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | x | 66, 67, 95, 122, 123, 127, 128, 132, 133, 134, 135, 136 | dominant type: overloaded role fibre, class partition W/R/prim, caps | T12 | - |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | ~ | 110, 121 | joint count 2^(/spine/+/free/) vs skeleton budget (121), negation (110) | T12 | Joint state count of the pair (r_p, r_q) at Z compared with the product of conditional counts is not stated; certificate: bound |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | x | 63, 121 | injective reconstruction: label-injective quotients, code realized among labelled skeletons | T15 T12 | - |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 26, 35, 61, 69, 70, 75, 78, 90, 91, 117, 119, 122 | double-counting: token/pair ledgers, dart identity, partition of C(sigma,2) | T15 | - |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 59, 64, 76, 79, 84, 85 | asymptotic/finite thresholds: C+1<=ceil sqrt n, scale pressure, high-surplus order | T17 | - |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 17 | 13 nu <= n and window-density inequalities in the slot relation | T06 T12 | - |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 24, 25, 43, 46, 59, 61, 71, 76, 78, 83, 92, 93, 118, 142 | deficiency-surplus balances: def+<=e, slot relation, deficits G2/G3, kept-degree deficit | T13 | - |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | ~ | 80, 117 | window structure of the canonical charge; charge single-valued (80,117) | T13 | Additivity of the charge over the overlap of the two supports X_p, X_q at Z is not stated |
| H03 | Connected negative support | A connected region with negative charge. | gap | - | Present at G: Z is connected (140), Z contains the canonical deficit vertex v when D != empty (142), and the overload D_all>0 (124) is a positive coupled excess; the net charge of a connected support has no sign fact. | T13 | Observable: net charge (deficit minus surplus, in the units of 92/93) of the connected region Z and of D; certificate: bound giving a negative connected support, or its exclusion |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | x | 69, 80 | discharge completes: extended charge leaves no free pair; recorded activation facts | T13 T14 | - |
| H05 | Load and saturation | Load compared with certified capacity. | x | 25, 52, 53, 66, 70, 71, 72, 73, 74, 78, 92, 95, 96, 119, 123, 124, 128 | load vs certified capacity: extended loads, new loads, caps M0, cut capacity | T13 | - |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | x | 69, 91, 108, 117, 122 | payment of deficits by distinct resources: blocked/free partition, canonical incidence ledger, extended charge | T14 T15 | - |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | gap | - | Present at G: demands (scheduled pairs, C(sigma,2)) and supports (tokens, incidences at bdry(Z)) form a bipartite demand-support network (117,119,122); only an assignment/count is stated, no flow value or cut. | T14 | Observable: integral flow in the demand-support network of the pair (p,q) into Z's boundary incidences; certificate: identity (max-flow = min-cut) or an obstruction cut |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 31, 70 | total exceptional mass: sums of C(d,2), extended loads, free-side count | T13 | - |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 52, 71, 74, 78, 92, 93, 94, 96, 97, 98, 109, 124 | competition of budgets: required tests vs token supply and certified budget (G2, G3, criterion) | T13 T12 | - |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 141 | well-founded measure internalVertexCount with size equality from minimality (141) | T19 | One-unit peel steps and the descent of the measure along the swap are not stated |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 2, 15, 39, 67 | finite label set, ten roles, deg>=5 or two deg-4 configuration | T17 | - |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | x | 116, 142 | canonical representatives: select?, min_prec, first deficient vertex in G's order | T16 | - |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 20, 29, 94 | exact collisions 2^k: star/meeting constraints, cross switch, certification iff | T01 T17 | - |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | x | 79, 85 | excluded small orders: n>C^2+C+1+t, C(C+1)+9<=n | T17 | - |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | ~ | 2, 15 | registered barrier table and 399-label census enter as facts (2,15) | T17 | Input schema, generator and verifier of the barrier table are not part of these facts |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | x | 2, 86 | p13-free law (HSS) at G and induced subgraphs; ex(6,C4)=7 | T18 | - |

## Table 2 — Facts of the residual → structural coordinates

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted length and no strictly smaller baseline object avoids the target (SelectionMinimality). | yes (extremality of G; smaller objects enter only through the order on G) | E01 C03 | exclusion + minimality | every later fact (baseline/minimality hypothesis); 139, 141 (size equality) |
| 2 | `cubicBaseline` | 221 | Presentation laws at G and its induced subgraphs: threshold 3, dyadic LengthOK, p13-free law (HSS), label census 399, barrier-table rows = legal labels. | yes (laws stated at G and G[S]) | I06 I01 I05 | classification (imported law + finite table) | 13, 14, 15, 39 |
| 3 | `minDegreeBaseline` | 2850 | Every vertex of G has degree >= 3. | yes | A04 A03 | bound | 5, 7, 19, 20, 22, 142 (kept-degree test), 131 |
| 4 | `returnAvoidance` | 1 | For every dart, the return-length set is disjoint from the shifted accepted set. | yes | C02 C04 | exclusion | 107, 29, 30, 34, 19-22 |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has min degree >= 3; G is connected. | yes | E02 B01 A07 | exclusion | 118, 141 (transplant is a subgraph), 142 |
| 6 | `slackIndependent` | 4 | Vertices of degree > 3 are pairwise nonadjacent. | yes | A06 A03 | exclusion | 7, 31, 55, 57 |
| 7 | `tightEndpoint` | 3 | Every dart has an endpoint of degree exactly 3 (tight endpoint). | yes | A03 A04 E03 | identity | 6, 82, 106, 107, 118 |
| 8 | `cycleRankConstraint` | 425 | 2*beta(G) >= n+2 with beta = m-n+1. | yes | A12 A13 | bound | unconsumed by another fact at [144a] (returned only) |
| 9 | `degreeProfileFibres` | 2300 | Readings of G at Z in different boundary-degree fibres are not identified by any admissible rank quotient of G. | yes | E06 B06 | exclusion | 10, 112, 138 (first disjunct) |
| 10 | `targetCompleteContextUniversality` | 2301 | Identified readings of G share their profile and their response in G-Z; no reading of G at any Z closes an accepted cycle in G-Z (G-only form). | yes (actualGlue is a subgraph of G, Lean actualGlue_hom) | E06 B07 C03 | exclusion | 138 (second disjunct is this fact for X=Xp,Xq), 140, 16 |
| 11 | `replacementExclusion` | 223 | No proper connected support Z of G has a replacement X' (boundary profile kept, glue has baseline, smaller than G, no target). | yes (universally quantified over candidate pieces X'; no X' asserted; content is minimality of G) | E05 E01 B06 E07 | exclusion | 12, 139, 141 (used by size equality) |
| 12 | `uncompressible` | 5 | No proper support Z of G has a strictly smaller compressing representative X' in G-Z. | yes (same remark as 11) | E05 | exclusion | 139, 141 |
| 13 | `windowPresent` | 608 | G has an induced path of the registered window order (13). | yes | C08 D02 | witness | 14, 48, 49 |
| 14 | `maximalPacking` | 6 | Canonical packing P0 is a nonempty maximum, maximal family of vertex-disjoint induced windows. | yes | C09 C10 D05 | decomposition | 17, 24, 25, 38, 46-53, 118, 141 (int(Z) vs windows unstated) |
| 15 | `localAlgebra` | 7 | Legal-label census: /Labels 13/ = 399 with size distribution [13,60,122,122,63,17,2,...]. | yes | G02 I01 I05 | classification | 39, 38, 2 |
| 16 | `everyWitnessSpectrumSplit` | 6702 | For every clause-(b) witness triple (A,B,Z) of G and X in {A,B}, glue(G-Z, X) has no accepted cycle. | yes | B07 C03 E09 | exclusion | 23, 99, 138 (second disjunct at the pattern pair, not at these witnesses) |
| 17 | `packingOrderBound` | 6611 | 13 * nu(P0) <= n. | yes | C09 G09 A01 | bound | 25, 46, 53, 90, 118 |
| 18 | `noSuppressionChordViolation` | 6620 | Every cycle of a compatible open-port suppression G/Q has non-accepted lifted length /walk/+/chords/. | no: cycles of the suppressed graph G/Q (a derived graph, not part of G) | - (nonG: none earned) | exclusion | nonG; consumed by 104 (mixed), exit (e) |
| 19 | `twoSwitchForcedPath` | 6800 | Two-edge switch of G forces a simple path u1-u2 in G-{u1v1,u2v2} with /p/+1 accepted (deg v1,v2 >= 4). | yes | E03 C01 C04 A04 | witness | 20, 82, 22, 131 (deletion of private edges) |
| 20 | `crossSwitchFamily` | 6802 | Cross-vertex switch family: forced paths u1->u in G-{u1v,uh'}; two such paths of length 2^j-1 are never both h'-free and internally disjoint. | yes | E03 C01 C13 C04 C05 I03 | witness + exclusion | 29, 30, 36, 82 |
| 21 | `highCentreSplitForced` | 6801 | At every vertex h of degree > 3, G ∪ M_h (all nonadjacent pairs of N(h) added as edges) has an accepted cycle avoiding h and using an added edge. | no: G ∪ M_h is a supergraph with added edges, not a subgraph of G | - (nonG: none earned) | witness | nonG; 22 (G-form for the switch) |
| 22 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch at h (deg >= 5) forces a path u1-u2 in G-{hu1,hu2} splitting exactly by h. | yes | E03 C01 C04 D03 | witness + decomposition | 82, 29, 34 |
| 23 | `specWitnessStructure` | 6677 | For every clause-(b) witness with canonical support Z: Z connected, contains both supports, minimum connected; no witness satisfies clause (b). | yes | B08 D08 E09 | identity + exclusion | 130, 140 (same Z object), 116 |
| 24 | `remainderDeficiencyBelowCut` | 6663 | def+(R) <= e(R,W) at P0 (R remainder, W window part). | yes | A11 A10 H01 C10 | bound | 25, 118, 43 |
| 25 | `windowCutCapacity` | 6664 | Window cut capacity: e(R,W) + 2(order-1)p <= delta*order*p + sigma_W. | yes | A10 H01 H05 | bound | 24, 118, 46 |
| 26 | `primitiveCarrierCount` | 6666 | /U_sp(G)/ = 4n + 2 sigma (primitive carrier). | yes | G07 G02 | identity | 90, 119 |
| 27 | `singleBoundaryShape` | 6627 | Single-boundary supports have exactly two neighbours of the boundary vertex inside and two outside (2+2 cut vertex). | yes | B03 B05 D02 | classification | 140 (U2-free needs cut vertices of Z) |
| 28 | `neighbourhoodPairCount` | 6900 | For every vertex h, G[N(h)] is a matching and N(h) has >= C(d,2)-floor(d/2) nonadjacent pairs. | yes | D03 A09 F01 | bound | 29-35 |
| 29 | `starCycleConstraint` | 6901 | Star constraint: paths x->y, x->z of G-h meeting only at x have /P/+/Q/+2 != 2^k. | yes | C05 C04 D03 I03 | exclusion | 30, 36, 20 |
| 30 | `meetingCycleConstraint` | 6902 | Meeting constraint: /P/+/Q/+2 != 2^k + /P1/+/Q1/ for meeting paths of G-h. | yes | C05 C04 C13 | exclusion | 29, 36 |
| 31 | `highDegreePairSum` | 6903 | Pair sums at high vertices: 5 sigma <= sum C(d_h,2), quadratic inequalities, 2 sum C(d,2) <= 16 sigma^2. | yes | A05 A09 H08 | bound | 35, 59, 43 |
| 32 | `vertexDeletionComponents` | 6904 | G-h is connected, or d_h is even with pairs of neighbours per block. | yes | B01 B03 | decomposition | 33, 34 |
| 33 | `cyclesThroughVertex` | 6905 | C(d,2) <= #cycles(h) (G-h connected) or d/2 <= #cycles(h). | yes | C03 B03 | bound | 35 |
| 34 | `cutVertexBlockPaths` | 6906 | Block paths at cut vertices: /r/+2 != 2^k, residues 3 and 1 mod 4 at length 2^j-1. | yes | B03 C01 C04 F08 | exclusion | 32 |
| 35 | `cycleDoubleCount` | 6907 | 2 sum_H #cycles(h) <= n #cycles(G), #cycles(G) <= 2^m. | yes | G07 G01 C03 | bound | 33, 31 |
| 36 | `threeRouteFan` | 7100 | Length-3 fan at every h: two length-3 routes from a neighbour force p1=q1. | yes | D03 C05 C13 | exclusion | 37, 39 |
| 37 | `threeRouteChain` | 7101 | Chain 3,3,3 at every h forces r1=p2, r2=q1. | yes | D03 C11 C13 | exclusion | 36, 68 |
| 38 | `windowPositionStubs` | 7102 | Each window of P0 has a placement; interior vertices carry d-2 external neighbours, end vertices d-1. | yes | D01 C12 A10 B09 | decomposition | 39, 49, 48 |
| 39 | `windowAttachmentGap` | 7103 | Cross-edge gap for placed disjoint paths; outside vertices carry legal labels; no two windows form a ladder. | yes | C12 D01 D05 C04 I01 | exclusion | 49, 53, 15 |
| 40 | `portEndDegree` | 7233 | Every selected port endpoint x(p) has degree 3. | yes | A04 D03 | identity | 106, 107, 73 |
| 41 | `hubLinkStructure` | 7217 | Link structure of the hubs of R at P0. | yes | D03 A06 D05 | classification | 42-46 |
| 42 | `hubClassCounts` | 7218 | Hub classes of the cubic vertices of G. | yes | A03 G02 D03 | classification | 43, 46 |
| 43 | `slotRelation` | 7219 | Slot relation 4 sigma + 21/H/ <= 3n + 6/H/^2. | yes | H01 A05 | bound | 46, 24 |
| 44 | `closedClasses` | 7220 | Closed bag-link classes of the hubs of R at P0. | yes | D08 D05 | classification | 45, 46 |
| 45 | `hubTwoHopLinks` | 7221 | Two-hop links between hubs of R at P0. | yes | A06 C01 | classification | 46 |
| 46 | `slotLinear` | 7222 | Slot relation linear in h_R: 4 sigma + 15/H/ <= 3n + K h_R + 584 nu + 32 sigma_W. | yes | H01 A05 C09 | bound | 76 (scale pressure) |
| 47 | `remainderPathBounds` | 7211 | Path and cycle bounds inside the remainder R of P0. | yes | C10 C01 C03 | bound | 48, 51, 53 |
| 48 | `windowFreeGeometry` | 7212 | Window-free geometry of P0 (R has no induced window). | yes | C10 C08 | classification | 47, 49 |
| 49 | `inducedPathAttachment` | 7213 | Attachments to induced P13s of G. | yes | D01 C08 C12 | classification | 39, 48, 38 |
| 50 | `densityExcess` | 7207 | Density in excess form; two-edge cut of every nonempty proper set; single-hub slack. | yes | A02 A13 B02 | bound | 51, 118 |
| 51 | `remainderSlack` | 7208 | Remainder slack of P0 and its hanging windows. | yes | C10 A13 | bound | 47, 52 |
| 52 | `hubWindowBudget` | 7209 | Hub-window budget at P0. | yes | H09 H05 | bound | 53, 46 |
| 53 | `windowHubBounds` | 7210 | Windows of P0 against big hubs. | yes | A06 C09 H05 | bound | 52, 46 |
| 54 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; /L/ <= 2e(L). | yes | A03 D03 A10 | bound | 55, 56, 57 |
| 55 | `hubCountBound` | 7201 | 5/H/ + sigma <= 2n. | yes | A05 A06 A14 | bound | 57, 59 |
| 56 | `lowEdgeParity` | 7202 | Parity of L-L edges on walks between cubic vertices. | yes | C04 C01 | identity | 57 |
| 57 | `bigHubBound` | 7203 | Hub domination and 2/B/ + sigma <= n. | yes | A06 A05 A14 | bound | 58, 59 |
| 58 | `bigHubVShapes` | 7204 | V-shape caps: <= 12 middles per pair of big hubs; 4 sigma + 93/B/ <= 2n + 75/B/^2 + 4/H/. | yes | D03 G02 A06 | bound | 59 |
| 59 | `highSurplusBound` | 7205 | 24 sigma + 465/B/ <= 18n + 375/B/^2 and 8n <= 32s + 125 s^2 (s = n - sigma). | yes | A05 H01 G08 | bound | 79 |
| 60 | `hubLengthThreePairs` | 7206 | Length-3 pairs at the hubs of G. | yes | A06 C01 | classification | 36, 45 |
| 61 | `surplusDartIdentity` | 6607 | Dart identity: sigma + 6/H/ + lowDarts = 3n. | yes | A05 G07 H01 | identity | 62, 83, 105 |
| 62 | `highDegreeCountBound` | 6608 | /H/ <= sigma. | yes | A05 A14 | bound | 87, 88 |
| 63 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible quotient of G is label-injective on its family. | yes | E06 G06 B07 | identity | 9, 121 (code), 112 |
| 64 | `surplusAbove` | 8 | Degree surplus exceeds the registered scale threshold. | yes | A05 G08 | bound | 76, 79, 84 |
| 65 | `highSurplusConfiguration` | 6703 | G has a vertex of degree >= 5 or two distinct vertices of degree 4. | yes | A03 A05 D10 A14 | classification | 82 |
| 66 | `pairArmAPattern` | 7234 | Arm A kind structure of the canonical homogeneous pattern (role, token, blocker kind, star/matching data). | yes | D03 D04 D07 G04 H05 D05 | classification | 99, 127 |
| 67 | `pairArmARoleAlphabet` | 7235 | Arm A: the canonical overload role is one of ten live roles. | yes | G02 G04 I01 | classification | 66, 99 |
| 68 | `pairArmB` | 7236 | Arm B outcomes: pair overlap system exists; (B1) [182] residual, (B3) obstruction handoff with canonical separator/envelope/escape; realizability failure gives split demands. | yes | E09 C13 C11 D09 D06 | classification | 99 |
| 69 | `extFreeEmpty` | 7227 | The extended charge leaves no pair free: Pi_free^ext is empty. | yes | H04 H06 G07 | identity | 70, 71, 72 |
| 70 | `extLoadSum` | 7228 | C(sigma,2) = sum_t load_ext(t), /T/ <= 8n + sigma. | yes | H05 G07 H08 | identity | 71, 72 |
| 71 | `extOverload` | 7229 | c^2 K + 2 M0 (8n+sigma-/T/) + 2B <= 2 sum (load_ext(t) - M0). | yes | H05 H01 H09 | bound | 72, 92 |
| 72 | `extOverloadedToken` | 7230 | When K > 0, some token has load_ext > M0. | yes | H05 | witness (existence) | 73, 95 |
| 73 | `newLoadBound` | 7231 | newLoad(p) <= (/H/-1) + [p triangular] sigma for every selected port. | yes | H05 A06 | bound | 74, 78 |
| 74 | `freeSideHubs` | 7226 | /Pi_free/ <= sigma(tau + /H/ - 1); n K <= 2 sigma(tau+/H/-1) in the capped arm. | yes | H09 H05 | bound | 78, 96 |
| 75 | `separatedPairs` | 7232 | Separated pairs (disjoint declared supports and returns) have only target-response or chord blockers; C(sigma,2) <= sum C(d_D,2) + sum C(d_R,2) + /Sep/. | yes | F05 F01 G07 F04 | bound | 77, 78 |
| 76 | `scalePressure` | 7223 | Scale pressure: C q + 15/H/ < 3s + K h_R + 584 nu + 32 sigma_W (q = ceil sqrt n). | yes | H01 G08 | bound | 79 |
| 77 | `freeSideStructure` | 7224 | Every free pair is two ports with disjoint declared supports, T, returns, distinct centres, no obstruction, and one triangular port or one centre in the other's T. | yes | F04 F05 D05 | decomposition | 78 |
| 78 | `freeSideCount` | 7225 | /Pi_free/ <= tau sigma + Lambda; capped-arm form of G2; bounds in Delta. | yes | H09 H05 H01 G07 | bound | 74, 96 |
| 79 | `highSurplusOrder` | 7214 | 8n <= 32 s + 125 s^2 at s = n - C ceil sqrt n - 1; every t with 125t^2+24t < 8(C^2+C+1) has n > C^2+C+1+t. | yes | G08 I04 | bound | 84, 85 |
| 80 | `windowChargeKinds` | 7215 | Window structure of the canonical charge and recorded activation facts (early-blocked same-hub pairs, no profile obstruction). | yes | H02 H04 D08 | decomposition | 69, 81 |
| 81 | `responseObstructionTargetDefect` | 7216 | Every target-response obstruction of G is a residual target defect. | yes | E09 F04 | classification | 113, 114 |
| 82 | `highEndpointSwitch` | 6704 | Switch at every high/baseline edge hc: forced path by same-vertex or two-edge switch. | yes | E03 C01 D03 | witness | 16 (witness clause b), 19-22 |
| 83 | `edgeSurplusIdentity` | 6606 | 2m = 3n + sigma. | yes | A02 A05 H01 | identity | 86, 92, 105 (same identity, counted once) |
| 84 | `ceilSqrtAboveScale` | 6612 | C + 1 <= ceil sqrt n. | yes | G08 | bound | 85, 76 |
| 85 | `orderAboveScaleSquare` | 6613 | C(C+1) + 9 <= n. | yes | A01 G08 I04 | bound | 79 |
| 86 | `sixVertexExtremalEnvelope` | 6614 | m + 4 <= 2n (from ex(6, C4) = 7). | yes | A02 A13 I06 | bound | 118 (m+2<=2n weaker) |
| 87 | `highDegreePositive` | 6609 | 1 <= /H/. | yes | A05 A06 | bound | 88 |
| 88 | `highDegreeSurplusCapacity` | 6610 | sigma <= /H/ (n - /H/ - 3). | yes | A05 A06 | bound | 62 |
| 89 | `canonicalCapacityExplicit` | 6665 | G's canonical capacity presentation is the explicit one (recorded activation on P0). | yes | D08 | identity | 90-98, 119 |
| 90 | `canonicalTokenCount` | 6667 | /T_cap/ + 2(order-1) nu = 4n + 3 sigma + 3 order nu. | yes | G02 G07 A01 | identity | 92, 26 |
| 91 | `canonicalBlockedFreePartition` | 6668 | /Pi_blk/ + /Pi_free/ = C(sigma,2) at the canonical ledger. | yes | G07 H06 | identity | 92, 117 |
| 92 | `canonicalLedgerDeficit` | 6669 | Deficit G2: c^2 K + 2 M0 (8n+sigma-/T/) <= 2(/Pi_free/-B) + 2(/Pi_blk/ - M0/T/). | yes | H01 H09 H05 | bound | 95, 96, 93 |
| 93 | `pairCountDeficit` | 6670 | Pair-count deficit G3: c^2 K + 2 M0 (8n+sigma) <= 2(C(sigma,2) - B). | yes | H01 H09 | bound | 92 |
| 94 | `canonicalCertificationCriterion` | 6671 | Certified ledger exists iff /Pi_free/ <= B. | yes | H09 I03 | identity (iff) | 95, 96, 98 |
| 95 | `canonicalOverloadOfFits` | 6674 | If /Pi_free/ <= B: blocked side overloaded and some token has load > M0 with an L_geom role-homogeneous matching or star. | yes | H05 D04 G04 F07 | bound + witness | 127, 124 |
| 96 | `canonicalFreeExcessOfCapped` | 6675 | If every token load <= M0: free side exceeds B. | yes | H05 H09 F07 | bound | 94, 78 |
| 97 | `paperBudgetBound` | 6672 | E_paper <= B at the canonical spine family. | yes | H09 | bound | 98 |
| 98 | `paperBudgetCertifies` | 6673 | /Pi_free/ <= E_paper certifies the canonical certified ledger. | yes | H09 | bound | 94 |
| 99 | `pairCodeConfiguration` | 6676 | Where G sits in the pair-code chain: [137]->[143] configuration, or canonical first failure ([182] residual), or obstruction handoff with Type B fan entry. | yes | E09 D08 | classification | 129 (routing) |
| 100 | `sparseSurplusSurvivor` | 119 | G survives the five sparse surplus exits (DeclaredSparseSurvivor). | yes | E09 | exclusion | not_spec_of_survivor; 129, 116 |
| 101 | `openPortSuppression` | 435 | Open-port suppression: for every compatible family of G, its vertex/left/right/centre configuration, disjointness, injectivity, CenterCapacity <-> centerLoad <= deg - 3, and the adjacency of G/Q. | mixed: the configuration and capacity clauses are about G; the last clause (adjacency of the suppressed graph G/Q) is not | D03 D07 | classification |  102, 104 |
| 102 | `openPortSuppressionSafe` | 436 | For every compatible family with capacity, every vertex of G/Q has degree >= 3. | no: degrees of the suppressed graph G/Q | - (nonG: none earned) | bound | nonG |
| 103 | `singleOpenPortSuppressionWitness` | 437 | Every high-centre configuration has an open-port witness path in G avoiding the port vertex with restored length 2^j-1. | yes | C01 C04 C12 | witness | 107 |
| 104 | `suppressedFamilyCriticalCycle` | 438 | Every compatible family with capacity has an accepted cycle of G/Q using a chord; every accepted cycle of G/Q expands to a simple cycle of G with non-accepted length. | mixed: first conjunct and the hypothesis cycle are in G/Q; the expanded cycle is in G | - (nonG: none earned) | exclusion | nonG (G/Q part) |
| 105 | `sparseSlackSurplus` | 109 | 2m = 3n + sigma (duplicate of 83 under the [126] publication). | yes | A02 A05 | identity | 106; duplicate of 83, not counted twice for H01 |
| 106 | `activeSurplusFamily` | 110 | /P_exc/ = sigma; each selected port has centre degree > 3, endpoint degree 3 and exactly 2 shoulders. | yes | A05 D03 F01 | decomposition | 107, 108 |
| 107 | `sparsePortActivation` | 111 | Each selected port carries a return path R_p; open ports a suppression witness in G-x(p); triangular ports a triangle. | yes | C02 C01 D01 C12 | witness | 108, 130, 77 |
| 108 | `activeSurplusDemands` | 120 | The active surplus family: sigma members each with canonical return. | yes | F01 H06 D03 | decomposition | 111, 117 |
| 109 | `baselineSpineDemand` | 112 | Canonical baseline spine family exists with its spec (cubic baseline budget B0(n), room, deficit E_spine). | yes | G03 G01 H09 | identity | 120, 121, 97 |
| 110 | `freePairCountFails` | 1600 | The free-pair entropy sandwich fails (negation). | yes | G03 G01 G05 | exclusion | 129 (routing), 95 |
| 111 | `dependentPairFamily` | 201 | Some pair of the schedule has a nonempty blocker set at the canonical activation. | yes | F07 F02 | witness (existence) | 116, 66, 99 |
| 112 | `pairDegreeProfileFibres` | 2902 | Determination certificates of scheduled pairs identify only coordinates in one boundary-degree fibre. | yes | E06 B06 | exclusion | 9, 113 |
| 113 | `pairNoProfileObstruction` | 2904 | No scheduled pair has a type-(d) profile obstruction. | yes | E09 B06 | exclusion | 111, 81 |
| 114 | `pairNoResponseObstruction` | 2901 | No scheduled pair has a type-(e) response obstruction. | yes | E09 B07 | exclusion | 111, 81 |
| 115 | `blockedPairNoExit` | 1602 | No sparse surplus exit settles the dependence. | yes | E09 F07 | exclusion | 129, 116 |
| 116 | `canonicalBlockerRoute` | 144 | Blocked pair with canonical blocker min_prec Blk(pi) at the canonical activation. | yes | D08 F03 I02 | identity | 117, 127 |
| 117 | `canonicalPairLedger` | 113 | /Pi/ = C(sigma,2); Pi_blk and Pi_free exhaust it; /Pi_blk/ = sum mu(B); a blocked pair exists. | yes | G07 F01 H06 F02 H02 | identity | 91, 122 |
| 118 | `sparseUpperEnvelope` | 129 | m + 2 <= 2n; window/remainder incidence identity at P0. | yes | A02 A13 A10 H01 A07 | bound + identity | 86, 25 |
| 119 | `capacityTokenLedger` | 114 | Capacity-token ledger: /T_cap/ accounting identities at the canonical presentation. | yes | G02 G07 H05 | identity | 122, 90 |
| 120 | `blockedPairEntropySetup` | 356 | Blocked-pair entropy setup: canonical capacity, spine family, /schedule/ = C(sigma,2). | yes | G01 G03 | identity | 121 |
| 121 | `blockedPairEntropySandwich` | 242 | 2^(/spine/ + /free side/) <= skeleton budget at G. | yes | G01 G03 G05 G06 | bound | 110, 66, 99 |
| 122 | `roleFibrePartition` | 115 | Exact partition of C(sigma,2) into Pi_free and class/token/role fibres; caps by Cap_hom(L) S_C. | yes | G04 G07 H06 | decomposition | 123, 124 |
| 123 | `fibrePressure` | 116 | High-load display C(s,2) <= E + L_max/T_cap/; a role fibre carries a Q_st-th of the load and contains a matching or star. | yes | G04 H05 D03 | bound | 124, 127 |
| 124 | `sparsePressureOverload` | 128 | Coupled excess D_all at the geometric caps is positive at the canonical certified ledger. | yes | H05 H09 | bound | 66, 99, 127 |
| 125 | `bridgeless` | 226 | Every edge of G lies on a cycle (bridgeless). | yes | B02 C02 E03 | exclusion | 4, 50 |
| 126 | `highCentreNormalForm` | 72 | Every high centre has cubic neighbours, a matching in N(h), and no common neighbour outside {h} for a nonadjacent pair. | yes | D03 D02 A06 | classification | 22, 82 |
| 127 | `homogeneousBottleneckPattern` | 141 | Canonical role-homogeneous same-token L_geom-matching or star at the overloading token, with declared same-root connector configuration. | yes | D03 D04 D07 G04 | classification | 129, 128, 130, 66 |
| 128 | `homogeneousCapsFail` | 601 | Homogeneous caps fail at the canonical ledger. | yes | H05 G04 | exclusion | 129 |
| 129 | `bottleneckRouting` | 142 | The canonical pattern routes to a sparse surplus exit, to the same-token Type B handoff, or to the unresolved pair. | yes | D03 E09 | classification (three-way disjunction) | 138, 137, 100 |
| 130 | `sameTokenPatternSupports` | 6804 | Routing exists; each pattern pair p,q has declared support X = select?(seed), connected, with two distinct vertices. | yes | B08 D08 B01 F04 | decomposition | 138-142 |
| 131 | `sameTokenPatternSwap` | 6805 | The swap of ret_q by ret_p and of ret_p by ret_q in G is G itself (every G-edge of G[Y] lies in G[X]) or loses the baseline at a tight endpoint of a private edge. | yes | E03 E05 A04 D07 | decomposition (exact dichotomy) | unconsumed at [144a] (returned only); needs combination with 142 |
| 132 | `windowClassOverload` | 130 | The canonical overload token lies in T_W. | yes | G04 D08 | classification | subtype selection; 129-138 for windowFails |
| 133 | `windowClassAbsent` | 131 | The canonical overload token lies outside T_W. | yes | G04 D08 | classification | subtype selection |
| 134 | `remainderClassOverload` | 132 | The canonical overload token lies in T_R. | yes | G04 D08 | classification | subtype selection |
| 135 | `remainderClassAbsent` | 133 | The canonical overload token lies outside T_R. | yes | G04 D08 | classification | subtype selection |
| 136 | `primitiveClassOverload` | 1603 | The canonical overload token lies in T_prim. | yes | G04 D08 | classification | subtype selection |
| 137 | `typeBHandoffFails` | 1801 | Exact complement of the same-token Type B handoff of G. | yes (negation of 129's second disjunct) | - (bookkeeping) | bookkeeping: pure branch tag; the complement carries no observable of its own, its content is 129 with the disjunct removed | 138 |
| 138 | `sameTokenPatternUnresolved` | 1802 | ENTRY TEST. Routing exists, r_p != r_q, Z = select?(X_p u X_q); boundary-degree profiles of the two readings at Z differ, OR glue(G-Z, X_p) and glue(G-Z, X_q) have the same cycle status. | yes (actualGlue is a subgraph of G) | B06 B07 D08 | classification (disjunction); second disjunct true for every pair at a target-avoiding G | 139, 140, 141, 142 (all at the same Z) |
| 139 | `sameTokenReadingsNotReplacement` | 2905 | At Z, no retained reading of G[Z] (any vertex subset) keeps the profile of G[Z], has the baseline in the glue, and is lexicographically smaller than G. | yes (retainedPiece/outside glue = subgraph of G) | E05 E07 B06 D09 | exclusion | 141 (transplant is not a reading), 138 |
| 140 | `sameTokenPairPartition` | 6806 | Exact partition at Z: X_p,X_q subset Z, Z connected; (U1) a separating boundary count at some b in bdry(Z), or (U2) equal counts with the G-only agreement in G-Z, free or shared; the one-sided region is empty. | yes | B05 B06 B03 B07 D05 D06 D08 D07 A10 A11 B01 | decomposition | 138, 141 (equal-count bijection contactEquiv unused as fact) |
| 141 | `sameTokenTransplantSize` | 8000 | Transplant of X_q (and of X_p) into Z: int(X') <= int(Z), linkage-included, profile iff no boundary vertex has a neighbour in D = int(Z)-Y, baseline iff kept degrees >= 3, and baseline+linkage force int(X') = int(Z). | yes (transplant = G-D, a subgraph) | E02 E03 E05 A01 A11 B04 B05 B06 B07 B09 C13 D09 H10 | replacement (exact conditions) + size equality | 142, 139, 11 |
| 142 | `sameTokenTransplantDeficit` | 8001 | The transplants of X_q and of X_p are exact: D empty with no deficit, or the canonical vertex v (first in G's order) lies in Z \ D, has a neighbour in D, and keeps fewer than 3 neighbours outside D. | yes | A04 A11 B09 E03 E08 E09 H01 D10 I02 | decomposition + obstruction (canonical deficit vertex) | 141; unconsumed by any inequality (returned only) |
| 143 | `sameTokenUnresolvedDecided` | 8100 | At the pinned Z: r_p != r_q; both readings actualGlue(Z,X_p), actualGlue(Z,X_q) are target-free and agree in G-Z; the arm "equal profiles and separated by G-Z" is empty. | yes (actualGlue is a subgraph of G) | B07 E06 B06 | exclusion | 138 (decides its test), 144, 145 |
| 144 | `sameTokenReadingsExact` | 8101 | Each edge restriction actualGlue(Z,Y) drops no edge of G[Z] with an interior end (it is G) or drops one, is lexicographically smaller than G and fails the baseline. | yes | E05 E02 B04 A04 E07 | replacement (exact) + minimality | 139 (special case), 145 |
| 145 | `sameTokenSwap` | 8102 | Rerouted swap P->Q at G, both directions: |int S|+|int Z n P| = |int Z|+|int Z n Q|; profile of G[Z] iff n_Q(b)=n_P(b) at every b in bdry(Z), with the copy attachments equal to the order-bijection images of the P-neighbours; baseline iff no vertex of G is deficient in any of four roles; linkage inclusion or a linkage using a vertex and its copy (and it holds when int Z n Q subset P); valid => |int Z n P| <= |int Z n Q| and not lexicographically smaller than G; every accepted cycle of the glued swap uses a vertex and its copy. | yes (S built from G, no other graph; linkages are subgraphs of the swap) | F06 B07 D07 E07 E05 E02 A01 A04 B04 B05 B06 C13 D09 | replacement (exact conditions) + size relation + descent + response | 146 |
| 146 | `sameTokenSwapExact` | 8103 | Each swap is valid (no deficient vertex, linkage-included, size inequality), or the canonical exceptional vertex swapDeficit lies in Z and is deficient in a role, or a linkage uses a vertex and its copy; both valid => |int Z n X_p| = |int Z n X_q|. | yes | F06 E03 E07 A04 A11 B09 E08 | decomposition + obstruction (canonical deficit vertex) + equality | returned only |
| 147 | `sameTokenU2FreeWhole` | 8104 | Neither support meets bdry(Z) and both glued transplants keep the baseline => X_p = X_q = Z, bdry(Z) empty, Z = V(G), every vertex outside a pair seed is a cut vertex of G. | yes | B01 B02 B04 E05 D06 | decomposition + exclusion | returned only |
| 148 | `sameTokenSeedCover` | 8105 | Each pair seed is at most 2 delta vertices and the supports of two canonical port paths (a triangular port: shortest return in G-cx, induced; an open port: suppression path), each with unaccepted-span chords and one stub per interior cubic vertex; with every degree-3 vertex in both seeds, the cubic vertices lie in 4 paths + 4 delta vertices and 3n <= 5(|T|+|P1|+|P2|). | yes | C01 C02 C06 C08 A03 A11 | decomposition + identity + bound | 147 (whole-graph arm), returned only |

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

1. **F06 Cancellation and repair structure (the swap)**. Present at G: the pair (p,q) is blocked (116), homogeneous with equal labels (127), and unresolved at Z (138) only through the vacuous disjunct; 131 and 141-142 build only edge deletions and the smaller transplant. Missing observable and certificate: canonical swap graph S(G,Z) (interior of X_p replaced by the interior of X_q inside Z, equal interior size) and its canonical degree-deficit vertex, or a target cycle of S(G,Z) mapped into G; certificate: replacement. Technique: T03 local graph modification (+T13 for the deficit). Existing facts it combines with (27): 3, 4, 7, 9, 10, 11, 12, 19, 20, 22, 63, 66, 82, 107, 111, 112, 116, 124, 127, 129, 130, 131, 138, 139, 140, 141, 142.
2. **H03 Connected negative support**. Present at G: Z is connected (140), contains the canonical deficit vertex when D is nonempty (142), and the canonical excess D_all is positive (124); no sign fact for a connected support. Missing observable and certificate: signed net charge of the connected region Z (and of D) in the units of 92/93; certificate: bound. Technique: T13 potential and discharging. Existing facts it combines with (18): 24, 25, 43, 46, 59, 71, 76, 83, 92, 93, 95, 96, 118, 124, 130, 140, 141, 142.
3. **H07 Flow-cut support**. Present at G: the pair schedule (C(sigma,2) demands), the tokens and incidences at bdry(Z) form a bipartite demand-support network (117, 119, 122); only counts and assignments are stated. Missing observable and certificate: integral flow of the pair demands into the incidences at bdry(Z) with a cut; certificate: identity or obstruction. Technique: T14 demand-supply and flow. Existing facts it combines with (16): 24, 25, 26, 69, 70, 75, 77, 78, 90, 91, 108, 117, 119, 122, 140, 141.
4. **C07 Cycle-space interaction of the two returns**. Present at G: the ports p and q have distinct return cycles (107, 127; r_p != r_q by 138); their symmetric difference is not measured. Missing observable and certificate: incidence vectors of the return cycles of p and q and their symmetric difference with its length; certificate: identity. Technique: T08 path-cycle and cycle-space analysis. Existing facts it combines with (16): 4, 19, 20, 22, 29, 30, 34, 36, 37, 56, 82, 103, 107, 127, 130, 138.
5. **C06 Ear structure of returns and private edges**. Present at G: return paths R_p, R_q (107) and the private-edge set of the swap (131) are attached to G[X]; the attachment only at their ends is not stated. Missing observable and certificate: ear decomposition of R_p, R_q and of E(G[Y])\E(G[X]) over G[X]; certificate: decomposition. Technique: T08. Existing facts it combines with (11): 14, 38, 39, 48, 49, 103, 107, 130, 131, 140, 141.

`~` rows, ranked by combined facts:

6. **B07 Response of the swapped piece**: missing response of the piece-for-piece swap (see F06); technique T05; combines with 9 facts: 9, 10, 16, 63, 114, 138, 139, 140, 141.
7. **E08 / A07 Peelability and core of G-D**: missing peeling sequence of D from G to the 3-core; technique T19 / T04; combines with 6 facts: 3, 5, 7, 118, 141, 142.
8. **D07 Equal-response identification of the two readings**: missing explicit bijection of the equal-count contacts (contactEquiv) as a ledger fact; technique T16; combines with 5 facts: 127, 131, 138, 140, 141.
9. **B01 Components of G-Z and G-D**: missing components of the rest; technique T04; combines with 5 facts: 5, 130, 140, 141, 142.
10. **E07 Descent on equal-size alternatives**: missing lexicographic comparison of the swapped object with G; technique T16; combines with 4 facts: 11, 139, 141, 131.

Other `~` rows (A12, B04, C11, D06, F02, F03, F08, G05, H02, H10, I05) have their missing accounting stated in Table 1. Reading of the ranking: F06 is the swap the paper needs; it is the only gap whose absence is exactly the defining failure, and it sits at the top of the count too (27 facts, including the whole switch/return family 19-22, 107, and the exclusions 9-12, 139, 141).

## Non-G facts

| # | Key | Non-G object | G-constructed replacement |
|---|---|---|---|
| 18 | `noSuppressionChordViolation` | cycles of the suppressed graph G/Q | For each compatible family, state the lifted length `|walk|+|chords|` of every G-cycle through the restored ports directly in G (the expansion), as a path statement in G minus the deleted vertices |
| 21 | `highCentreSplitForced` | supergraph G u M_h with added edges | The G-form: for nonadjacent neighbours u1,u2 of h, a path u1-u2 in G-h with |p|+2 accepted (a path in G, cycle closed through h); 22 already gives the same-vertex switch version at deg >= 5 |
| 101 (last clause only) | `openPortSuppression` | adjacency of G/Q | Drop the G/Q adjacency clause; the configuration and capacity clauses (G) are kept and earn D03, D07 |
| 102 | `openPortSuppressionSafe` | degrees of G/Q | The closed formula deg_{G/Q}(v) = deg_G(v) - (deleted neighbours) + (chord ends at v) as an identity over G-degrees, which yields the >= 3 bound from centerLoad <= deg - 3 (already in 101) |
| 104 | `suppressedFamilyCriticalCycle` | the accepted cycle of G/Q (first conjunct and hypothesis of the second) | Its expansion, the simple cycle of G with one extra edge per used chord and non-accepted length, stated without the G/Q cycle |

Borderline cases kept as facts about G, with the reason: 1 `selection` and 11-12 quantify over smaller objects / candidate pieces X', but assert no witness on them (they are extremality and exclusion statements about G); 138-142 use `actualGlue`, the retained pieces and the transplant, all of which are subgraphs of G (`actualGlue_hom`, `Transplant`: glue = G - D).

## Outside the register

- **Swap object as a piece-for-piece replacement.** Observable: the graph S(G,Z) obtained from G by replacing the interior of Z by an isomorphic copy of the interior of X_q (respectively X_p) on the same boundary labels. It fits F06/E05 but has no coordinate of its own beyond them; recorded here to prevent it being forced into a row.

## Cross-check results

1. Every coordinate code in Table 2 has status x or ~ in Table 1 and lists the fact: **pass** (generated by inversion; no Table-2 code sits on a gap, n/a or nonG row).
2. Every x or ~ in Table 1 cites at least one Table-2 row: **pass** (81 rows, each derived from Table 2, none empty).
3. Every Table-2 row accounts for at least one coordinate or is bookkeeping: **pass with the flagged rows** 137 (bookkeeping: branch tag, complement of the handoff) and the four nonG rows 18, 21, 102, 104, which by the G-only rule account for no coordinate (their replacements are in the Non-G section).
4. No fact counted twice for the same demand in different currencies: **pass with one merge**: 83 and 105 state one identity (2m=3n+sigma) and count once. 92, 93, 95, 96 are different inequalities of the same ledger (G2, G3 and two implications) and are each listed once per coordinate; 141 (size equality) and 5 (no proper baseline subgraph) both feed E02 as different demands (minimality of G versus of the transplant).

Caveats on marks. (a) Global facts about G (A-group, G-group) are accepted at G; boundary/support coordinates (B, D06-D07, E05-E09) require the certificate at Z, X_p, X_q. (b) "Combined" is read inside the residual: through a shared statement, ledger identity or the routing decision 129/138; the leaf [144a] itself has no closing inequality. (c) Rows 141/142 were marked from the Lean statements `SameTokenTransplantAt` / `SameTokenTransplantExactAt`.

## After G audit S144a

- **Built (gap or ~ to x).** F06 (the rerouted swap `swapPiece`, facts 145-146), B07 (response of the swapped object: every accepted cycle uses a vertex and its copy, fact 145), D07 (order-fixed equal-count contact bijection `orderEquiv` and the copy-attachment identity, fact 145), E07 (descent: a valid swap is not lexicographically smaller than G, equal interior sizes when both swaps are valid, facts 145-146). Fact 143 records that the entry test is decided at G; fact 144 that every edge-restricted reading is G or loses the baseline; fact 147 is R5's unimplemented boundary-free argument.
- **Still `gap`: H03, H07, C07** (C06 moved to `~` by fact 148, the port paths and their stubs). They are present at G (Table 1) but the `[144a]` test does not consume them: the pair test consumes swap validity (profile, degrees, linkage, size, descent), which is now measured. They enter only through the token-flow and return-cycle currencies of the parent routing (facts 24-26, 103, 107), not through the unresolved pair.
- **Still `~`.** B01 (components of G-Z and G-D), E08/A07 (iterated peeling of D), A12, B04, C11, D06, F02, F03, F08, G05, H02, H10, I05: unchanged from the table above.
- **Closure test (explicit).** The swap facts, the reading facts and 147 were combined with the partition arms: U2-free with both transplants valid is `X_p = X_q = Z = V(G)` (there the swaps are the identity, so no contradiction is derived from them); U1 and U2-shared give contact counts `c_Y(b)` that include `dZ`-neighbours, while the swap profile identity counts interior neighbours only, so neither refutes it. No arm closes; the remaining proposition is `K .sameTokenSwapExact` at the two swaps, with the boundary-free arm reduced to "both pair supports are all of V(G)".
- **Non-G facts 18, 21, 101 (last clause), 102, 104** are on the shared entry prefix (suppressed graph `G/Q`, supergraph `G ∪ M_h`); they are not on the `[144a]`-specific path and are not touched here.
