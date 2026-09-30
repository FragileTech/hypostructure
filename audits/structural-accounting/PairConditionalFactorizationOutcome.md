# Structural accounting: `PairConditionalFactorizationOutcome` (node [182])

> Coverage: the generic `PairConditionalFactorizationOutcome` has 120 facts, as in the section "Rows read at the canonical obstruction `F₀`" (119 + `pairCorrelation`). Subtype extras (+3/+8/+12/+12/+17/+21) match, except `K .pairUncrossing` (register, "follow-up 2 (uncrossing, repetition)"), a conjunct of the realizability subtypes that this report does not account. Fact list compared with the `Holds` conjuncts of the Lean abbrevs in `Assembly/Residuals.lean` and `Assembly/Residuals/`.

**Defining failure.** The first failed coverage implication of the pair-code chain [178]/[179]/[180] on the strict-surplus branch (sigma above the scale threshold), at G's canonical objects: after the entropy count fails at the canonical realization of the spine code (free side: [131] `freePairCountFails`; blocked side: [137] `blockedPairCountFails`), the retained residual is one of (a) [178] the canonical overlap system does not satisfy conditional factorization (the product-code realization of separated pair supports fails in the fixed-(n,m) skeleton fibre), (b) [179] the canonical return system has no realizability outcome (no target cycle, target defect, compression or Type B handoff, and no serial system), (c) [180] the canonical serial system has no increment outcome (no full-modulus arithmetic input and no periodic routed outcome).

**Facts.** The Lean abbrev has **119** conjuncts (generic residual, all six subtypes; with `pairCorrelation` the generic residual has 120, see Coverage). Six subtypes add extras (22 distinct keys, 3 to 18 facts each): 141 distinct keys in Table 2.

**Status counts (88 coordinates, generic residual 119 facts; subtype extras noted in the cells):** x = 65, ~ = 18, gap = 2, n/a = 3, nonG = 0 (no coordinate is touched only by nonG facts). Facts marked nonG in Table 2: 3 (9 degreeProfileFibres, 10 targetCompleteContextUniversality, 64 admissibleQuotientsLabelInjective).

Marking notes. (1) G-only rule applied to the exact Statements. `actualGlue G Z X` is a subgraph of G, so readings glued into `G - Z` are G facts. (2) The [178] response (`SparsePairSkeletonModel.response`: a class member's reading of X_pi glued into `G - X_pi`, `memberPiece`) and the labelled (n,m) class count are accepted as G-side per the audit context; facts that speak through them carry that tag in the G column. (3) Table 1 statuses are relative to the generic residual; where a subtype-only extra carries the certificate it is named in the cell. (4) "Consumed by" lists facts sharing a quantity in one inequality/identity/decision with the row, read off the Lean statements; every fact is also a conjunct of the residual.

## Table 1 — Structural coordinates


### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 17, 27, 56, 80, 84, 85, 86, 87, 106, 115, 116 | induction parameter / threshold | T01 T12 | none for the accounted part |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 84, 87, 106, 112, 115, 116 | sparse branch and counting budget | T01 T12 | none; 8 (cycle rank) is a separate ~ row |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 6, 7, 32, 41, 43, 44, 47, 53, 55, 58, 62, 63, 66, 74, 75, 77, 88, 89 | degree-class counts and case splits | T01 T07 T15 | none for the accounted part |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 2, 3, 5, 7, 79, 103 | core / bounded-high-degree branch | T01 T02 T04 | none for the accounted part |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 27, 32, 56, 62, 65, 77, 80, 84, 89, 94, 106, 107, 116 | distance from regularity and excess supply (sigma, sigma ports) | T01 T13 T15 | none for the accounted part |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 7, 42, 46, 57, 61 | hub non-adjacency, link and two-hop distance bounds | T01 T07 | none for the accounted part |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | x | 5, 42, 46, 47, 48 | degeneracy bounds of link graphs and of R | T04 T15 | none for the accounted part |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | — | — | — | Absent at G: delta(G) >= 3 (fact 3, threshold 3 by fact 2) so G has no degree-two vertex, hence no degree-two chain. The suppressed derived graph (102-105) keeps degree >= 3 (103). |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 29, 34, 36, 61 | wedge counts (nonadjacent pairs of N(h), C(d,2)) entering cycle counts | T01 T07 T15 | none for the accounted part |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 25, 26, 45, 52, 112 | crossing counts e(R,W) and closed-class bound | T01 T14 | none for the accounted part |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 25, 26, 39, 112 | boundary degree deficit def+(R) <= e(R,W) | T01 T13 | none for the accounted part |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | bound (2 beta >= n+2) | T01 | Proved (fact 8) but combined with no pair-code inequality; cycle space of the overlap support and of the closing cycles unmeasured (see C07). |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 51, 52, 87, 112, 116 | linear sparsity slack, globally and over every subset | T01 T13 | none for the accounted part |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 54, 56, 58, 59, 60, 63, 65, 88 | bounded exceptional set: \|H\| <= sigma, 5\|H\|+sigma <= 2n, sigma above scale | T01 T13 | none for the accounted part |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | x | 5, 33, 45, 48 | components of G, of G-h, of R and closed classes | T04 | none for the accounted part |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 24, 28, 51 | no bridge; >= 2 edges leave every nonempty proper set; 2+2 cut vertices | T04 | none for the accounted part |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 28, 33, 34, 35, 69 | block structure at cut vertices, first separator of the Type B handoff | T04 | none for the accounted part |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 20, 30, 31, 37 | disjoint-path exclusions (two paths meeting only at x) and >=2-edge cuts | T04 T08 | No Menger number: the maximum number of internally disjoint paths between the two demands of the failed pair inside the overlap support is not recorded (only forced meeting of forward/backward routes in 69). |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 11, 23, 25, 26, 28, 39, 118, 132 | boundary of Z, X_pi, R, W with terminal degrees | T05 | none for the accounted part |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | ~ | 11, 12, 132, 133 | boundary-degree exclusions (11, 12, 132, 133) | T05 T16 | Boundaried type (ordered terminals, degree profile) of the canonical failing supports X_pi and of the overlap support is not recorded; 9, 10, 64 (nonG) are not counted. |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 16, 23, 82, 128 | G-form context equivalence: G - Z never separates two readings | T05 | none for the accounted part; abstract-quotient forms 9, 10 are nonG and not counted |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 23, 113, 118, 124 | minimal connected support of the failed extension / overlap support | T10 | none for the accounted part |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 25, 26, 27, 81, 90, 109, 138 | demand-support relation: def+ vs e(R,W), primitive carrier, token capacity | T05 T14 | none for the accounted part |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | ~ | 19, 20, 22, 35, 37, 38, 48, 49, 61, 83, 104, 108, 129 | forced simple paths with accepted closing length at switch ports, returns, suppression witnesses | T08 | Set of attainable path lengths between the failed pair terminals (needed by [179] serial system) is only in the subtype-only 129 as a witness; no generic length-set observable. |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 24, 35, 108, 109, 125 | return sets avoid the shifted accepted set; canonical return paths per demand | T08 | none for the accounted part |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 18, 30, 34, 36, 48, 105 | cycle-length spectrum of G: no dyadic length; cycle counts | T08 T12 | none for the accounted part |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | ~ | 2, 4, 22, 35, 40, 57, 69, 104, 130 | residues mod 4, parity, dyadic closing constraints, serial closing lengths non-accepted (69) | T08 T09 | Arithmetic class of the canonical serial system (modulus, frequent increments, offsets/smear, order of 2 mod modulus) is not recorded by any fact; 130 asserts only the failure of coverage. |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 20, 30, 31, 37, 38 | two-path / theta constraints at a common endpoint and fan/chain rigidity | T08 T10 | none for the accounted part |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | x | 49, 102, 104, 105, 108, 129 | ears: suppression shoulder paths, chords, serial cell pieces | T08 | none for the accounted part |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | ~ | 36 | cycle counts and double count (36) | T08 T11 | Incidence vectors over E(G) of the two canonical closing cycles and their symmetric difference are not recorded; interaction of the left/right demand cycles is unmeasured. |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 14, 48, 49, 50 | induced window, packing, P13-free remainder, attachments | T06 T07 | none for the accounted part |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 17, 26, 53, 54, 91, 138 | packing number nu and 13 nu <= n, token identity with nu | T06 T15 | none for the accounted part |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 25, 26, 42, 45, 46, 47, 48, 49, 52 | structure of the remainder R: links, degeneracy, path bounds, closed classes | T06 T04 | none for the accounted part |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | 69, 129, 130 | forced serial-system properties (69) and existence witness (129, subtype) | T08 T09 T10 | Generic residual has only the case analysis 69; increment structure (base lengths, increments bounded by D_sp, closing) is a witness only in increment subtypes and is never combined with an arithmetic hit (130 is the failure). |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 39, 40, 41, 49, 50, 69, 107, 129 | endpoint degrees and external attachment counts at windows, ports, serial ends | T07 | none for the accounted part |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | x | 69, 76, 78, 126, 127, 129 | exact collision certificate: if realizability fails, forward and backward routes meet; separated-pair disjointness | T07 T10 T15 | none for the accounted part |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 15, 39, 40, 50 | attachment of outside vertices to windows / P13 (<=7 neighbours, legal labels) | T07 | none for the accounted part |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 2, 15, 40 | finite local type: legal labels (399), C1-safe adjacency | T07 T17 | none for the accounted part |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 21, 22, 29, 37, 38, 41, 43, 55, 78, 107, 125 | centre, typed neighbours, ports, pair compatibilities | T07 | none for the accounted part |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | x | 67, 68, 96 | matching-versus-star concentration inside the overloaded token role fibre | T15 | none for the accounted part |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 76, 78, 118, 124 | overlap counts of declared/return supports (76) and overlap system (118) | T10 | none for the accounted part |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 118, 119, 124 | existence of an obstruction to realizingOrder (118), minimal-connected version in 124 (subtype) | T10 | Size, support and shape of the minimal connected overlap obstruction are not measured in the generic residual; 119 is an existence claim. |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 67, 68, 96 | equal signatures: role-homogeneous patterns and token roles | T16 | none for the accounted part |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 90, 109, 110, 113, 118, 121, 125, 136, 137, 139, 141 | canonical packing, capacity, spine, first failure, rank order | T02 T16 | none for the accounted part |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | ~ | 118, 119, 122, 123, 126 | existence of the overlap system and of one of the three failing tests (118, 119); CF and its negation in subtypes (122, 123) | T05 T15 | The outcome of the graph-realization test (CF) at the canonical system is not decided in the generic residual; no compatibility/uniqueness statement for reconstructed skeleton readings. |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 59, 66, 83 | bounded exceptional configurations (deg >= 5 vertex or two deg-4 vertices; V-shapes) | T07 | none for the accounted part |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1 | minimality of G under the lexicographic order | T02 | none for the accounted part |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5 | no proper baseline subgraph | T02 | none for the accounted part |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 19, 20, 21, 22, 24, 33, 83, 102 | deletion / switch criticality (bridgeless, forced paths, vertex deletion) | T03 | none for the accounted part |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | x | 18, 101, 102, 103, 104, 105 | safe suppression and the excluded exits (b)-(e) | T03 | none for the accounted part |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 101, 128, 134, 135 | no smaller replacement / compression, no (e) obstruction | T03 | none for the accounted part; 64 (nonG) not counted |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 16, 82, 101, 128, 132, 133, 134 | G-form quotient distinguishability: readings never separated by G - Z; no profile/response obstruction | T05 T16 | none for the accounted part; 9, 10, 64 (nonG) not counted |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | ~ | 113, 118, 136 | canonical order on decompositions: least failed extension, rank injectivity, min_prec blocker | T02 T16 | No neutral-move descent: no strict decrease of a secondary order under a size-preserving replacement is recorded. |
| E08 | Peelability | A removable unit preserving the residual invariant. | n/a | — | — | — | Absent at G: no proper subgraph has delta >= 3 (fact 5) and delta(G) >= 3 (fact 3), so no removable unit preserves the baseline invariant. |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 16, 23, 69, 78, 82, 100, 101, 113, 119, 122, 126, 127, 128, 130, 134, 135 | completion/target-defect status of the first failed pair extension and of each early arm | T10 T02 | none for the accounted part |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 27, 71, 79, 90, 92, 94, 98, 107, 109, 110, 121, 131, 137, 139 | family of tests: sigma ports, C(sigma,2) pairs, spine family, tokens | T01 T15 | none for the accounted part |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | ~ | 114, 120 | independence dichotomy of the mixed family (114) and its free branch (120) | T11 | No rank number: the rank of the response family (or its maximum independent subfamily) of the pair coordinates is not recorded; rank field of 118 is an exposure order, not a linear rank. |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | ~ | 114, 124, 131 | sparse exit or (d)/(e) blocker at a dependent mixed family (114); minimal obstruction (124, subtype); Pi_blk nonempty (131) | T10 T11 | Inclusion-minimal dependent subfamily is not recorded at generic level; no size or support measured. |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | x | 76, 78, 113, 118, 124 | supports of the first failure, of pair responses, declared/return/T supports | T10 | none for the accounted part |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 76, 78, 120, 123 | separated pairs: disjoint declared and return supports, counted | T10 | none for the accounted part |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | gap | — | — | T08 T10 T11 | Present at G: 118 (failedFamily_obstruction) gives a family of response coordinates whose product code is not realized. Missing: the relation among those coordinates and the repair network of routes (observable: composite response relation and smaller support/corridor; certificate: smaller support, corridor or exact global profile). |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 100, 111, 114, 119, 120, 122, 131 | dichotomy: independent family (120) / dependent blocked family (131) / mixed dependence; count fails | T10 T11 T12 | none for the accounted part |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | gap | — | — | T09 T16 | Present at G: the serial system (129, increment subtypes) has length sets with increments bounded by D_sp. Missing: repeated response under additive increments (modulus, frequent set, base with base+modulus in lengths); certificate: finite response class, hit, or compression. 130 records only the failure. |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 110, 115, 116, 117, 121, 139, 140, 141 | size of the labelled (n,m) skeleton class vs 2^(\|spine\|+\|code\|) | T12 | none for the accounted part; class count accepted per context |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 2, 15, 27, 68, 71, 91, 138 | legal-state counts: 399 labels, token counts, \|tokens\| <= 8n+sigma | T12 T17 | none for the accounted part |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | ~ | 118, 122, 123 | realizingOrder needs >= 2 conditional values per step (encoded in 118, 122, 123) | T11 T12 | No quantity: the exact sizes (log2) of the conditional fibres conditionalValues at each exposure step of the failed family are not recorded. |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | x | 67, 73, 96, 97 | largest role fibre / overloaded token with load above cap | T12 T15 | none for the accounted part |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | ~ | 111, 118, 121, 122, 123, 124, 140, 141 | joint code count vs skeleton budget (111, 121, 140, 141), overlap (118) | T10 T11 T12 | Comparison of the joint state count with conditional products (fibre sizes) on the failed family is missing; the count fails but the correlation is not quantified. |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | ~ | 117, 121, 141 | state-count bound for any state map (117); canonical realization of the spine code (121, 141) | T05 T15 | Injectivity of the decoding of (baseline word, outside edges, exposed prefix) into labelled skeletons is not asserted; 64 (nonG) not counted. |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 36, 43, 44, 53, 62, 71, 79, 91, 92, 93, 137, 138 | tokens/edges/incidences charged once: dart identity, token partition, ledger identities | T15 | none for the accounted part |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 2, 65, 72, 77, 79, 80, 85, 86, 93, 94 | explicit thresholds and error terms (ceilSqrt, spine scale, C(C+1)+9 <= n) | T09 T17 | none for the accounted part |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 17, 47, 52, 54 | packing density 13 nu <= n and window density inequalities | T06 T12 | none for the accounted part |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 2, 25, 26, 52, 53, 84, 106, 112 | deficiency-surplus balance with order | T01 T13 | none for the accounted part |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | x | 51, 52, 53, 81 | superadditive slack over disjoint windows; density potential | T13 | none for the accounted part |
| H03 | Connected negative support | A connected region with negative charge. | n/a | — | — | — | Absent at G: fact 51 gives, for every proper S with \|S\|>=2, sum(d-3) <= \|S\|+bd(S)-6 and 52 gives slack over hanging windows nonnegative; no proper connected support has negative charge in this potential. |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | x | 70, 74, 81, 90, 95, 99, 138 | discharge from capacity to pairs: certified iff free <= budget; new-load bound | T13 T15 | none for the accounted part |
| H05 | Load and saturation | Load compared with certified capacity. | x | 67, 71, 72, 73, 74, 75, 79, 93, 96, 97 | token load against certified capacity (cap, overload witnesses) | T13 T14 T15 | none for the accounted part |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | x | 27, 70, 71, 74, 91, 92, 93, 136, 137, 138 | payment of pair demands by tokens with bounded multiplicity (ledger identities) | T14 T15 | none for the accounted part |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | ~ | 25, 26, 45 | cut inequalities e(R,W), closed classes <= e(R,W) | T10 T14 | No integral flow / matching of pair demands into legal supporting incidences on the graph-realizable interface; only cut-type inequalities. |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 32, 53, 54, 56, 58, 60, 63, 89 | total exceptional mass: \|H\| <= sigma, \|B\| bounds | T13 T15 | none for the accounted part |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 72, 75, 77, 79, 93, 94, 95, 96, 97, 98, 99, 110, 111, 115, 116, 117, 121, 140, 141 | required tests 2^(\|spine\|+\|code\|) vs the skeleton budget of the same (n,m) class; ledger deficit vs budget | T01 T11 T12 T13 | none for the accounted part |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 113 | well-founded index: least failed extension | T14 T19 | No one-unit peel step preserving interface response; only the index of the first failure. |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 2, 15, 40, 117 | finite label/state spaces (399 labels, skeleton class, token universe) | T07 T17 | none for the accounted part |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | ~ | 14 | canonical representatives of G-objects (P0, capacity, spine) | T16 T17 | Skeleton class is counted as labelled; no orbit representative / isomorphism reduction of the skeletons; 64 (nonG) not counted. |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 40, 62, 84, 91, 92, 137 | integer identities and exact collisions (dart identity, gap rule, ledger identities) | T15 T17 | none for the accounted part |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | x | 80, 85, 86 | explicit finite thresholds where the asymptotic argument starts | T17 | none for the accounted part |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | x | 2, 15, 40 | computational certificate: label census and barrier table row semantics at G | T17 | none for the accounted part |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | x | 2 | instance of imported HSS closure law at G and G[S] with exact hypotheses | T18 | none; used by 13 |

## Table 2 — Facts of the residual → structural coordinates

Subtype tags: fF/fR/fI = free side, [178]/[179]/[180] fails; bF/bR/bI = blocked side, same arms. Facts 1-119 are in all six.

| # | Key | idx | Subtypes | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | all six | G has no cycle of dyadic length (>=4) and no lexicographically smaller baseline object avoids the target | yes | E01 C03 | exclusion | 5, 11, 12, 24 (minimality reads it); every target-avoidance step |
| 2 | `cubicBaseline` | 221 | all six | Presentation laws: delta=3, s=4, 2 not accepted, accepted = dyadic, Labels(13) census 399, fan/deficit slacks, sparse-surplus identities, HSS closure law at G and G[S] (baseline and P13-free implies accepted cycle), scale family log2, net-cap slack, barrier-table row semantics | yes | A04 C04 D02 G02 G08 H01 I01 I05 I06 | identity + instance of imported theorem | 13 (HSS gives windowPresent), 15, 40, 65, 85, 86, 93 |
| 3 | `minDegreeBaseline` | 2850 | all six | delta(G) >= 3 | yes | A04 | bound | 5, 7, 102-105 (degree >=3 of suppressed graph), 55 |
| 4 | `returnAvoidance` | 1 | all six | for every dart, return-length set of G is disjoint from the shifted accepted set | yes | C02 C04 | exclusion | 24, 108, 109, 113 (returns), 125 |
| 5 | `noProperBaseline` | 2 | all six | no proper subgraph of G has min degree >= 3; G connected | yes | E02 B01 A04 A07 | exclusion | 11, 12, 51, 101 |
| 6 | `slackIndependent` | 4 | all six | vertices of degree > 3 are pairwise nonadjacent | yes | A03 A06 | classification | 43, 55-61, 62, 63 (hub/joint bounds) |
| 7 | `tightEndpoint` | 3 | all six | every dart of G has an endpoint of degree exactly 3 | yes | A03 A04 A06 | classification | 41, 66, 83, 107 |
| 8 | `cycleRankConstraint` | 425 | all six | n + 2 <= 2(m + 1 - n) | yes | A12 | bound | unconsumed (conjunct; not in any pair-code inequality) |
| 9 | `degreeProfileFibres` | 2300 | all six | for every region, every abstract CurvatureQuotient of its coordinates and any two readings: different boundary-degree profiles are not identified (follows from the quotient structure field `fibrewise`) | no: universal over abstract quotient structures (abstract Label/Value types, value map, representative fields) that nothing constructs from G | — (nonG: B06 B07 E05 E06) | n/a (nonG) | consumed by nothing at G; touches B06 B07 E05 E06 as nonG |
| 10 | `targetCompleteContextUniversality` | 2301 | all six | identified readings of any abstract CurvatureQuotient have equal profile and equal response in actualGlue (G-subgraph); second clause: no accepted cycle in any actualGlue G Z X | no: first clause universal over abstract quotient structures; second clause is G-only (vacuous) | — (nonG: B07 E05 E06) | n/a (nonG) | touches B07 E05 E06 as nonG; G-only half is decided by actualGlue_agree |
| 11 | `replacementExclusion` | 223 | all six | no connected proper support Z of G has a smaller baseline replacement piece with the same boundary-degree profile and no target cycle in glue(replacement, G-Z) | yes | E05 B06 B05 | exclusion | 12; early arm "compression" of [179]/[180] (128, 130 outcomes); 132-134 |
| 12 | `uncompressible` | 5 | all six | no support of G is a nontrivial target-complete compression (same clauses as 11) | yes | E05 B06 | exclusion | 128 (compression arm empty), 130 |
| 13 | `windowPresent` | 608 | all six | G has an induced path of order 13 | yes | C08 | witness | 14, 17, 39, 40, 48-50 |
| 14 | `maximalPacking` | 6 | all six | nu(G)>0; canonical packing P0 is a valid vertex-disjoint window family, \|P0\| = nu, and every induced window meets P0 | yes | C09 C10 C08 D08 I02 | witness + decomposition | 17, 25, 26, 39, 42-54, 90, 91 |
| 15 | `localAlgebra` | 7 | all six | \|Labels(13)\| = 399 and the first size-distribution entries are 13,60,122,122,63,17,2 | yes | D01 D02 G02 I01 I05 | classification | 40 (legal labels), 39 |
| 16 | `everyWitnessSpectrumSplit` | 6702 | all six | for every G-declared target-defect witness w and X in pairSupports: actualGlue G w.support X has no accepted cycle | yes | B07 E06 E09 | exclusion | 23, 82, 128, 130 (empty target-defect arm) |
| 17 | `packingOrderBound` | 6611 | all six | 13 * \|P0\| <= n | yes | C09 G09 A01 | bound | 26, 53, 91, 112 |
| 18 | `noSuppressionChordViolation` | 6620 | all six | no open-port suppression cycle has \|walk\| + \|chords\| accepted | yes | E04 C03 | exclusion | 105, 102-104 |
| 19 | `twoSwitchForcedPath` | 6800 | all six | two-edge switch of G with distinct ends, u1 not~ u2, deg v1,v2 >= 4 forces a simple u1-u2 path in G - {u1v1,u2v2} with accepted p+1 | yes | C01 E03 | witness | 20, 83, 69 (endpoint switch clause) |
| 20 | `crossSwitchFamily` | 6802 | all six | cross-vertex switch: forced u1-u path with accepted closing length; two 2^j-1 paths into two neighbours of h are never h-free and internally disjoint | yes | C01 C05 B04 E03 | witness + exclusion | 19, 30, 31, 37 |
| 21 | `highCentreSplitForced` | 6801 | all six | at every h with deg > 3, G plus the non-adjacent pairs of N(h) has an accepted cycle avoiding h through an absent edge | yes | E03 D03 | witness | 29, 83 |
| 22 | `sameVertexSwitchForcedPath` | 6803 | all six | non-adjacent neighbours u1,u2 of h (deg >= 5): forced simple path with accepted p+1, splitting exactly as (avoid h, p+2 not accepted) or (l1+l2=p, neither l_i+1 accepted) | yes | C01 C04 E03 D03 | witness + classification | 19, 20, 35 |
| 23 | `specWitnessStructure` | 6677 | all six | every canonical-support witness w of G: Z connected, contains both declared supports, minimum connected superset, and not w.Spec (G-Z does not separate) | yes | B05 B07 B08 E09 | decomposition + exclusion | 16, 82, 113 |
| 24 | `bridgeless` | 226 | all six | every edge of G has a simple return after its deletion (R_e(G) nonempty) | yes | B02 C02 E03 | exclusion | 4, 51, 108, 109 |
| 25 | `remainderDeficiencyBelowCut` | 6663 | all six | positive deficiency of the remainder R of P0 <= boundary incidences e(R,W) | yes | A10 A11 B05 B09 C10 H01 H07 | bound | 26, 45, 52, 112 |
| 26 | `windowCutCapacity` | 6664 | all six | e(R,W) + 2(order-1)\|P0\| <= 3*13*\|P0\| + ambient surplus of W | yes | A10 A11 B05 B09 C09 C10 H01 H07 | bound | 25, 52, 53, 112 |
| 27 | `primitiveCarrierCount` | 6666 | all six | \|primitive carrier\| = 4n + 2 sigma | yes | A01 A05 B09 F01 G02 H06 | identity | 91, 138, 71 (token counts) |
| 28 | `singleBoundaryShape` | 6627 | all six | a support with a single boundary vertex b has exactly 2 neighbours of b inside and 2 outside (deg b = 4, 2+2 cut vertex) | yes | B02 B03 B05 | classification | 35, 33 |
| 29 | `neighbourhoodPairCount` | 6900 | all six | G[N(h)] is a matching; N(h) has >= C(d,2) - floor(d/2) nonadjacent pairs; each x in N(h) has >= d-2 nonadjacent partners | yes | A09 D03 | bound | 34, 36, 61, 43 |
| 30 | `starCycleConstraint` | 6901 | all six | paths P: x->y, Q: x->z in G-h meeting only at x have \|P\|+\|Q\|+2 not a power of two | yes | B04 C03 C05 | exclusion | 31, 37, 20 |
| 31 | `meetingCycleConstraint` | 6902 | all six | paths P,Q in G-h to distinct neighbours of h meeting at t satisfy \|P\|+\|Q\|+2 != 2^k + \|P1\| + \|Q1\| | yes | B04 C05 | exclusion | 30, 20 |
| 32 | `highDegreePairSum` | 6903 | all six | sigma = sum_H (d-3); 5 sigma <= sum C(d,2); sigma^2+5 sigma \|H\|+6\|H\|^2 <= 2\|H\| sum C(d,2); 2 sum C(d,2) <= 16 sigma^2; sigma=0 or some h with sigma <= \|H\|(d_h-3) | yes | A03 A05 H08 | bound + identity | 36, 43, 63, 106 |
| 33 | `vertexDeletionComponents` | 6904 | all six | at each h, G-h is connected, or d_h = 2 #blocks(h) and every component meeting N(h) holds exactly two neighbours | yes | B01 B03 E03 | classification | 34, 35 |
| 34 | `cyclesThroughVertex` | 6905 | all six | C(d_h,2) <= #cycles(h) when G-h connected; otherwise 2 #pairs = d_h and d_h/2 <= #cycles(h) | yes | A09 B03 C03 | bound | 33, 36 |
| 35 | `cutVertexBlockPaths` | 6906 | all six | at cut vertices h: block {a,b}; a-b paths of G-h have \|r\|+2 not dyadic; returns of ha are a..b h; length residues mod 4 when \|p\|+1=2^j | yes | B03 C01 C02 C04 | classification + exclusion | 33, 34 |
| 36 | `cycleDoubleCount` | 6907 | all six | 2 sum_H #cycles(h) <= n #cycles(G); 2 sum L_h <= n #cycles(G); #cycles(G) <= 2^m | yes | A09 C03 C07 G07 | bound | 34, 29, 32 |
| 37 | `threeRouteFan` | 7100 | all six | two length-3 paths of G-h from a neighbour a to distinct neighbours share first step and differ at second, else closes an 8-cycle | yes | B04 C01 C05 D03 | classification | 20, 38, 30 |
| 38 | `threeRouteChain` | 7101 | all six | chain of three length-3 paths of G-h between neighbours of h forces r1=p2, r2=q1 | yes | C01 C05 D03 | classification | 37 |
| 39 | `windowPositionStubs` | 7102 | all six | every window of P0 has a placement; interior vertex has d-2 external neighbours, end vertex d-1 | yes | A11 B05 C12 D01 | identity | 40, 25, 26 |
| 40 | `windowAttachmentGap` | 7103 | all six | cross-edge gap \|i-i'\|+2+\|j-j'\| not accepted; outside vertices carry legal labels; adjacent outside vertices C1-safe; no ladders | yes | C04 C12 D01 D02 I01 I03 I05 | exclusion + classification | 15, 39, 2 |
| 41 | `portEndDegree` | 7233 | all six | every excess port (centre above 3, end d.2) has deg d.2 = 3 | yes | A03 C12 D03 | classification | 7, 107, 108, 78 |
| 42 | `hubLinkStructure` | 7217 | all six | no long hub chains in R, no rainbow 5-path of links, link graph 18429-degenerate, strong link graph 3-degenerate, sum bounds <= 36858 h_R, weak pairs carry <= 3*6142 linked vertices | yes | A06 A07 C10 | bound | 46, 47, 77 |
| 43 | `hubClassCounts` | 7218 | all six | A0+A1+A2 = \|L\|; A1+2 A2 = 3\|H\|+sigma; A2 <= C(\|H\|,2); A2+n = A0+4\|H\|+sigma; \|U\| <= 3 A0; d_h <= (\|H\|-1)+\|N(h) cap U\|+\|N(h) cap linked\| | yes | A03 D03 G07 | identity + bound | 44, 47, 77 |
| 44 | `slotRelation` | 7219 | all six | A1 <= 3 A0 + A2 + 2(\|H\|^2-\|H\|) + 2C(\|H\|,2); 4 sigma + 21\|H\| <= 3n + 6\|H\|^2; <= 2 matched-link and 2 link-link vertices per hub pair | yes | A03 G07 | bound | 43, 47 |
| 45 | `closedClasses` | 7220 | all six | closed bag-link classes: edges leaving a closure end in W; disjoint classes have disjoint closures; with a window a nonempty closed class reaches W; disjoint nonempty classes <= e(R,W) | yes | A10 B01 C10 H07 | decomposition + bound | 25, 26, 42 |
| 46 | `hubTwoHopLinks` | 7221 | all six | no 6-path of two-hop links, 25-degenerate two-hop graph (sum <= 50 h_R), per-centre partner bounds 6142, 12286-degenerate, sum <= 24572\|S\| | yes | A06 A07 C10 | bound | 42, 47 |
| 47 | `slotLinear` | 7222 | all six | \|B_W\| <= 13 nu + 4 e(R,W); A2, ML, LL counts outside B_W bounded by link sums; 4 sigma + 15\|H\| <= 3n + K h_R + 8\|B_W\| and <= 3n + K h_R + 584 nu + 32 sigma_W | yes | A03 A07 C10 G09 | bound | 77, 42-46, 53 |
| 48 | `remainderPathBounds` | 7211 | all six | R has no induced P13; components of R minus hubs <= 6142 vertices; paths/cycles through k hubs <= 6143k+6142; path with m>=12 closes cycle length L with m+11<=11L; R is 12-degenerate | yes | A07 B01 C01 C03 C08 C10 | bound | 42, 46, 47 |
| 49 | `windowFreeGeometry` | 7212 | all six | window-free connected sets have induced walks <= 11 and <= 1+2047(3+sigma_K) vertices; hub-cycle dichotomy on x,y in N(h); one chord per 13 consecutive vertices | yes | C01 C06 C08 C10 C12 | classification + bound | 48, 50 |
| 50 | `inducedPathAttachment` | 7213 | all six | a vertex off an induced P13 has <= 7 neighbours on it; every vertex of an induced P13 has a neighbour off it | yes | C08 C12 D01 | bound | 39, 40, 48 |
| 51 | `densityExcess` | 7207 | all six | every proper S (\|S\|>=2): int(S)+6 <= 4\|S\| (excess form sum(d-3) <= \|S\|+bd(S)-6); >=2 edges leave every nonempty proper set; single-hub density | yes | A13 B02 H02 | bound | 52, 53, 25, 24 |
| 52 | `remainderSlack` | 7208 | all six | slack(R) = (n - sigma) + 2\|P0\| + 2 sigma_W - e_cross - 6; hanging windows sum(2+2 sigma_P) <= slack(K); window density 2 e_cross + 6 <= 28 nu and sigma_W + 6 <= e(R,W)+13 nu | yes | A10 A13 C10 G09 H01 H02 | identity + bound | 25, 26, 53, 47 |
| 53 | `hubWindowBudget` | 7209 | all six | 24\|P0\|+2 hubEnds+isoCubic+6\|H\|+sigma <= 3n+4 hubsW, plus three exact window-sum identities | yes | A03 C09 G07 H01 H02 H08 | identity + bound | 54, 47, 52 |
| 54 | `windowHubBounds` | 7210 | all six | for s = n - sigma: 12\|P0\|+31\|B\| <= 2s+2\|H\|+25\|B\|^2; 23\|P0\|+31\|B\| <= n+3s+25\|B\|^2; 22\|P0\|+93\|B\|+6 hubsR+4 hubEnds+2 isoCubicW <= 6s+75\|B\|^2 | yes | A14 C09 G09 H08 | bound | 53, 59, 60 |
| 55 | `cubicNeighbourSupply` | 7200 | all six | cubic-supply property of G (JointSystem.CubicSupply): supply of cubic neighbours around hubs | yes | A03 D03 | bound | 56, 58 |
| 56 | `hubCountBound` | 7201 | all six | 5\|H\| + sigma <= 2n | yes | A01 A05 A14 H08 | bound | 58, 63, 88 |
| 57 | `lowEdgeParity` | 7202 | all six | parity of L-L edges on walks (JointSystem.LowEdgeParity) | yes | A06 C04 | classification | 44 |
| 58 | `bigHubBound` | 7203 | all six | hub domination and 2\|B\| + sigma <= n | yes | A03 A14 H08 | bound | 59, 60, 54 |
| 59 | `bigHubVShapes` | 7204 | all six | V-shape caps and 4 sigma + 93\|B\| <= 2n + 75\|B\|^2 + 4\|H\| | yes | A14 D10 | bound | 60, 54 |
| 60 | `highSurplusBound` | 7205 | all six | 24 sigma + 465\|B\| <= 18n + 375\|B\|^2 and 8n <= 32 s + 125 s^2 for s = n - sigma | yes | A14 H08 | bound | 80 |
| 61 | `hubLengthThreePairs` | 7206 | all six | at a hub with cubic second neighbourhood, <= 4d ordered nonadjacent pairs of N(h) are joined by a length-3 path avoiding h, and >= d(d-2)-4d have none | yes | A06 A09 C01 | bound | 29, 37 |
| 62 | `surplusDartIdentity` | 6607 | all six | sigma + 2*3*\|H\| + lowDarts = 3n | yes | A03 A05 G07 I03 | identity | 63, 43, 106 |
| 63 | `highDegreeCountBound` | 6608 | all six | \|H\| <= sigma | yes | A03 A14 H08 | bound | 56, 89 |
| 64 | `admissibleQuotientsLabelInjective` | 6626 | all six | every DeclaredQuotient of G on any Coordinate type, family and supports is injective on its labels | no: universal over abstract quotient structures (arbitrary Coordinate type, abstract Label/Value, representative fields) | — (nonG: G06 E05 E06) | n/a (nonG) | touches G06 E05 E06 as nonG |
| 65 | `surplusAbove` | 8 | all six | spine scale threshold < sigma(G) (strict arm) | yes | A05 A14 G08 | bound | 77, 85, 86, 93 |
| 66 | `highSurplusConfiguration` | 6703 | all six | G has a vertex of degree >= 5, or two distinct vertices of degree 4 | yes | A03 D10 | classification | 83, 22 |
| 67 | `pairArmAPattern` | 7234 | all six | if (dependent pair family, blocked count, homogeneous bottleneck schema, sparse pressure schema, caps fail) then the explicit canonical capacity, the canonical overload token/role, a homogeneous pattern (star or matching) of size > support with blocker kinds classified | yes | D04 D07 G04 H05 | classification | 68, 96, 72, 73 |
| 68 | `pairArmARoleAlphabet` | 7235 | all six | under the same hypotheses, the overloaded token and role satisfy (blocker, token) in liveRoles | yes | D04 D07 G02 | classification | 67, 96 |
| 69 | `pairArmB` | 7236 | all six | implications on the canonical first failure: overlap system exists and (not CF, or returns without target defect, or handoff with Type B fan); if not realizable then forward/backward connector routes meet; canonical serial system has all closing+sum+offset lengths non-accepted, ends of degree >3 / =3, endpoint switch path | yes | B03 C04 C11 C12 C13 E09 | classification + exclusion | 119, 113, 128-130; universal clauses range over all returns of G, not only the canonical one |
| 70 | `extFreeEmpty` | 7227 | all six | canonical capacity c has extFree(c) = empty | yes | H04 H06 | exclusion | 71, 70 with 92 (free side) |
| 71 | `extLoadSum` | 7228 | all six | C(sigma,2) = sum over tokens of extLoad; \|tokens\| <= 8n + sigma | yes | F01 G02 G07 H05 H06 | identity + bound | 72, 73, 91, 92 |
| 72 | `extOverload` | 7229 | all six | ceilSqrt(n)^2 K + 2 cap (8n+sigma-\|tokens\|) + 2 budget <= 2 sum(extLoad - cap) | yes | G08 H05 H09 | bound | 71, 93, 96 |
| 73 | `extOverloadedToken` | 7230 | all six | if the pair deficit coefficient is positive, some token has extLoad > homogeneous cap | yes | G04 H05 | witness | 67, 96 |
| 74 | `newLoadBound` | 7231 | all six | every excess port p has newLoad(p) <= (\|H\|-1) + [tri-port] sigma | yes | A03 H04 H05 H06 | bound | 75, 79 |
| 75 | `freeSideHubs` | 7226 | all six | freeCount <= sigma(tau + \|H\| - 1); if all token loads <= cap and coefficient >= 0 then n * coeff <= 2 sigma(tau + \|H\|-1) | yes | A03 H05 H09 | bound | 79, 93, 97 |
| 76 | `separatedPairs` | 7232 | all six | for a pair with disjoint declared and return supports, all blockers are target-response or arithmetic-chord; C(sigma,2) <= sum_v C(#ports with v in declared,2) + sum_v C(#ports with v in return,2) + #separated pairs | yes | C13 D05 F04 F05 | bound + decomposition | 78, 79, 118 |
| 77 | `scalePressure` | 7223 | all six | C*q < sigma implies C q + 15\|H\| < 3(n-sigma) + K h_R + 584 nu + 32 sigma_W; and the s-form | yes | A03 A05 G08 H09 | bound | 47, 65, 86 |
| 78 | `freeSideStructure` | 7224 | all six | every free-side pair has two ports with disjoint declared supports, T, return supports, p.1 != q.1, no response obstruction, no chord obstructions, and an adjacency/port-membership witness | yes | C13 D03 D05 E09 F04 F05 | decomposition + exclusion | 76, 79, 41 |
| 79 | `freeSideCount` | 7225 | all six | \|ports\| = sigma; freeCount <= tau*sigma + sum local buffers; deficit inequality against blocked side; all-capped inequality; degree-bounded form freeCount <= sigma(tau + 3(Delta-3)) | yes | A04 F01 G07 G08 H05 H09 | bound | 93, 97, 75, 92 |
| 80 | `highSurplusOrder` | 7214 | all six | 8n <= 32 t + 125 t^2 at t = n - spineScale*ceilSqrt(n) - 1; and small-t bound | yes | A01 A05 G08 I04 | bound | 60, 85, 86 |
| 81 | `windowChargeKinds` | 7215 | all six | canonical capacity is explicit; window charge structure and recorded activation facts at P0 | yes | B09 H02 H04 | decomposition | 90, 138 |
| 82 | `responseObstructionTargetDefect` | 7216 | all six | every response obstruction of the pair activation yields an attempted determination quotient (tied to G exact response valuation) with a residual target defect | yes | B07 E06 E09 | implication (classification) | 16, 23, 128-134 |
| 83 | `highEndpointSwitch` | 6704 | all six | high h adjacent to a degree-3 vertex c: deg h >= 5 with a forced c-u path, or a second high vertex h2 with forced switch path | yes | C01 D10 E03 | witness | 19, 22, 66, 69 |
| 84 | `edgeSurplusIdentity` | 6606 | all six | 2m = 3n + sigma | yes | A01 A02 A05 H01 I03 | identity | 106 (same statement), 62, 112 |
| 85 | `ceilSqrtAboveScale` | 6612 | all six | spineScale + 1 <= ceilSqrt(n) | yes | A01 G08 I04 | bound | 93, 94, 77 |
| 86 | `orderAboveScaleSquare` | 6613 | all six | C(C+1) + 9 <= n | yes | A01 G08 I04 | bound | 80, 85 |
| 87 | `sixVertexExtremalEnvelope` | 6614 | all six | m + 4 <= 2n | yes | A01 A02 A13 | bound | 112, 84 |
| 88 | `highDegreePositive` | 6609 | all six | 1 <= \|H\| | yes | A03 A14 | bound | 56, 89 |
| 89 | `highDegreeSurplusCapacity` | 6610 | all six | sigma <= \|H\| (n - \|H\| - 3) | yes | A03 A05 H08 | bound | 63, 56 |
| 90 | `canonicalCapacityExplicit` | 6665 | all six | canonicalCapacity = explicitCapacity(active family, avoids, connected) | yes | B09 D08 F01 H04 | identity (canonical object) | 91-97, 138 |
| 91 | `canonicalTokenCount` | 6667 | all six | \|tokens\| + 2(order-1) nu = 4n + 3 sigma + 3*order*nu | yes | C09 G02 G07 H06 I03 | identity | 93, 96, 97, 72 |
| 92 | `canonicalBlockedFreePartition` | 6668 | all six | \|blocked\| + freeCount = C(sigma,2) | yes | F01 G07 H06 I03 | identity | 93, 94, 95 |
| 93 | `canonicalLedgerDeficit` | 6669 | all six | ceilSqrt(n)^2 K + 2 cap (8n+sigma-\|tokens\|) <= 2(freeCount - budget) + 2(\|blocked\| - cap*\|tokens\|) | yes | G07 G08 H05 H06 H09 | bound | 92, 96, 97, 94 |
| 94 | `pairCountDeficit` | 6670 | all six | ceilSqrt(n)^2 K + 2 cap (8n+sigma) <= 2(C(sigma,2) - budget) | yes | A05 F01 G08 H09 | bound | 93, 111, 121 |
| 95 | `canonicalCertificationCriterion` | 6671 | all six | canonical certified capacity exists iff freeCount <= budget | yes | H04 H09 | identity | 96, 97, 99 |
| 96 | `canonicalOverloadOfFits` | 6674 | all six | if freeCount <= budget: deficit inequality on the blocked side and some token has load > cap carrying a role-homogeneous matching or star of size >= geometric bound | yes | D04 D07 G04 H05 H09 | bound + witness | 67, 68, 72, 73 |
| 97 | `canonicalFreeExcessOfCapped` | 6675 | all six | if every token has load <= cap then ceilSqrt(n)^2 K + 2 cap(...) <= 2(freeCount - budget) | yes | G04 H05 H09 | bound | 93, 79 |
| 98 | `paperBudgetBound` | 6672 | all six | at the canonical spine family, paperBudget <= certification budget | yes | F01 H09 | bound | 99, 95 |
| 99 | `paperBudgetCertifies` | 6673 | all six | freeCount <= paperBudget implies the canonical certified capacity exists | yes | H04 H09 | implication | 98, 95 |
| 100 | `pairCodeConfiguration` | 6676 | all six | either (dependent family, blocked count, bottleneck schema, pressure schema, caps fail) or (first failure and ([182]-residual or handoff with Type B fan)) | yes | E09 F07 | classification | 67-69, 113, 119 |
| 101 | `sparseSurplusSurvivor` | 119 | all six | G survives the five sparse surplus exits of its declared family | yes | E04 E05 E06 E09 | exclusion | 135, 136, 128 |
| 102 | `openPortSuppression` | 435 | all six | literal compatible family of open-port suppressions and its simultaneous delete-and-add graph (vertices removed, shoulder chords added) | yes | C06 E03 E04 | decomposition | 103-105, 18 |
| 103 | `openPortSuppressionSafe` | 436 | all six | every vertex surviving a suppressible family has degree >= 3 in the suppressed graph | yes | A04 E04 | bound | 105 |
| 104 | `singleOpenPortSuppressionWitness` | 437 | all six | each open tight port has a simple shoulder-to-shoulder path in G minus the vertex whose restored length is accepted | yes | C01 C04 C06 E04 | witness | 105, 108 |
| 105 | `suppressedFamilyCriticalCycle` | 438 | all six | nonempty suppressible family: accepted suppressed cycle uses added chords, and every such cycle expands to a non-accepted source-cycle length | yes | C03 C06 E04 | witness + exclusion | 18 |
| 106 | `sparseSlackSurplus` | 109 | all six | 2m = 3n + sigma | yes | A01 A02 A05 H01 | identity | 84 (duplicate statement), 112, 115, 116 |
| 107 | `activeSurplusFamily` | 110 | all six | \|excess ports\| = sigma; each port has centre above 3, endpoint of degree 3 and exactly delta-1 shoulders | yes | A05 C12 D03 F01 | identity + classification | 41, 108, 109, 27 |
| 108 | `sparsePortActivation` | 111 | all six | each port carrying a shoulder pair has a return path R_p, an open port has a suppression witness with accepted restored length, and a closed pair is a triangle | yes | C01 C02 C06 | witness | 109, 104, 125 |
| 109 | `activeSurplusDemands` | 120 | all six | G carries ActiveSurplusDemands: active family = excess ports, sigma members, each with canonical return path | yes | B09 C02 D08 F01 | witness (canonical family) | 90, 113, 125, 108 |
| 110 | `baselineSpineDemand` | 112 | all six | exists canonical spine family with BaselineSpineFamilySpec (coordinates, supports) | yes | D08 F01 G01 H09 | witness (canonical family) | 111, 115, 116, 121, 139-141 |
| 111 | `freePairCountFails` | 1600 | all six | not (2^(\|spine\|+\|R_Pi\|) <= skeleton budget) at the canonical activation | yes | G05 H09 F07 | obstruction (count) | 121; free side no-arm of [131]; blocked side reuse at [130] |
| 112 | `sparseUpperEnvelope` | 129 | all six | m + 2 <= 2n and the window-remainder / cross-window incidence identity e(R,W)+2(order-1)\|P0\|+e_cross = 3*13\|P0\| + ambient surplus of W | yes | A02 A10 A11 A13 H01 | bound + identity | 25, 26, 52, 87 |
| 113 | `pairOverlapFirstFailure` | 357 | all six | the route-independent least failed pair extension exists at canonical pair code (with connected response support) | yes | B08 D08 E07 E09 F04 H10 | witness (canonical object) | 118, 119, 69, 100, 124 |
| 114 | `mixedSparseSpineDependence` | 203 | all six | at the canonical activation and spine, for the canonical mixed dependence quotient: sparse exit or type-(d)/(e) blocker | yes | F02 F03 F07 | classification | 101, 131, 120, 136 |
| 115 | `exactCubicBaselineBudget` | 204 | all six | cubic baseline budget <= (2n)^E and, when 2E <= C(n,2), (n-1)^E <= budget (2(3+1))^E | yes | A01 A02 G01 H09 | bound | 116, 117, 121 |
| 116 | `incrementalSkeletonRoom` | 205 | all six | skeleton budget <= cubic budget * n^(m - E) and 2(m - E) <= sigma + 2 | yes | A01 A02 A05 A13 G01 H09 | bound | 115, 117, 111, 121 |
| 117 | `skeletonDominates` | 206 | all six | \|Skeleton(n,m)\| = skeleton budget and any state map from the labelled skeleton class realizes <= budget states | yes (labelled (n,m) class count over G-pulled-back skeletons: encoding bound on G quantities; accepted per context) | G01 G06 H09 I01 | identity + bound | 111, 115, 116, 121, 140, 141, 118 (class) |
| 118 | `pairOverlapSystem` | 401 | all six | the canonical overlap system exists: baseline word, outside code, per-pair connected supports, rank, failed family with obstruction to realizingOrder, conditional fibres in the (n,m) skeleton class | yes (class-member reading of X_pi glued into G - X_pi; accepted per context) | B05 B08 D05 D06 D08 D09 E07 F04 G03 G05 | decomposition (existence) | 119, 122-124, 69, 76 |
| 119 | `pairConditionalFactorizationResidual` | 413 | all six | Nonempty PairUncoveredResidual: one of (factorization fails at overlap system \| realizability fails at returns \| increment coverage fails at serial system) | yes | D06 D09 E09 F07 | classification (existence) | endpoint: [182] return; 69 (case analysis) |
| 120 | `independentPairFamily` | 202 | fF fR fI | exists canonical pair activation with no blocked pair on the port-pair schedule | yes | F02 F05 F07 | classification | 121 (free branch), 131 (its complement) |
| 121 | `freePairCodeUnrealized` | 241 | fF fR fI | canonical activation, spine, realization; no blocked pair on the code schedule; \|schedule\| = C(sigma,2); not 2^(\|spine\|+C(sigma,2)) <= budget; schedule nonempty | yes | D08 F01 G01 G05 G06 H09 | obstruction (count) at canonical realization | 122-126 as input of [178]; 111, 117 |
| 122 | `pairFactorizationFails` | 1604 | fF bF | the canonical overlap system does not satisfy ConditionalFactorization (not CF) | yes (class-member reading of X_pi glued into G - X_pi; accepted per context) | D09 E09 F07 G03 G05 | obstruction | 119 (factorization constructor); 118 |
| 123 | `pairConditionalFactorization` | 412 | fR fI bR bI | the canonical overlap system satisfies ConditionalFactorization (separated families and disjoint concatenation realize an exposure order) | yes (class-member reading of X_pi glued into G - X_pi; accepted per context) | D09 F05 G03 G05 | identity (product code) | 124, 125; 118 |
| 124 | `pairFailureOverlap` | 402 | fR fI bR bI | a minimal-by-inclusion obstruction family with an overlap witness pair and connected overlap support exists | yes (class-member reading of X_pi glued into G - X_pi; accepted per context) | B08 D05 D06 F03 F04 G05 | decomposition + obstruction | 125, 126 |
| 125 | `pairDemandReturns` | 405 | fR fI bR bI | two active demands of the failed pair with their canonical return paths and return bound l_ret = max of their lengths | yes | C02 D03 D08 | decomposition | 126-130; 69 |
| 126 | `pairRealizabilityFails` | 1605 | fR bR | the canonical return system has no PairSystemRealizabilityOutcome (no early outcome and no serial system) | yes | C13 D09 E09 | obstruction | 119 (systemRealizability constructor); 69 |
| 127 | `pairSystemRealizability` | 414 | fI bI | the canonical return system has a PairSystemRealizabilityOutcome | yes | C13 E09 | classification | 128, 129 |
| 128 | `pairSystemNoEarlyOutcome` | 1606 | fI bI | none of (i) target cycle, (ii) target defect, (iii) compression, (iv) Type B handoff holds for the canonical returns | yes | B07 E05 E06 E09 | exclusion | 129; 11, 12, 16, 82 |
| 129 | `pairSerialDemandSystem` | 416 | fI bI | the canonical serial system exists: cells, length sets, interface vertices, internally disjoint pieces inside the overlap support, closing return, offsets, increments <= D_sp, realized cycles for every choice | yes | C01 C06 C11 C12 C13 | decomposition + witness | 130; 69 |
| 130 | `pairIncrementFails` | 1607 | fI bI | the canonical serial system has no PairIncrementOutcome (no full-modulus arithmetic input and no periodic early outcome) | yes | C04 C11 E09 | obstruction | 119 (incrementArithmetic constructor); 69 |
| 131 | `dependentPairFamily` | 201 | bF bR bI | at the canonical activation the blocked set Pi_blk is nonempty | yes | F01 F03 F07 | classification | 132-141; 120 (complement) |
| 132 | `pairDegreeProfileFibres` | 2902 | bF bR bI | for every attempted determination quotient of the pair family tied to G exact response data, identified pair coordinates lie in one boundary-degree fibre (profile of G piece at X_pi) | yes | B05 B06 E06 | exclusion | 133; 82 |
| 133 | `pairNoProfileObstruction` | 2904 | bF bR bI | no scheduled pair carries a type-(d) profile obstruction | yes | B06 E06 | exclusion | 101, 135 |
| 134 | `pairNoResponseObstruction` | 2901 | bF bR bI | no scheduled pair carries a type-(e) response obstruction | yes | E05 E06 E09 | exclusion | 101, 135; 82 |
| 135 | `blockedPairNoExit` | 1602 | bF bR bI | the dependence of the blocked pair is not settled by a sparse surplus exit | yes | E05 E09 | exclusion | 101, 136 |
| 136 | `canonicalBlockerRoute` | 144 | bF bR bI | G survives the declared exits and the blocked pair has a canonical blocker min_prec Blk(pi) | yes | D08 E07 H06 | witness (canonical selection) | 137, 138 |
| 137 | `canonicalPairLedger` | 113 | bF bR bI | blocked+unblocked = C(sigma,2) pairs; canonical incidence ledger has \|blocked\| entries; \|blocked\| = sum of blocker multiplicities; some pair has a blocker | yes | D08 F01 G07 H06 I03 | identity | 92, 138, 141 |
| 138 | `capacityTokenLedger` | 114 | bF bR bI | canonical capacity presentation with \|primitive\| = n+2m+sigma <= supply, concrete token ledger, connectedness and packing = P0 | yes | B09 C09 G02 G07 H04 H06 | identity + decomposition | 90-97, 141 |
| 139 | `blockedPairEntropySetup` | 356 | bF bR bI | canonical capacity and spine exist and \|code schedule\| = C(sigma,2) | yes | D08 F01 G01 | identity | 140, 141 |
| 140 | `blockedPairCountFails` | 1601 | bF bR bI | not (2^(\|spine\| + \|free side\|) <= skeleton budget) | yes | G01 G05 H09 | obstruction (count) | 141; 92-97 |
| 141 | `blockedPairCodeUnrealized` | 243 | bF bR bI | canonical realization of the spine code; not 2^(\|spine\|+\|free side\|) <= budget; free side nonempty | yes | D08 G01 G05 G06 H09 | obstruction (count) at canonical realization | 122-126 as input of [178] |

## Gaps ranked (joint check)

Ranking = number of existing facts each coordinate would combine with once measured (gap and ~ rows). Rows tagged `gap` in Table 1: F06, F08. All others below are `~`.

| Rank | Coordinate | Status | Why present at G | Missing observable and certificate | Technique | Existing facts it combines with (count) |
|---|---|---|---|---|---|---|
| 1 | G03 | ~ | 118 defines the conditional fibres; 122/123 test them (realizingOrder needs >= 2 values per step) | conditional fibre sizes at each exposure step of the failed family; certificate: exact log2 \|conditionalValues\| per step and family, additive cost or detected correlation | T12 T11 | 111, 117, 110, 115, 116, 118, 121, 122, 123, 124, 140, 141, 93, 94 (14) |
| 2 | G05 | ~ | 111/121/140/141: the additive count exceeds the class; 118 has overlapping supports | joint state count vs conditional products on the failed family; certificate: product bound or overlap obstruction (joint 2^(sum) vs product of conditional fibre sizes) | T10 T11 T12 | 111, 117, 110, 115, 116, 118, 121, 122, 123, 124, 140, 141, 76, 78 (14) |
| 3 | F08 | gap | 129 serial system has increments; 130 is the failing coverage test | periodicity of the serial response under additive increments; certificate: modulus, frequent increments, base, offsets/smear of the canonical serial system; finite response class, hit or compression | T09 T16 | 69, 129, 130, 2, 4, 35, 57, 22, 104, 108, 109, 125, 126 (13) |
| 4 | C04 | ~ | 129 and 69 carry closing+sum+offset lengths; 130 | arithmetic class of the serial system lengths; certificate: residues of closing+sum+offset modulo the modulus; modular hit or obstruction | T08 T09 | 69, 129, 130, 2, 4, 35, 57, 22, 104, 108, 109, 125 (12) |
| 5 | F06 | gap | 118: failed family whose product is not realized | cancellation relation among response coordinates of the minimal obstruction and repair network; certificate: composite response relation and smaller support/corridor/exact global profile | T08 T10 T11 | 114, 118, 119, 124, 131, 132, 133, 134, 82, 16, 101, 113 (12) |
| 6 | C07 | ~ | 125/129: closing and route cycles of the two demands share vertices (69) | cycle-space interaction of the two closing cycles and the serial cycles; certificate: incidence vectors over E(G) and their symmetric difference: cancellation relation or support decomposition | T08 T11 | 8, 36, 34, 69, 125, 126, 129, 124, 118, 108 (10) |
| 7 | C11 | ~ | 129 exists in increment subtypes; 69 constrains it | increment structure of the serial system beyond existence; certificate: base lengths and increments per cell with increments <= D_sp, sumset interval / orbit | T08 T09 T10 | 69, 129, 130, 4, 108, 109, 125, 126, 124, 118 (10) |
| 8 | D06 | ~ | 118/119 minimal obstruction exists | size, support and shape of the minimal connected overlap obstruction; certificate: \|family\|, \|overlap support\|, connectedness certificate compared with l_ret and D_sp | T10 | 118, 119, 124, 113, 23, 76, 78, 125, 129, 69 (10) |
| 9 | B04 | ~ | 20/30/31/37 exclude disjoint pairs; 69 forces meeting | Menger number between the two demands inside the overlap support; certificate: max internally disjoint paths / separating cut | T04 T08 T14 | 69, 129, 125, 126, 124, 20, 30, 31, 37 (9) |
| 10 | C01 | ~ | 19/20/104/108 give paths; 129 needs sets | attainable length sets between the failed pair terminals; certificate: length set L(u,v) in the overlap support | T08 | 69, 129, 19, 20, 22, 104, 108, 125, 126 (9) |
| 11 | D09 | ~ | 118/119/122/123 | decision of the graph-realization test at the canonical system; certificate: CF or exact collision, uniqueness of reconstructed readings | T05 T15 | 118, 119, 122, 123, 124, 126, 117, 121, 141 (9) |
| 12 | F02 | ~ | 114: mixed family dependent/independent | rank of the pair response family; certificate: rank of response vectors or maximum independent subfamily of R_Pi | T11 | 114, 120, 131, 111, 117, 118, 121, 140, 141 (9) |
| 13 | F03 | ~ | 114/131: dependence exit or blocker | inclusion-minimal dependent subfamily; certificate: circuit, its size and support | T10 T11 | 114, 118, 124, 131, 132, 133, 134, 101, 76 (9) |
| 14 | H07 | ~ | 25/26/45 cuts exist; 71/92 charge pairs to tokens | integral flow of pair demands into legal supporting incidences; certificate: flow / matching or deficient graph-realizable cut | T10 T14 | 25, 26, 45, 71, 74, 92, 138, 91 (8) |
| 15 | B06 | ~ | 11/12/132/133 profile exclusions | boundaried type of X_pi and of the overlap support; certificate: ordered terminals with degree profile | T05 T16 | 11, 12, 132, 133, 118, 113, 124 (7) |
| 16 | G06 | ~ | 117/121/141 use the encoding | injective decoding of the pair code; certificate: no-overcounting theorem: (baseline word, outside edges, prefix) -> labelled skeleton injective | T05 T15 | 117, 121, 141, 110, 118, 111, 140 (7) |
| 17 | I02 | ~ | 14/90/110 canonical, 117 labelled | isomorphism reduction of the skeleton class; certificate: canonical labels / orbit representatives of skeletons | T16 T17 | 117, 111, 115, 116, 121, 141 (6) |
| 18 | A12 | ~ | 8 alone | cycle rank of the overlap support / closing cycles; certificate: dim of the binary cycle space restricted to the support | T01 T08 | 8, 36, 124, 118, 129 (5) |
| 19 | E07 | ~ | 113/118 canonical orders | neutral-move descent for equal-size decompositions; certificate: strict decrease of the secondary order for a size-preserving replacement | T02 T16 | 113, 118, 136, 90, 110 (5) |
| 20 | H10 | ~ | 113 index | one-unit peel steps of the exposure order; certificate: well-founded measure with response-preserving steps | T14 T19 | 113, 118, 124, 123, 122 (5) |

## Non-G facts

| # | Fact | Non-G object | G-constructed replacement |
|---|---|---|---|
| 9 | `degreeProfileFibres` | universal over abstract `CurvatureQuotient` structures (abstract Label/Value types and value map; the conclusion is the structure field `fibrewise`) | the canonical labelling of X_pi readings by (readingProfile, response in actualGlue) as in `SparsePairExactValuation`; state that the canonical quotient of G is target-complete (built from G) |
| 10 | `targetCompleteContextUniversality` | first clause: same abstract quotients; second clause (no cycle in `actualGlue`) is G-only | drop the quotient quantifier: keep `actualGlue_agree` (both readings agree in G - Z) as the G-only half; the swap of G at Z with its canonical degree deficit for the profile half |
| 64 | `admissibleQuotientsLabelInjective` | universal over any Coordinate type and abstract `DeclaredQuotient` (label/value types, representative fields) | injectivity of the canonical pair-code labelling of G: label of coordinate = (profile, response at Z) is injective on the declared family, derived from 11/12 |

Borderline items kept as G: 11, 12 (negated existence of a smaller replacement piece; the piece is compared only via glue into G - Z, i.e. minimality of G); 132-134 and 82 (quantify over attempted quotients whose labels are tied to G's exact response data by `SparsePairExactValuation`); 16, 23 (declared witnesses of G, read via `actualGlue`); 117, 118, 122, 123, 124, 126 (class-member reading and class count, accepted per context; note `response` evaluates the *member* graph glued into `G - X_pi`, so the certificate is about that hybrid, not about G alone); 69 (its last three clauses quantify over all `returns` of G, not only the canonical one).

## Cross-check results

1. Every coordinate code in Table 2 has status x or ~ in Table 1 and lists that fact: **PASS** (Table 1 fact lists are generated from Table 2).
2. Every x or ~ row in Table 1 cites at least one Table-2 row: **PASS**.
3. Every Table-2 row accounts for at least one coordinate or is nonG: **PASS**. Rows 9, 10, 64 account for none (nonG). No row is a pure bookkeeping tag.
4. No demand counted twice in different currencies: **PASS with one duplicate noted.** Facts 84 (`edgeSurplusIdentity`) and 106 (`sparseSlackSurplus`) state the same identity 2m = 3n + sigma in the same currency (edges vs vertices and surplus); rows 84 and 106 both list A01 A02 A05 H01 but count once. 27 (|primitive carrier| = 4n + 2 sigma), 138 (|primitive| = n + 2m + sigma) and 91 (|tokens| identity) count different token sets of the same ledger (identical under 84/106 substitution), not additional demand. 92 and 137 both state |blocked|+|free|=C(sigma,2); listed once for G07/H06 demand accounting by 92 (137 subtype-only). No fact charges one pair demand both to a token (H06) and to a skeleton state (G01): the two budgets are separate currencies combined only in 93/94/141.

## Outside the register

- Class-member response: the [178] test ranges over members of the labelled (n,m) skeleton class with G-boundary pull-back. The observable "response state of a member at X_pi in the context G - X_pi" is not a register coordinate; it is the object on which G03/G05/D09 fail. If treated strictly as G-only, the G-constructed reformulation is G's own swap at X_pi (`ActualContext.swap`) with its canonical degree deficit, on which `actualGlue_agree` already decides the response at G.
- Fact 69 `pairArmB` and 100 `pairCodeConfiguration` are routing/classification conjunctions over the residual's own upstream facts; they account for coordinates only through the clauses listed, and their universal clauses over all `returns` are not canonical-object statements.

## Rows read at the canonical obstruction `F₀` (keys 8200-8202)

This section gives the Lean statements of rows 9, 10, 118, 122-124 and of the keys
8200-8202, and the resulting statuses; for these rows and coordinates it takes precedence
over the entries of Tables 1 and 2 above (register section "G audit:
PairConditionalFactorizationOutcome").

**Facts (Table 2 rows).**

| # | Fact | Lean statement |
|---|---|---|
| 9 | `degreeProfileFibres` | about G: canonical quotient `canonicalReadingLabel` (readingProfile, response in `actualGlue`) |
| 10 | `targetCompleteContextUniversality` | about G: same canonical quotient in the first clause; second clause as in Table 2 |
| 118 | `pairOverlapSystem` (`failedFamily_obstruction`) | `¬ CountRealizing`: for every exposure order some step has `P_{k+1} < 2 P_k` (a count over G's class, no member) |
| 122 | `pairFactorizationFails` | `¬ FactorizesAt F₀`, F₀ = G's canonical minimal obstruction; exact shape `not_conditionalFactorization_iff` |
| 123, 124 | `pairConditionalFactorization`, `pairFailureOverlap` | positive arm of the F₀-test; `family` of `PairFailureOverlap` is `obstructionFamily` |
| 8200 | `pairCorrelation` (generic) | correlation profile: `P_0 = 2^b`, `P_k ≤ P_{k+1} ≤ 2P_k`, `P_t ≤ |class|`, `2^{b+t} ≤ |class| + mass`, first non-branching index `k*`; per-step bound `2^{t-1-k} (2P_k − P_{k+1}) ≤ 2^{b+t-1}` and `2^{b+t-1} ≤ |class|` (one correlated step can carry the whole gap) |
| 8201 | `pairCoverage` (realizability/increment subtypes) | coverage of `[179]`/`[180]` decided at G: handoff or serial (`[179]`), no arithmetic input and handoff (`[180]`) |
| 8202 | `pairFullModulus` (increment subtypes) | canonical Frobenius-filled full-modulus data of the serial system, `¬ FullModulusArithmetic` (frequent increments, gcd modulus, canonical smear, central range); it does not close `[180]` (see register) |

**Statuses (generic residual, 88 coordinates).**

| Code | Status | Reason |
|---|---|---|
| G03 | x | `pairCorrelation` gives the exact signature counts `P_k` (log2 conditional fibre sizes as ratios `P_{k+1}/P_k`) along the canonical order, combined with `skeletonBudget`, `baselineFamily` and the first-failure index in one identity |
| G05 | x | `2^{b+t} ≤ |class| + mass`: the joint count compared with the conditional products, the deficit being the correlation mass; first non-branching index `k*` |
| D06 | ~ | `F₀` is a canonical generic object (unique by cardinality then colex rank) with exact shape on failure; size, support and connectedness measured against `ℓ_ret`, `D_sp` missing |
| F03 | ~ | same: the minimal dependent subfamily `F₀` is canonical, its size/support unmeasured |
| D09 | ~ | decided at `F₀` in aggregate form; no decision of the reconstruction test itself |
| F06 | gap | the relation among the coordinates of `F₀` is exactly the correlation at `k*`; the repair network is not constructed (it needs the uncrossing of the overlap support) |
| F08 | ~ | full-modulus data built as data and tested (8202); coverage reduces `[180]` to the Type B handoff and shows the arithmetic input cannot exist at G; the periodic class is not constructed |
| C04, C11 | ~ | as F08 |
| C07 | ~ | as in Table 1 |

Totals for the generic residual: x = 67, ~ = 17, gap = 1, n/a = 3, nonG = 0
(fact 64 `admissibleQuotientsLabelInjective` is a nonG fact).  Total facts of the generic residual: 120 (119 +
`pairCorrelation`); `pairCoverage` adds one extra fact to each of the four
realizability/increment subtypes and `pairFullModulus` one to each increment subtype.

**Class-member check (the rule "a test whose conclusion is a class member is an
other-graph witness").**  `[178]`: the test is an aggregate count (row 118), not a class
member.  `[179]`, `[180]`: the failures conclude that no outcome object of G exists
(`¬ Nonempty`), not a class member.  The class enters only inside `signatureCount`.
