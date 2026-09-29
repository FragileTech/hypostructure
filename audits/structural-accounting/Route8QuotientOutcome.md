# Structural accounting: `Route8QuotientOutcome`

Worktree: `/home/guillem/hs-wt-SR8Q` (branch `g-audit-r8q`). Node `[187]` = `[348]`, route-8 quotient failure.

**Defining failure.** `Route8QuotientFreeStatement` fails at G: some entry `xi = (X, w, u)` of the unified collection `Xi~ = route8UnifiedEntries` (saturated receivers `w` and unpaid excess loads `u` of the negative zero-surplus, no-handoff pieces `X` of the remainder `R0` of `P0`) has a selected trace basin `B_u` carrying a nontrivial target-complete trace-response quotient (alternative (b) of `def:typeA-trace-basin`, G-form: the only outside context is `G - B_u`). At G alternative (b) holds at every routed load (`exists_traceResponseQuotient_of_avoids`), so the residual is exactly `Xi~ != empty`. Fact 114 (`route8QuotientEntriesAtG`) records the consequences at every entry: `alpha(xi) = 0` (essential core empty), the canonical representative of G's piece at `B_u` is valid and of size `∣piece∣` (not lex-smaller), no quotient reading is a smaller valid replacement, no exit-(5) datum; and `∣dR∣ < delta*∣Xi~∣` (rate 88 + unified deficit 112 + stage accounting of the descent). The paper's `lem:typeA-unified-carriers` needs `alpha >= 2` via "(b) implies exit (5)", which needs a strictly smaller representative; none exists at G.

**Fact count: 114** keys in the `Route8QuotientOutcome` abbrev of this worktree (the brief said 93 and the header of `Residuals/Route8QuotientOutcome.lean` says 87 common facts; the abbrev in `Assembly/Residuals.lean` lines 3067-3296 holds 114 `Holds` conjuncts, including `route8QuotientEntriesAtG` idx 8150 as the last). Table 2 covers all 114.

**Status counts (Table 1, 88 coordinates):** x = 66, ~ = 18, gap = 3, n/a = 1, nonG = 0.
**Table 2 facts not about G:** nonG = 2 (facts 15, 66: `localAlgebra`, `barrierEnumeration`). Facts 10 and 16 use `actualGlue` (G's piece into G - Z, a subgraph of G by `actualGlue_hom`) and fact 113/114 use the G-form `TraceResponseQuotient`; they are marked about G.

Status legend: `x` accounted, `~` partially accounted, `gap` present at G but unaccounted, `n/a` absent at G, `nonG` accounted only through an object outside G.

## Table 1 — Structural coordinates (same for every residual)

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 8, 17, 26, 55, 61 | bound, identity | T01, T06 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 8, 50 | bound | T01 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 3, 6, 7, 31, 40, 42, 54, 56, 61 | bound, classification, exclusion, identity | T01, T07, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 3, 7 | bound, classification | T01 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 26, 31, 42, 43, 46, 50, 51, 55, 57, 58, 59, 61, 62, 64, 65, 73, 74 | bound, exclusion, identity | T01, T07, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 41, 42, 43, 44, 45, 46, 52, 53, 54, 55, 57, 58, 59, 60, 62, 95, 98 | bound, classification, exclusion, identity | T01, T04, T07, T08, T19 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | x | 5, 41, 45, 47, 77 | bound, exclusion | T02, T04, T06, T07, T08 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | none | none | none | Absent at G: fact 2 gives delta = 3 and fact 3 gives min degree >= delta, so G has no vertex of degree two and no degree-two chain (excluding facts 2, 3). |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 80, 82, 84 | bound, identity | T01, T11, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 24, 25, 44, 75, 76, 78, 79, 88, 90, 112, 114 | bound, classification, identity | T01, T02, T03, T05, T07, T08, T10, T13, T15, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | ~ | 24, 78, 79, 80 | bound | T01, T05, T13 | Certified at R0 and its pieces (24, 78, 79, 80) only. Missing at the residual's canonical objects: for every entry xi = (X,w,u) and every retained coordinate set, the baseline degree deficit delta - deg of the retained reading glued into G - B_u at the vertices of B_u (bound; T05 + T01). Without it the baseline-preserving readings of 114 are not quantified. |
| A12 | Cycle rank | Dimension of the binary cycle space. | x | 8 | bound | T01 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 8, 50, 51 | bound, identity | T01 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 64, 65, 73, 105 | bound, exclusion | T01, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | x | 5, 32, 48, 77, 96, 107 | classification, decomposition, exclusion | T02, T04, T06, T08, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 50, 89 | bound, exclusion | T01, T04, T08 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 32, 33, 34 | bound, classification | T04, T08, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 19, 20, 36, 37 | classification, witness | T07, T08, T09 | Existence witnesses only (19, 20, 36, 37); no Menger number. Missing: maximum number of internally disjoint w-u routes inside the piece X and inside B_u for each entry (bound; T08/T14). |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 25, 27, 50, 90, 114 | bound, classification | T01, T02, T03, T05, T08, T10, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | x | 9, 114 | classification, exclusion | T02, T03, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10, 113, 114 | classification, exclusion, obstruction | T02, T03, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | ~ | 23 | decomposition | T10 | Minimal connected support certified only for sparse target-defect witnesses (23). Missing: connectivity and size ∣B_u∣ of the basin and the connected support of the forgotten coordinate of the (b) quotient at each Xi~ entry (bound + decomposition; T10). |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 24, 25, 78, 88 | bound | T01, T05, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 4, 19, 22, 34, 60, 89 | bound, classification, exclusion, witness | T04, T07, T08, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 22, 89, 101 | exclusion, witness | T04, T07, T08, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 10, 16, 18, 21, 29, 30, 33, 35, 47, 93 | bound, exclusion, witness | T02, T03, T04, T05, T07, T08, T09, T10, T15 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 2, 4, 20, 29, 30, 34, 56, 101 | classification, exclusion, identity, witness | T01, T04, T07, T08, T09, T18 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 19, 20, 22, 36 | classification, witness | T07, T08, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | ~ | 89, 101 | exclusion, witness | T04, T07, T08 | Ear existence only (89, 101). Missing: ear decomposition of the trace path u -> w inside B_u relative to the retained reading (decomposition; T08). |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | gap | none | none | none | Present at G: fact 8 gives a nontrivial cycle space and every retained reading is G's piece with internal edges dropped (114). No fact gives incidence vectors or symmetric differences. Missing: cycle-space class of the dropped internal edges of each entry's forgotten coordinates and of glue(retained reading, G - B_u) against G (decomposition; T08). |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 47, 48, 49, 77 | bound, classification, exclusion, witness | T04, T06, T07, T08 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 17, 38, 52, 53, 69 | bound, classification, decomposition | T01, T06, T07 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 14, 24, 25, 47, 48, 51, 77, 78, 80 | bound, classification, decomposition, exclusion, identity | T01, T04, T05, T06, T08, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | ~ | 90, 91, 92 | classification, witness | T08, T10, T17 | Serial corridors certified only for cold windows (90, 91, 92). Missing: length and increment structure of the trace path load u -> receiver w selected at each Xi~ entry (bound; T09). |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 7, 27, 38, 39, 40, 48, 49, 99, 100, 101 | bound, classification, exclusion, identity, witness | T01, T05, T06, T07, T08 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | x | 19, 20, 21, 36, 37, 39 | classification, exclusion, witness | T07, T08, T09 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 38, 39, 49 | bound, classification, exclusion | T06, T07 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 38, 39, 75, 91 | classification, exclusion, identity, witness | T01, T06, T07, T08, T17 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 20, 21, 22, 28, 29, 30, 32, 36, 37, 40, 41, 44, 58, 60, 97, 98, 99, 100 | bound, classification, exclusion, identity, witness | T01, T04, T07, T08, T09, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | ~ | 28, 103, 110, 114 | bound, classification, identity | T02, T03, T05, T07, T13, T14, T15, T16 | Matching structure at N(h) (28) and the core-incidence view (103, 110 on the silent-first collection; 114: alpha = 0 means the incidence graph between Xi~ and the cut edges of R0 through essential cores is empty). Missing: incidence graph between Xi~ (demand) and the legal non-core resources (ports of w, edges of B_u, cut edges) with matching-versus-star concentration (decomposition; T14/T15). |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | ~ | 108 | classification | T10, T13 | Overlap of supports certified only for Type B centres (108). Missing: overlap graph of the basins B_u, B_u' of distinct Xi~ entries (same receiver, same piece, different pieces) (decomposition; T10). |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 108 | classification | T10, T13 | Overlap obstruction only for Type B (108). Missing: inclusion-minimal connected family of Xi~ basins on which additivity of the entry charge fails (obstruction; T10). |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 9, 113, 114 | classification, exclusion, obstruction | T02, T03, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 69, 106, 111, 114 | bound, classification, decomposition | T02, T03, T05, T06, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | x | 10, 94, 114 | classification, exclusion | T02, T03, T05, T10, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 27, 100, 101 | classification, witness | T05, T07, T08 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1, 114 | classification, exclusion | T02, T03, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5, 11, 12, 114 | classification, exclusion | T02, T03, T04, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 19, 22, 32, 89, 114 | classification, exclusion, witness | T02, T03, T04, T05, T08, T09, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | x | 18 | exclusion | T03 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 94, 114 | classification, exclusion | T02, T03, T05, T10, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 63, 109, 113, 114 | classification, exclusion, obstruction | T02, T03, T05, T12, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | x | 114 | classification | T02, T03, T05, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 114 | classification | T02, T03, T05, T13, T16 | Only the consequence ∣dR∣ < delta∣Xi~∣ of the peeling descent is retained (114). The descent statement (key route8PeelingDescent, idx 282: peel chain, StageAccounting equalities, StageOutcome) is consumed by row 114 but is not among the residual's 114 facts. Missing: peel chain, stage equalities ∣Xi~∣ = ∣peeledEntries∣ + ∣chain∣ and the deficit-below-∣Xi~∣ inequality as residual facts (identity; T19). |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 16, 23, 92, 93, 94, 107, 108, 109, 110, 113, 114 | classification, decomposition, exclusion, obstruction, witness | T02, T03, T05, T08, T10, T13, T14, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 80, 82, 90 | bound, classification, identity | T01, T08, T10, T11, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | x | 81, 83, 84, 85 | bound, classification, identity, witness | T11, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | x | 83 | classification | T11 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | ~ | 23, 83 | classification, decomposition | T10, T11 | Dependence supports certified for sparse witnesses (23) and target-rank circuits (83). Missing: declared support (vertices, edges, contexts) of the changed coordinate of the (b) quotient of each Xi~ entry (decomposition; T10). |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 63, 67 | classification, exclusion | T05, T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | ~ | 94, 114 | classification, exclusion | T02, T03, T05, T10, T13, T16 | 114 records that the canonical piece repairs the forgotten coordinates (representative of equal size) and 94 excludes a repair at cold corridors. Missing: relations among the trace coordinates that the quotient forgets and the network that repairs them (decomposition; T11). |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 81, 83, 84 | classification, identity, witness | T11 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 34, 91 | classification, witness | T04, T08, T09, T17 | Mod-4 and first-repeat laws only on block paths and cold corridors (34, 91). Missing: periodic response of the trace incidence of a Xi~ entry under additive length increments (classification; T09). |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 35, 68 | bound | T12, T15 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 67 | classification | T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 67, 70, 71, 86 | bound, classification | T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | x | 69, 71, 72, 73 | bound, decomposition | T01, T06, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | x | 67, 86 | classification | T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | x | 63, 67 | classification, exclusion | T05, T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | ~ | 26, 35, 61, 74, 76, 103, 110, 114 | bound, classification, identity | T01, T02, T03, T05, T13, T14, T15, T16 | Multiplicity certified for darts, cycles, primitive carriers, stubs (26, 35, 61, 74, 76) and for cut incidences of entries (103, 110 on the silent-first collection; 114: alpha = 0, no cut incidence is charged to any Xi~ entry). Missing: where each entry's unit of the cleared deficit is charged, with a multiplicity bound (bound; T15). |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 2, 64, 73, 79, 87, 88, 112 | bound, identity | T01, T09, T13, T18 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 14, 17, 25, 51, 72, 87 | bound, decomposition, identity | T01, T05, T06, T12, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 24, 25, 43, 46, 52, 53, 78, 79, 80, 85, 87, 88, 102, 104, 106, 112 | bound, decomposition | T01, T05, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | x | 96, 104, 105 | bound, decomposition | T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H03 | Connected negative support | A connected region with negative charge. | x | 96, 104, 106, 107, 108 | bound, classification, decomposition | T10, T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | x | 87, 95, 97, 108, 111, 112 | bound, classification | T10, T13, T19 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H05 | Load and saturation | Load compared with certified capacity. | ~ | 102, 109, 110, 111, 114 | bound, classification | T02, T03, T05, T13, T14, T16 | Load versus capacity certified for Type B handoff receivers (111), thresholds (109) and the silent-first collection (102). Missing for the receivers of Xi~: ∣E(w)∣ against s*missingPorts(w) per saturated receiver and its sum against ∣dR∣ (bound; T13/T01). |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | ~ | 102, 103, 110, 114 | bound, classification, identity | T02, T03, T05, T13, T14, T15, T16 | Aggregate payment only: s*∣dR∣ pays (88, 112), silent-first entries pay from private carriers (102, 103, 110), and alpha = 0 at Xi~ (114). Missing: per-entry payment assignment for Xi~ entries whose essential core is empty (bounded-multiplicity map; T14/T15). |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | gap | none | none | none | Present at G: saturated receivers have ports (missingPorts) and Xi~ entries are indexed by them; the network entries -> resources exists. Nothing gives a flow or cut on it. Missing: integral flow / Hall witness from Xi~ to legal resources and its min cut (witness or obstruction; T14). |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 97, 102, 104, 105, 106, 111, 112 | bound, decomposition | T13 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 70, 71, 72, 85, 86, 88, 112, 114 | bound, classification | T02, T03, T05, T12, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 114 | classification | T02, T03, T05, T13, T16 | Only the final consequence of the descent is retained (114). Missing: the well-founded measure and one-unit peel steps as residual facts (identity + witness; T19). |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 67, 68 | bound, classification | T11, T12 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | x | 14, 114 | classification, decomposition | T02, T03, T05, T06, T13, T16 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 26 | identity | T01 | No unmeasured sub-observable identified at the residual's canonical objects; the cited facts enter shared identities and inequalities with the other currencies. |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | gap | none | none | none | Present at G: fact 87 is conditional on SufficientlyLargeForNetCap and 88, 112 carry o(n) slacks; no fact excludes or enumerates small orders of G. Missing: explicit N0 with n >= N0 at G, or the finite list of orders (exclusion; T17). |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | ~ | 2, 67 | classification, identity | T01, T09, T11, T12, T18 | Table certificates: 15 and 66 (parameter-only, nonG) and the rate/label semantics consumed at G (2, 67). Missing: input schema, generator and verifier of the barrier table stated at G (I05 certificate; T17). |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | ~ | 2 | identity | T01, T09, T18 | HSS closure law stated at G with exact hypotheses in 2, but not consumed by any other fact of this residual. Missing: a consumer in an inequality of the residual (T18). |

## Table 2 — Facts of the residual → structural coordinates

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted length and no lexicographically smaller baseline object avoids the target (selection minimality) | yes | E01, C03 | exclusion | **read by 114**; derives residual keys: admissibleQuotientsLabelInjective, bigHubBound, bigHubVShapes, bridgeless, closedClasses (+44 more) |
| 2 | `cubicBaseline` | 221 | delta=3, s=4, 2 not accepted, accepted lengths exactly dyadic, window rate = barrier-table rate, slacks; HSS closure law at G and its induced subgraphs (3 of 4 components parameter-only identities, 4th stated at G) | yes (mixed: only SpinePresentationLaws is about G) | C04, G08, I05, I06 | identity | derives residual keys: bigHubBound, bigHubVShapes, bridgeless, closedClasses, crossSwitchFamily (+49 more) |
| 3 | `minDegreeBaseline` | 2850 | min degree of G >= delta | yes | A03, A04 | bound | derives residual keys: bigHubBound, bigHubVShapes, closedClasses, crossSwitchFamily, cubicNeighbourSupply (+31 more) |
| 4 | `returnAvoidance` | 1 | for every dart the return-length set is disjoint from the shifted accepted set | yes | C01, C02, C04 | exclusion | derives residual keys: sameVertexSwitchForcedPath |
| 5 | `noProperBaseline` | 2 | no proper subgraph of G has min degree >= delta; G connected | yes | E02, A07, B01 | exclusion | derives residual keys: bigHubBound, bigHubVShapes, closedClasses, cubicNeighbourSupply, cutVertexBlockPaths (+19 more) |
| 6 | `slackIndependent` | 4 | no two vertices of degree > delta are adjacent | yes | A03, A06 | exclusion | derives residual keys: bigHubBound, bigHubVShapes, closedClasses, cubicNeighbourSupply, cycleDoubleCount (+12 more) |
| 7 | `tightEndpoint` | 3 | every edge has an endpoint of degree exactly delta | yes | A03, A04, C12 | classification | derives residual keys: highCentreNormalForm, highCentreSplitForced, highDegreeCountBound, surplusDartIdentity |
| 8 | `cycleRankConstraint` | 425 | n + 2 <= 2(m + 1 - n) | yes | A01, A02, A12, A13 | bound | unconsumed |
| 9 | `degreeProfileFibres` | 2300 | for every region and curvature quotient, regions with different reading profiles are not identified | yes | B06, D07, E06 | exclusion | derives residual keys: targetCompleteContextUniversality |
| 10 | `targetCompleteContextUniversality` | 2301 | identified readings have equal profile and equal target-cycle status in G's own glue (piece X at Z glued into G - Z, a subgraph of G); no such glue has a target cycle | yes (context = G - Z only) | B07, D09, E06, C03 | exclusion | unconsumed |
| 11 | `replacementExclusion` | 223 | no ReplacementSupport (smaller context-equivalent representative) in G | yes | E02, E05 | exclusion | derives residual keys: admissibleQuotientsLabelInjective, route8ExtractedEntryCensus, typeAExclusion, uncompressible, windowPackageSeparated |
| 12 | `uncompressible` | 5 | no CompressibleSupport in G (cor:uncompressible) | yes | E02, E05 | exclusion | **read by 114**; derives residual keys: route8QuotientEntriesAtG, typeBBridgeReduction |
| 13 | `windowPresent` | 608 | G has an induced path on windowOrder (13) vertices | yes | C08 | witness | derives residual keys: maximalPacking |
| 14 | `maximalPacking` | 6 | canonical maximum window packing P0: positive number, meets every induced window | yes | C09, C10, D08, G09, I02 | decomposition | unconsumed |
| 15 | `localAlgebra` | 7 | ∣Labels(13)∣ = 399 and the first size-distribution entries: window-label algebra; the `_object` argument is unused | no: parameter-only (registered window-label algebra, no G object) -> nonG | none accounted (nonG; touches G02, I01, I05 whose G-side accounting is 2, 67, 68) | identity | no residual key derives from it; 1 other rows read it |
| 16 | `everyWitnessSpectrumSplit` | 6702 | for every sparse target-defect witness and pair support, the actualGlue (G-piece into G - Z) has no target cycle | yes (G-form actualGlue) | C03, E09 | exclusion | unconsumed |
| 17 | `packingOrderBound` | 6611 | 13 * ∣P0∣ <= n | yes | A01, C09, G09 | bound | unconsumed |
| 18 | `noSuppressionChordViolation` | 6620 | for every compatible tight-vertex suppression of G no certificate cycle plus used chords has accepted length | yes | C03, E04 | exclusion | unconsumed |
| 19 | `twoSwitchForcedPath` | 6800 | any two disjoint edges with high endpoints: a path in G minus both edges with accepted length + 1 | yes | B04, C01, C05, C13, E03 | witness | no residual key derives from it; 1 other rows read it |
| 20 | `crossSwitchFamily` | 6802 | cross-switch family: forced path to each neighbour of h' and power-of-two exclusion for pairs of paths | yes | B04, C04, C05, C13, D03 | witness | unconsumed |
| 21 | `highCentreSplitForced` | 6801 | every high vertex h: an accepted cycle in G + antiPairs(h) avoiding h and using an added edge | yes (graph built from G) | C03, C13, D03 | witness | unconsumed |
| 22 | `sameVertexSwitchForcedPath` | 6803 | same-vertex switch: path u1..u2 avoiding h with accepted length + 1 and an exclusion disjunction | yes | C01, C02, C05, D03, E03 | witness | no residual key derives from it; 1 other rows read it |
| 23 | `specWitnessStructure` | 6677 | connected minimal support of a sparse target-defect witness contains both declared supports and is not Spec | yes | B08, E09, F04 | decomposition | unconsumed |
| 24 | `remainderDeficiencyBelowCut` | 6663 | def+(R0) <= e(R0, W) | yes | A10, A11, B09, C10, H01 | bound | unconsumed |
| 25 | `windowCutCapacity` | 6664 | e(R0,W) + 2(13-1)p <= delta*13p + sigma_W | yes | A10, B05, B09, C10, G09, H01 | bound | unconsumed |
| 26 | `primitiveCarrierCount` | 6666 | ∣primitive carrier∣ = 4n + 2 sigma | yes | A01, A05, G07, I03 | identity | unconsumed |
| 27 | `singleBoundaryShape` | 6627 | a set with cut boundary exactly {b} forces b to have exactly 2 neighbours inside and 2 outside | yes | B05, C12, D10 | classification | unconsumed |
| 28 | `neighbourhoodPairCount` | 6900 | G[N(h)] is a matching and N(h) has >= C(d,2) - floor(d/2) nonadjacent pairs | yes | D03, D04 | bound | unconsumed |
| 29 | `starCycleConstraint` | 6901 | star constraint: two paths to distinct neighbours of h meeting at x have ∣P∣+∣Q∣+2 != 2^k | yes | C03, C04, D03 | exclusion | unconsumed |
| 30 | `meetingCycleConstraint` | 6902 | meeting constraint: ∣P∣+∣Q∣+2 != 2^k + ∣P1∣ + ∣Q1∣ | yes | C03, C04, D03 | exclusion | unconsumed |
| 31 | `highDegreePairSum` | 6903 | sigma = sum over H of (d-3); 5 sigma <= sum C(d,2); Cauchy-Schwarz form; cap 16 sigma^2 | yes | A03, A05 | bound | unconsumed |
| 32 | `vertexDeletionComponents` | 6904 | for every vertex h: G-h connected or d_h even, d_h = 2 #blocks, each neighbour's component holds exactly 2 neighbours of h | yes | B01, B03, D03, E03 | classification | unconsumed |
| 33 | `cyclesThroughVertex` | 6905 | cycles through a vertex: >= C(d,2) if G-h connected, else >= d/2 | yes | B03, C03 | bound | unconsumed |
| 34 | `cutVertexBlockPaths` | 6906 | block paths at a cut vertex: block of a is {a,b}, path-length exclusions and mod-4 laws | yes | B03, C01, C04, F08 | classification | unconsumed |
| 35 | `cycleDoubleCount` | 6907 | double count of cycles at high vertices <= n * #cycles(G) and #cycles <= 2^m | yes | C03, G01, G07 | bound | unconsumed |
| 36 | `threeRouteFan` | 7100 | length-3 fan: two 3-paths from a to b, c leave through the same vertex and meet nowhere else | yes | B04, C05, C13, D03 | classification | unconsumed |
| 37 | `threeRouteChain` | 7101 | chain 3,3,3: middle path passes through inner vertices of the outer two | yes | B04, C13, D03 | classification | unconsumed |
| 38 | `windowPositionStubs` | 7102 | at every placement of a packed window, interior positions have d-2 external neighbours, ends d-1 | yes | C09, C12, D01, D02 | classification | unconsumed |
| 39 | `windowAttachmentGap` | 7103 | cross-edge gap, attachment labels legal, C1-safe adjacent labels, no ladders between windows | yes | C12, C13, D01, D02 | exclusion | unconsumed |
| 40 | `portEndDegree` | 7233 | every excess port ends at a vertex of degree exactly delta | yes | A03, C12, D03 | identity | unconsumed |
| 41 | `hubLinkStructure` | 7217 | hub link structure in R: no long hub chains, no rainbow 5-path, link graph 18429-degenerate | yes | A06, A07, D03 | exclusion | unconsumed |
| 42 | `hubClassCounts` | 7218 | hub class counts ∣A0∣+∣A1∣+∣A2∣ = ∣L∣, ∣A1∣+2∣A2∣ = 3∣H∣+sigma, ... | yes | A03, A05, A06 | identity | unconsumed |
| 43 | `slotRelation` | 7219 | slot relation: ∣A1∣ <= 3∣A0∣+∣A2∣+2(∣H∣^2-∣H∣)+..., 4 sigma + 21∣H∣ <= 3n + 6∣H∣^2 | yes | A05, A06, H01 | bound | unconsumed |
| 44 | `closedClasses` | 7220 | closed bag-link classes: closures disjoint, reach W, number <= e(R,W) | yes | A06, A10, D03 | classification | unconsumed |
| 45 | `hubTwoHopLinks` | 7221 | no 7 hubs of R joined by two-hop links; two-hop graph 25-degenerate | yes | A06, A07 | exclusion | unconsumed |
| 46 | `slotLinear` | 7222 | slot classes linear in h_R: ∣B_W∣ <= 13 nu + 4e(R,W), 4 sigma + 15∣H∣ <= 3n + K h_R + ... | yes | A05, A06, H01 | bound | unconsumed |
| 47 | `remainderPathBounds` | 7211 | no induced P13 in R, bags <= 6142, path/cycle length bounds through hubs, R is 12-degenerate | yes | A07, C03, C08, C10 | bound | unconsumed |
| 48 | `windowFreeGeometry` | 7212 | window-free sets: short induced walks, hub-pair dichotomy, connected window-free sets have <= 1+2047(3+sigma_K) vertices | yes | B01, C08, C10, C12 | classification | unconsumed |
| 49 | `inducedPathAttachment` | 7213 | vertex off an induced P13 has <= 7 neighbours on it; every path vertex has a neighbour off it | yes | C08, C12, D01 | bound | unconsumed |
| 50 | `densityExcess` | 7207 | proper sets span few edges (int S + 6 <= 4∣S∣); >= 2 edges leave every nonempty proper set | yes | A02, A05, A13, B02, B05 | bound | unconsumed |
| 51 | `remainderSlack` | 7208 | slack of R0 = (n - sigma) + 2p + 2 sigma_W - cross-window incidences - 6; hanging windows; density | yes | A05, A13, C10, G09 | identity | unconsumed |
| 52 | `hubWindowBudget` | 7209 | hub-window budget: 24p + 2 hubEnds + ... <= 3n + 4 hubsW, and companions | yes | A06, C09, H01 | bound | unconsumed |
| 53 | `windowHubBounds` | 7210 | windows against big hubs: 12p + 31∣B∣ <= 2s + 2∣H∣ + 25∣B∣^2 and companions | yes | A06, C09, H01 | bound | unconsumed |
| 54 | `cubicNeighbourSupply` | 7200 | cubic neighbour supply (JointSystem.CubicSupply) | yes | A03, A06 | bound | unconsumed |
| 55 | `hubCountBound` | 7201 | 5∣H∣ + sigma <= 2n | yes | A01, A05, A06 | bound | unconsumed |
| 56 | `lowEdgeParity` | 7202 | parity of L-L edges on walks | yes | A03, C04 | classification | unconsumed |
| 57 | `bigHubBound` | 7203 | hub domination and 2∣B∣ + sigma <= n | yes | A05, A06 | bound | no residual key derives from it; 1 other rows read it |
| 58 | `bigHubVShapes` | 7204 | V-shape caps and 4 sigma + 93∣B∣ <= 2n + 75∣B∣^2 + 4∣H∣ | yes | A05, A06, D03 | bound | unconsumed |
| 59 | `highSurplusBound` | 7205 | 24 sigma + 465∣B∣ <= 18n + 375∣B∣^2; 8n <= 32 s + 125 s^2 | yes | A05, A06 | bound | no residual key derives from it; 1 other rows read it |
| 60 | `hubLengthThreePairs` | 7206 | at a hub with cubic second neighbourhood: <= 4d length-3 pairs, >= d(d-2)-4d pairs without | yes | A06, C01, D03 | bound | unconsumed |
| 61 | `surplusDartIdentity` | 6607 | sigma + 2 delta ∣H∣ + lowDarts = delta n | yes | A01, A03, A05, G07 | identity | unconsumed |
| 62 | `highDegreeCountBound` | 6608 | ∣H∣ <= sigma | yes | A05, A06 | bound | unconsumed |
| 63 | `admissibleQuotientsLabelInjective` | 6626 | every admissible declared quotient is label-injective on its family | yes | E06, F05, G06 | exclusion | unconsumed |
| 64 | `surplusAtOrBelow` | 9 | sigma <= T(n) (surplusThreshold) | yes | A05, A14, G08 | bound | derives residual keys: route8Rate, route8UnifiedDeficit, stubSupply, typeBBridgeSublinear |
| 65 | `sparseSurplusSurvivor` | 119 | none of the five sparse-surplus conclusions occurs (DeclaredSparseSurvivor) | yes | A05, A14 | exclusion | no residual key derives from it; 2 other rows read it |
| 66 | `barrierEnumeration` | 211 | barrier-table counts: safe, flat, curvature-positive, log2 ratio equalities | no: parameter-only (registered barrier table; no G object) -> nonG | none accounted (nonG; touches G02, I01, I05 whose G-side accounting is 2, 67, 68) | identity | unconsumed |
| 67 | `windowPackageSeparated` | 35 | window packages of P0: disjoint, bits = rate*scales*..., functional admissible quotients label-injective (also jointly with the spine family) | yes | F05, G02, G03, G05, G06, I01, I05 | classification | no residual key derives from it; 1 other rows read it |
| 68 | `skeletonDominates` | 206 | ∣Skeleton(n,m)∣ = skeletonBudget and every state map has range <= budget | yes | G01, I01 | bound | no residual key derives from it; 1 other rows read it |
| 69 | `hotColdPartition` | 200 | hot/cold partition of P0 | yes | C09, D08, G04 | decomposition | unconsumed |
| 70 | `barrierCap` | 10 | 2^(rate*scales*∣hot∣) <= skeletonBudget | yes | G03, H09 | bound | unconsumed |
| 71 | `coldHotEntropyCap` | 215 | cold window bit rate * ∣hot∣ <= cold skeleton allowance | yes | G03, G04, H09 | bound | unconsumed |
| 72 | `coldMass` | 216 | rate*∣P0∣ <= rate*∣cold∣ + allowance | yes | G04, G09, H09 | bound | unconsumed |
| 73 | `coldAmbientCubic` | 217 | ∣cold∣ <= ∣cubic cold∣ + sigma and sigma <= T(n) | yes | A05, A14, G04, G08 | bound | unconsumed |
| 74 | `coldStubExcess` | 218 | per-window branch excess times ∣cold∣ <= ... + excess*sigma | yes | A05, G07 | bound | unconsumed |
| 75 | `coldAmbientCubicStubExcess` | 180 | each ambient-cubic cold window has exactly c external stubs | yes | A10, D02 | identity | unconsumed |
| 76 | `coldSelectedBranchExcess` | 179 | selected stubs = excess*∣cubic∣ and each is selected by a unique window | yes | A10, G07 | identity | unconsumed |
| 77 | `remainderNormalized` | 13 | every subregion of R0 is window-free and carries no baseline subgraph | yes | A07, B01, C08, C10 | exclusion | derives residual keys: route8BasinBurden, typeAExclusion, typeBBridgeReduction |
| 78 | `boundaryDemand` | 14 | def+(R0) <= e(R0,W) <= 15p + sigma_W (the chain of facts 24 and 25 restated) | yes | A10, A11, B09, C10, H01 | bound | derives residual keys: stubSupply |
| 79 | `stubSupply` | 15 | def+(R0) + 2*12p <= 39p + T(n) | yes | A10, A11, G08, H01 | bound | derives residual keys: wedgeSupply |
| 80 | `wedgeSupply` | 16 | delta∣X∣ <= W2(X) + 2 def+(X) for every X in R0, and at R0 in cleared form | yes | A09, A11, C10, F01, H01 | bound | derives residual keys: forcedCurvatureCost |
| 81 | `curvatureTargetRank` | 18 | maximum surviving subfamily of the curvature tests attained and an upper bound | yes | F02, F07 | witness | derives residual keys: targetRankCircuit |
| 82 | `exactResponseProfile` | 207 | #declared curvature tests = W2(R0) | yes | A09, F01 | identity | unconsumed |
| 83 | `targetRankCircuit` | 210 | target-rank circuit: a raw test outside the surviving family is determined by a finite subfamily under a rank-reducing functional quotient | yes | F02, F03, F04, F07 | classification | unconsumed |
| 84 | `curvatureFullRank` | 20 | r_Omega(R0) = W2(R0) | yes | A09, F02, F07 | identity | derives residual keys: forcedCurvatureCost |
| 85 | `forcedCurvatureCost` | 37 | c_Omega * (delta∣R∣ + 4*12p) <= c_Omega r_Omega(R) + c_Omega*2(...) | yes | F02, H01, H09 | bound | unconsumed |
| 86 | `largeBudgetResidual` | 42 | joint package demand * 2^forced bits <= skeleton budget, or below the entropy rate | yes | G03, G05, H09 | classification | derives residual keys: netDeficiencyCap |
| 87 | `netDeficiencyCap` | 222 | n sufficiently large implies s(delta*13p + spine*sqrt n) < s*2*12p + ∣R0∣ | yes | G08, G09, H01, H04 | bound | unconsumed |
| 88 | `route8Rate` | 264 | (delta*s + 1)∣dR∣ + delta*slack < delta∣R∣  (private-carrier rate, tau < delta/(delta s+1)) | yes | A10, B09, G08, H01, H09 | bound | **read by 114**; derives residual keys: route8QuotientEntriesAtG |
| 89 | `bridgeless` | 226 | every oriented edge of G has a simple return after its deletion (no bridge) | yes | B02, C01, C02, C06, E03 | exclusion | derives residual keys: cutVertexBlockPaths, cycleDoubleCount, cyclesThroughVertex, densityExcess, remainderSlack (+3 more) |
| 90 | `coldReturnCorridors` | 227 | cold corridors: componentwise corridor theorem and partition of selected stubs into outside-foot and cross-window | yes | A10, B05, C11, F01 | classification | unconsumed |
| 91 | `coldCorridorState` | 30 | retained corridor presentations, state readings, first repeat, table record | yes | C11, D02, F08 | witness | unconsumed |
| 92 | `coldFirstFailureOccurrence` | 404 | nonempty cold first-failure occurrence data | yes | C11, E09 | witness | unconsumed |
| 93 | `coldFailureCycle` | 64 | clause (F1) of the cold first failure never occurs (no accepted cycle) | yes | C03, E09 | exclusion | unconsumed |
| 94 | `coldFailureCompression` | 66 | clause (F3) of the cold first failure never occurs (no smaller equal-response representative) | yes | D09, E05, E09, F06 | exclusion | unconsumed |
| 95 | `coldHandoffTransfer` | 69 | a candidate prefix is subcubic or its first high head is handed to the high-degree ledger | yes | A06, H04 | classification | unconsumed |
| 96 | `netChargeLocalization` | 46 | negative net charge of R0 localizes to a negative canonical piece (decomposition exact) | yes | B01, H02, H03 | decomposition | no residual key derives from it; 1 other rows read it |
| 97 | `typeBAbsorbedCharge` | 2800 | absorbed half-edges: assigned support, high centre, core in R0, Type B deficit bound | yes | D03, H04, H08 | bound | unconsumed |
| 98 | `highCentreNormalForm` | 72 | normal form at every high centre | yes | A06, D03 | classification | derives residual keys: sameCenterOpenPortCompatibility, triangularPortReturn, triangularShoulderCompletion |
| 99 | `sameCenterOpenPortCompatibility` | 354 | same-centre open ports are fan-compatible | yes | C12, D03 | classification | unconsumed |
| 100 | `triangularShoulderCompletion` | 426 | triangular shoulder completion at every centre of degree > delta+1 | yes | C12, D03, D10 | witness | derives residual keys: triangularPortReturn |
| 101 | `triangularPortReturn` | 427 | triangular port return with a non-accepted closing length | yes | C02, C04, C06, C12, D10 | witness | no residual key derives from it; 1 other rows read it |
| 102 | `route8BasinBurden` | 161 | s * D_A(X_A) <= N_basin(X_A): cleared route-8 deficit of the silent-first collection bounded by its basin count | yes | H01, H05, H06, H08 | bound | no residual key derives from it; 1 other rows read it |
| 103 | `route8CarrierCore` | 163 | every indexed entry of the silent-first route-8 collection has CarrierCoreFacts (complete essential core inside the declared supply, forced deletion target defect) | yes | D04, G07, H06 | identity | unconsumed |
| 104 | `typeBBridgeMass` | 85 | Type B bridge mass: centre bridge-mass bounds and the route-8 deficit sum <= route8Deficit + F s sigma | yes | H01, H02, H03, H08 | bound | derives residual keys: typeBBridgeSublinear |
| 105 | `typeBBridgeSublinear` | 189 | Type B bridge sublinearity: ordinary + grouped sums <= 2 F s sigma, sigma <= T(n) | yes | A14, H02, H08 | bound | unconsumed |
| 106 | `route8UnifiedNegative` | 336 | canonical collection X~ of Xi~: sigma = 0, negative net charge, no separator handoff, positive cleared summand; its defining sum | yes | D08, H01, H03, H08 | decomposition | unconsumed |
| 107 | `typeAExclusion` | 343 | at every negative zero-surplus piece of the canonical remainder: the Type A exclusion trichotomy | yes | B01, E09, H03 | classification | derives residual keys: route8PiecesClassified |
| 108 | `typeBBridgeReduction` | 344 | every negative positive-surplus piece: exact augmented ledger with negative remaining core and grouped coverage, or an overlap obstruction | yes | D05, D06, E09, H03, H04 | classification | derives residual keys: route8PiecesClassified |
| 109 | `route8PiecesClassified` | 266 | at negative zero-surplus pieces: each unpaid silent-excess/overloaded-port load of a saturated receiver is a route-8 entry or realizes the (b) quotient; or a Type B handoff; positive surplus: bridge pair | yes | E06, E09, H05 | classification | unconsumed |
| 110 | `route8ExtractedEntryCensus` | 350 | at extracted route-8 cores (quotient-free by construction): every entry has a selected basin, alpha >= 2, and is target-complete-minimal or (a) with an exit-(4) witness | yes | D04, E09, G07, H05, H06 | classification | unconsumed |
| 111 | `typeBSublinearLedger` | 345 | Type B handoff pieces: absorbed core, degree/trace conditions, non-absorbed receivers satisfy 1 + restrictedLoad <= s*missingPorts | yes | D08, H04, H05, H08 | bound | derives residual keys: route8UnifiedDeficit |
| 112 | `route8UnifiedDeficit` | 339 | ∣R0∣ <= route8Deficit(X~) + s∣dR∣ + F s T(n)  (cleared unified deficit) | yes | A10, G08, H01, H04, H08, H09 | bound | **read by 114**; derives residual keys: route8QuotientEntriesAtG |
| 113 | `route8QuotientResidual` | 348 | NOT Route8QuotientFree: some unified entry (X,w,u) has a selected basin B_u carrying a nontrivial target-complete trace-response quotient (alt (b), G-form: only outside context G - B_u) | yes | B07, D07, E06, E09 | obstruction | unconsumed within the residual: it is the failing test's negation (Free is decided by 114's first conjunct) |
| 114 | `route8QuotientEntriesAtG` | 8150 | Free <-> Xi~ = empty; ∣dR∣ < delta∣Xi~∣; at every entry alpha = 0, basin selected, (b) quotient present, canonical representative valid of size ∣piece∣ and not lex-smaller, no quotient reading lex-smaller with baseline, no exit-(5) datum | yes | A10, B05, B06, B07, D04, D07, D08, D09, E01, E02, E03, E05, E06, E07, E08, E09, F06, G07, H05, H06, H09, H10, I02 | classification | unconsumed within the residual: it is the residual's decision fact (with 113) |


## Gaps ranked

Ranking rule: number of distinct existing facts of the residual that would be combined with the new observable (ties broken by closeness to the defining failure). Fact numbers are Table 2 rows. Only structure present at G is listed; no numerical point is claimed.

Derived observation used throughout (from the Lean statements of 88, 112, 113, 114): the second conjunct of 114 gives `∣dR∣ < delta*∣Xi~∣`, hence `Xi~ != empty`, hence (first conjunct) `not Free`. So the Free arm is already closed by 114 (Free implies `Xi~ = empty` implies `∣dR∣ < 0`), and 113 is the whole outcome. A closure of `[187]` therefore needs a G-fact contradicting `Xi~ != empty` together with `alpha = 0` at every entry, i.e. an upper bound `delta*∣Xi~∣ <= ∣dR∣`-type charge, which the paper obtains from `alpha >= delta` (private carriers) and which the target-essential core cannot supply at G: completeness of the empty carrier set holds vacuously because every glue into `G - B_u` is a subgraph of G (`ofTraceBasin_alpha_eq_zero`).

| Rank | Coordinates | Present at G because | Missing observable and certificate | Technique | Existing facts it combines with (count) | Relevance to defining failure |
|---|---|---|---|---|---|---|
| 1 | H06 ~, G07 ~, D04 ~, H07 gap | 114 gives `Xi~ != empty` with `alpha = 0` at every entry, so the entries' units of the cleared deficit `D~_A` (88, 112) are charged to no cut incidence; saturated receivers have ports | G-constructed replacement of the target-essential core: for each entry `xi` the baseline-essential carrier set `C_delta(xi)` = incidences of `B_u` and `dB_u` whose retention is forced by `MinimumDegreeAtLeast delta` of `glue(retainedReading, G - B_u)` (the criterion 114 already uses in `Route8QuotientReadingsNotSmaller`); certificate: bound `∣C_delta(xi)∣ >= c` with a bounded-multiplicity map to edges of `R0 u W`, plus an integral flow / Hall witness or a min-cut obstruction from `Xi~` to legal resources | T15, T14 (T05) | 3, 5, 6, 7, 12, 24, 25, 26, 61, 78, 79, 88, 102, 103, 106, 109, 110, 112, 114 (19) | Direct: this is the missing charge for `delta*∣Xi~∣ <= ∣dR∣` against `∣dR∣ < delta*∣Xi~∣` |
| 2 | H05 ~ | Xi~ is indexed by saturated receivers and their unpaid excess loads (114, 106); 111 has the capacity inequality only for Type B handoff receivers | per saturated receiver of a Xi~ piece: `∣E(w)∣` against `s*missingPorts(w)` and the sum over receivers against `∣dR∣` / `def+(R0)`; certificate: bound | T13, T01 | 3, 6, 7, 24, 25, 26, 78, 79, 80, 88, 102, 106, 109, 111, 112, 114 (16) | Upper bound on `∣Xi~∣` in the units of `∣dR∣`, to be set against 114's lower bound |
| 3 | C06 ~, C07 gap, C11 ~, B04 ~, F08 ~ | each entry has a selected trace path `u -> w` inside `B_u`; retained readings are G's piece with internal edges dropped; 89 and 101 give returns | ear decomposition, cycle-space class and length/increment structure of the trace path and of the dropped internal edges; number of internally disjoint `w`-`u` routes; certificate: decomposition and bound | T08, T09 | 1, 2, 4, 8, 19, 20, 21, 22, 29, 30, 33, 34, 35, 89, 101, 114 (16) | Would say why a forgotten coordinate is or is not forced by the baseline/target; feeds gap 1 |
| 4 | B08 ~, D05 ~, D06 ~, F04 ~ | every entry has a basin `B_u` (114); entries of one receiver or piece share vertices | connectivity, size `∣B_u∣`, declared support of the changed coordinate, overlap graph of the basins of distinct entries and a minimal connected overlap obstruction; certificate: decomposition, bound | T10, T05 | 5, 9, 10, 11, 12, 23, 63, 77, 83, 96, 106, 108, 113, 114 (14) | Needed to make any per-entry charge injective (gap 1) |
| 5 | A11 ~ | `G[X]` is glued with its outside and readings drop internal edges (114); `def+` is certified only at `R0` | `delta - deg` of the retained reading at vertices of `B_u` for every retained coordinate set; certificate: bound | T05, T01 | 3, 5, 6, 7, 9, 24, 25, 27, 78, 79, 80, 114 (12) | Component observable of gap 1 |
| 6 | E08 ~, H10 ~ | the peeling descent of `[123]` (key `route8PeelingDescent`, idx 282) is consumed by row 114 (`Strategy/SpineRows/Route8QuotientEntriesAtG.lean`) but is not a fact of the residual | publish peel chain, `StageAccounting` equalities `∣Xi~∣ = ∣peeledEntries∣ + ∣chain∣`, `route8Deficit <= ∣peeledEntries∣`, `StageOutcome`; certificate: identity + witness | T19 | 88, 96, 102, 106, 107, 109, 110, 112, 113, 114 (10) | The rate vs stage accounting: without it the residual carries only the consequence `∣dR∣ < delta*∣Xi~∣` |
| 7 | I04 gap | 87 is conditional on `SufficientlyLargeForNetCap`; 88, 112 carry `o(n)` slacks | explicit `N0` with `n >= N0` at G or the finite list of small orders; certificate: exclusion | T17 | 8, 14, 17, 64, 79, 87, 88, 112 (8) | Side condition of the rate |
| 8 | F06 ~ | the forgotten coordinates of the (b) quotient are repaired by the canonical piece (114) | relation network among trace coordinates; certificate: decomposition | T11 | 11, 12, 63, 83, 94, 114 (6) | Explains why the quotient is target-complete |
| 9 | I05 ~, I06 ~ | 2 carries the HSS closure law and table semantics at G; 15, 66 are parameter tables | schema/generator/verifier of the barrier table; a consumer of the HSS law in a residual inequality | T17, T18 | 2, 15, 66, 67, 70 (5) | Not related to the failure |

## Non-G facts

| Fact | Object outside G | G-constructed accounting that replaces it |
|---|---|---|
| 15 `localAlgebra` | the abstract window-label algebra of order 13 (`∣Labels∣ = 399`, size distribution); the object argument is unused | the window packages and attachment labels at G's own packing: 67 (`windowPackageSeparated`), 38, 39 |
| 66 `barrierEnumeration` | the registered barrier table (safe/flat counts, log2 ratio); takes `data` only | 68 (`skeletonDominates`), 70 (`barrierCap`) stated at G's order and size |
| 2 `cubicBaseline` (partly) | three of its four components (`CubicBaselineStatement`, `TypeBPresentationStatement`, `SurplusPresentationStatement`) are parameter-only identities; the fourth (`SpinePresentationLawsStatement`) is stated at G | kept as about G for C04, G08, I05, I06; its parameter-only components earn nothing by themselves |

Checked and found about G (not marked nonG): 10 and 16 (`actualGlue` is G's piece glued into `G - Z`, a subgraph of G by `actualGlue_hom`; the "every reading" quantifier ranges over subsets of G's own vertices); 113 and 114 (`TraceResponseQuotient` is stated in its G-form, the only outside context being `G - B_u`; the paper's "every outside ∂B_u-context compatible with the boundary profile" is not asserted); 18, 21 (graphs built from G by suppression or antiPairs). The paper's all-context alternative (b) would be nonG; its G-constructed accounting is fact 114's representative/readings clauses.

## Cross-check results

1. Every coordinate code in Table 2 has status `x` or `~` in Table 1 and lists that fact: **PASS** (checked by the generator: no code in Table 2 belongs to a `gap`/`n/a` row; facts 15 and 66 list no code).
2. Every `x`/`~` in Table 1 cites at least one Table 2 row: **PASS** (the Table 1 fact column is generated from Table 2 membership; no `x`/`~` row is empty).
3. Every Table 2 row accounts for at least one coordinate or is labelled: **PASS with 2 labelled rows**: facts 15 and 66 are labelled nonG (parameter-only), not bookkeeping; no other row is empty.
4. No fact counted twice for the same demand in different currencies: **PASS on currencies, with restatements to count once**: 24 and 25 are conjuncts of 78 (same demand `def+(R0) <= e(R0,W) <= 15p + sigma_W`); 64 is the second conjunct of 73 and of 105; 84 is the equality of 81's maximum with 82's count; 113 is equivalent to `Xi~ != empty`, the first conjunct of 114; the second conjunct of 114 is derived from 88, 112 and the descent (282), so it is a consequence of those, not an independent certificate for A10/H09. In Table 1 these count as one certificate each.

Consistency notes (no failure): row 114's own requirements are 1, 12, 88, 112 and the descent 282; 282 is not among the residual's 114 keys (E08, H10 above). Key `route8UnifiedEmptyAtG` (idx 7900) is also absent from this residual; it holds for the quotient-free arm and is consistent with 114 only when `Xi~ = empty`.

## Outside the register

None forced. The target-relative essential-core measure `alpha` is a special case of H06/G07/D04; its degeneracy at G is recorded under gap 1.
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

## Addendum after the G-audit edits (author's note; not a re-run of the tables)

The tables above were generated on the residual with the first version of fact
114 (`route8QuotientEntriesAtG`, idx 8150) and without the descent fact.
Afterwards the following were added on the residual arm; the status counts
above (x 66, ~ 18, gap 3, n/a 1, nonG 0 at the fact level for 15 and 66) were
NOT recomputed:

- `K .route8PeelingDescent` (idx 282) is now a fact of `Route8QuotientOutcome`
  (Residuals.lean), so the ranked gap 6 (E08 ~, H10 ~) is built: the peel chain,
  the `StageAccounting` equalities and the `StageOutcome` are on the residual
  ledger, not only their consequence `|∂R| < δ·|Ξ̃|`.
- Fact 114 now also carries, at every unified entry: the constructed
  size-preserving canonical representative (`Route8BasinRepresentative`), the
  quotient readings that are not smaller valid replacements
  (`Route8QuotientReadingsNotSmaller`; an A11 baseline-deficit statement at the
  reading level), the folds of G's piece as smaller valid realizations with an
  accepted cycle (`Route8BasinFoldsCarryCycles`), and the undeclared target
  cycle of every smaller valid realization
  (`Route8SmallerRealizationsUndeclared`).
- Not built (would need new mathematics, see the register): the entry-charge
  map / baseline-essential carriers (gap 1), per-receiver load versus capacity
  (gap 2), trace-path ear structure (gap 3), basin overlap (gap 4).

Class-quantification check (route-8 quotient path): the test `[348]` and the
residual are stated over G's own entries `route8UnifiedEntries data G`, not over
a class containing other graphs; the counting consumes `|Ξ̃|`, and fact 114
publishes the aggregate form (`Free ↔ Ξ̃ = ∅`, `|∂R| < δ·|Ξ̃|`).  The universal
statements over pieces `Q` (`Route8SmallerRealizationsUndeclared`,
`Route8BasinFoldsCarryCycles`) are consequences of minimality with conclusions
about `glue Q (G − B_u)`; no residual concludes that some member fails.
