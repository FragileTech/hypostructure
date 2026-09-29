# Structural accounting: `BlockedBarrierOverlapOutcome` (node [172a]), final state

Worktree `/home/guillem/hs-wt-S172a`, branch `g-audit-172a`, uncommitted edits included. Recomputed from scratch on the exact `Holds` / Statement propositions (`Graph/Statements/Spine.lean`, `BlockedFailureG.lean`, `BlockedOverlapG.lean`, `Strategy/SpineVocabulary.lean`). Read-only.

## Header

- **Residual**: `BlockedBarrierOverlapOutcome` (generic; `Assembly/Residuals.lean` l.582) with the subtypes of `Assembly/Residuals/BlockedBarrierOverlapOutcome.lean`: `_DeficiencyAtOrAbove` (generic + `K .denseDeficiencyAtOrAbove`, arm A) and `_DeficiencyBelowRateFails` (generic + `K .denseDeficiencyBelow` + `K .route8RateFails`, arm B).
- **Fact count** (from the conjunction, confirmed by the template script: 125 keys): generic **125** facts (Table 2 rows 1-125); arm A adds row 126 (**126** facts); arm B adds rows 127, 128 (**127** facts). Table 2 has 128 rows. The docstrings ("99 common", "94 / 95 / 96") are stale against the code.
- **Defining failure**: at G's fixed maximal packing P0 the joint window package is not realized by the labelled skeleton class (`skeletonBudget < 2^(windowPackageBits*|P0|)`, fact 69), and on the dense-packing branch the aggregate test of `lem:scale-additivity` fails at G's class: at the first exposure coordinate c (window of P0, dyadic scale, barrier row (a,b); rank k in `blockedEncodingRank`), all earlier coordinates pass and `F_c * A_k < W_c * A_{k+1}`, where `A_k = blockedReachedCount k` (facts 120, 122). It is a numerical statement about G's class; it names no record and no member. The `[160]` split only records how the dense residual entered `[162]`: net-deficiency cap violated (tau >= 1/4, fact 126) or holding with the private-carrier rate failing (3/13 <= tau < 1/4, facts 127 + 128).

### Status counts (Table 1, 88 coordinates)

| x | ~ | gap | n/a | nonG |
|---|---|---|---|---|
| 65 | 18 | 3 | 2 | 0 |

Gaps: G04, G06, H04. n/a: A08, I04. No coordinate is nonG. (Previous report: 62 / 19 / 4 / 2 / 1.)

Changes against the previous report: D05 `~` to `x` (125); D06 `nonG` to `~` (122, 125); F06 `gap` to `~` (121); G03 `~` to `x` (120-124); G05 `~` to `x` (120, 122-124); G01, H09, H05, G09, I03, B01, B08, C01, C03, C13, D02, I02 gain citations. Arm rows renumbered 121-123 to 126-128.

### Headline answers on the changed facts

- **120 `blockedBarrierOverlap`**: the failing clause (first coordinate with `F_c*A_k < W_c*A_{k+1}`, earlier ones passing) is a count of G's class, determined by P0, B(P0), the near-cubic class and the coordinate order: about G. The first conjunct (`forall coordinate, BlockedStateFibreBoundAt and BlockedGraphFibreMonotonicityAt`) quantifies `forall member0 : blockedClassAt`, i.e. per-member fibre bounds for arbitrary members of B(P0) (labelled skeletons on V(G)); G is one of them (119, 121), but the conclusion is not about G alone. It is class quantification with a non-G conclusion, so it is **not credited** anywhere (in particular it does not earn G04). This is a partly-nonG conjunct inside an otherwise G fact; no Table 1 coordinate depends only on it, so the nonG count is 0.
- **121 `blockedOwnRecord`**: about G (`own.1.1 = objectSkeletonMember G`; surviving state at every coordinate; `1 <= |S fibre| <= |A fibre|` at G's own record).
- **122 `blockedFailureSlack`**, **123 `blockedPrefixCompression`**, **124 `blockedFailingSetCarries`**: numerical facts about G's class and the package rate (`windowPackageBits`, `canonicalWindowPacking`): about G.
- **125 `blockedOverlapSupport`**: for `own` = G's skeleton, constructions on G's graph (completion supports, closed walks in G, connectivity in G): about G.
- `K .blockedScaleAdditive` is not a fact of this residual (it is the positive arm of node [170], a decision input); it does not appear in the conjunction.

## Table 1 — Structural coordinates

Criterion for `x`: a Table-2 fact about G (cited) gives the coordinate's observable a certificate of the register's type at P0 / R / hot-cold / B(P0), and at least one cited fact is itself an inequality or identity that mixes the coordinate with another currency (or is read by another fact's statement). Because `[172a]` is a terminal residual, 'consumed' is read inside the fact statements only.

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 17, 68, 126, 127 | bound, identity | T01 T06 T12 T13 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 8, 50, 68 | bound, identity | T01 T04 T12 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 6, 7, 28, 31, 42, 56, 61 | exclusion, identity, bound, classification | T01 T07 T09 T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 2, 3, 7, 40 | identity, bound | T01 T07 T18 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 31, 55, 59, 61, 62, 64 | bound, identity | T01 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 21, 31, 41, 45, 55, 57, 62, 100 | exclusion, witness, bound, classification | T01 T03 T07 T08 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | ~ | 80 | exclusion | T06 | Only the emptiness of the 3-core of R (fact 80). No degeneracy number and no peeling order of R are published, and nothing combines them with the deficiency currency: publish a peeling order of G[R] with its degeneracy (T04/T19, certificate: decomposition) and consume it in 83/126-127. |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | none | none | none needed | G has no vertex of degree 2 (fact 3: delta(G) >= 3), so no maximal path with degree-two interior exists in G; excluded by fact 3. |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 28, 43, 54, 58, 83 | bound | T01 T07 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 24, 25, 53, 77, 81 | bound, identity | T01 T06 T07 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 24, 25, 38, 76, 77, 81 | bound, classification, identity | T01 T06 T07 T13 T14 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | bound | T01 | Bound 2 beta >= n+2 (fact 8) is proved but no other currency reads it: the skeleton class (68) and barrier code use m only through binomials, not beta. Missing: beta(G) versus the number of barrier-state coordinates or the free edges outside windows of the encoding (T01/T15, bound). |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 50, 51, 64, 82, 127 | bound | T01 T04 T06 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 54, 64, 65, 75 | bound, exclusion | T01 T07 T10 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | x | 5, 32, 89, 91, 125 | exclusion, classification, decomposition | T02 T04 T05 T08 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 50, 90 | bound, exclusion | T01 T04 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 27, 32, 33, 34 | classification, bound | T04 T07 T08 T09 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 20, 50 | witness, bound | T01 T03 T04 T08 | Only edge connectivity >= 2 (fact 50) and forced single paths (19-22); Menger-type count of internally disjoint paths between the two ends of a window (or between two placed windows) is not certified. Missing: max number of internally disjoint window-to-window paths at G (T08/T14, bound). |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 24, 25, 27, 38, 40 | bound, classification, identity | T01 T06 T07 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | x | 9, 11, 92 | exclusion, replacement, decomposition | T03 T05 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10, 16, 98, 112 | exclusion | T05 T08 | G-only: contexts are G - Z (facts 10, 98, 112); no glued outside context earns the mark. |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 23, 102, 125 | exclusion, bound | T10 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 25, 81, 82, 91 | bound, decomposition | T01 T05 T06 T08 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 19, 20, 22, 34, 36, 47, 60, 125 | witness, classification, bound | T03 T04 T06 T07 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 90 | exclusion | T04 T05 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 4, 16, 18, 29, 30, 33, 35, 97, 125 | exclusion, bound | T02 T03 T05 T08 T09 T10 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 2, 22, 29, 30, 34, 56, 110, 111 | identity, witness, exclusion, classification | T01 T03 T04 T08 T09 T18 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 20, 29, 30 | witness, exclusion | T03 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | ~ | 91 | decomposition | T05 T08 | Corridors are ears of the cold windows (91) but no ear decomposition of G, or of R, is certified. Missing: ear structure of G[R] relative to the windows of P0, counted (T04/T08, decomposition). |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | ~ | 30 | exclusion | T08 T09 | Only the meeting constraint (30) touches symmetric differences of two paths; no incidence-vector / cycle-space rank of the cycles through the windows (the ones the blocked class forbids) is certified. Missing: rank of the window cycle vectors in the cycle space of G (T08/T11, bound). |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 48, 49, 80, 119 | witness, classification, exclusion | T06 T07 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 70 | decomposition | T06 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 47, 48, 51, 80 | bound, classification, exclusion | T06 T07 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | x | 37, 91, 92, 93, 95, 96, 109 | classification, decomposition, witness | T05 T07 T08 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 39, 49, 119 | exclusion, classification, witness | T07 T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | ~ | 20, 39, 125 | witness, exclusion | T03 T07 T08 | Exclusions of simultaneous realizability at placed windows (20, 39) exist, but joint realizability of the two barrier legs a,b at scale 2^j (existence of a completion support, the some/none of the barrier code) is not certified for G's own windows. Missing: for each G-window, scale, row (a,b): completion present or absent in G (T08/T17, witness or exclusion). Fact 125 adds only conditional information: where a completion support is present it is a closed non-cycle walk of length 2^j through a root-window vertex; presence or absence at each (window, scale, row) is still not decided. |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 13, 36, 38, 39, 49, 119 | witness, classification, exclusion | T07 T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 15, 92, 121 | identity, decomposition | T05 T16 T17 | Local types of G's windows and attachments (labels 15, 39); the barrier STATE of G at each (window, scale, row) is not a fact: see G03/G05/F06. |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 21, 22, 28, 29, 32, 36, 37, 41, 42, 44, 45, 53, 54, 58, 60, 95, 100, 105, 106 | witness, bound, exclusion, classification | T03 T04 T07 T08 T09 T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | ~ | 28, 44 | bound, classification | T07 | Matching-in-N(h) and closed bag-link classes (28, 44) only. The incidence graph between barrier-demand coordinates and supporting incidences of G is not certified. Missing: matching-versus-star concentration of the coordinate/edge incidence of B(P0)'s code (T14, classification). |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 39, 78, 103, 125 | exclusion, identity, decomposition, bound | T06 T07 T08 T10 T15 | Fact 125 constructs the overlap relation of the barrier-state completion supports at G's own coordinates (same scale and row, different windows, supports meeting outside the root windows), bounds each support by 2^j + 1 vertices and proves the union over an overlap component connected in G; it reads fact 119 (no accepted cycle through a window makes each present walk a non-cycle) and 39 (window gap). The overlap graph is not yet combined with the F/W counts (see D06). |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 122, 125 | obstruction, decomposition | T10 T12 | Present: the failure is located at the first failing coordinate (fact 122: earlier aggregate tests hold) and the overlap support of every coordinate is connected (125). Missing: nothing ties the failing inequality to that support: the smallest connected family (overlap support of the failing coordinate, or a sub-family of it) on which additivity fails is not extracted. Missing observable: minimal connected sub-family of the overlap component of the failing coordinate, with a count of the F and W carriers charged to it (T10, certificate: obstruction). |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 108, 109, 114, 116 | exclusion, classification | T10 T16 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 70, 89, 116, 117 | decomposition, exclusion, replacement | T03 T06 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | ~ | 11, 92, 117 | replacement, decomposition | T03 T05 T10 T16 | Glue compatibility of swaps (11, 117) and pinned states (92); uniqueness of reconstruction from the barrier code is not certified (see G06). Missing: glue/decode uniqueness for B(P0) (T16, identity). |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 102, 103, 104, 105, 107 | bound, decomposition, witness, classification, exclusion | T06 T07 T10 T13 T15 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1, 11, 117 | exclusion, replacement | T02 T03 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5, 80 | exclusion | T02 T06 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 19, 20, 22, 32, 90 | witness, classification, exclusion | T03 T04 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | x | 12, 18, 21 | replacement, exclusion, witness | T03 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 99, 110, 111 | replacement, exclusion | T03 T09 T10 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 63, 67, 98, 108, 112 | exclusion, decomposition | T05 T10 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | x | 117, 118 | replacement, identity | T03 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 14, 80 | decomposition, exclusion | T06 T16 | Peeling of the windows leaves R with no window and no baseline subgraph (14, 80), but no one-unit peel step with a decreasing invariant is published. Missing: unit peel of R against def+(R) (T19, decomposition). |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 10, 16, 23, 65, 93, 97, 98, 101, 107, 108, 113, 115 | exclusion, witness, classification | T05 T08 T10 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 83, 85 | bound, identity | T11 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | x | 63, 84, 87, 88 | exclusion, bound, identity | T05 T11 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | x | 86 | decomposition | T11 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | ~ | 86 | decomposition | T11 | Determiners are finite subsets of the independent family (86); the vertices/contexts used by a dependence are not certified. Missing: geometric support of each dependence (T11/T10, decomposition). |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 67, 94 | decomposition, exclusion | T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | ~ | 121 | identity | T05 | Fact 121 certifies that G's own barrier state is a surviving state (IsBlockedSurvivingState) at every coordinate, but the absent-completion state `none` is also surviving, so this does not certify the composite (a, b, a+b) leg responses or their cancellations at G's windows. Missing: the composition table of the three Safe relations realized at G's windows (T05/T11, certificate: identity/decomposition). |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 86, 87 | decomposition, identity | T11 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 94, 111 | exclusion | T08 T09 T16 | Non-repetition of cut states up to first failure (94) and exclusion of a shortening germ (111); no periodicity/period statement for the barrier states across dyadic scales 2^j (registered scales) is certified. Missing: response of a window's barrier state as a function of the scale index (T09, classification). |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 68, 69, 71, 119, 120, 121, 122, 123, 124 | identity, bound, witness | T12 T15 T16 | Class B(P0) is counted through the budget bound (119), the joint package inequality (69, 71) and the reached counts A_k: 1 <= |B(P0)| <= A_{k+1} (122), |B|*prod W <= |A|*prod F on passing prefixes (123) and the failing-set inequality against the a-priori class (124). All counts are numerical facts about G's canonical class (n, m, delta, P0 positions), no member witness. |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 15, 42, 66, 67, 85 | identity, classification, decomposition | T07 T11 T12 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 67, 71, 73, 120, 121, 122, 123, 124 | decomposition, bound | T12 | Conditional information is measured as the ratios A_{k+1}/A_k of reached classes against F_{a,b}/W_{a,b} at every coordinate (120, 122, 123), summed over the failing set against the package bits (124), plus 1 <= |S fibre| <= |A fibre| at G's own record (121). The per-record fibre sizes at G are only certified qualitatively (121); the class-level state-fibre bound F+1 is the uncredited first conjunct of 120 (see G04). |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | gap | none | none | none used | Present at G: the barrier code of G's skeleton takes values in Option(label triple) with the distinguished absent-completion state 'none' (IsBlockedSurvivingState none = True), so the state fibres of each coordinate form a finite partition on B(P0). No fact bounds the largest state fibre. Missing: size of the largest fibre (in particular of 'none') of the barrier code at each coordinate, T12, certificate: bound. |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | x | 67, 69, 120, 122, 123, 124 | decomposition, bound, obstruction | T12 T15 | none at this residual's canonical objects: the additivity test W*A_{k+1} <= F*A_k is stated at G's class (120), located as the first failure (122), propagated over passing prefixes (123) and combined with the joint package rate 2^(bits*|P0|) (69, 124). |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | gap | none | none | none used | Present at G: blockedBarrierCode (lem:blocked-graphs-compress) is defined on B(P0), and G lies in B(P0) (119); its injectivity (reconstruction of the labelled skeleton from outside edges plus barrier states, in the order blockedEncodingRank) is not a fact. Missing: injectivity of the code on B(P0) (or an exact multiplicity), T15, certificate: identity/injection. |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 26, 33, 35, 61, 75, 76, 78, 91, 103 | identity, bound, decomposition | T01 T05 T06 T08 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 46, 64, 79, 82, 126, 127 | bound | T01 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 14, 17, 69, 71, 72, 74, 124, 126, 127 | decomposition, bound | T01 T06 T12 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 24, 43, 46, 57, 58, 59, 61, 81, 82, 83, 88, 126, 127 | bound, identity | T01 T06 T07 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | ~ | 89 | decomposition | T13 T16 | 89 gives the exact decomposition of the net charge over canonical pieces, conditional on NegativeNetCharge(R); no fact decides the sign of the charge of R or of a piece at G on this residual, and 126-128 do not read it. Missing: net charge of R and of its pieces at G (T13, bound). |
| H03 | Connected negative support | A connected region with negative charge. | ~ | 89 | decomposition | T13 T16 | 89 is an existence claim conditional on negative charge; on arm B, 127 is the strict cap handed to [57]-[62], but the connected negative piece of G[R] is not constructed. Missing: the piece and its charge (T13/T16, witness). |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | gap | none | none | none used | Present at G on arm B: 127 is the strict net-deficiency cap that hands R to the discharge of [57]-[62]; no fact gives the transfer rule from suppliers (stubs 82, wedges 83, window cut 25) to the deficits of R at G. Missing: an integral discharge/transfer scheme on G[R] with its feasibility inequality, T13/T14, certificate: decomposition. |
| H05 | Load and saturation | Load compared with certified capacity. | x | 25, 52, 69, 71, 82, 124, 128 | bound | T01 T06 T12 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | ~ | 26, 78 | identity | T15 | Assignment of selected stubs / primitive carriers to cold windows exactly once (26, 78, 91); the route-8 private carriers whose rate fails (128 is only the negation of Rate) are not assigned. Missing: the private-carrier assignment to entries of e(R,W) at G on arm B (T14/T15, decomposition). |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | ~ | 25 | bound | T01 T06 | Cut capacity e(R,W) (25) and deficiency <= cut (24) only; no integral flow in the demand-support network between R and the windows. Missing: an integral flow/matching certificate for the boundary incidences of R (T14, decomposition). |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 31, 74, 75, 79, 103, 104 | bound, decomposition, witness | T01 T06 T13 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 52, 69, 71, 72, 73, 88, 120, 122, 123, 124, 126, 127, 128 | bound | T02 T12 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 117, 118 | replacement, identity | T03 T16 | Single canonical swap descent (117, 118) under a well-founded piece order; no one-unit demand peel with a decreasing measure links def+(R) to descent. Missing: one-unit peel of def+(R) (T19, decomposition). |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 15, 66, 102, 114 | identity, bound, classification | T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | x | 14, 117, 118, 119, 121 | decomposition, replacement, identity, witness | T03 T06 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 69, 124, 126, 127 | bound | T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | n/a | none | none | none needed | Every asymptotic o(n) on this ledger is an exact allowance T(n) at G's own n (64, 79, 82, 88, 127); no fact carries a hypothesis 'n >= N0' and no small-order arm (unlike RealizedOrderSmall / BoundedOrderSmall) is on the ledger of [172a]; excluded by the exact statements 64, 79, 82, 127. |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | x | 15, 66, 71 | identity, bound | T12 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | x | 2 | identity | T01 T18 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |


## Table 2 — Facts of the residual -> structural coordinates

Columns as in the template. Arm rows: 126 arm A only; 127 and 128 arm B only. The residual is terminal, so unlisted consumers are `unconsumed within [172a]`.

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of an accepted (dyadic) length, and every strictly smaller baseline object (size order and refined order) has one. | yes | E01, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 2 | `cubicBaseline` | 221 | Presentation laws at G: delta=3, s=4, accepted lengths are exactly the dyadic ones, Type B and sparse-surplus presentation identities, HSS closure law at G and its induced subgraphs (bookkeeping-heavy; publishes the imported closure law). | yes | C04, I06, A04 | identity | read by every arithmetic of lengths and rate (windowRate, registered constants) |
| 3 | `minDegreeBaseline` | 2850 | Every vertex of G has degree >= 3. | yes | A04 | bound | unconsumed within [172a] (terminal residual) |
| 4 | `returnAvoidance` | 1 | At every dart of G the return-length set is disjoint from the shifted accepted set. | yes | C02, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has minimum degree >= 3, and G is connected. | yes | E02, B01 | exclusion | unconsumed within [172a] (terminal residual) |
| 6 | `slackIndependent` | 4 | Two vertices of G of degree > 3 are never adjacent. | yes | A06, A03 | exclusion | unconsumed within [172a] (terminal residual) |
| 7 | `tightEndpoint` | 3 | Every dart of G has an endpoint of degree exactly 3. | yes | A03, A04 | identity | unconsumed within [172a] (terminal residual) |
| 8 | `cycleRankConstraint` | 425 | n + 2 <= 2(m + 1 - n): cycle rank of G is at least n/2 + 1. | yes | A12, A02 | bound | unconsumed within [172a] (terminal residual) |
| 9 | `degreeProfileFibres` | 2300 | For every region X, admissible rank quotient and two readings of G at its support Z: different boundary-degree profile implies not identified. | yes | B06, E06 | exclusion | unconsumed within [172a] (terminal residual) |
| 10 | `targetCompleteContextUniversality` | 2301 | Identified readings of G share degree profile and power-of-two response in G - Z; no reading of G at any Z closes an accepted cycle in G - Z (G-only restatement). | yes | B07, E06, E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 11 | `replacementExclusion` | 223 | No proper connected support Z of G has a smaller degree-profile-preserving replacement X' whose swap glue X' (G - Z) is baseline and target-avoiding. | yes | E05, E01, B06, D09 | replacement | unconsumed within [172a] (terminal residual) |
| 12 | `uncompressible` | 5 | No proper support Z of G has a strictly smaller target-complete compression in G - Z. | yes | E05, E04 | replacement | unconsumed within [172a] (terminal residual) |
| 13 | `windowPresent` | 608 | G contains an induced path on windowOrder (13) vertices. | yes | C08, D01 | witness | unconsumed within [172a] (terminal residual) |
| 14 | `maximalPacking` | 6 | The canonical packing P0 of G is a maximum maximal vertex-disjoint family of induced windows, nonempty, every window of G meets a member. | yes | C09, D08, G09, I02, E08 | decomposition | unconsumed within [172a] (terminal residual) |
| 15 | `localAlgebra` | 7 | Label census at window order: \|Labels 13\| = 399 and size distribution [13,60,122,122,63,17,2] (statement about the label alphabet, not about a support of G). | yes | I01, I05, G02, D02 | identity | unconsumed within [172a] (terminal residual) |
| 16 | `everyWitnessSpectrumSplit` | 6702 | For every clause-(b) witness triple (A,B,Z) of G and X in {A,B}, ret_X glued into G - Z has no accepted cycle (G-only). | yes | E09, B07, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 17 | `packingOrderBound` | 6611 | 13 * \|P0\| <= n. | yes | G09, A01 | bound | unconsumed within [172a] (terminal residual) |
| 18 | `noSuppressionChordViolation` | 6620 | No open-port suppression cycle of G has accepted lifted length \|walk\| + \|chords\|. | yes | E04, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 19 | `twoSwitchForcedPath` | 6800 | Two-edge switch of G at u1v1,u2v2 (4 distinct ends, u1 not adjacent u2, deg v_i >= 4) forces a simple u1-u2 path of G minus the two edges with accepted closing length. | yes | C01, E03 | witness | unconsumed within [172a] (terminal residual) |
| 20 | `crossSwitchFamily` | 6802 | Cross-vertex switch family of G: forced simple paths u1 to u in G - {u1v,uh'}, and two h'-free internally disjoint paths of length 2^j - 1 into distinct neighbours of h' never coexist. | yes | C01, E03, C05, C13, B04 | witness | unconsumed within [172a] (terminal residual) |
| 21 | `highCentreSplitForced` | 6801 | Vertex split of G at every centre of degree > 3 forces an accepted cycle avoiding h that uses a new edge of the antipair set. | yes | D03, E04, A06 | witness | unconsumed within [172a] (terminal residual) |
| 22 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch of G forces a path u1-u2 in G - {hu1,hu2} with accepted \|p\|+1, splitting exactly (avoid h with \|p\|+2 not accepted, or split lengths with neither l_i+1 accepted). | yes | C01, C04, D03, E03 | witness | unconsumed within [172a] (terminal residual) |
| 23 | `specWitnessStructure` | 6677 | Every clause-(b) witness triple of G whose support is the canonical support of A u B has Z connected, containing A and B, a minimum connected set, and is not a Spec witness (G-only restatement). | yes | B08, E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 24 | `remainderDeficiencyBelowCut` | 6663 | def+(R) <= e(R,W) at P0 (R remainder, W union of windows). | yes | A10, A11, B05, H01 | bound | unconsumed within [172a] (terminal residual) |
| 25 | `windowCutCapacity` | 6664 | e(R,W) + 2(order-1)\|P0\| <= delta*order*\|P0\| + sigma_W (window cut capacity). | yes | A10, A11, B05, B09, H05, H07 | bound | unconsumed within [172a] (terminal residual) |
| 26 | `primitiveCarrierCount` | 6666 | \|U_sp(G)\| = 4n + 2 sigma (primitive carrier count). | yes | G07, H06 | identity | unconsumed within [172a] (terminal residual) |
| 27 | `singleBoundaryShape` | 6627 | Every support S of G with one boundary vertex b, a second vertex and an outside vertex has b with exactly two neighbours in S and two outside (2+2 cut vertex). | yes | B03, B05 | classification | unconsumed within [172a] (terminal residual) |
| 28 | `neighbourhoodPairCount` | 6900 | For every vertex h of G, G[N(h)] is a matching, N(h) has >= C(d,2) - floor(d/2) nonadjacent pairs, each x in N(h) has >= d-2 nonadjacent partners. | yes | D03, D04, A09, A03 | bound | unconsumed within [172a] (terminal residual) |
| 29 | `starCycleConstraint` | 6901 | Star constraint at every vertex h of G: paths x-y, x-z in G - h meeting only at x have \|P\|+\|Q\|+2 not a power of two >= 4. | yes | C03, C04, C05, D03 | exclusion | unconsumed within [172a] (terminal residual) |
| 30 | `meetingCycleConstraint` | 6902 | Meeting constraint at every vertex h of G for paths P,Q in G - h meeting at t: \|P\|+\|Q\|+2 != 2^k + \|P1\|+\|Q1\|. | yes | C03, C04, C05, C07 | exclusion | unconsumed within [172a] (terminal residual) |
| 31 | `highDegreePairSum` | 6903 | Pair sums over H = {d != 3}: 5 sigma <= sum C(d_h,2), quadratic sigma/\|H\| inequalities, 2 sum C(d_h,2) <= 16 sigma^2. | yes | A03, A05, A06, H08 | bound | unconsumed within [172a] (terminal residual) |
| 32 | `vertexDeletionComponents` | 6904 | For every vertex h of G, G - h is connected or d_h = 2 * blocks(h) with exactly two neighbours per component meeting N(h). | yes | B01, B03, E03, D03 | classification | unconsumed within [172a] (terminal residual) |
| 33 | `cyclesThroughVertex` | 6905 | C(d_h,2) <= #cycles through h when G - h connected; else d_h/2 <= #cycles(h). | yes | C03, G07, B03 | bound | unconsumed within [172a] (terminal residual) |
| 34 | `cutVertexBlockPaths` | 6906 | Block paths at cut vertices h of G: a-b paths of G - h have \|r\|+2 != 2^k, returns of ha end by bh, residue 3 mod 4 / 1 mod 4 conditions at lengths 2^j - 1. | yes | B03, C01, C04 | classification | unconsumed within [172a] (terminal residual) |
| 35 | `cycleDoubleCount` | 6907 | 2 sum_H #cycles(h) <= n #cycles(G), 2 sum_H L_h <= n #cycles(G), #cycles(G) <= 2^m. | yes | G07, C03 | bound | unconsumed within [172a] (terminal residual) |
| 36 | `threeRouteFan` | 7100 | Length-3 fan at G: two length-3 paths of G - h from a to distinct neighbours b,c of h share the first step and differ at the last. | yes | D03, C01, D01 | classification | unconsumed within [172a] (terminal residual) |
| 37 | `threeRouteChain` | 7101 | Chain 3,3,3 at G: length-3 paths a-b, b-c, c-d in G - h between neighbours of h force r1 = p2, r2 = q1. | yes | C11, D03 | classification | unconsumed within [172a] (terminal residual) |
| 38 | `windowPositionStubs` | 7102 | Every window of P0 has a placement; an interior placed vertex has d-2 external neighbours (1 when cubic), an end vertex d-1. | yes | D01, B05, A11 | classification | unconsumed within [172a] (terminal residual) |
| 39 | `windowAttachmentGap` | 7103 | Cross-edge gap: vertex-disjoint placed paths joined at (i,j),(i',j') have \|i-i'\|+2+\|j-j'\| not accepted; outside vertices of placed windows carry legal labels, adjacent ones C1-safe, two windows obey the gap rule, no ladder. | yes | D01, C12, C13, D05 | exclusion | unconsumed within [172a] (terminal residual) |
| 40 | `portEndDegree` | 7233 | Every selected port endpoint of G has degree 3. | yes | A04, B05 | identity | unconsumed within [172a] (terminal residual) |
| 41 | `hubLinkStructure` | 7217 | Link structure of the hubs of R at P0. | yes | D03, A06 | classification | unconsumed within [172a] (terminal residual) |
| 42 | `hubClassCounts` | 7218 | Hub classes of the cubic vertices of G. | yes | A03, D03, G02 | classification | unconsumed within [172a] (terminal residual) |
| 43 | `slotRelation` | 7219 | Slot relation of G: 4 sigma + 21\|H\| <= 3n + 6\|H\|^2. | yes | A09, H01 | bound | unconsumed within [172a] (terminal residual) |
| 44 | `closedClasses` | 7220 | Closed bag-link classes of the hubs of R at P0. | yes | D03, D04 | classification | unconsumed within [172a] (terminal residual) |
| 45 | `hubTwoHopLinks` | 7221 | Two-hop links between the hubs of R at P0. | yes | A06, D03 | classification | unconsumed within [172a] (terminal residual) |
| 46 | `slotLinear` | 7222 | 4 sigma + 15\|H\| <= 3n + K h_R + 584 nu + 32 sigma_W at P0 (K = 1811497284). | yes | H01, G08 | bound | unconsumed within [172a] (terminal residual) |
| 47 | `remainderPathBounds` | 7211 | Paths and cycles inside the remainder R of P0 (path bounds). | yes | C10, C01 | bound | unconsumed within [172a] (terminal residual) |
| 48 | `windowFreeGeometry` | 7212 | Window-free geometry of P0 (induced structure of R and windows). | yes | C10, C08 | classification | unconsumed within [172a] (terminal residual) |
| 49 | `inducedPathAttachment` | 7213 | Attachments of the induced P13s of G to the rest of G. | yes | D01, C08, C12 | classification | unconsumed within [172a] (terminal residual) |
| 50 | `densityExcess` | 7207 | Density of G in excess form; every nonempty proper vertex set has a >= 2-edge cut; single-hub slack. | yes | A02, A13, B02, B04 | bound | unconsumed within [172a] (terminal residual) |
| 51 | `remainderSlack` | 7208 | Remainder slack of P0 and its hanging windows. | yes | C10, A13 | bound | unconsumed within [172a] (terminal residual) |
| 52 | `hubWindowBudget` | 7209 | Hub-window budget at P0. | yes | H05, H09 | bound | unconsumed within [172a] (terminal residual) |
| 53 | `windowHubBounds` | 7210 | The windows of P0 against the big hubs (bounds). | yes | A10, D03 | bound | unconsumed within [172a] (terminal residual) |
| 54 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; \|L\| <= 2e(L). | yes | A09, A14, D03 | bound | unconsumed within [172a] (terminal residual) |
| 55 | `hubCountBound` | 7201 | 5\|H\| + sigma <= 2n. | yes | A05, A06 | bound | unconsumed within [172a] (terminal residual) |
| 56 | `lowEdgeParity` | 7202 | On walks of G, #LL + [u in H] + [v in H] + \|p\| is even; odd walks between cubic vertices use an odd number of L-L edges. | yes | C04, A03 | identity | unconsumed within [172a] (terminal residual) |
| 57 | `bigHubBound` | 7203 | Hub domination and 2\|B\| + sigma <= n. | yes | A06, H01 | bound | unconsumed within [172a] (terminal residual) |
| 58 | `bigHubVShapes` | 7204 | V-shape caps: <= 12 middles per pair of big hubs, \|X2\| <= 12(\|B\|^2 - \|B\|), 4 sigma + 93\|B\| <= 2n + 75\|B\|^2 + 4\|H\|. | yes | A09, D03, H01 | bound | unconsumed within [172a] (terminal residual) |
| 59 | `highSurplusBound` | 7205 | 24 sigma + 465\|B\| <= 18n + 375\|B\|^2 and 8n <= 32 s + 125 s^2 with s = n - sigma. | yes | H01, A05 | bound | unconsumed within [172a] (terminal residual) |
| 60 | `hubLengthThreePairs` | 7206 | Length-3 pairs at the hubs of G. | yes | C01, D03 | classification | unconsumed within [172a] (terminal residual) |
| 61 | `surplusDartIdentity` | 6607 | Dart identity: sigma + 2 delta \|H\| + lowDarts = delta n. | yes | A05, H01, G07, A03 | identity | unconsumed within [172a] (terminal residual) |
| 62 | `highDegreeCountBound` | 6608 | \|H\| <= sigma. | yes | A05, A06 | bound | unconsumed within [172a] (terminal residual) |
| 63 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible declared quotient of G is label-injective on its family. | yes | E06, F02 | exclusion | unconsumed within [172a] (terminal residual) |
| 64 | `surplusAtOrBelow` | 9 | sigma(G) <= T(n) (exact near-cubic allowance). | yes | A05, A13, A14, G08 | bound | unconsumed within [172a] (terminal residual) |
| 65 | `sparseSurplusSurvivor` | 119 | G survives the five sparse surplus exits of its declared sparse family. | yes | E09, A14 | exclusion | unconsumed within [172a] (terminal residual) |
| 66 | `barrierEnumeration` | 211 | Certified barrier enumeration read from the registered (1,1) row: safe, curvature-positive, flat counts, and their entropy cost log2(safe/flat). | yes | I01, I05, G02 | identity | unconsumed within [172a] (terminal residual) |
| 67 | `windowPackageSeparated` | 35 | Window package of P0: bits per window >= windowRate * scales, packages pairwise disjoint, \|family\| = bits * \|P0\|, every functional declared quotient is label-injective on the package and on package + spine family. | yes | F05, G02, G03, G05, E06 | decomposition | unconsumed within [172a] (terminal residual) |
| 68 | `skeletonDominates` | 206 | Skeleton class C(n,m): \|labelled skeletons\| = skeletonBudget and every state map on it realizes <= skeletonBudget states. | yes | G01, A01, A02 | identity | unconsumed within [172a] (terminal residual) |
| 69 | `windowPackageUnrealized` | 229 | skeletonBudget < 2^(windowPackageBits * \|P0\|): the joint window package is not realized (strict integer inequality retained through [169]-[171]). | yes | I03, G01, G05, H09, G09, H05 | bound | unconsumed within [172a] (terminal residual) |
| 70 | `hotColdPartition` | 200 | Canonical hot/cold partition of P0. | yes | D08, C09 | decomposition | unconsumed within [172a] (terminal residual) |
| 71 | `barrierCap` | 10 | 2^(windowRate * scales * \|hot\|) <= skeletonBudget. | yes | H09, G01, G09, H05, G03, I05 | bound | unconsumed within [172a] (terminal residual) |
| 72 | `coldRoute8AtOrAbove` | 213 | P0 is not below the route-8 density threshold ([146] no). | yes | G09, H09 | bound | unconsumed within [172a] (terminal residual) |
| 73 | `coldHotEntropyCap` | 215 | coldWindowBitRate * \|hot\| <= coldSkeletonAllowance. | yes | H09, G03 | bound | unconsumed within [172a] (terminal residual) |
| 74 | `coldMass` | 216 | coldRate * \|P0\| <= coldRate * \|cold\| + coldSkeletonAllowance. | yes | H08, G09 | bound | unconsumed within [172a] (terminal residual) |
| 75 | `coldAmbientCubic` | 217 | \|cold\| <= \|cubic cold\| + sigma and sigma <= T(n). | yes | A14, H08, G07 | bound | unconsumed within [172a] (terminal residual) |
| 76 | `coldStubExcess` | 218 | perWindow * \|cold\| <= perWindow * \|cubic cold\| + perWindow * sigma. | yes | G07, A11 | bound | unconsumed within [172a] (terminal residual) |
| 77 | `coldAmbientCubicStubExcess` | 180 | Every ambient-baseline member of the cold family has exactly 15 external stubs. | yes | A11, A10 | identity | unconsumed within [172a] (terminal residual) |
| 78 | `coldSelectedBranchExcess` | 179 | Selected half-edge mass of the cubic cold family = 9 * \|cubic cold\|, each selected half-edge charged at exactly one cold window. | yes | G07, H06, D05 | identity | unconsumed within [172a] (terminal residual) |
| 79 | `coldMassLinear` | 224 | (perWindow + (delta+1) * overlapBound) * sigma < perWindow * \|cold\|. | yes | G08, H08 | bound | unconsumed within [172a] (terminal residual) |
| 80 | `remainderNormalized` | 13 | Every subregion of the remainder R of P0 is window-free and carries no baseline subgraph. | yes | C10, C08, E02, A07, E08 | exclusion | unconsumed within [172a] (terminal residual) |
| 81 | `boundaryDemand` | 14 | def+(R) <= e(R,W) and e(R,W) + 2(order-1)\|P0\| <= delta*order*\|P0\| + sigma_W (both links). | yes | B09, A11, A10, H01 | bound | unconsumed within [172a] (terminal residual) |
| 82 | `stubSupply` | 15 | def+(R) + 2(order-1)\|P0\| <= delta*order*\|P0\| + T(n). | yes | B09, H01, A13, G08, H05 | bound | unconsumed within [172a] (terminal residual) |
| 83 | `wedgeSupply` | 16 | For every region X of R, delta\|X\| <= W2(X) + 2 def+(X); and delta\|R\| + 4(order-1)\|P0\| <= W2(R) + 2(delta*order*\|P0\| + T(n)). | yes | A09, F01, H01 | bound | unconsumed within [172a] (terminal residual) |
| 84 | `curvatureTargetRank` | 18 | r_Omega(R) is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily. | yes | F02 | bound | unconsumed within [172a] (terminal residual) |
| 85 | `exactResponseProfile` | 207 | The declared curvature tests of R number exactly W2(R). | yes | F01, G02 | identity | unconsumed within [172a] (terminal residual) |
| 86 | `targetRankCircuit` | 210 | Every raw test outside the maximal surviving family carries a proper finite target-dependence; no dependence means full survival. | yes | F03, F04, F07 | decomposition | unconsumed within [172a] (terminal residual) |
| 87 | `curvatureFullRank` | 20 | r_Omega(R) = W2(R) (full rank). | yes | F07, F02 | identity | unconsumed within [172a] (terminal residual) |
| 88 | `forcedCurvatureCost` | 37 | c_Omega (delta\|R\| + 4(order-1)\|P0\|) <= c_Omega r_Omega(R) + 2 c_Omega (delta*order*\|P0\| + T(n)). | yes | H09, H01, F02 | bound | unconsumed within [172a] (terminal residual) |
| 89 | `netChargeLocalization` | 46 | A remainder of negative net charge has a connected canonical piece of negative net charge. | yes | H02, H03, D08, B01 | decomposition | unconsumed within [172a] (terminal residual) |
| 90 | `bridgeless` | 226 | Every dart of G has a simple return after deletion: G is bridgeless. | yes | B02, E03, C02 | exclusion | unconsumed within [172a] (terminal residual) |
| 91 | `coldReturnCorridors` | 227 | Every boundary stub of every outside component of the cold windows has a return corridor; the selected stubs split as outside-foot plus cross-window. | yes | C11, C06, B09, B01, G07 | decomposition | unconsumed within [172a] (terminal residual) |
| 92 | `coldCorridorState` | 30 | Pinned cold corridor states (cut-state presentation) of every retained corridor, canonical second representative of every exchange germ, active interface width bound. | yes | D02, B06, C11, D09 | decomposition | unconsumed within [172a] (terminal residual) |
| 93 | `coldFirstFailureOccurrence` | 404 | The retained first-failure occurrence data of the cold corridors is inhabited. | yes | E09, C11 | witness | unconsumed within [172a] (terminal residual) |
| 94 | `coldCutStatesDistinct` | 3200 | Along each retained corridor the pinned cut states are pairwise distinct up to the first failure. | yes | F05, F08 | exclusion | unconsumed within [172a] (terminal residual) |
| 95 | `coldHeavyEntryTerminal` | 3202 | A corridor whose first failure is an (F4) entry into a heavy centre before its terminal segment is still terminal. | yes | D03, C11 | classification | unconsumed within [172a] (terminal residual) |
| 96 | `denseColdCorridorsTerminal` | 403 | Every return corridor of the dense hot/cold pass is terminal (F5). | yes | C11 | classification | read by 109 (first conjunct of NeutralEqualLengthTerminal) |
| 97 | `coldFailureCycle` | 64 | No segment of a retained cold corridor closes an accepted cycle through a placed window (F1 excluded). | yes | E09, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 98 | `coldFailureDefectRoute` | 422 | No segment of a retained corridor carries an (F2) target-defect (decided in G - J). | yes | E09, E06, B07 | exclusion | unconsumed within [172a] (terminal residual) |
| 99 | `coldFailureCompression` | 66 | No segment of a retained corridor carries a strictly smaller proper representative of its prefix support with G's response in G - J (F3 excluded). | yes | E05 | replacement | unconsumed within [172a] (terminal residual) |
| 100 | `coldHandoffTransfer` | 69 | First-high subcase of (F4): least corridor segment with head above the baseline, earlier heads at the baseline, root within exchangeBound + 2 of the selected half-edge in the subcubic reach. | yes | D03, A06 | classification | unconsumed within [172a] (terminal residual) |
| 101 | `coldFailureRouting` | 68 | Routing (F1)-(F5) of G's first failures, with (F2) excluded (structure holding surviving first-failure occurrence). | yes | E09 | classification | read by 102, 103, 105, 106 (each takes the routing as its existential witness) |
| 102 | `coldExchangeBound` | 177 | Terminal corridors satisfy statesRead + interfaceBudget <= exchangeBound (M_cold = Q_cold + 30). | yes | D10, I01, B08 | bound | unconsumed within [172a] (terminal residual) |
| 103 | `coldGermCandidates` | 219 | Extracted cold germ family: candidates, disjoint family, corridor loss, with #F4 handoff occurrences <= corridorLoss. | yes | D10, G07, H08, D05 | decomposition | unconsumed within [172a] (terminal residual) |
| 104 | `coldGermFamilyPositive` | 181 | The canonical extracted disjoint cold germ family is nonempty. | yes | D10, H08 | witness | unconsumed within [172a] (terminal residual) |
| 105 | `absorbedGermSplit` | 327 | Per-half-edge dichotomy: in the candidate set, or a least high vertex whose neighbours all sit at the threshold; cross-window occurrences are always candidates. | yes | D03, D10 | classification | unconsumed within [172a] (terminal residual) |
| 106 | `absorbedGermFanData` | 235 | Every occurrence outside the routed candidate set carries its least high vertex with all neighbours at degree 3. | yes | D03 | classification | unconsumed within [172a] (terminal residual) |
| 107 | `coldGermNoneRealizing` | 603 | No canonical active cold germ is realizing. | yes | E09, D10 | exclusion | unconsumed within [172a] (terminal residual) |
| 108 | `coldGermNoneDistinguishing` | 605 | No canonical active cold germ is distinguishing (in G - Z). | yes | E06, E09, D07 | exclusion | unconsumed within [172a] (terminal residual) |
| 109 | `coldNeutralEqualLengthTerminal` | 406 | Terminal (F5) corridors (from 96) and the silent family's neutral configuration with marked canonical exchange representative. | yes | D07, C11 | classification | read by 116-118 (marked neutral germ) |
| 110 | `coldGermRouted` | 71 | No canonical active cold germ has negative increment. | yes | E05, C04 | exclusion | unconsumed within [172a] (terminal residual) |
| 111 | `coldGermSilent` | 34 | A canonical active cold germ with negative increment is not neutral. | yes | E05, C04, F08 | exclusion | unconsumed within [172a] (terminal residual) |
| 112 | `coldGermDistinguished` | 33 | No canonical active cold germ is hit-distinguished (G2 empty at G). | yes | E06, B07 | exclusion | unconsumed within [172a] (terminal residual) |
| 113 | `coldGermRealized` | 32 | No canonical active cold germ is realizing (G1 excluded). | yes | E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 114 | `coldSameInterfaceTable` | 31 | Same-interface table of G's silent configurations: rows not realizing, in the (F4) registry or distinguishing; short self-returns survive smear; every row has increment 0. | yes | I01, D07 | classification | unconsumed within [172a] (terminal residual) |
| 115 | `coldBranchClosed` | 176 | No length-changing non-distinguishing germ, no terminal table row, no terminal self-return remain. | yes | E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 116 | `coldCanonicalNeutralConfiguration` | 233 | The marked neutral germ has no genuine second-strand realization (canonical-replacement case). | yes | D07, D08 | exclusion | unconsumed within [172a] (terminal residual) |
| 117 | `coldCanonicalReplacementSwap` | 408 | If the marked representative E differs from Q, gluing E into the retained outside gives a baseline target-avoiding graph with the same n and m and a strict predecessor. | yes | E07, D08, D09, E01, I02, H10 | replacement | unconsumed within [172a] (terminal residual) |
| 118 | `coldCanonicalReplacementTrivial` | 409 | The marked configuration has trivial canonical replacement E = Q. | yes | E07, I02, H10 | identity | read by 119 (residual hypothesis of blocked-class membership, per its docstring) |
| 119 | `blockedClassMember` | 238 | G's own labelled skeleton (G transported to Fin n) has min degree >= 3, contains every window of P0 at its position, has no accepted cycle through a window, and card of the blocked class B(P0) on V(G) with m edges is <= skeletonBudget. | yes | G01, C12, D01, I02, C08 | witness | read by 121, 122, 124, 125 (own = objectSkeletonMember G; the class blockedClassAt) |
| 120 | `blockedBarrierOverlap` | 321 | Aggregate failure of G's class: at the first exposure coordinate c (rank k) F_c * A_k < W_c * A_{k+1} with all earlier aggregate tests holding, where A_k = blockedReachedCount k (a-priori near-cubic graphs sharing outside record and earlier states with some member of B(P0)); no member witness. Plus the class-level conjunct: for every coordinate and every member0 of B(P0), state fibre <= F+1 and surviving fibre <= a-priori fibre. | yes for the failing clause (a numerical fact about G's class, determined by G's packing, class and coordinate order). Partly no for the first conjunct: `forall member0 : blockedClassAt` states per-member fibre bounds for arbitrary members of B(P0) (G is one, by 119/121); it is NOT credited on its own (its G-instance is only what 121 states for own = G's skeleton). No coordinate depends only on it. | G01, G03, G05, H09 | obstruction | terminal (the residual's defining failure); read by 122, 123, 124 through the shared aggregate test BlockedAggregateBoundAt |
| 121 | `blockedOwnRecord` | 8600 | G's own skeleton is a member `own` of B(P0) (own = objectSkeletonMember G); its barrier state is a surviving state at every coordinate; and at every coordinate 1 <= \|S fibre(own)\| <= \|A fibre(own)\| (G lies in its own conditional fibres). | yes | G03 (~ sub-object: qualitative), G01, D02, I02, F06 (~) | witness, bound | unconsumed within [172a] (terminal residual) |
| 122 | `blockedFailureSlack` | 8601 | At the first failing coordinate c (rank k): F_c*A_k < W_c*A_{k+1}, A_{k+1} <= A_k, 1 <= \|B(P0)\| <= A_{k+1}, and F_c < W_c; all earlier coordinates pass the aggregate test. | yes | G01, G03, G05, H09, D06 (~) | bound, obstruction | unconsumed within [172a] (terminal residual) |
| 123 | `blockedPrefixCompression` | 8602 | At every coordinate all of whose predecessors pass the aggregate test: \|B(P0)\| * prod_{pred} W <= \|A-class\| * prod_{pred} F (the exposure counting of lem:blocked-graphs-compress on the passing prefix). | yes | G01, G03, G05, H09 | bound | unconsumed within [172a] (terminal residual) |
| 124 | `blockedFailingSetCarries` | 8603 | With Phi the set of coordinates whose aggregate test fails: \|B(P0)\| * 2^(windowPackageBits*\|P0\|) * prod_Phi F <= \|A-class\| * prod_Phi W, so the package saving over the class bound is carried by Phi. | yes | G05, G03, G01, G09, H05, H09, I03 | bound | unconsumed within [172a] (terminal residual) |
| 125 | `blockedOverlapSupport` | 8604 | For G's own skeleton and every coordinate (window, scale 2^j, row): the canonical completion support has at most 2^j + 1 vertices; if present it is the support of a closed non-cycle walk of length 2^j in G through a root-window vertex; and the union of the supports over the overlap component of the coordinate is connected in G. | yes | D05, D06 (~), B08, B01, C03, C01, C13 (~) | bound, decomposition, exclusion | unconsumed within [172a] (terminal residual) |
| 126 | `denseDeficiencyAtOrAbove` | 231 | ARM A. Not(DenseDeficiencyBelow): discharge*(delta*order*p + T(n)) >= discharge*2(order-1)p + (n - order*p), i.e. tau(theta) >= 1/4 up to T(n). | yes | H01, G09, H09, G08, I03, A01 | bound | routing at [160]; selects the dense hot/cold pass [162] |
| 127 | `denseDeficiencyBelow` | 230 | ARM B. discharge*(delta*order*p + T(n)) < discharge*2(order-1)p + (n - order*p), i.e. tau(theta) < 1/4 up to T(n) (the strict cap [56] hands to [57]-[62]). | yes | H01, G09, H09, G08, A13, I03, A01 | bound | routing at [160]; with 128 selects the delicate interval 3/13 <= tau < 1/4 |
| 128 | `route8RateFails` | 265 | ARM B. Not Rate: (delta*s + 1)*e(R,W) + delta*slack >= delta*\|R\| with slack = bridgeMass*discharge*T(n), i.e. the private-carrier rate tau < 3/13 fails. | yes | H09, H05 | bound | routing at [160] (rate reading fails) |
## Gaps ranked (joint check, gaps and `~`)

Ranking = number of existing Table-2 facts that would be combined with the coordinate once measured. Coordinates that are `gap`: G06, G04, H04. The rest of the list is `~`.

1. **G06 (gap): injective reconstruction from local data (barrier code on B(P0))** (17 facts)
   - Why present at G: `blockedBarrierCode` is defined on B(P0) and G lies in it (119, 121); the encoding is (outside edge set, Option-valued states in `blockedEncodingRank` order). The reached class `A_k` (120) is defined by agreement with a member's code on the first k coordinates, so the multiplicity of the code is exactly what relates A_k to |B(P0)| and to the outside-record count. No fact states injectivity or a multiplicity.
   - Missing observable and certificate: multiplicity of `blockedBarrierCode` on B(P0) (injectivity, or the exact fibre over G's code word) and the number of admissible outside edge sets given the window edges. Certificate: injection / identity, giving `|B(P0)| <=` number of code words.
   - Technique: T15 (injection / reconstruction), T12.
   - Combines with: 14, 15, 38, 39, 66, 67, 68, 69, 70, 71, 119, 120, 121, 123, 124, 126, 127.

2. **D06 (`~`): minimal connected overlap obstruction at the failing coordinate** (14 facts)
   - Why present at G: the failing coordinate exists (122) and its overlap support is a connected subset of G (125); nothing says the failure lives on it or on a sub-family.
   - Missing observable and certificate: minimal connected sub-family of the overlap component of the failing coordinate together with the F and W carriers charged to it. Certificate: obstruction / decomposition.
   - Technique: T10 (uncrossing, minimal obstruction), T12.
   - Combines with: 14, 23, 39, 47, 48, 49, 70, 78, 80, 103, 119, 120, 122, 125.

3. **G04 (gap): dominant or repetitive local type (largest barrier-state fibre, in particular the absent state)** (13 facts; tie with H04)
   - Why present at G: the barrier code of G's skeleton takes Option-valued states; `none` (absent completion) is a surviving state with no cost in `blockedSurvivingCountAt`, so the state fibres form a partition of B(P0). The only bound on the largest state fibre (`<= F+1`) is the class-quantified first conjunct of 120, which is not credited; 121 gives only `1 <= |S| <= |A|` at G's own record.
   - Missing observable and certificate: size of the largest state fibre (especially `none`) at each coordinate as a G fact, e.g. the state-fibre bound instantiated at G's own record. Certificate: bound.
   - Technique: T12.
   - Combines with: 15, 66, 67, 68, 69, 71, 73, 119, 120, 121, 122, 126, 127.

3. **H04 (gap, arm B): feasibility of the local discharge on R (with H02/H03 and H06/H07)** (13 facts)
   - Why present at G: arm B is the strict cap `K .denseDeficiencyBelow` that hands R to `prop:negative-net-charge` ([57]-[62]); with `route8RateFails` the residual sits in 3/13 <= tau < 1/4. Suppliers (stubs 82, wedges 83, window cut 25, carriers 26) and deficits (24) are certified, but no transfer scheme, no negative piece (89 is conditional), no private-carrier assignment (128 is the negation of Rate).
   - Missing observable and certificate: integral transfer / flow from suppliers to the deficits of G[R], net charge of R and of a connected piece, private-carrier census at P0. Certificate: decomposition (flow) with the feasibility inequality.
   - Technique: T13, T14, T16.
   - Combines with: 24, 25, 26, 43, 46, 52, 81, 82, 83, 88, 89, 127, 128.

5. **F06 (`~`): cancellation and repair structure (composite (a,b,a+b) legs)** (10 facts)
   - Why present at G: `IsBlockedSurvivingState` composes Safe(a), Safe(b), Safe(a+b) on three labels at every G window / scale / row; 121 certifies survival at every coordinate but `none` also survives.
   - Missing observable and certificate: composition table of the leg responses realized at G's windows and its cancellations. Certificate: identity / decomposition.
   - Technique: T05, T11.
   - Combines with: 13, 15, 38, 39, 48, 49, 66, 67, 119, 121.

6. **C13 (`~`): joint realizability of the barrier legs (completion present or absent) at G's windows** (9 facts): observable: for each (window, scale, row) whether G realizes both legs simultaneously and simply; certificate witness / exclusion; T08, T17; combines with 20, 38, 39, 47, 48, 49, 66, 119, 125.
7. **H06/H07 (`~`, arm B): private-carrier assignment and flow-cut support of e(R,W)** (9 facts): `route8RateFails` is only `not Rate`; observable: integral assignment of the boundary incidences of R to entries / private carriers; certificate decomposition; T14, T15; combines with 24, 25, 26, 52, 78, 81, 82, 91, 128.
8. **A07 / E08 / H10 (`~`): degeneracy and unit peel of R** (7 facts): fact 80 empties the 3-core of R; observable: degeneracy and peeling order of G[R], one-unit peel against def+(R); certificate decomposition; T04, T19; combines with 14, 80, 83, 89, 117, 126, 127.
9. **H02 / H03 (`~`): net charge of R and connected negative piece** (5 facts): observable: net charge of R and of a canonical piece; certificate bound / witness; T13, T16; combines with 24, 82, 83, 89, 127.
10. **A12, B04, C06, C07, D04, D09, F04, F08 (each `~`)**: unranked tail, each combines with 2-4 facts (see Table 1 'Missing accounting'); union: 8, 50, 33, 20, 91, 30, 28, 44, 11, 92, 117, 86, 94, 111.

### Gaps relevant to the deficiency / rate split ([160])

- Facts 126 (arm A), 127 and 128 (arm B) are inequalities in (n, |P0|, |R|, e(R,W), T(n)). They meet the fibre failure only through |P0|: it enters `2^(windowPackageBits*|P0|)` (69), which fact 124 puts on the left of the failing-set inequality against `skeletonBudget`-side counts. The missing bridge is G06 (the outside-record count) plus G04, which turn 124 into a bound on |P0| that arms A and B can be tested against.
- Arm A (126) is only the negation of the strict cap; its margin is not measured. Arm B (127 + 128): H04, H02/H03 and H06/H07 above are the unmeasured structure.
- The split gives no evidence about which coordinate fails; the failing coordinate (122) is independent of tau in the ledger.

## Non-G facts

No fact is wholly nonG and no Table 1 coordinate is nonG.

| Fact | Non-G object | Treatment / G-constructed replacement |
|---|---|---|
| 120 `blockedBarrierOverlap`, first conjunct only | `forall member0 : blockedClassAt` (arbitrary members of B(P0)) in `BlockedStateFibreBoundAt` and `BlockedGraphFibreMonotonicityAt`; conclusion is a per-member fibre bound | Not credited to any coordinate. Replacement: the same two bounds at `own` = `objectSkeletonMember G` (121 already gives `1 <= |S| <= |A|` there); the missing G fact is `|state fibre(own)| <= F+1` (G04). The failing clause of 120 is G-only and is credited. |

Checked and kept as G-only: 1, 9, 10, 16, 23, 98, 112 (readings in G - Z), 11, 12, 99, 117 (swaps glued into G's own rest), 107, 108, 110-113 (germs of G's family), 63, 67 (quotients declared on G), 68 (class count in G's n, m), 119 (G's own skeleton; class cardinality is a parameter count), 121-125 (constructions at `own` = G's skeleton or numerical facts about G's class).

## Cross-check results

1. **Every coordinate code in Table 2 is `x` or `~` in Table 1 and lists that fact: PASS** (checked programmatically over all 128 rows; 0 offenders).
2. **Every `x` or `~` in Table 1 cites at least one Table-2 row, and each cited row lists the code: PASS** (65 x, 18 ~; 0 empty, 0 mismatches).
3. **Every Table-2 row accounts for at least one coordinate or is bookkeeping: PASS.** All 128 rows carry >= 1 code; none is labelled bookkeeping (row 2 partly, but keeps C04, A04, I06). Row 120 keeps G01, G03, G05, H09 through its failing clause only.
4. **No fact counted twice for the same demand in different currencies: PASS**, with the same-currency overlaps to be counted once: def+(R) <= e(R,W) <= capacity is published by 24 and 25, again in 81, 82, 83, 88; 76 = 75 scaled; 109 contains 96; 126 and 127 are complementary arms. New overlaps: 122 (failure slack) repeats the failing inequality of 120 and adds monotonicity and F < W; 123 and 124 are the same exposure counting on the passing prefix and on the failing set (complementary sets, one product each); 121 and 125 are at `own` = G's skeleton and measure different objects (fibres vs supports). None is a cross-currency double count.

## Outside the register

- The encoding order `blockedEncodingRank` (scale major, window, barrier row minor), the reached-class counts `A_k = blockedReachedCount k`, and the dyadic scale family `separatedScaleCount` index the G03/G05/G06 accounting but fit no separate coordinate. Nothing was forced into a row.
- Fact-count discrepancy (bookkeeping): docstrings state 94 / 99 common and 95 / 96 per arm; the code has 125 common, 126 (arm A), 127 (arm B).
