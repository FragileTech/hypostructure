# Structural accounting: `BlockedBarrierOverlapOutcome` (node [172a]), final state

> Coverage: the fact list of this report equals the Lean ledger: generic `BlockedBarrierOverlapOutcome` 124 facts, `_DeficiencyAtOrAbove` +1, `_DeficiencyBelowRateFails` +2 (127 keys, same set). Keys 9800-9807, 9850-9855, 9900-9902, 9975-9980, 9990-9991 are not on this residual. Fact list compared with the `Holds` conjuncts of the Lean abbrevs in `Assembly/Residuals.lean` and `Assembly/Residuals/`.

Worktree `/home/guillem/hs-wt-S172a`, branch `g-audit-172a`, uncommitted edits included. Recomputed from scratch on the exact `Holds` / Statement propositions (`Graph/Statements/Spine.lean`, `BlockedFailureG.lean`, `BlockedOverlapG.lean`, `Strategy/SpineVocabulary.lean`). Read-only.

## Header

- **Residual**: `BlockedBarrierOverlapOutcome` (generic; `Assembly/Residuals.lean` l.582) with the subtypes of `Assembly/Residuals/BlockedBarrierOverlapOutcome.lean`: `_DeficiencyAtOrAbove` (generic + `K .denseDeficiencyAtOrAbove`, arm A) and `_DeficiencyBelowRateFails` (generic + `K .denseDeficiencyBelow` + `K .route8RateFails`, arm B).
- **Fact count** (from the conjunction, confirmed by the template script: 124 keys): generic **124** facts (Table 2 rows 1-124); arm A adds row 125 (**125** facts); arm B adds rows 126, 127 (**126** facts). Table 2 has 127 rows.
- **Defining failure**: at G's fixed maximal packing P0 the joint window package is not realized by the labelled skeleton class (`skeletonBudget < 2^(windowPackageBits*|P0|)`, fact 68), and on the dense-packing branch the aggregate test of `lem:scale-additivity` fails at G's class: at the first exposure coordinate c (window of P0, dyadic scale, barrier row (a,b); rank k in `blockedEncodingRank`), all earlier coordinates pass and `F_c * A_k < W_c * A_{k+1}`, where `A_k = blockedReachedCount k` (facts 119, 121). It is a numerical statement about G's class; it names no record and no member. The `[160]` split only records how the dense residual entered `[162]`: net-deficiency cap violated (tau >= 1/4, fact 125) or holding with the private-carrier rate failing (3/13 <= tau < 1/4, facts 126 + 127).

### Status counts (Table 1, 88 coordinates)

| x | ~ | gap | n/a | nonG |
|---|---|---|---|---|
| 66 | 18 | 2 | 2 | 0 |

Gaps: G06, H04. n/a: A08, I04. No coordinate is nonG. (Original report: 62 / 19 / 4 / 2 / 1.) Final commit 3d95809: fact 119 lost its class-quantified first conjunct and fact 120 gained the largest-state-fibre bound (G04 built).

Changes against the previous report: D05 `~` to `x` (124); D06 `nonG` to `~` (121, 124); F06 `gap` to `~` (120); G03 `~` to `x` (119-123); G05 `~` to `x` (119, 121-123); G01, H09, H05, G09, I03, B01, B08, C01, C03, C13, D02, I02 gain citations. Arm rows renumbered 121-123 to 125-127.

### Headline answers on the changed facts

- **119 `blockedBarrierOverlap`**: fully about G. It is the first failing aggregate coordinate (earlier ones pass, `F_c*A_k < W_c*A_{k+1}`), a count of G's class; it has no class-quantified fibre conjunct.
- **120 `blockedOwnRecord`**: about G (`own` = objectSkeletonMember G; surviving state at every coordinate; `1 <= |S| <= |A|`; and the conditional fibre of the barrier code at own has at most F+1 elements at every coordinate, so G04 is built).
- **121 `blockedFailureSlack`**, **122 `blockedPrefixCompression`**, **123 `blockedFailingSetCarries`**: numerical facts about G's class and the package rate (`windowPackageBits`, `canonicalWindowPacking`): about G.
- **124 `blockedOverlapSupport`**: for `own` = G's skeleton, constructions on G's graph (completion supports, closed walks in G, connectivity in G): about G.
- `K .blockedScaleAdditive` is not a fact of this residual (it is the positive arm of node [170], a decision input); it does not appear in the conjunction.

## Table 1 — Structural coordinates

Criterion for `x`: a Table-2 fact about G (cited) gives the coordinate's observable a certificate of the register's type at P0 / R / hot-cold / B(P0), and at least one cited fact is itself an inequality or identity that mixes the coordinate with another currency (or is read by another fact's statement). Because `[172a]` is a terminal residual, 'consumed' is read inside the fact statements only.

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | x | 16, 67, 125, 126 | bound, identity | T01 T06 T12 T13 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A02 | Size and edge density | Number of edges and density relative to order. | x | 8, 49, 67 | bound, identity | T01 T04 T12 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | x | 6, 7, 27, 30, 41, 55, 60 | exclusion, identity, bound, classification | T01 T07 T09 T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | x | 2, 3, 7, 39 | identity, bound | T01 T07 T18 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | x | 30, 54, 58, 60, 61, 63 | bound, identity | T01 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | x | 6, 20, 30, 40, 44, 54, 56, 61, 99 | exclusion, witness, bound, classification | T01 T03 T07 T08 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | ~ | 79 | exclusion | T06 | Only the emptiness of the 3-core of R (fact 79). No degeneracy number and no peeling order of R are published, and nothing combines them with the deficiency currency: publish a peeling order of G[R] with its degeneracy (T04/T19, certificate: decomposition) and consume it in 82/125-126. |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | n/a | none | none | none needed | G has no vertex of degree 2 (fact 3: delta(G) >= 3), so no maximal path with degree-two interior exists in G; excluded by fact 3. |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | x | 27, 42, 53, 57, 82 | bound | T01 T07 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | x | 23, 24, 52, 76, 80 | bound, identity | T01 T06 T07 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | x | 23, 24, 37, 75, 76, 80 | bound, classification, identity | T01 T06 T07 T13 T14 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A12 | Cycle rank | Dimension of the binary cycle space. | ~ | 8 | bound | T01 | Bound 2 beta >= n+2 (fact 8) is proved but no other currency reads it: the skeleton class (67) and barrier code use m only through binomials, not beta. Missing: beta(G) versus the number of barrier-state coordinates or the free edges outside windows of the encoding (T01/T15, bound). |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | x | 49, 50, 63, 81, 126 | bound | T01 T04 T06 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | x | 53, 63, 64, 74 | bound, exclusion | T01 T07 T10 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | x | 5, 31, 88, 90, 124 | exclusion, classification, decomposition | T02 T04 T05 T08 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | x | 49, 89 | bound, exclusion | T01 T04 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | x | 26, 31, 32, 33 | classification, bound | T04 T07 T08 T09 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | ~ | 19, 49 | witness, bound | T01 T03 T04 T08 | Only edge connectivity >= 2 (fact 49) and forced single paths (18-21); Menger-type count of internally disjoint paths between the two ends of a window (or between two placed windows) is not certified. Missing: max number of internally disjoint window-to-window paths at G (T08/T14, bound). |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | x | 23, 24, 26, 37, 39 | bound, classification, identity | T01 T06 T07 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | x | 9, 11, 91 | exclusion, replacement, decomposition | T03 T05 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | x | 10, 97, 111 | exclusion | T05 T08 | G-only: contexts are G - Z (facts 10, 97, 111); no glued outside context earns the mark. |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | x | 22, 101, 124 | decomposition, exclusion, bound | T10 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | x | 24, 80, 81, 90 | bound, decomposition | T01 T05 T06 T08 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | x | 18, 19, 21, 33, 35, 46, 59, 124 | witness, classification, bound | T03 T04 T06 T07 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | x | 4, 89 | exclusion | T04 T05 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | x | 1, 4, 17, 28, 29, 32, 34, 96, 124 | exclusion, bound | T02 T03 T05 T08 T09 T10 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | x | 2, 21, 28, 29, 33, 55, 109, 110 | identity, witness, exclusion, classification | T01 T03 T04 T08 T09 T18 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | x | 19, 28, 29 | witness, exclusion | T03 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | ~ | 90 | decomposition | T05 T08 | Corridors are ears of the cold windows (90) but no ear decomposition of G, or of R, is certified. Missing: ear structure of G[R] relative to the windows of P0, counted (T04/T08, decomposition). |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | ~ | 29 | exclusion | T08 T09 | Only the meeting constraint (29) touches symmetric differences of two paths; no incidence-vector / cycle-space rank of the cycles through the windows (the ones the blocked class forbids) is certified. Missing: rank of the window cycle vectors in the cycle space of G (T08/T11, bound). |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | x | 13, 47, 48, 79, 118 | witness, classification, exclusion | T06 T07 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | x | 14, 69 | decomposition | T06 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | x | 46, 47, 50, 79 | bound, classification, exclusion | T06 T07 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | x | 36, 90, 91, 92, 94, 95, 108 | classification, decomposition, witness | T05 T07 T08 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | x | 38, 48, 118 | exclusion, classification, witness | T07 T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | ~ | 19, 38, 124 | witness, exclusion | T03 T07 T08 | Exclusions of simultaneous realizability at placed windows (19, 38) exist, but joint realizability of the two barrier legs a,b at scale 2^j (existence of a completion support, the some/none of the barrier code) is not certified for G's own windows. Missing: for each G-window, scale, row (a,b): completion present or absent in G (T08/T17, witness or exclusion). Fact 124 adds only conditional information: where a completion support is present it is a closed non-cycle walk of length 2^j through a root-window vertex; presence or absence at each (window, scale, row) is still not decided. |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | x | 13, 35, 37, 38, 48, 118 | witness, classification, exclusion | T07 T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | x | 15, 91, 120 | identity, decomposition | T05 T16 T17 | Local types of G's windows and attachments (labels 15, 38); the barrier STATE of G at each (window, scale, row) is not a fact: see G03/G05/F06. |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | x | 20, 21, 27, 28, 31, 35, 36, 40, 41, 43, 44, 52, 53, 57, 59, 94, 99, 104, 105 | witness, bound, exclusion, classification | T03 T04 T07 T08 T09 T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | ~ | 27, 43 | bound, classification | T07 | Matching-in-N(h) and closed bag-link classes (27, 43) only. The incidence graph between barrier-demand coordinates and supporting incidences of G is not certified. Missing: matching-versus-star concentration of the coordinate/edge incidence of B(P0)'s code (T14, classification). |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | x | 38, 77, 102, 124 | exclusion, identity, decomposition, bound | T06 T07 T08 T10 T15 | Fact 124 constructs the overlap relation of the barrier-state completion supports at G's own coordinates (same scale and row, different windows, supports meeting outside the root windows), bounds each support by 2^j + 1 vertices and proves the union over an overlap component connected in G; it reads fact 118 (no accepted cycle through a window makes each present walk a non-cycle) and 38 (window gap). The overlap graph is not yet combined with the F/W counts (see D06). |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | ~ | 121, 124 | obstruction, decomposition | T10 T12 | Present: the failure is located at the first failing coordinate (fact 121: earlier aggregate tests hold) and the overlap support of every coordinate is connected (124). Missing: nothing ties the failing inequality to that support: the smallest connected family (overlap support of the failing coordinate, or a sub-family of it) on which additivity fails is not extracted. Missing observable: minimal connected sub-family of the overlap component of the failing coordinate, with a count of the F and W carriers charged to it (T10, certificate: obstruction). |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | x | 107, 108, 113, 115 | exclusion, classification | T10 T16 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | x | 14, 69, 88, 115, 116 | decomposition, exclusion, replacement | T03 T06 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | ~ | 11, 91, 116 | replacement, decomposition | T03 T05 T10 T16 | Glue compatibility of swaps (11, 116) and pinned states (91); uniqueness of reconstruction from the barrier code is not certified (see G06). Missing: glue/decode uniqueness for B(P0) (T16, identity). |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | x | 101, 102, 103, 104, 106 | bound, decomposition, witness, classification, exclusion | T06 T07 T10 T13 T15 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | x | 1, 11, 116 | exclusion, replacement | T02 T03 T10 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | x | 5, 79 | exclusion | T02 T06 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | x | 18, 19, 21, 31, 89 | witness, classification, exclusion | T03 T04 T08 T09 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | x | 12, 17, 20 | replacement, exclusion, witness | T03 T08 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | x | 11, 12, 98, 109, 110 | replacement, exclusion | T03 T09 T10 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | x | 9, 10, 62, 66, 97, 107, 111 | exclusion, decomposition | T05 T10 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | x | 116, 117 | replacement, identity | T03 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| E08 | Peelability | A removable unit preserving the residual invariant. | ~ | 14, 79 | decomposition, exclusion | T06 T16 | Peeling of the windows leaves R with no window and no baseline subgraph (14, 79), but no one-unit peel step with a decreasing invariant is published. Missing: unit peel of R against def+(R) (T19, decomposition). |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | x | 10, 64, 92, 96, 97, 100, 106, 107, 112, 114 | exclusion, witness, classification | T05 T08 T10 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | x | 82, 84 | bound, identity | T11 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | x | 62, 83, 86, 87 | exclusion, bound, identity | T05 T11 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | x | 85 | decomposition | T11 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | ~ | 85 | decomposition | T11 | Determiners are finite subsets of the independent family (85); the vertices/contexts used by a dependence are not certified. Missing: geometric support of each dependence (T11/T10, decomposition). |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | x | 66, 93 | decomposition, exclusion | T08 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | ~ | 120 | identity | T05 | Fact 120 certifies that G's own barrier state is a surviving state (IsBlockedSurvivingState) at every coordinate, but the absent-completion state `none` is also surviving, so this does not certify the composite (a, b, a+b) leg responses or their cancellations at G's windows. Missing: the composition table of the three Safe relations realized at G's windows (T05/T11, certificate: identity/decomposition). |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | x | 85, 86 | decomposition, identity | T11 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | ~ | 93, 110 | exclusion | T08 T09 T16 | Non-repetition of cut states up to first failure (93) and exclusion of a shortening germ (110); no periodicity/period statement for the barrier states across dyadic scales 2^j (registered scales) is certified. Missing: response of a window's barrier state as a function of the scale index (T09, classification). |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | x | 67, 68, 70, 118, 119, 120, 121, 122, 123 | identity, bound, witness | T12 T15 T16 | Class B(P0) is counted through the budget bound (118), the joint package inequality (68, 70) and the reached counts A_k: 1 <= |B(P0)| <= A_{k+1} (121), |B|*prod W <= |A|*prod F on passing prefixes (122) and the failing-set inequality against the a-priori class (123). All counts are numerical facts about G's canonical class (n, m, delta, P0 positions), no member witness. |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | x | 15, 41, 65, 66, 84 | identity, classification, decomposition | T07 T11 T12 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | x | 66, 70, 72, 119, 120, 121, 122, 123 | decomposition, bound | T12 | Conditional information is measured as the ratios A_{k+1}/A_k of reached classes against F_{a,b}/W_{a,b} at every coordinate (119, 121, 122), summed over the failing set against the package bits (123), plus 1 <= |S fibre| <= |A fibre| at G's own record (120). The per-record fibre sizes at G are only certified qualitatively (120); the state-fibre bound F+1 at G's own record is in 120 (G04). |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | x | 120 | bound | T12 | Fact 120 bounds the barrier states realized at G's own record (the conditional fibre of the barrier code at own = G's skeleton) by F_{a,b}+1 at every coordinate, the same F_{a,b} that enters the failing inequality (119, 121), the prefix counting (122) and the failing-set inequality (123). Not measured: the fibre of the absent state `none` separately, and fibres at other members. |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | x | 66, 68, 119, 121, 122, 123 | decomposition, bound, obstruction | T12 T15 | none at this residual's canonical objects: the additivity test W*A_{k+1} <= F*A_k is stated at G's class (119), located as the first failure (121), propagated over passing prefixes (122) and combined with the joint package rate 2^(bits*|P0|) (68, 123). |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | gap | none | none | none used | Present at G: blockedBarrierCode (lem:blocked-graphs-compress) is defined on B(P0), and G lies in B(P0) (118); its injectivity (reconstruction of the labelled skeleton from outside edges plus barrier states, in the order blockedEncodingRank) is not a fact. Missing: injectivity of the code on B(P0) (or an exact multiplicity), T15, certificate: identity/injection. |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | x | 25, 32, 34, 60, 74, 75, 77, 90, 102 | identity, bound, decomposition | T01 T05 T06 T08 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | x | 45, 63, 78, 81, 125, 126 | bound | T01 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | x | 14, 16, 68, 70, 71, 73, 123, 125, 126 | decomposition, bound | T01 T06 T12 T13 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | x | 23, 42, 45, 56, 57, 58, 60, 80, 81, 82, 87, 125, 126 | bound, identity | T01 T06 T07 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | ~ | 88 | decomposition | T13 T16 | 88 gives the exact decomposition of the net charge over canonical pieces, conditional on NegativeNetCharge(R); no fact decides the sign of the charge of R or of a piece at G on this residual, and 125-127 do not read it. Missing: net charge of R and of its pieces at G (T13, bound). |
| H03 | Connected negative support | A connected region with negative charge. | ~ | 88 | decomposition | T13 T16 | 88 is an existence claim conditional on negative charge; on arm B, 126 is the strict cap handed to [57]-[62], but the connected negative piece of G[R] is not constructed. Missing: the piece and its charge (T13/T16, witness). |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | gap | none | none | none used | Present at G on arm B: 126 is the strict net-deficiency cap that hands R to the discharge of [57]-[62]; no fact gives the transfer rule from suppliers (stubs 81, wedges 82, window cut 24) to the deficits of R at G. Missing: an integral discharge/transfer scheme on G[R] with its feasibility inequality, T13/T14, certificate: decomposition. |
| H05 | Load and saturation | Load compared with certified capacity. | x | 24, 51, 68, 70, 81, 123, 127 | bound | T01 T06 T12 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | ~ | 25, 77 | identity | T15 | Assignment of selected stubs / primitive carriers to cold windows exactly once (25, 77, 90); the route-8 private carriers whose rate fails (127 is only the negation of Rate) are not assigned. Missing: the private-carrier assignment to entries of e(R,W) at G on arm B (T14/T15, decomposition). |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | ~ | 24 | bound | T01 T06 | Cut capacity e(R,W) (24) and deficiency <= cut (23) only; no integral flow in the demand-support network between R and the windows. Missing: an integral flow/matching certificate for the boundary incidences of R (T14, decomposition). |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | x | 30, 73, 74, 78, 102, 103 | bound, decomposition, witness | T01 T06 T13 T15 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | x | 51, 68, 70, 71, 72, 87, 119, 121, 122, 123, 125, 126, 127 | bound | T02 T12 T13 T14 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | ~ | 116, 117 | replacement, identity | T03 T16 | Single canonical swap descent (116, 117) under a well-founded piece order; no one-unit demand peel with a decreasing measure links def+(R) to descent. Missing: one-unit peel of def+(R) (T19, decomposition). |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | x | 15, 65, 101, 113 | identity, bound, classification | T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | x | 14, 116, 117, 118, 120 | decomposition, replacement, identity, witness | T03 T06 T12 T16 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | x | 68, 123, 125, 126 | bound | T12 T13 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | n/a | none | none | none needed | Every asymptotic o(n) on this ledger is an exact allowance T(n) at G's own n (63, 78, 81, 87, 126); no fact carries a hypothesis 'n >= N0' and no small-order arm (unlike RealizedOrderSmall / BoundedOrderSmall) is on the ledger of [172a]; excluded by the exact statements 63, 78, 81, 126. |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | x | 15, 65, 70 | identity, bound | T12 T17 | none at this residual's canonical objects (P0, R, hot/cold, B(P0)) |
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
| 16 | `packingOrderBound` | 6611 | 13 * \|P0\| <= n. | yes | G09, A01 | bound | unconsumed within [172a] (terminal residual) |
| 17 | `noSuppressionChordViolation` | 6620 | No open-port suppression cycle of G has accepted lifted length \|walk\| + \|chords\|. | yes | E04, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 18 | `twoSwitchForcedPath` | 6800 | Two-edge switch of G at u1v1,u2v2 (4 distinct ends, u1 not adjacent u2, deg v_i >= 4) forces a simple u1-u2 path of G minus the two edges with accepted closing length. | yes | C01, E03 | witness | unconsumed within [172a] (terminal residual) |
| 19 | `crossSwitchFamily` | 6802 | Cross-vertex switch family of G: forced simple paths u1 to u in G - {u1v,uh'}, and two h'-free internally disjoint paths of length 2^j - 1 into distinct neighbours of h' never coexist. | yes | C01, E03, C05, C13, B04 | witness | unconsumed within [172a] (terminal residual) |
| 20 | `highCentreSplitForced` | 6801 | Vertex split of G at every centre of degree > 3 forces an accepted cycle avoiding h that uses a new edge of the antipair set. | yes | D03, E04, A06 | witness | unconsumed within [172a] (terminal residual) |
| 21 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch of G forces a path u1-u2 in G - {hu1,hu2} with accepted \|p\|+1, splitting exactly (avoid h with \|p\|+2 not accepted, or split lengths with neither l_i+1 accepted). | yes | C01, C04, D03, E03 | witness | unconsumed within [172a] (terminal residual) |
| 22 | `declaredPairSupportStructure` | 6677 | For every two declared sparse coordinates A, B of G, the canonical support Z = select?(A u B) is connected in G, contains A and B, and is a minimum connected set of G containing A u B. | yes | B08 | decomposition | unconsumed within [172a] (terminal residual) |
| 23 | `remainderDeficiencyBelowCut` | 6663 | def+(R) <= e(R,W) at P0 (R remainder, W union of windows). | yes | A10, A11, B05, H01 | bound | unconsumed within [172a] (terminal residual) |
| 24 | `windowCutCapacity` | 6664 | e(R,W) + 2(order-1)\|P0\| <= delta*order*\|P0\| + sigma_W (window cut capacity). | yes | A10, A11, B05, B09, H05, H07 | bound | unconsumed within [172a] (terminal residual) |
| 25 | `primitiveCarrierCount` | 6666 | \|U_sp(G)\| = 4n + 2 sigma (primitive carrier count). | yes | G07, H06 | identity | unconsumed within [172a] (terminal residual) |
| 26 | `singleBoundaryShape` | 6627 | Every support S of G with one boundary vertex b, a second vertex and an outside vertex has b with exactly two neighbours in S and two outside (2+2 cut vertex). | yes | B03, B05 | classification | unconsumed within [172a] (terminal residual) |
| 27 | `neighbourhoodPairCount` | 6900 | For every vertex h of G, G[N(h)] is a matching, N(h) has >= C(d,2) - floor(d/2) nonadjacent pairs, each x in N(h) has >= d-2 nonadjacent partners. | yes | D03, D04, A09, A03 | bound | unconsumed within [172a] (terminal residual) |
| 28 | `starCycleConstraint` | 6901 | Star constraint at every vertex h of G: paths x-y, x-z in G - h meeting only at x have \|P\|+\|Q\|+2 not a power of two >= 4. | yes | C03, C04, C05, D03 | exclusion | unconsumed within [172a] (terminal residual) |
| 29 | `meetingCycleConstraint` | 6902 | Meeting constraint at every vertex h of G for paths P,Q in G - h meeting at t: \|P\|+\|Q\|+2 != 2^k + \|P1\|+\|Q1\|. | yes | C03, C04, C05, C07 | exclusion | unconsumed within [172a] (terminal residual) |
| 30 | `highDegreePairSum` | 6903 | Pair sums over H = {d != 3}: 5 sigma <= sum C(d_h,2), quadratic sigma/\|H\| inequalities, 2 sum C(d_h,2) <= 16 sigma^2. | yes | A03, A05, A06, H08 | bound | unconsumed within [172a] (terminal residual) |
| 31 | `vertexDeletionComponents` | 6904 | For every vertex h of G, G - h is connected or d_h = 2 * blocks(h) with exactly two neighbours per component meeting N(h). | yes | B01, B03, E03, D03 | classification | unconsumed within [172a] (terminal residual) |
| 32 | `cyclesThroughVertex` | 6905 | C(d_h,2) <= #cycles through h when G - h connected; else d_h/2 <= #cycles(h). | yes | C03, G07, B03 | bound | unconsumed within [172a] (terminal residual) |
| 33 | `cutVertexBlockPaths` | 6906 | Block paths at cut vertices h of G: a-b paths of G - h have \|r\|+2 != 2^k, returns of ha end by bh, residue 3 mod 4 / 1 mod 4 conditions at lengths 2^j - 1. | yes | B03, C01, C04 | classification | unconsumed within [172a] (terminal residual) |
| 34 | `cycleDoubleCount` | 6907 | 2 sum_H #cycles(h) <= n #cycles(G), 2 sum_H L_h <= n #cycles(G), #cycles(G) <= 2^m. | yes | G07, C03 | bound | unconsumed within [172a] (terminal residual) |
| 35 | `threeRouteFan` | 7100 | Length-3 fan at G: two length-3 paths of G - h from a to distinct neighbours b,c of h share the first step and differ at the last. | yes | D03, C01, D01 | classification | unconsumed within [172a] (terminal residual) |
| 36 | `threeRouteChain` | 7101 | Chain 3,3,3 at G: length-3 paths a-b, b-c, c-d in G - h between neighbours of h force r1 = p2, r2 = q1. | yes | C11, D03 | classification | unconsumed within [172a] (terminal residual) |
| 37 | `windowPositionStubs` | 7102 | Every window of P0 has a placement; an interior placed vertex has d-2 external neighbours (1 when cubic), an end vertex d-1. | yes | D01, B05, A11 | classification | unconsumed within [172a] (terminal residual) |
| 38 | `windowAttachmentGap` | 7103 | Cross-edge gap: vertex-disjoint placed paths joined at (i,j),(i',j') have \|i-i'\|+2+\|j-j'\| not accepted; outside vertices of placed windows carry legal labels, adjacent ones C1-safe, two windows obey the gap rule, no ladder. | yes | D01, C12, C13, D05 | exclusion | unconsumed within [172a] (terminal residual) |
| 39 | `portEndDegree` | 7233 | Every selected port endpoint of G has degree 3. | yes | A04, B05 | identity | unconsumed within [172a] (terminal residual) |
| 40 | `hubLinkStructure` | 7217 | Link structure of the hubs of R at P0. | yes | D03, A06 | classification | unconsumed within [172a] (terminal residual) |
| 41 | `hubClassCounts` | 7218 | Hub classes of the cubic vertices of G. | yes | A03, D03, G02 | classification | unconsumed within [172a] (terminal residual) |
| 42 | `slotRelation` | 7219 | Slot relation of G: 4 sigma + 21\|H\| <= 3n + 6\|H\|^2. | yes | A09, H01 | bound | unconsumed within [172a] (terminal residual) |
| 43 | `closedClasses` | 7220 | Closed bag-link classes of the hubs of R at P0. | yes | D03, D04 | classification | unconsumed within [172a] (terminal residual) |
| 44 | `hubTwoHopLinks` | 7221 | Two-hop links between the hubs of R at P0. | yes | A06, D03 | classification | unconsumed within [172a] (terminal residual) |
| 45 | `slotLinear` | 7222 | 4 sigma + 15\|H\| <= 3n + K h_R + 584 nu + 32 sigma_W at P0 (K = 1811497284). | yes | H01, G08 | bound | unconsumed within [172a] (terminal residual) |
| 46 | `remainderPathBounds` | 7211 | Paths and cycles inside the remainder R of P0 (path bounds). | yes | C10, C01 | bound | unconsumed within [172a] (terminal residual) |
| 47 | `windowFreeGeometry` | 7212 | Window-free geometry of P0 (induced structure of R and windows). | yes | C10, C08 | classification | unconsumed within [172a] (terminal residual) |
| 48 | `inducedPathAttachment` | 7213 | Attachments of the induced P13s of G to the rest of G. | yes | D01, C08, C12 | classification | unconsumed within [172a] (terminal residual) |
| 49 | `densityExcess` | 7207 | Density of G in excess form; every nonempty proper vertex set has a >= 2-edge cut; single-hub slack. | yes | A02, A13, B02, B04 | bound | unconsumed within [172a] (terminal residual) |
| 50 | `remainderSlack` | 7208 | Remainder slack of P0 and its hanging windows. | yes | C10, A13 | bound | unconsumed within [172a] (terminal residual) |
| 51 | `hubWindowBudget` | 7209 | Hub-window budget at P0. | yes | H05, H09 | bound | unconsumed within [172a] (terminal residual) |
| 52 | `windowHubBounds` | 7210 | The windows of P0 against the big hubs (bounds). | yes | A10, D03 | bound | unconsumed within [172a] (terminal residual) |
| 53 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour and <= 2 hub neighbours; \|L\| <= 2e(L). | yes | A09, A14, D03 | bound | unconsumed within [172a] (terminal residual) |
| 54 | `hubCountBound` | 7201 | 5\|H\| + sigma <= 2n. | yes | A05, A06 | bound | unconsumed within [172a] (terminal residual) |
| 55 | `lowEdgeParity` | 7202 | On walks of G, #LL + [u in H] + [v in H] + \|p\| is even; odd walks between cubic vertices use an odd number of L-L edges. | yes | C04, A03 | identity | unconsumed within [172a] (terminal residual) |
| 56 | `bigHubBound` | 7203 | Hub domination and 2\|B\| + sigma <= n. | yes | A06, H01 | bound | unconsumed within [172a] (terminal residual) |
| 57 | `bigHubVShapes` | 7204 | V-shape caps: <= 12 middles per pair of big hubs, \|X2\| <= 12(\|B\|^2 - \|B\|), 4 sigma + 93\|B\| <= 2n + 75\|B\|^2 + 4\|H\|. | yes | A09, D03, H01 | bound | unconsumed within [172a] (terminal residual) |
| 58 | `highSurplusBound` | 7205 | 24 sigma + 465\|B\| <= 18n + 375\|B\|^2 and 8n <= 32 s + 125 s^2 with s = n - sigma. | yes | H01, A05 | bound | unconsumed within [172a] (terminal residual) |
| 59 | `hubLengthThreePairs` | 7206 | Length-3 pairs at the hubs of G. | yes | C01, D03 | classification | unconsumed within [172a] (terminal residual) |
| 60 | `surplusDartIdentity` | 6607 | Dart identity: sigma + 2 delta \|H\| + lowDarts = delta n. | yes | A05, H01, G07, A03 | identity | unconsumed within [172a] (terminal residual) |
| 61 | `highDegreeCountBound` | 6608 | \|H\| <= sigma. | yes | A05, A06 | bound | unconsumed within [172a] (terminal residual) |
| 62 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible declared quotient of G is label-injective on its family. | yes | E06, F02 | exclusion | unconsumed within [172a] (terminal residual) |
| 63 | `surplusAtOrBelow` | 9 | sigma(G) <= T(n) (exact near-cubic allowance). | yes | A05, A13, A14, G08 | bound | unconsumed within [172a] (terminal residual) |
| 64 | `sparseSurplusSurvivor` | 119 | G survives the five sparse surplus exits of its declared sparse family. | yes | E09, A14 | exclusion | unconsumed within [172a] (terminal residual) |
| 65 | `barrierEnumeration` | 211 | Certified barrier enumeration read from the registered (1,1) row: safe, curvature-positive, flat counts, and their entropy cost log2(safe/flat). | yes | I01, I05, G02 | identity | unconsumed within [172a] (terminal residual) |
| 66 | `windowPackageSeparated` | 35 | Window package of P0: bits per window >= windowRate * scales, packages pairwise disjoint, \|family\| = bits * \|P0\|, every functional declared quotient is label-injective on the package and on package + spine family. | yes | F05, G02, G03, G05, E06 | decomposition | unconsumed within [172a] (terminal residual) |
| 67 | `skeletonDominates` | 206 | Skeleton class C(n,m): \|labelled skeletons\| = skeletonBudget and every state map on it realizes <= skeletonBudget states. | yes | G01, A01, A02 | identity | unconsumed within [172a] (terminal residual) |
| 68 | `windowPackageUnrealized` | 229 | skeletonBudget < 2^(windowPackageBits * \|P0\|): the joint window package is not realized (strict integer inequality retained through [169]-[171]). | yes | I03, G01, G05, H09, G09, H05 | bound | unconsumed within [172a] (terminal residual) |
| 69 | `hotColdPartition` | 200 | Canonical hot/cold partition of P0. | yes | D08, C09 | decomposition | unconsumed within [172a] (terminal residual) |
| 70 | `barrierCap` | 10 | 2^(windowRate * scales * \|hot\|) <= skeletonBudget. | yes | H09, G01, G09, H05, G03, I05 | bound | unconsumed within [172a] (terminal residual) |
| 71 | `coldRoute8AtOrAbove` | 213 | P0 is not below the route-8 density threshold ([146] no). | yes | G09, H09 | bound | unconsumed within [172a] (terminal residual) |
| 72 | `coldHotEntropyCap` | 215 | coldWindowBitRate * \|hot\| <= coldSkeletonAllowance. | yes | H09, G03 | bound | unconsumed within [172a] (terminal residual) |
| 73 | `coldMass` | 216 | coldRate * \|P0\| <= coldRate * \|cold\| + coldSkeletonAllowance. | yes | H08, G09 | bound | unconsumed within [172a] (terminal residual) |
| 74 | `coldAmbientCubic` | 217 | \|cold\| <= \|cubic cold\| + sigma and sigma <= T(n). | yes | A14, H08, G07 | bound | unconsumed within [172a] (terminal residual) |
| 75 | `coldStubExcess` | 218 | perWindow * \|cold\| <= perWindow * \|cubic cold\| + perWindow * sigma. | yes | G07, A11 | bound | unconsumed within [172a] (terminal residual) |
| 76 | `coldAmbientCubicStubExcess` | 180 | Every ambient-baseline member of the cold family has exactly 15 external stubs. | yes | A11, A10 | identity | unconsumed within [172a] (terminal residual) |
| 77 | `coldSelectedBranchExcess` | 179 | Selected half-edge mass of the cubic cold family = 9 * \|cubic cold\|, each selected half-edge charged at exactly one cold window. | yes | G07, H06, D05 | identity | unconsumed within [172a] (terminal residual) |
| 78 | `coldMassLinear` | 224 | (perWindow + (delta+1) * overlapBound) * sigma < perWindow * \|cold\|. | yes | G08, H08 | bound | unconsumed within [172a] (terminal residual) |
| 79 | `remainderNormalized` | 13 | Every subregion of the remainder R of P0 is window-free and carries no baseline subgraph. | yes | C10, C08, E02, A07, E08 | exclusion | unconsumed within [172a] (terminal residual) |
| 80 | `boundaryDemand` | 14 | def+(R) <= e(R,W) and e(R,W) + 2(order-1)\|P0\| <= delta*order*\|P0\| + sigma_W (both links). | yes | B09, A11, A10, H01 | bound | unconsumed within [172a] (terminal residual) |
| 81 | `stubSupply` | 15 | def+(R) + 2(order-1)\|P0\| <= delta*order*\|P0\| + T(n). | yes | B09, H01, A13, G08, H05 | bound | unconsumed within [172a] (terminal residual) |
| 82 | `wedgeSupply` | 16 | For every region X of R, delta\|X\| <= W2(X) + 2 def+(X); and delta\|R\| + 4(order-1)\|P0\| <= W2(R) + 2(delta*order*\|P0\| + T(n)). | yes | A09, F01, H01 | bound | unconsumed within [172a] (terminal residual) |
| 83 | `curvatureTargetRank` | 18 | r_Omega(R) is attained by a surviving subfamily of raw curvature tests and bounds every surviving subfamily. | yes | F02 | bound | unconsumed within [172a] (terminal residual) |
| 84 | `exactResponseProfile` | 207 | The declared curvature tests of R number exactly W2(R). | yes | F01, G02 | identity | unconsumed within [172a] (terminal residual) |
| 85 | `targetRankCircuit` | 210 | Every raw test outside the maximal surviving family carries a proper finite target-dependence; no dependence means full survival. | yes | F03, F04, F07 | decomposition | unconsumed within [172a] (terminal residual) |
| 86 | `curvatureFullRank` | 20 | r_Omega(R) = W2(R) (full rank). | yes | F07, F02 | identity | unconsumed within [172a] (terminal residual) |
| 87 | `forcedCurvatureCost` | 37 | c_Omega (delta\|R\| + 4(order-1)\|P0\|) <= c_Omega r_Omega(R) + 2 c_Omega (delta*order*\|P0\| + T(n)). | yes | H09, H01, F02 | bound | unconsumed within [172a] (terminal residual) |
| 88 | `netChargeLocalization` | 46 | A remainder of negative net charge has a connected canonical piece of negative net charge. | yes | H02, H03, D08, B01 | decomposition | unconsumed within [172a] (terminal residual) |
| 89 | `bridgeless` | 226 | Every dart of G has a simple return after deletion: G is bridgeless. | yes | B02, E03, C02 | exclusion | unconsumed within [172a] (terminal residual) |
| 90 | `coldReturnCorridors` | 227 | Every boundary stub of every outside component of the cold windows has a return corridor; the selected stubs split as outside-foot plus cross-window. | yes | C11, C06, B09, B01, G07 | decomposition | unconsumed within [172a] (terminal residual) |
| 91 | `coldCorridorState` | 30 | Pinned cold corridor states (cut-state presentation) of every retained corridor, canonical second representative of every exchange germ, active interface width bound. | yes | D02, B06, C11, D09 | decomposition | unconsumed within [172a] (terminal residual) |
| 92 | `coldFirstFailureOccurrence` | 404 | The retained first-failure occurrence data of the cold corridors is inhabited. | yes | E09, C11 | witness | unconsumed within [172a] (terminal residual) |
| 93 | `coldCutStatesDistinct` | 3200 | Along each retained corridor the pinned cut states are pairwise distinct up to the first failure. | yes | F05, F08 | exclusion | unconsumed within [172a] (terminal residual) |
| 94 | `coldHeavyEntryTerminal` | 3202 | A corridor whose first failure is an (F4) entry into a heavy centre before its terminal segment is still terminal. | yes | D03, C11 | classification | unconsumed within [172a] (terminal residual) |
| 95 | `denseColdCorridorsTerminal` | 403 | Every return corridor of the dense hot/cold pass is terminal (F5). | yes | C11 | classification | read by 108 (first conjunct of NeutralEqualLengthTerminal) |
| 96 | `coldFailureCycle` | 64 | No segment of a retained cold corridor closes an accepted cycle through a placed window (F1 excluded). | yes | E09, C03 | exclusion | unconsumed within [172a] (terminal residual) |
| 97 | `coldFailureDefectRoute` | 422 | No segment of a retained corridor carries an (F2) target-defect (decided in G - J). | yes | E09, E06, B07 | exclusion | unconsumed within [172a] (terminal residual) |
| 98 | `coldFailureCompression` | 66 | No segment of a retained corridor carries a strictly smaller proper representative of its prefix support with G's response in G - J (F3 excluded). | yes | E05 | replacement | unconsumed within [172a] (terminal residual) |
| 99 | `coldHandoffTransfer` | 69 | First-high subcase of (F4): least corridor segment with head above the baseline, earlier heads at the baseline, root within exchangeBound + 2 of the selected half-edge in the subcubic reach. | yes | D03, A06 | classification | unconsumed within [172a] (terminal residual) |
| 100 | `coldFailureRouting` | 68 | Routing (F1)-(F5) of G's first failures, with (F2) excluded (structure holding surviving first-failure occurrence). | yes | E09 | classification | read by 101, 102, 104, 105 (each takes the routing as its existential witness) |
| 101 | `coldExchangeBound` | 177 | Terminal corridors satisfy statesRead + interfaceBudget <= exchangeBound (M_cold = Q_cold + 30). | yes | D10, I01, B08 | bound | unconsumed within [172a] (terminal residual) |
| 102 | `coldGermCandidates` | 219 | Extracted cold germ family: candidates, disjoint family, corridor loss, with #F4 handoff occurrences <= corridorLoss. | yes | D10, G07, H08, D05 | decomposition | unconsumed within [172a] (terminal residual) |
| 103 | `coldGermFamilyPositive` | 181 | The canonical extracted disjoint cold germ family is nonempty. | yes | D10, H08 | witness | unconsumed within [172a] (terminal residual) |
| 104 | `absorbedGermSplit` | 327 | Per-half-edge dichotomy: in the candidate set, or a least high vertex whose neighbours all sit at the threshold; cross-window occurrences are always candidates. | yes | D03, D10 | classification | unconsumed within [172a] (terminal residual) |
| 105 | `absorbedGermFanData` | 235 | Every occurrence outside the routed candidate set carries its least high vertex with all neighbours at degree 3. | yes | D03 | classification | unconsumed within [172a] (terminal residual) |
| 106 | `coldGermNoneRealizing` | 603 | No canonical active cold germ is realizing. | yes | E09, D10 | exclusion | unconsumed within [172a] (terminal residual) |
| 107 | `coldGermNoneDistinguishing` | 605 | No canonical active cold germ is distinguishing (in G - Z). | yes | E06, E09, D07 | exclusion | unconsumed within [172a] (terminal residual) |
| 108 | `coldNeutralEqualLengthTerminal` | 406 | Terminal (F5) corridors (from 95) and the silent family's neutral configuration with marked canonical exchange representative. | yes | D07, C11 | classification | read by 115-117 (marked neutral germ) |
| 109 | `coldGermRouted` | 71 | No canonical active cold germ has negative increment. | yes | E05, C04 | exclusion | unconsumed within [172a] (terminal residual) |
| 110 | `coldGermSilent` | 34 | A canonical active cold germ with negative increment is not neutral. | yes | E05, C04, F08 | exclusion | unconsumed within [172a] (terminal residual) |
| 111 | `coldGermDistinguished` | 33 | No canonical active cold germ is hit-distinguished (G2 empty at G). | yes | E06, B07 | exclusion | unconsumed within [172a] (terminal residual) |
| 112 | `coldGermRealized` | 32 | No canonical active cold germ is realizing (G1 excluded). | yes | E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 113 | `coldSameInterfaceTable` | 31 | Same-interface table of G's silent configurations: rows not realizing, in the (F4) registry or distinguishing; short self-returns survive smear; every row has increment 0. | yes | I01, D07 | classification | unconsumed within [172a] (terminal residual) |
| 114 | `coldBranchClosed` | 176 | No length-changing non-distinguishing germ, no terminal table row, no terminal self-return remain. | yes | E09 | exclusion | unconsumed within [172a] (terminal residual) |
| 115 | `coldCanonicalNeutralConfiguration` | 233 | The marked neutral germ has no genuine second-strand realization (canonical-replacement case). | yes | D07, D08 | exclusion | unconsumed within [172a] (terminal residual) |
| 116 | `coldCanonicalReplacementSwap` | 408 | If the marked representative E differs from Q, gluing E into the retained outside gives a baseline target-avoiding graph with the same n and m and a strict predecessor. | yes | E07, D08, D09, E01, I02, H10 | replacement | unconsumed within [172a] (terminal residual) |
| 117 | `coldCanonicalReplacementTrivial` | 409 | The marked configuration has trivial canonical replacement E = Q. | yes | E07, I02, H10 | identity | read by 118 (residual hypothesis of blocked-class membership, per its docstring) |
| 118 | `blockedClassMember` | 238 | G's own labelled skeleton (G transported to Fin n) has min degree >= 3, contains every window of P0 at its position, has no accepted cycle through a window, and card of the blocked class B(P0) on V(G) with m edges is <= skeletonBudget. | yes | G01, C12, D01, I02, C08 | witness | read by 120, 121, 123, 124 (own = objectSkeletonMember G; the class blockedClassAt) |
| 119 | `blockedBarrierOverlap` | 321 | Aggregate failure of G's class: at the first exposure coordinate c (rank k) F_c * A_k < W_c * A_{k+1} with all earlier aggregate tests holding, where A_k = blockedReachedCount k. No member witness and no other conjunct. | yes: a numerical fact about G's class, determined by G's packing, class and coordinate order | G01, G03, G05, H09 | obstruction | terminal (the residual's defining failure); read by 121, 122, 123 through the shared aggregate test BlockedAggregateBoundAt |
| 120 | `blockedOwnRecord` | 8600 | G's own skeleton is a member `own` of B(P0) (own = objectSkeletonMember G); its barrier state is a surviving state at every coordinate; and at every coordinate 1 <= \|S fibre(own)\| <= \|A fibre(own)\| (G lies in its own conditional fibres). Also, at every coordinate, the conditional fibre of the barrier code at own has at most F+1 elements (largest barrier-state fibre at G's record). | yes | G03 (~ sub-object: qualitative), G01, G04, D02, I02, F06 (~) | witness, bound | unconsumed within [172a] (terminal residual) |
| 121 | `blockedFailureSlack` | 8601 | At the first failing coordinate c (rank k): F_c*A_k < W_c*A_{k+1}, A_{k+1} <= A_k, 1 <= \|B(P0)\| <= A_{k+1}, and F_c < W_c; all earlier coordinates pass the aggregate test. | yes | G01, G03, G05, H09, D06 (~) | bound, obstruction | unconsumed within [172a] (terminal residual) |
| 122 | `blockedPrefixCompression` | 8602 | At every coordinate all of whose predecessors pass the aggregate test: \|B(P0)\| * prod_{pred} W <= \|A-class\| * prod_{pred} F (the exposure counting of lem:blocked-graphs-compress on the passing prefix). | yes | G01, G03, G05, H09 | bound | unconsumed within [172a] (terminal residual) |
| 123 | `blockedFailingSetCarries` | 8603 | With Phi the set of coordinates whose aggregate test fails: \|B(P0)\| * 2^(windowPackageBits*\|P0\|) * prod_Phi F <= \|A-class\| * prod_Phi W, so the package saving over the class bound is carried by Phi. | yes | G05, G03, G01, G09, H05, H09, I03 | bound | unconsumed within [172a] (terminal residual) |
| 124 | `blockedOverlapSupport` | 8604 | For G's own skeleton and every coordinate (window, scale 2^j, row): the canonical completion support has at most 2^j + 1 vertices; if present it is the support of a closed non-cycle walk of length 2^j in G through a root-window vertex; and the union of the supports over the overlap component of the coordinate is connected in G. | yes | D05, D06 (~), B08, B01, C03, C01, C13 (~) | bound, decomposition, exclusion | unconsumed within [172a] (terminal residual) |
| 125 | `denseDeficiencyAtOrAbove` | 231 | ARM A. Not(DenseDeficiencyBelow): discharge*(delta*order*p + T(n)) >= discharge*2(order-1)p + (n - order*p), i.e. tau(theta) >= 1/4 up to T(n). | yes | H01, G09, H09, G08, I03, A01 | bound | routing at [160]; selects the dense hot/cold pass [162] |
| 126 | `denseDeficiencyBelow` | 230 | ARM B. discharge*(delta*order*p + T(n)) < discharge*2(order-1)p + (n - order*p), i.e. tau(theta) < 1/4 up to T(n) (the strict cap [56] hands to [57]-[62]). | yes | H01, G09, H09, G08, A13, I03, A01 | bound | routing at [160]; with 127 selects the delicate interval 3/13 <= tau < 1/4 |
| 127 | `route8RateFails` | 265 | ARM B. Not Rate: (delta*s + 1)*e(R,W) + delta*slack >= delta*\|R\| with slack = bridgeMass*discharge*T(n), i.e. the private-carrier rate tau < 3/13 fails. | yes | H09, H05 | bound | routing at [160] (rate reading fails) |
## Gaps ranked (joint check, gaps and `~`)

Ranking = number of existing Table-2 facts that would be combined with the coordinate once measured. Coordinates that are `gap`: G06, H04. The rest of the list is `~`.

1. **G06 (gap): injective reconstruction from local data (barrier code on B(P0))** (17 facts)
   - Why present at G: `blockedBarrierCode` is defined on B(P0) and G lies in it (118, 120); the encoding is (outside edge set, Option-valued states in `blockedEncodingRank` order). The reached class `A_k` (119) is defined by agreement with a member's code on the first k coordinates, so the multiplicity of the code is exactly what relates A_k to |B(P0)| and to the outside-record count. No fact states injectivity or a multiplicity.
   - Missing observable and certificate: multiplicity of `blockedBarrierCode` on B(P0) (injectivity, or the exact fibre over G's code word) and the number of admissible outside edge sets given the window edges. Certificate: injection / identity, giving `|B(P0)| <=` number of code words.
   - Technique: T15 (injection / reconstruction), T12.
   - Combines with: 14, 15, 37, 38, 65, 66, 67, 68, 69, 70, 118, 119, 120, 122, 123, 125, 126.

2. **D06 (`~`): minimal connected overlap obstruction at the failing coordinate** (14 facts)
   - Why present at G: the failing coordinate exists (121) and its overlap support is a connected subset of G (124); nothing says the failure lives on it or on a sub-family.
   - Missing observable and certificate: minimal connected sub-family of the overlap component of the failing coordinate together with the F and W carriers charged to it. Certificate: obstruction / decomposition.
   - Technique: T10 (uncrossing, minimal obstruction), T12.
   - Combines with: 14, 22, 38, 46, 47, 48, 69, 77, 79, 102, 118, 119, 121, 124.


3. **H04 (gap, arm B): feasibility of the local discharge on R (with H02/H03 and H06/H07)** (13 facts)
   - Why present at G: arm B is the strict cap `K .denseDeficiencyBelow` that hands R to `prop:negative-net-charge` ([57]-[62]); with `route8RateFails` the residual sits in 3/13 <= tau < 1/4. Suppliers (stubs 81, wedges 82, window cut 24, carriers 25) and deficits (23) are certified, but no transfer scheme, no negative piece (88 is conditional), no private-carrier assignment (127 is the negation of Rate).
   - Missing observable and certificate: integral transfer / flow from suppliers to the deficits of G[R], net charge of R and of a connected piece, private-carrier census at P0. Certificate: decomposition (flow) with the feasibility inequality.
   - Technique: T13, T14, T16.
   - Combines with: 23, 24, 25, 42, 45, 51, 80, 81, 82, 87, 88, 126, 127.

5. **F06 (`~`): cancellation and repair structure (composite (a,b,a+b) legs)** (10 facts)
   - Why present at G: `IsBlockedSurvivingState` composes Safe(a), Safe(b), Safe(a+b) on three labels at every G window / scale / row; 120 certifies survival at every coordinate but `none` also survives.
   - Missing observable and certificate: composition table of the leg responses realized at G's windows and its cancellations. Certificate: identity / decomposition.
   - Technique: T05, T11.
   - Combines with: 13, 15, 37, 38, 47, 48, 65, 66, 118, 120.

6. **C13 (`~`): joint realizability of the barrier legs (completion present or absent) at G's windows** (9 facts): observable: for each (window, scale, row) whether G realizes both legs simultaneously and simply; certificate witness / exclusion; T08, T17; combines with 19, 37, 38, 46, 47, 48, 65, 118, 124.
7. **H06/H07 (`~`, arm B): private-carrier assignment and flow-cut support of e(R,W)** (9 facts): `route8RateFails` is only `not Rate`; observable: integral assignment of the boundary incidences of R to entries / private carriers; certificate decomposition; T14, T15; combines with 23, 24, 25, 51, 77, 80, 81, 90, 127.
8. **A07 / E08 / H10 (`~`): degeneracy and unit peel of R** (7 facts): fact 79 empties the 3-core of R; observable: degeneracy and peeling order of G[R], one-unit peel against def+(R); certificate decomposition; T04, T19; combines with 14, 79, 82, 88, 116, 125, 126.
9. **H02 / H03 (`~`): net charge of R and connected negative piece** (5 facts): observable: net charge of R and of a canonical piece; certificate bound / witness; T13, T16; combines with 23, 81, 82, 88, 126.
10. **A12, B04, C06, C07, D04, D09, F04, F08 (each `~`)**: unranked tail, each combines with 2-4 facts (see Table 1 'Missing accounting'); union: 8, 49, 32, 19, 90, 29, 27, 43, 11, 91, 116, 85, 93, 110.

### Gaps relevant to the deficiency / rate split ([160])

- Facts 125 (arm A), 126 and 127 (arm B) are inequalities in (n, |P0|, |R|, e(R,W), T(n)). They meet the fibre failure only through |P0|: it enters `2^(windowPackageBits*|P0|)` (68), which fact 123 puts on the left of the failing-set inequality against `skeletonBudget`-side counts. The missing bridge is G06 (the outside-record count), which turns 123 into a bound on |P0| that arms A and B can be tested against.
- Arm A (125) is only the negation of the strict cap; its margin is not measured. Arm B (126 + 127): H04, H02/H03 and H06/H07 above are the unmeasured structure.
- The split gives no evidence about which coordinate fails; the failing coordinate (121) is independent of tau in the ledger.

## Non-G facts

No fact is nonG, wholly or partly, and no Table 1 coordinate is nonG. Fact 119 (no member quantifier after the final commit) and facts 120-124 are stated at G's own skeleton or as numerical facts about G's class.


Checked and kept as G-only: 1, 9, 10, 97, 111 (readings in G - Z), 22 (canonical connected support of two declared coordinates), 11, 12, 98, 116 (swaps glued into G's own rest), 106, 107, 109-112 (germs of G's family), 62, 66 (quotients declared on G), 67 (class count in G's n, m), 118 (G's own skeleton; class cardinality is a parameter count), 120-124 (constructions at `own` = G's skeleton or numerical facts about G's class).

## Cross-check results

1. **Every coordinate code in Table 2 is `x` or `~` in Table 1 and lists that fact: PASS** (re-checked programmatically over all 127 rows after the G04 edit; 0 offenders).
2. **Every `x` or `~` in Table 1 cites at least one Table-2 row, and each cited row lists the code: PASS** (66 x, 18 ~; 0 empty, 0 mismatches).
3. **Every Table-2 row accounts for at least one coordinate or is bookkeeping: PASS.** All 127 rows carry >= 1 code; none is labelled bookkeeping (row 2 partly, but keeps C04, A04, I06). Row 119 keeps G01, G03, G05, H09.
4. **No fact counted twice for the same demand in different currencies: PASS**, with the same-currency overlaps to be counted once: def+(R) <= e(R,W) <= capacity is published by 23 and 24, again in 80, 81, 82, 87; 75 = 74 scaled; 108 contains 95; 125 and 126 are complementary arms. New overlaps: 121 (failure slack) repeats the failing inequality of 119 and adds monotonicity and F < W; 122 and 123 are the same exposure counting on the passing prefix and on the failing set (complementary sets, one product each); 120 and 124 are at `own` = G's skeleton and measure different objects (fibres vs supports). None is a cross-currency double count.

## Outside the register

- The encoding order `blockedEncodingRank` (scale major, window, barrier row minor), the reached-class counts `A_k = blockedReachedCount k`, and the dyadic scale family `separatedScaleCount` index the G03/G05/G06 accounting but fit no separate coordinate. Nothing was forced into a row.
