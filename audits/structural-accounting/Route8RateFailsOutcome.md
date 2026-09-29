# Structural accounting: `Route8RateFailsOutcome`

Residual: node `[187]` (private-carrier rate failure, thm:main (vi), tex 369-378). Worktree `/home/guillem/hs-wt-SR8R`.

**Defining failure.** At G's `canonicalWindowPacking` P0 (p = |P0|, R = `remainderSupport`), the private-carrier rate `Graph.Route8Census.Rate` fails (`K .route8RateFails`, fact #92):

`(threshold*discharge + 1)*|supply| + threshold*slack < threshold*|R|` is false, with `supply = Route8.cutEdges R` (so `|supply| = |dR| = boundaryIncidence R = e(R,W)`), `slack = bridgeMassFactor*discharge*surplusThreshold(n)`. At the registered delta=3, s=4 this reads `13*|dR| + 3*slack >= 3*|R|`.

Facts: **92 on the generic residual** (the `abbrev` in `Residuals.lean` conjoins 92 `Holds` keys, not 66 or the 71 of its docstring; the count is checked against the fact-key extraction of the template script) plus the **union of 18 extra facts** of the 11 subtype paths (`Route8RateFailsOutcome_*`, 5-8 extras each; listed separately in section 'Subtype extras'). Table 1 marks the generic residual; the effect of the extras is the section 'Table 1 delta from the extras'.

Status counts (Table 1, 88 coordinates, generic residual): `x` 45, `~` 28, `gap` 7, `n/a` 3, `nonG` 5.

Reading convention: 'Consumed by' in Table 2 records statement-level co-occurrence (same inequality, identity or quantity: |R|, |dR|, slack, p, n, sigma), not a trace of Lean proof terms; the Rate-facing quantity a fact feeds is named explicitly. The quantities: **|R|** = `(remainderSupport P0).card` (= n - 13p when P0 is a valid packing), **|dR|** = `boundaryIncidence R` = `|supply|`, **slack** = `bridgeMassFactor*dischargeScale*surplusThreshold n`.

Derived consequence of the stated facts (a proved inequality among G's quantities, not a picture of G): from #92 and the cap #82 (`|dR| <= 15p + sigma_W`), `3|R| <= 13|dR| + 3 slack <= 195p + 13 sigma_W + 3 slack`; from #91 (for n large enough for the net cap) `|R| > 60p + 4*spineScale*ceilSqrt n`. So at G the failing rate confines |R| to `60p < |R| <= 65p + (13/3)sigma_W + slack`, and `|dR| >= (3|R| - 3 slack)/13 > (180p - 3 slack)/13`, i.e. the cut is within a constant factor of the whole stub capacity `15p + sigma_W` of #26/#82. No fact measures |R| or |dR| more finely inside this window.

## Table 1 - Structural coordinates

Statuses: `x` accounted, `~` partial, `gap` present at G and unaccounted, `n/a` absent, `nonG` only non-G facts. 'Accounting facts' lists Table-2 fact numbers (#n) whose G-only part gives the certificate; for `nonG` rows the non-G facts are listed with prefix `nonG:`.

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. | `x` | #17, #53 | bound/identity on n | T01 T13 | - |
| A02 | Size and edge density | Number of edges and density relative to order. | `x` | #8, #51 | bound on int(S), identity for e(R) | T01 T13 | - |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. | `x` | #2, #7, #43, #53, #55, #62 | classification (hub/cubic classes, dart identity) | T01 T15 | - |
| A04 | Minimum and maximum degree | Extremal vertex degrees. | `~` | #3 | bound (minimum degree >= 3, fact 3) | T01 | Maximum degree of G is never certified: no fact states Delta(G) <= 3 + sigma <= 3 + T(n) (the hubs' individual degrees enter only through sigma, #32/#63). |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. | `x` | #32, #43, #44, #53, #54, #56, #58, #59, #60, #62, #63, #65, #66, #75, #79 | identity + bound (sigma as hub excess, dart identity) | T01 T13 | - |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. | `x` | #6, #7, #32, #41, #42, #56, #58, #59, #63 | classification + bound (independent hubs, \|H\| <= sigma, link degeneracy) | T01 T07 | - |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. | `x` | #5, #42, #46, #48 | bound (degeneracy of R and of link graphs; G equals its own 3-core) | T04 T19 | - |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. | `n/a` | excluded by #3 | exclusion | T04 | Absent: fact 3 (delta(G) >= 3) excludes degree-two vertices, hence every degree-two chain and subdivision. |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. | `x` | #29, #32, #59, #61, #84, #89 | bound (non-adjacent pair counts, W2 vs deficiency) | T01 T12 | - |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. | `x` | #25, #26, #45, #47, #51, #52, #72, #82, #92 | bound (e(R,W) between stub capacity and deficit/closed-class lower bounds) | T14 T13 | - |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. | `x` | #25, #39, #50, #77, #82, #83, #84, #91 | bound (def+(R) <= e(R,W) <= 15p + sigma_W; stub excess per window) | T13 T14 | - |
| A12 | Cycle rank | Dimension of the binary cycle space. | `~` | #8 | bound (2*beta(G) >= n+2, fact 8), global only | T01 | Cycle rank of the pieces is never measured: beta(G[R]) and beta of the cut are not tied to e(R), \|R\| although fact 52 gives 2e(R) exactly; missing observable: beta(G[R]) = e(R) - \|R\| + c(R), certificate = identity, technique T08/T01. |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. | `x` | #51, #52 | bound (slack of every proper S, slack(R) identity) | T01 T13 | - |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. | `x` | #56, #58, #63, #65 | bound (\|H\| <= sigma <= T(n); 5\|H\|+sigma <= 2n) | T01 T13 | - |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. | `~` | #5, #48, #49 | bound on sub-objects (bags of R minus hubs <= 6142, window-free connected sets <= 1+2047(3+sigma_K); G connected) | T04 | The components of G[R] themselves (the index set of the Rate's entries) are never named: no fact gives the decomposition R = union of components C with \|C\| and \|dC\| per component. |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. | `x` | #24, #51 | exclusion + bound (bridgeless; >= 2 edges leave every proper nonempty set) | T04 T01 | - |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. | `~` | #28, #33, #34, #35 | classification (cut-vertex blocks, single-vertex boundaries) | T04 T08 | Proved at cut vertices of G and pieces with one boundary vertex, never combined with the cut of R or with \|dR\|; missing: block-cut structure of G[R] joined to W. |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. | `~` | #20, #51 | witness (two disjoint forced paths; bridgeless) | T08 T14 | Existence of two paths only; no quantity: maximum number of internally disjoint paths between R's terminals (Menger value) is not certified. |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. | `x` | #25, #26, #28, #45, #82 | identity (marked boundary of R with degrees, cut edges, window stubs) | T05 T14 | - |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. | `~` | #9 | exclusion (boundary-degree profile separates readings, fact 9) | T05 | Certified for readings at supports Z of G, not for R: the boundaried type of (R, dR) (ordered terminals, degrees, incidence) is not recorded. |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. | `~` | #10 | exclusion (G's own rest only) | T05 T10 | Only the G-restricted form (fact 10): no context of G separates two readings. The all-context form is nonG (facts 11-12 touch B07-style equivalence only through replacement pieces); the G-constructed reformulation is already fact 10, but it is never combined with the R cut. |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. | `~` | #23 | decomposition (minimum connected support of a defect witness; bags of R) | T04 T10 | Witness locality is certified only for sparse target-defect witnesses (fact 23); the support of the Rate's failing entries is not localized. |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. | `x` | #25, #26, #45, #82, #83, #92 | bound (deficit demand vs stub supply at the cut of R) | T14 T13 | - |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. | `~` | #19, #20, #22, #35, #49, #61 | witness (forced simple paths with accepted closing length; short induced walks) | T08 | Attainable-length sets are certified only as existence of one path per configuration; the set of simple path lengths inside G[R] between cut vertices is never bounded. |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. | `x` | #4, #22, #24 | exclusion + witness (return-length avoidance at every dart; bridgeless returns) | T08 T01 | - |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. | `x` | #1, #16, #30, #34, #36 | exclusion (no accepted cycle in G; star/meeting/return constraints; cycle counts) | T08 T12 | - |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. | `x` | #2, #4, #30, #31, #35, #57 | classification (dyadic accepted set, parity, residues mod 4) | T09 | - |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. | `x` | #20, #30, #31, #37 | exclusion (h'-free internally disjoint paths; star/meeting/fan constraints) | T08 T07 | - |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. | `~` | #35 | classification (blocks with paths at cut vertices, chords/outside returns of long window-free paths) | T08 T04 | Ears are certified only at cut vertices (fact 35) and for window-free paths (fact 49); the ear structure of G[R] over G[W] is not measured. |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. | `gap` | none | - | T08 T11 | Present at G: beta(G) >= n/2+1 (fact 8) and cycles are counted at every vertex (facts 34, 36), so the binary cycle space is nontrivial; no fact measures cycle-space interaction (symmetric differences of cycles through cut edges). Missing: binary incidence vectors of the cycles through dR and a dependence bound; certificate: rank/independence bound. |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. | `x` | #13, #14, #48, #49, #81 | witness + exclusion (induced P13 present; R induced-P13-free) | T06 T07 | - |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. | `x` | #13, #14, #17, #70 | identity + bound (maximum maximal packing, 13p <= n, density cap) | T06 T13 | - |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. | `x` | #42, #46, #48, #49, #81 | bound + exclusion (R has no window, 12-degenerate, bags, hub-linked structure) | T06 T04 | - |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. | `~` | #38 | classification (chain 3,3,3 at a vertex; cold stub counts) | T07 T09 | Serial corridor increments are certified only locally at a vertex (fact 38); corridor bases and increments along R's cut are not tabulated on this ledger. |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. | `x` | #39, #40, #49, #50 | identity + exclusion (positions/stubs, attachment gaps, <= 7 neighbours on P13) | T07 | - |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. | `x` | #20, #30, #31, #37, #38 | exclusion (joint disjointness + endpoint compatibility of two paths with dyadic closing length) | T08 T07 | - |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. | `x` | #39, #40, #50, #76, #77, #78 | identity + bound (window position stubs, attachment rules, cold window stubs) | T07 | - |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. | `~` | #39 | identity (window position types; attachment labels of P0) | T07 T17 | Local types are certified only at windows of P0. The radius-2 rooted local type of the subcubic remainder is decided only in the subtype arms (extras X9-X13). |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. | `x` | #20, #22, #29, #30, #31, #37, #38, #41, #42, #43, #46, #54, #55, #61 | classification + bound (centre neighbourhoods, fans, hub links) | T07 | - |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. | `~` | #29 | classification (G[N(h)] is a matching) | T07 T14 | The auxiliary incidence graph of demands (cut stubs of R) against resources (windows) is not built; only the matching property of neighbourhoods is certified. |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. | `x` | #45, #46, #78, #79 | decomposition + injection (disjoint closed classes, unique window per stub, overlap bound) | T15 T07 | - |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. | `~` | #23 | decomposition (minimum connected support of a defect witness) | T10 T07 | Minimality is certified for witness supports only; a smallest connected family of private carriers where the Rate fails is not named. |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. | `gap` | none | - | T16 | P0 = canonicalWindowPacking is a canonical selection among maximum packings (fact 14 proves maximum and maximal, not unique). No fact records that \|R\|, \|dR\| and the Rate are invariant under the choice, nor the multiplicity of maximum packings. Missing: equal-response classification of maximum packings; certificate: identity or bound on \|R\|, \|dR\| across the class. |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. | `x` | #14, #23, #70 | decomposition (canonical packing, canonical support, hot/cold partition) | T16 T06 | - |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. | `~` | #10 | exclusion (G's own actualGlue never closes a dyadic cycle) | T05 T17 | Reconstruction of G from its boundaried pieces (R with dR, W) as a uniqueness/compatibility statement is not recorded; the all-context gluing forms (facts 11-12) are nonG. |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. | `x` | #48, #49, #50 | bound (bounded exceptional configurations: bags 6142, window-free sets, 7 neighbours) | T07 T17 | - |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. | `nonG` | nonG: #1 | - | T02 | Only fact 1 touches it, through 'every strictly smaller baseline object' (other graphs). G-constructed replacement: proper subgraphs of G fail the baseline (fact 5) plus no accepted cycle in G (fact 1, first conjunct). |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. | `x` | #5, #55, #81 | exclusion (no proper subgraph at the baseline; every proper set spans a vertex of internal degree <= 2) | T02 T04 | - |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. | `x` | #19, #20, #22, #24 | witness (effect of deleting each pair of edges; bridgeless) | T03 T08 | - |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. | `nonG` | nonG: #18 | - | T03 | Facts 18 and 21 only, through the suppressed graph and G join M_h. G-constructed replacement: the walk in G obtained by un-suppressing tight vertices with its chord count, and the G-local switch facts 19, 20, 22 as the certificate at G itself. |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. | `nonG` | nonG: #11, #12 | - | T03 T05 | Facts 11 and 12 only, through replacement pieces X' and glue(X', G-Z). G-constructed replacement: the swap of G at Z (Z re-glued into G's own rest, cf. facts 10 and 16) and its canonical degree deficit at dZ, measured against def+(R). |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. | `x` | #9, #10, #64, #68 | exclusion (different profile not identified; identified means equal response; label injectivity) | T05 T11 | - |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. | `gap` | none | - | T16 T19 | Present at G: equal-size choices exist in canonicalWindowPacking and CanonicalSupport.select? (facts 14, 23). No fact gives a secondary order on neutral changes of P0 (windows swapped for equal-size ones) with a monotone quantity for \|R\|, \|dR\|. Missing: neutral-move descent order; certificate: strict decrease of a secondary invariant. |
| E08 | Peelability | A removable unit preserving the residual invariant. | `gap` | none | - | T19 T03 | Present at G: every cubic vertex has a cubic neighbour (fact 55) and windows are removable units of P0 (fact 14); no fact gives a removable unit that preserves the residual invariant (Rate failure). Missing: peel step from P0 to a smaller packing/remainder with the invariant 13\|dR\|+3slack >= 3\|R\| tracked; certificate: replacement/descent. |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. | `x` | #10, #16, #23, #66 | exclusion (no target-defect witness; G survives sparse exits) | T10 T05 | - |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. | `x` | #84, #85, #86 | bound + identity (W2(R) supply of wedge tests, exact response profile) | T11 T01 | - |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. | `x` | #64, #85, #88, #89 | bound + identity (r_Omega(R) = W2(R); label injectivity) | T11 | - |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. | `x` | #87, #88 | classification (dependence exists for outside tests; absent when full rank) | T11 T10 | - |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. | `~` | #87 | classification (determiners B subset surviving family) | T11 | The geometric support (vertices, edges, contexts) of a target dependence is not localized: fact 87 gives determiner sets, not their support in R. |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. | `x` | #68 | identity (window packages disjoint; label injective) | T11 T15 | - |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. | `n/a` | excluded by #88 | exclusion | T11 | Absent for the wedge tests of R: fact 88 (r_Omega(R) = W2(R)) with fact 87 leaves no dependence to cancel, so no repair network on that family; window packages are disjoint and injective (fact 68). |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. | `x` | #64, #87, #88 | classification (full rank versus localized dependence) | T11 T10 | - |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. | `~` | #35 | classification (residue 3 mod 4 at cut vertices) | T09 | Periodicity of a response family under additive increments is certified only at cut-vertex blocks (fact 35); the repetitive rooted-type arm is decided only in extras X10. |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. | `nonG` | nonG: #69, #80 | - | T12 | Only fact 69 (and the second conjunct of fact 80) counts the labelled skeleton class, a class of graphs other than G. G-constructed replacement: the number of skeleton codes of G's own canonical decomposition (packing + remainder), i.e. the range of G's own state map. |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. | `~` | #40, #68, #86 | identity (attachment labels of P0 windows are legal) | T12 T17 | The cardinality of legal states (399 labels, fact 15) and the barrier row (fact 67) are nonG; the census of labels realized on G's own windows is not recorded. |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. | `x` | #68, #71, #73, #80, #90 | bound (bits per window, rate*scales*p vs budget) | T12 | - |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. | `gap` | none | - | T12 T16 | Present at G: fact 88 (full rank) makes the type coordinate of the subcubic remainder decidable; the dominant/repetitive fibre of radius-2 rooted types of G[R] exists as canonicalDominantRootedType?. No generic fact measures it; it is decided only in the subtype arms (extras X9-X13). Missing: size of the dominant type fibre versus \|R\|; certificate: bound. |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. | `~` | #68, #90 | identity (window family additive: \|family\| = bits*p; joint demand) | T12 | Joint versus conditional-product count of window package and remainder is compared only in the high-entropy extras (X7, X8); the generic residual carries fact 90 as an undecided disjunction. |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. | `~` | #64, #68 | bound (label-injective quotient on G's coordinate families) | T12 T11 | Injective reconstruction from decomposition states to labelled graphs rests on the class count (fact 69, nonG); G-constructed: the injectivity of G's own code map on G. |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. | `x` | #27, #36, #43, #44, #47, #53, #62, #75, #76, #77, #78, #79 | identity + injection (carrier count 4n+2sigma, double counts of cold stubs/cycles) | T15 T12 | - |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. | `~` | #2, #60, #65, #72, #75, #79, #80, #83, #91 | bound (T(n) exact, explicit thresholds; net-cap hypothesis) | T12 | Small orders are not resolved on the generic ledger: fact 91 is conditional on 'sufficiently large', and the finite-order arms n < N0 appear only in extras X16, X18. |
| G09 | Density of a packed pattern | Packing number normalized by graph order. | `x` | #14, #17, #52, #54, #71, #73, #74, #80 | bound (13p <= n, density cap on p) | T13 T12 | - |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. | `x` | #25, #26, #44, #47, #51, #52, #53, #54, #62, #72, #82, #83, #84, #89, #91, #92 | identity + bound (deficiency/surplus balance at R) | T13 T01 | - |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. | `x` | #52, #53 | identity (sum over windows and over components) | T13 | - |
| H03 | Connected negative support | A connected region with negative charge. | `gap` | none | - | T13 T10 | Present at G: Rate failure 13\|dR\|+3slack >= 3\|R\| is an aggregate statement over components of R (Rate = entries per component summed); no fact exhibits a connected region C of R with private charge 3\|C\| - 13\|dC\| <= its share of slack. Missing: connected negative support of the charge 3\|X\| - 13\|dX\|; certificate: witness component. |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. | `~` | #91, #92 | obstruction (discharge scale s=4 per supply edge in the Rate; net-cap discharge) | T13 | The transfer rule from entries to supply edges (entriesOfComponents, core in supply) is not on this ledger: only its total (fact 92) and the scale (fact 2, 91). |
| H05 | Load and saturation | Load compared with certified capacity. | `x` | #26, #27, #72, #82, #83, #91, #92 | bound (stub capacity vs deficiency load; carriers vs supply) | T14 T13 | - |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. | `~` | #25, #45 | bound + injection (def+(R) <= e(R,W); closed classes inject into R-W edges) | T14 T15 | The assignment of private essential carriers to cut edges of R with multiplicity <= s = 4 is not certified: fact 27 counts carriers of G (4n+2sigma), not those charged to dR. |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. | `~` | #45 | bound (closed classes <= e(R,W)) | T14 | A flow from window stub capacity (15p + sigma_W) to the deficits of R is not built; only cut-type counting bounds (facts 25, 26, 45). |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. | `~` | #32, #44, #47, #52, #53, #56, #58, #59, #60, #65, #74, #75, #76, #79 | bound (sigma-masses of cold windows, hubs, surplus) | T13 T12 | The mass that defines the Rate's slack, the Type B bridge mass F*s*T(n), is not bounded by any fact on this ledger: facts 65, 63, 75, 79 bound sigma-type masses, but the bridge family's mass is presented only as a constant (fact 2). |
| H09 | Competition between two budgets | Required tests compared with available states or supply. | `x` | #68, #71, #73, #74, #80, #89, #90 | bound (window package vs skeleton budget; cold mass; density cap) | T12 T13 | - |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. | `gap` | none | - | T19 | Present at G: n is a well-founded measure and windows/hubs are countable units. No fact provides one-unit peel steps on a demand measure for the Rate (13\|dR\|+3slack vs 3\|R\|). Missing: well-founded demand measure with a peel step; certificate: descent. |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. | `~` | #48, #49, #50 | bound (bags <= 6142, window-free sets, <= 7 neighbours) | T17 T07 | Bounded sizes are certified but no explicit finite list of configurations is given. |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. | `~` | #14, #23, #70 | decomposition (canonical packing and canonical support) | T16 T17 | Canonical choices are fixed; isomorphism classes/orbit representatives of the remainder types are not produced on the generic ledger. |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. | `x` | #40, #68 | identity (length equalities 2^k, label collisions) | T17 T11 | - |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. | `~` | #91 | bound (net-cap hypothesis) | T17 | Small-order residual n < N0 is carried only by the extras X16, X18; the generic ledger has the implication of fact 91 without the small arm. |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. | `nonG` | nonG: #15, #67 | - | T17 | Facts 15 and 67 (label census; barrier table row) are checked computations about the label alphabet, not about G. G-constructed replacement: a verified census of the labels realized by G's own windows with generator and verifier. |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. | `n/a` | all 92 (checked) | exclusion | T18 | No statement among the 92 (or the 18 extras) takes an imported classification theorem as hypothesis; every Holds proposition is an in-Lean definition. |

## Table 2 - Facts of the residual -> structural coordinates

Coordinates prefixed `!` are touched only through an object outside G and are not accounted (they appear as `nonG` rows in Table 1).

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 | G has no cycle of accepted (power-of-two) length; and every strictly smaller baseline object has one (SelectionMinimality) | mixed: no-cycle conjunct is G; minimality quantifies over strictly smaller baseline objects (other graphs) | C03 !E01 | exclusion | every fact; entry of ledger |
| 2 | `cubicBaseline` | 221 | Presentation laws of G: delta=3, s=4, 2 not accepted, accepted lengths exactly dyadic, Type B fan/deficit/bridge-mass slack identities, sparse-surplus identities, HSS closure law at G and its induced subgraphs, scale family, net-cap slack, barrier-table label semantics | yes (constants and laws stated at G; the barrier-table semantics is presentation data) | C04 A03 G08 | identity | Rate constants (delta*s+1=13, bridgeMassFactor); #82-#91; #71-#80 |
| 3 | `minDegreeBaseline` | 2850 | Every vertex of G has degree >= 3 | yes | A04 | bound | all degree facts, #5, #51, #55, #62 |
| 4 | `returnAvoidance` | 1 | At every dart of G the return-length set is disjoint from the shifted accepted set | yes | C02 C04 | exclusion | #19-#22, #24, #30, #31 |
| 5 | `noProperBaseline` | 2 | No proper subgraph of G has minimum degree >= 3; G is connected | yes | E02 B01 A07 | exclusion | #51, #53, #55 (cubic neighbour), #47-#48 |
| 6 | `slackIndependent` | 4 | Vertices of degree > 3 are pairwise non-adjacent (hubs H independent) | yes | A06 | classification | #42-#47, #53, #56-#60, #63 |
| 7 | `tightEndpoint` | 3 | Every dart of G has an endpoint of degree exactly 3 | yes | A06 A03 | classification | #41, #43, #62 |
| 8 | `cycleRankConstraint` | 425 | n + 2 <= 2(m + 1 - n): cycle rank beta(G) >= n/2 + 1 | yes | A12 A02 | bound | unconsumed by the Rate currencies (global only) |
| 9 | `degreeProfileFibres` | 2300 | For every region X, every admissible rank quotient of X's coordinates on G and every two readings of G at its support Z: different boundary-degree profile implies not identified | yes (readings and quotients of G at supports Z subset G) | B06 E06 | exclusion | #10, #64, #68 |
| 10 | `targetCompleteContextUniversality` | 2301 | Identified readings have equal profile and equal power-of-two-cycle response in G's own rest G-Z (actualGlue); no reading at any support closes a dyadic cycle in G-Z | yes (G-only restatement: actualGlue is G's own piece glued to G's own rest) | B07 E06 E09 D09 | exclusion | #9, #16, #23 |
| 11 | `replacementExclusion` | 223 | No proper connected support Z of G has a replacement X' (boundaried piece with G's boundary-degree profile) such that glue(X', G-Z) meets the baseline, is smaller than G and has no dyadic cycle | no: replacement piece X' and the glued graph glue(X', G-Z) are graphs other than G | !E05 | exclusion | #12; entry-level closure of the canonical-swap branches |
| 12 | `uncompressible` | 5 | No proper support Z of G has a strictly smaller target-complete compression X' in G's rest (CompressibleSupport) | no: compressed representative X' glued to G-Z is a graph other than G | !E05 | exclusion | derived from #11 |
| 13 | `windowPresent` | 608 | G has an induced path on 13 vertices | yes | C08 C09 | witness | #14, #17, #39, #50 |
| 14 | `maximalPacking` | 6 | P0 = canonicalWindowPacking is a nonempty maximum, maximal vertex-disjoint family of induced 13-windows; every induced window meets a member | yes | C09 C08 D08 G09 I02 | decomposition | every window/remainder fact; p = \|P0\| in the Rate |
| 15 | `localAlgebra` | 7 | The window label alphabet has 399 legal labels and size distribution begin [13,60,122,122,63,17,2] | no: statement about the label alphabet of a fixed window order, carries no guard over G's windows | !G02 !I05 | classification | #40 (legal-label rule), #67 |
| 16 | `everyWitnessSpectrumSplit` | 6702 | For every sparse target-defect witness w on G and every pair support X of w, actualGlue(G, w.support, X) has no accepted-length cycle | yes (actualGlue is G's own rest glued to a reading of G) | E09 C03 | exclusion | #10, #23 |
| 17 | `packingOrderBound` | 6611 | 13*p <= n | yes | G09 A01 C09 | bound | fixes \|R\| = n - 13p; #80, #91, #E3/E4 |
| 18 | `noSuppressionChordViolation` | 6620 | For every compatible tight-vertex-suppression family tvs and every cycle certificate of the suppressed graph, walk length + used chords is not accepted | no: cycle certificates live on the suppressed graph tvs.suppressed, not on G | !E04 !C03 | exclusion | (none on this ledger) |
| 19 | `twoSwitchForcedPath` | 6800 | For edges u1v1, u2v2 of G (distinct ends, u1 !~ u2, deg v1, v2 >= 4), G-{u1v1,u2v2} has a simple u1-u2 path p with \|p\|+1 accepted | yes (G minus two edges) | C01 E03 | witness | #22, #20 |
| 20 | `crossSwitchFamily` | 6802 | Cross-vertex switch family of G: forced simple paths u1 -> u in G-{u1v,uh'} with accepted closing length; two h'-free internally disjoint paths of length 2^j-1 into distinct neighbours of h' never coexist | yes (subgraphs of G) | C01 E03 C05 C13 D03 B04 | witness exclusion | #19, #22, #30 |
| 21 | `highCentreSplitForced` | 6801 | At every vertex h of degree > 3, the graph G join M_h (M_h = non-adjacent pairs of N(h)) has an accepted cycle avoiding h that uses an edge of M_h absent from G | no: the cycle lives on G join M_h, which has edges not in G | !D03 !C03 | witness | (none on this ledger) |
| 22 | `sameVertexSwitchForcedPath` | 6803 | Same-vertex switch: for non-adjacent neighbours u1,u2 of h (deg h >= 5), G-{hu1,hu2} has a simple u1-u2 path p with \|p\|+1 accepted, and either p avoids h and \|p\|+2 is not accepted or p splits into returns l1+l2=\|p\| with neither l_i+1 accepted | yes (G minus two edges) | C01 C02 D03 E03 | witness decomposition | #19, #20, #4 |
| 23 | `specWitnessStructure` | 6677 | For every sparse target-defect witness w with canonical support: support connected, contains the declared supports, minimum-size connected superset, and not w.Spec | yes (witness on G, canonical support of G) | B08 E09 D08 D06 I02 | decomposition | #16, #10 |
| 24 | `bridgeless` | 226 | Every edge of G lies on a cycle (HasReturn for every edge contraction) | yes | B02 C02 E03 | exclusion | #51, #4 |
| 25 | `remainderDeficiencyBelowCut` | 6663 | def+(R) <= e(R,W) = boundaryIncidence(R): positive degree deficiency of R below its cut | yes | A11 A10 B05 B09 H01 H06 | bound | #82, #83, #92 (\|dR\| = e(R,W)) |
| 26 | `windowCutCapacity` | 6664 | e(R,W) + 2*12*p <= 3*(13p) + sigma_W: window stub capacity of the cut | yes | A10 B05 B09 H05 H01 | bound | #82, #47, #92 (upper bound on \|dR\|) |
| 27 | `primitiveCarrierCount` | 6666 | \|primitiveCarrier(G)\| = 4n + 2*sigma (carrier count at the registered discharge scale s=4) | yes | G07 H05 | identity | #92 (carriers per supply edge); not restricted to R |
| 28 | `singleBoundaryShape` | 6627 | If S has cut boundary a single vertex b, then for z in S, z != b, b has exactly 2 neighbours in S and 2 outside S | yes | B03 B05 | classification | unconsumed by Rate (single-vertex boundaries of pieces) |
| 29 | `neighbourhoodPairCount` | 6900 | For every vertex h: G[N(h)] is a matching; N(h) has >= C(d,2)-floor(d/2) non-adjacent pairs; every neighbour has >= d-2 non-adjacent partners | yes | A09 D03 D04 | bound | #30, #31, #61 |
| 30 | `starCycleConstraint` | 6901 | Star constraint: two h-free paths x->y, x->z (y != z neighbours of h) meeting only at x have \|P\|+\|Q\|+2 != 2^k (k>=2) | yes | C03 C04 C05 C13 D03 | exclusion | #31, #37, #38 |
| 31 | `meetingCycleConstraint` | 6902 | Meeting constraint: two h-free paths x->y, x->z to distinct neighbours of h admit a meeting vertex t with \|P\|+\|Q\|+2 != 2^k+\|P1\|+\|Q1\| | yes | C04 C05 C13 D03 | exclusion | #30, #37 |
| 32 | `highDegreePairSum` | 6903 | sigma = sum over off-baseline vertices of (d-3); 5*sigma <= sum C(d,2); sigma^2+5*sigma*\|H\|+6\|H\|^2 <= 2\|H\| sum C(d,2); 2 sum C(d,2) <= 16 sigma^2; sigma = 0 or some h with sigma <= \|H\|(d_h-3) | yes | A05 A06 A09 H08 | identity bound | #56, #58, #59, #60, #65 |
| 33 | `vertexDeletionComponents` | 6904 | For every vertex h: G-h is connected, or deg h is even, deg h = 2*#blocks and each neighbour's component of G-h contains exactly 2 neighbours of h | yes | B03 | classification | #34, #35 |
| 34 | `cyclesThroughVertex` | 6905 | Cycles through h: C(d,2) if G-h connected; otherwise exactly d/2 closed pairs and >= d/2 cycles | yes | C03 B03 | bound | #36, #33 |
| 35 | `cutVertexBlockPaths` | 6906 | At a cut vertex h with G-h disconnected, each neighbour a has block {a,b}; a-b paths avoiding h have length + 2 != 2^k; returns transfer; 3 mod 4 length residue | yes | B03 C01 C04 C06 F08 | classification exclusion | #33, #34 |
| 36 | `cycleDoubleCount` | 6907 | 2 sum_{h in H} #cycles(h) <= n*#cycles(G), 2 sum L_h <= n*#cycles(G), #cycles(G) <= 2^m | yes | C03 G07 | bound | #34 |
| 37 | `threeRouteFan` | 7100 | Length-3 fan: at every h, two length-3 h-free paths from a to distinct neighbours b,c leave a through the same vertex and meet nowhere else | yes | D03 C05 C13 | classification | #30, #38 |
| 38 | `threeRouteChain` | 7101 | Chain 3,3,3: paths of length 3 in G-h joining neighbours a->b->c->d of h have their middle path through the inner vertices of the outer two | yes | D03 C11 C13 | classification | #37 |
| 39 | `windowPositionStubs` | 7102 | Every window of P0 has a placement; interior position i carries d(q_i)-2 external neighbours, an end position d-1 | yes (windows of P0 in G) | D01 D02 C12 A11 | identity | #26 (stub capacity), #50, #40, #82 |
| 40 | `windowAttachmentGap` | 7103 | Cross-gap and window attachment rules: outside attachment labels legal and C1-safe; two windows joined at (i,j),(i',j') have \|i-i'\|+2+\|j-j'\| not accepted; no ladder | yes | D01 C12 G02 I03 | exclusion | #39, #50, #26 |
| 41 | `portEndDegree` | 7233 | Every excess port d has degree exactly 3 at its far end | yes | A06 D03 | classification | #7, #42 |
| 42 | `hubLinkStructure` | 7217 | Hub-link structure in R: no long hub chains, no rainbow 5-path of links, link graph on S_R 18429-degenerate (sum <= 36858 h_R), strong link graph 3-degenerate, non-strong pair carries <= 3*6142 linked vertices | yes | D03 A07 C10 A06 | bound exclusion | #46, #47, #48 (all in h_R) |
| 43 | `hubClassCounts` | 7218 | Hub classes: \|A0\|+\|A1\|+\|A2\|=\|L\|; \|A1\|+2\|A2\|=3\|H\|+sigma; \|A2\|<=C(\|H\|,2); \|A2\|+n=\|A0\|+4\|H\|+sigma; \|U\|<=3\|A0\|; d_h <= (\|H\|-1)+\|N(h) cap U\|+\|N(h) cap (A1\U)\| | yes | A03 A05 G07 D03 | identity bound | #44, #47, #62 |
| 44 | `slotRelation` | 7219 | Slot relation: \|A1\| <= 3\|A0\|+\|A2\|+2(\|H\|^2-\|H\|)+2C(\|H\|,2); 4sigma+21\|H\| <= 3n+6\|H\|^2; 4sigma+18\|H\| <= 3n+6\|A2\|+3\|H\|^2; <=2 matched-link and 2 link-link vertices per hub pair | yes | H01 A05 H08 G07 | bound | #43, #47, #56 |
| 45 | `closedClasses` | 7220 | Closed bag-link classes of R: edges leaving a closure end in W; disjoint classes have disjoint closures; a nonempty class reaches W along an R-W edge; number of pairwise disjoint nonempty closed classes <= e(R,W) | yes | A10 B05 B09 D05 H06 H07 | bound decomposition | #25, #47, #82 (lower-bounds \|dR\|) |
| 46 | `hubTwoHopLinks` | 7221 | Two-hop links between hubs of R: no 7 hubs consecutively joined by common neighbours; common-neighbour graph 25-degenerate (sum <= 50 h_R); per-centre 12286-degenerate, sum <= 24572\|S\| | yes | D03 D05 A07 C10 | bound exclusion | #42, #47, #48 |
| 47 | `slotLinear` | 7222 | Slot classes are linear in h_R: \|B_W\| <= 13p + 4e(R,W); \|A2\B_W\| <= sum Lk2 partners; 4sigma+15\|H\| <= 3n + K*h_R + 8\|B_W\| and <= 3n + K*h_R + 584p + 32 sigma_W (K = 1811497284) | yes | A10 H01 H08 G07 | bound | #42, #46, #52, #53, #82 (joins e(R,W), h_R, p, sigma) |
| 48 | `remainderPathBounds` | 7211 | R has no induced P13; bags of R minus hubs have <= 6142 vertices; paths/cycles through k hubs of R have <= 6143k+6142 vertices; R is 12-degenerate; m+11 <= 11L for cycle closures | yes | C10 C08 A07 B01 D10 I01 | bound exclusion | #42, #46, #49, #81 |
| 49 | `windowFreeGeometry` | 7212 | Window-free sets: induced walks of length <= 11; hub-pair dichotomy; chord/residue laws; outside-return dichotomy; window-free connected sets have <= 1+2047(3+sigma_K) vertices | yes | C10 C01 C12 C08 D10 B01 I01 | bound classification | #48, #81 |
| 50 | `inducedPathAttachment` | 7213 | A vertex off an induced P13 has <= 7 neighbours on it; every vertex of an induced P13 has a neighbour off it | yes | D01 C12 D10 A11 I01 | bound | #39, #40, #26 |
| 51 | `densityExcess` | 7207 | Density in excess form: int(S)+6 <= 4\|S\| for proper S; surplus(S) <= \|S\|+bd(S)-6; >= 2 edges leave every nonempty proper S; single-hub set slack >= \|S\|-d_h-1 | yes | A13 A10 A02 B02 H01 B04 | bound | #52, #53, #24 (applies to S = R) |
| 52 | `remainderSlack` | 7208 | slack(R) = 4\|R\|-6-2e(R) = (n-sigma)+2p+2 sigma_W - cross(P) - 6; hanging windows: sum(2+2 sigma_P) <= slack(K); cross(P)+6 <= 28p and sigma_W+6 <= e(R,W)+13p | yes | H01 H02 A13 A10 H08 G09 | identity bound | #51, #53, #47, #82, #92 |
| 53 | `hubWindowBudget` | 7209 | Hub-window budget: 24p+2eps+I+6\|H\|+sigma <= 3n+4h_W; 2\|H\|+3h_R+2eps+I_W <= 2p+\|R\|+(n-sigma); window internal-degree sum identity; low-dart identity | yes | H01 H02 A05 A03 G07 H08 A01 | identity bound | #52, #47, #62 (contains \|R\|, p, n, sigma) |
| 54 | `windowHubBounds` | 7210 | Windows vs big hubs (B), s = n-sigma: 12p+31\|B\| <= 2s+2\|H\|+25\|B\|^2; 23p+31\|B\| <= n+3s+25\|B\|^2; 22p+93\|B\|+6h_R+4eps+2I_W <= 6s+75\|B\|^2 | yes | H01 A05 G09 D03 | bound | #53, #58, #59 (bounds p, h_R by n, sigma) |
| 55 | `cubicNeighbourSupply` | 7200 | Every cubic vertex has a cubic neighbour (CubicSupply) | yes | A03 D03 E02 | witness | #53 (I isolated cubic), #5 |
| 56 | `hubCountBound` | 7201 | 5\|H\| + sigma <= 2n | yes | A05 A06 H08 A14 | bound | #58, #62, #63 |
| 57 | `lowEdgeParity` | 7202 | Parity of L-L edges on walks (LowEdgeParity) | yes | C04 | classification | (none on this ledger) |
| 58 | `bigHubBound` | 7203 | Hub domination and 2\|B\| + sigma <= n | yes | A05 A06 H08 A14 | bound | #56, #59 |
| 59 | `bigHubVShapes` | 7204 | V-shape caps and 4sigma + 93\|B\| <= 2n + 75\|B\|^2 + 4\|H\| | yes | A09 A05 H08 A06 | bound | #54, #60 |
| 60 | `highSurplusBound` | 7205 | 24sigma + 465\|B\| <= 18n + 375\|B\|^2 and, for s = n-sigma, 8n <= 32s + 125s^2 | yes | A05 H08 G08 | bound | #59, #65 |
| 61 | `hubLengthThreePairs` | 7206 | At a hub h with cubic second neighbourhood: <= 4d ordered non-adjacent pairs of N(h) joined by a length-3 path avoiding h; >= d(d-2)-4d have none | yes | D03 C01 A09 | bound | #29, #37 |
| 62 | `surplusDartIdentity` | 6607 | Dart identity: sigma + 2*delta*\|H\| + lowDarts = delta*n | yes | A05 A03 H01 G07 | identity | #53, #63, #43 |
| 63 | `highDegreeCountBound` | 6608 | \|H\| <= sigma | yes | A05 A06 A14 | bound | #56, #62, #65 |
| 64 | `admissibleQuotientsLabelInjective` | 6626 | Every admissible declared quotient (any coordinate family, any support) is label-injective on its family | yes (declared quotients of G's own coordinates) | F02 F07 E06 G06 | exclusion | #68, #88 |
| 65 | `surplusAtOrBelow` | 9 | sigma(G) <= T(n) = surplusThreshold(n) | yes | A05 A14 G08 H08 | bound | #75, #79, #83, #84, #89, #91, #92 (slack = F*s*T(n)) |
| 66 | `sparseSurplusSurvivor` | 119 | G survives the five sparse-surplus exits of its declared sparse family | yes | E09 A05 | exclusion | (block entry; #16, #23) |
| 67 | `barrierEnumeration` | 211 | Barrier-table row: stored safe/flat counts, curvature-positive = safe - flat, profile counts agree, log2(safe/flat) identity | no: statement of the presentation data alone (no object argument); a table row, not G's windows | !I05 !G02 | identity | #68, #71 (the window rate) |
| 68 | `windowPackageSeparated` | 35 | Window package of P0: bits per window, packages pairwise disjoint, \|family\| = bits*p, rate*scales <= bits, every functional admissible quotient is label-injective on family and on family union spine family | yes | G02 G03 G05 G06 F05 E06 H09 I03 | identity bound exclusion | #71, #73, #74, #80, #90 |
| 69 | `skeletonDominates` | 206 | The labelled skeleton class Skeleton(n,m) has exactly skeletonBudget(G) elements, and every state map stateOf on it has range <= budget | no: counts a class of labelled graphs of order n, size m and quantifies over all state maps on it | !G01 !G06 | identity bound | #71, #73, #74, #80, #90 (the budget number) |
| 70 | `hotColdPartition` | 200 | P0 is partitioned into canonical hot windows and cold windows | yes | D08 C09 I02 | decomposition | #71-#79 |
| 71 | `barrierCap` | 10 | 2^(rate*scales*\|hot\|) <= skeletonBudget(n,m) | yes (G's hot windows against the budget number of its own (n,m)) | H09 G03 G09 | bound | #73, #80, #90 |
| 72 | `coldRoute8AtOrAbove` | 213 | Cold route-8 test at or above: NOT[(3*4+1)(stubs*p+T) + 3*F*s*T < 3(n-13p)]  (cold-arm form of the Rate) | yes | H05 H01 A10 G08 | obstruction | #92 (the same test with the true supply \|dR\|) |
| 73 | `coldHotEntropyCap` | 215 | coldWindowBitRate * \|hot\| <= coldSkeletonAllowance | yes | H09 G03 G09 | bound | #71, #74 |
| 74 | `coldMass` | 216 | rate*p <= rate*\|cold\| + allowance (cold mass) | yes | H08 H09 G09 | bound | #75, #79, #80 |
| 75 | `coldAmbientCubic` | 217 | \|cold\| <= \|cold windows ambient cubic\| + sigma and sigma <= T(n) | yes | H08 G07 G08 A05 | bound | #65, #76, #79 |
| 76 | `coldStubExcess` | 218 | perWindow*\|cold\| <= perWindow*\|cubic cold\| + perWindow*sigma | yes | G07 H08 D01 | bound | #75, #77, #78 |
| 77 | `coldAmbientCubicStubExcess` | 180 | Every ambient-cubic cold window has external stub list of length coldExternalStubCount | yes | D01 A11 G07 | identity | #76, #78, #72 (stub count 15) |
| 78 | `coldSelectedBranchExcess` | 179 | Selected stubs of cubic cold windows number excess*\|cubic\| and each stub belongs to a unique window | yes | G07 D05 D01 | identity | #76, #79 |
| 79 | `coldMassBounded` | 225 | perWindow*\|cold\| <= (perWindow + (delta+1)*overlapBound)*sigma | yes | H08 G07 D05 A05 G08 | bound | #65, #74, #75 |
| 80 | `densityCap` | 12 | Density cap: 2*rate*scales*p <= (scaleCount+1)(delta*n+T) + densitySlack*rate*scales*T; and for every state map on the skeleton class, high-entropy joint package fits the skeleton budget | mixed: first conjunct is G; second quantifies over all state maps on the labelled skeleton class (other graphs) | G09 G08 H09 G03 !G01 | bound | #17, #71, #91, #E15, #E17 (upper-bounds p, hence lower-bounds \|R\| = n-13p) |
| 81 | `remainderNormalized` | 13 | Every subregion of R is window-free and carries no baseline subgraph | yes | C10 C08 E02 | exclusion | #48, #49, #84 |
| 82 | `boundaryDemand` | 14 | def+(R) <= e(R,W) <= (delta*13 - 2*12)p + sigma_W = 15p + sigma_W | yes | A11 A10 B05 B09 H05 H01 | bound | #25, #26, #83, #92 (caps \|dR\|) |
| 83 | `stubSupply` | 15 | def+(R) + 24p <= 3*13p + T(n)  (def+(R) <= 15p + T) | yes | A11 B09 H05 G08 H01 | bound | #82, #65, #84 |
| 84 | `wedgeSupply` | 16 | delta*\|X\| <= W2(X) + 2def+(X) for X subset R; and delta\|R\| + 48p <= W2(R) + 2(39p + T) | yes | A09 A11 F01 H01 | bound | #83, #85, #86, #88, #89 (lower-bounds W2 by \|R\|) |
| 85 | `curvatureTargetRank` | 18 | A maximum surviving subfamily of the wedge tests of R exists with size r_Omega(R), and is an upper bound for every surviving subfamily | yes | F01 F02 | bound witness | #86, #88, #89 |
| 86 | `exactResponseProfile` | 207 | Exact response profile of R has exactly W2(R) labelled entries | yes | F01 G02 | identity | #84, #88 |
| 87 | `targetRankCircuit` | 210 | Every raw wedge test outside the maximum surviving family has a proper target dependence (a,B) with B subset the family; if no proper dependence exists among raw tests the whole family survives | yes | F03 F07 F04 | classification | #88, #85 |
| 88 | `curvatureFullRank` | 20 | r_Omega(R) = W2(R) (full rank) | yes | F02 F07 F03 | identity | #89, #E9-#E14 |
| 89 | `forcedCurvatureCost` | 37 | c_Omega*(delta\|R\| + 48p) <= c_Omega*r_Omega(R) + c_Omega*2(39p + T) | yes | H09 H01 F02 A09 | bound | #84, #88, #65 (lower-bounds r_Omega by \|R\|) |
| 90 | `largeBudgetResidual` | 42 | jointPackageDemand*2^forcedObstructionBits <= skeletonBudget  OR  BelowEntropyRate holds at (n, d, 13, delta, def+(R), int(R), \|R\|) | yes | H09 G03 G05 | bound | #68, #71, #E5-#E8 (arm split on the remainder entropy) |
| 91 | `netDeficiencyCap` | 222 | If n is sufficiently large for the net cap: 4*(3*13p + spineScale*ceilSqrt(n)) < 4*24p + \|R\| | yes | H01 H05 G08 A11 I04 H04 | bound | #92 (lower-bounds \|R\| against 60p), #E3/#E4 |
| 92 | `route8RateFails` | 265 | NOT[(delta*s+1)*\|supply\| + delta*slack < delta*\|R\|] with supply = cut edges of R, s=4, slack = F*s*T(n): i.e. 13*\|dR\| + 3*slack >= 3*\|R\| at G's canonical packing | yes | H05 H01 A10 B09 H04 | obstruction | defining failure; dichotomy row Route8RateDichotomy |

## Subtype extras (union of the 11 subtype paths)

Each subtype path `Route8RateFailsOutcome_<lanePrefix>_<entropy>` is the generic residual (`.toGeneric`) conjoined with its own facts. Paths: realized/{highEntropy, lowNonrepetitive, lowWedgeFree, lowWedge}, denseAtOrAbove/{highEntropy, lowNonrepetitive, lowWedgeFree, lowWedge}, denseBelow/{lowNonrepetitive, lowWedgeFree, lowWedge}. The union has 18 extra keys (X1-X18); no other key is added by any path.

| # | Key | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by | Paths carrying it |
|---|---|---|---|---|---|---|---|
| X1 | `windowPackageRealized` | 2^(bits*p) <= skeletonBudget: the joint window package of P0 fits the skeleton budget | yes | H09 G03 G09 | bound | #68, #71, #E15 | realized (4 paths) |
| X2 | `windowPackageUnrealized` | skeletonBudget < 2^(bits*p): the window package does not fit | yes | H09 G03 G09 | bound | #68, #E3-#E4, #E17 | denseAtOrAbove (4), denseBelow (3) |
| X3 | `denseDeficiencyAtOrAbove` | NOT[4*(3*13p + spineScale*ceilSqrt n) < 4*24p + (n - 13p)]: dense-deficiency test at or above (n-13p = \|R\| by the window count) | yes | H01 H05 A11 G08 | bound | #91 (contrapositive of its hypothesis), #83 | denseAtOrAbove (4) |
| X4 | `denseDeficiencyBelow` | 4*(3*13p + spineScale*ceilSqrt n) < 4*24p + (n - 13p) | yes | H01 H05 A11 G08 | bound | #91, #92 | denseBelow (3) |
| X5 | `remainderEntropyHigh` | AtLeastEntropyRate at R: remainder states >= n^(\|R\|/d) | yes | G03 H09 | bound | #E7, #E8, #90 | highEntropy (2) |
| X6 | `remainderEntropyLow` | BelowEntropyRate at R (exact complement) | yes | G03 H09 | bound | #90, #E9, #E10 | lowNonrepetitive/lowWedgeFree/lowWedge (7) |
| X7 | `entropyPackageDemand` | (2^(rate*scales*p))^d * n^\|R\| <= jointPackageDemand^d | yes | G03 G05 H09 | bound | #E5, #E8, #80 | highEntropy (2) |
| X8 | `entropyCapBound` | jointPackageDemand * 2^forcedObstructionBits <= skeletonBudget | yes | H09 G03 | bound | #90, #E7 | highEntropy (2) |
| X9 | `localTypeCoordinateNonrepetitive` | r_Omega(R) = W2(R) and the radius-2 rooted type coordinate of the subcubic remainder is not structurally repetitive | yes | G04 F07 D02 | classification | #88, #E6 | lowNonrepetitive (3) |
| X10 | `localTypeCoordinateRepetitive` | r_Omega(R) = W2(R) and the rooted type coordinate is structurally repetitive (below the finite relabelling threshold) | yes | G04 F07 D02 F08 | classification | #88, #E6, #E11 | lowWedgeFree/lowWedge (4) |
| X11 | `dominantRootedType` | r_Omega(R) = internal wedge count of R and a canonical dominant rooted type (root) exists | yes | G04 D02 D08 F02 | witness | #88, #E10, #E12, #E13 | lowWedgeFree/lowWedge (4) |
| X12 | `dominantRootedTypeWedgeFree` | the canonical dominant root does not satisfy the internal-wedge clause | yes | G04 D02 A09 | classification | #E11 | lowWedgeFree (3) |
| X13 | `dominantRootedWedgeType` | the canonical dominant root satisfies the internal-wedge clause | yes | G04 D02 A09 | classification | #E11, #E14 | lowWedge (3) |
| X14 | `independentObstructionTranslates` | \|R\| <= (1 + 3*(2^4 - 1))*r_Omega(R) + 2*T(n) = 46*r_Omega(R) + 2T(n) | yes | F02 G04 G07 H08 | bound | #88, #E13, #92 (upper-bounds \|R\|) | lowWedge (3) |
| X15 | `realizedDensityOrder` | DensityOrderBound(A,D,rate,0,3,n,log2 n,T): 2*rate*L*(3n) <= A*(L+1)*(3n+T) + L*T*(2*rate*D). It packages the Rate failure (3n <= A*p + D*T, with D = 13 + 3*F*s) with the density cap #80 at P0 | yes | G09 G08 H09 H01 | bound | #80, #92, #E16 | realized (4) |
| X16 | `realizedOrderSmall` | NOT[n large enough for the realized density order]: n < N0 | yes | G08 I04 | classification | #E15 | realized (4) |
| X17 | `boundedDensityOrder` | DensityOrderBound with slack densitySlack*rate: 2*rate*L*(3n) <= A(L+1)(3n+T) + L*T*(A*densitySlack*rate + 2*rate*D): the Rate failure combined with cap [24] at P0 | yes | G09 G08 H09 H01 | bound | #80, #92, #E18 | denseAtOrAbove (4), denseBelow (3) |
| X18 | `boundedOrderSmall` | NOT[n large enough for the [24]-arm density order]: n < N0 | yes | G08 I04 | classification | #E17 | denseAtOrAbove (4), denseBelow (3) |

Per-path extras: realized_highEntropy: X1,X5,X7,X8,X15,X16. realized_lowNonrepetitive: X1,X6,X9,X15,X16. realized_lowWedgeFree: X1,X6,X10,X11,X12,X15,X16. realized_lowWedge: X1,X6,X10,X11,X13,X14,X15,X16. denseAtOrAbove_highEntropy: X2,X3,X5,X7,X8,X17,X18. denseAtOrAbove_lowNonrepetitive: X2,X3,X6,X9,X17,X18. denseAtOrAbove_lowWedgeFree: X2,X3,X6,X10,X11,X12,X17,X18. denseAtOrAbove_lowWedge: X2,X3,X6,X10,X11,X13,X14,X17,X18. denseBelow_lowNonrepetitive: X2,X4,X6,X9,X17,X18. denseBelow_lowWedgeFree: X2,X4,X6,X10,X11,X12,X17,X18. denseBelow_lowWedge: X2,X4,X6,X10,X11,X13,X14,X17,X18.

Reading of the extras against the Rate: X15/X17 (`DensityOrderBound`) are the joint statement 'Rate fails at P0 and the density cap #80 holds at P0'; their `n < N0` complements X16/X18 close the order. X3/X4 are the two sides of the net cap #91 with |R| = n - 13p. X14 (lowWedge only) is the only extra that bounds |R| from above by a rank: `|R| <= 46 r_Omega(R) + 2T(n)`.

### Table 1 delta from the extras

Coordinates whose Table-1 status is changed or sharpened by the union of extras (the generic marks above are unchanged; the extras raise a path's accounting, not the generic residual's):

| Code | Generic status | Extras giving certificate | Effect |
|---|---|---|---|
| A09 | x | X12, X13 | x, X12/X13 wedge clause at the dominant root |
| A11 | x | X3, X4 | x |
| D02 | ~ | X9, X10, X11, X12, X13 | ~ -> rooted types of G[R] decided on low arms |
| D08 | x | X11 | x, canonical dominant root X11 |
| F02 | x | X11, X14 | x, sharpened by X11, X14 (rank vs |R|) |
| F07 | x | X9, X10 | x |
| F08 | ~ | X10 | ~ -> repetitive arm X10 |
| G03 | x | X1, X2, X5, X6, X7, X8 | x, extended to remainder entropy (X5-X8) |
| G04 | gap | X9, X10, X11, X12, X13, X14 | gap -> accounted on the low arms (dominant/repetitive fibre); still no size bound of the fibre versus |R| except X14 on lowWedge |
| G05 | ~ | X7 | ~ -> conditional-product comparison of window and remainder on high arm (X7, X8) |
| G07 | x | X14 | x, X14 double count |
| G08 | ~ | X3, X4, X15, X16, X17, X18 | ~ -> small-order arms X16, X18 close n < N0 on every path |
| G09 | x | X1, X2, X15, X17 | x, X15/X17 give p against n |
| H01 | x | X3, X4, X15, X17 | x, X3/X4 restate the net-cap side with |R| = n - 13p |
| H05 | x | X3, X4 | x |
| H08 | ~ | X14 | ~, X14 adds 2T(n) mass term only |
| H09 | x | X1, X2, X5, X6, X7, X8, X15, X17 | x, extended to the remainder entropy budget (X5-X8) |
| I04 | ~ | X16, X18 | ~ -> same small-order arms |

## Gaps ranked

Ranking: number of existing facts (generic ledger) that would combine with the coordinate once measured; ties broken by directness to the three rate currencies. 'Feeds' names which of |R|, |dR|, slack the missing observable enters. All 'present at G' claims are anchored in the cited facts; every entry is a `gap` or `~` row of Table 1.

| Rank | Coordinate | Status | Feeds the rate | Why present at G | Missing observable and certificate | Technique | Existing facts it combines with | Count |
|---|---|---|---|---|---|---|---|---|
| 1 | H08 Total exceptional mass | `~` | slack | slack = bridgeMassFactor*dischargeScale*T(n) in fact 92; fact 2 only presents the constant, facts 65/63/75/79 bound other sigma-masses | the Type B bridge mass: number/mass of bridge entries <= F*s*sigma, with F = bridgeMassFactor; certificate = bound (the slack term F*s*T(n) of the Rate) | T13 + T12 | #2, #32, #44, #47, #53, #56, #58, #59, #60, #62, #63, #65, #75, #79, #92 | 15 |
| 2 | B01 Connected-component structure | `~` | |R| and |dR| | R is the induced remainder of P0 and Rate sums over its components (entriesOfComponents); facts 48/49 already bound sub-objects of R | components C of G[R] (the index set of the Rate's entries) with \|C\| and \|dC\| per component; certificate = decomposition plus a per-component bound \|dC\| <= rho*\|C\| + slack share (isoperimetric ratio of each component of the remainder) | T04 + T14 | #25, #26, #45, #47, #48, #49, #51, #52, #53, #81, #82, #83, #84, #92 | 14 |
| 3 | H03 Connected negative support | `gap` | |R| vs |dR| (component-wise) | fact 92 is exactly an aggregate non-positive charge over components of R; the pigeonhole step produces a component, but no fact states it | a connected region C of R with 3\|C\| <= 13\|dC\| + share of slack (connected negative support of the charge 3\|X\| - 13\|dX\|); certificate = witness component, obtained by pigeonhole over components from fact 92 | T13 + T10 | #25, #45, #48, #49, #51, #81, #82, #83, #84, #89, #91, #92 | 12 |
| 4 | H06 Incidence payment of deficits | `~` | |dR| | the Rate itself charges s per supply edge; fact 27 counts 4n+2sigma carriers of G but none is attributed to dR | assignment of the private essential carriers of R's entries to the cut edges of R with multiplicity <= s = 4; certificate = injection with bounded multiplicity onto Route8.cutEdges (supply) | T15 + T14 | #25, #26, #27, #39, #45, #47, #51, #52, #82, #83, #91, #92 | 12 |
| 5 | H07 Flow–cut structural support | `~` | |dR| | demand def+(R) (fact 25) and supply e(R,W) <= 15p+sigma_W (facts 26, 82) are both present; only counting bounds, no flow | integral flow in the network windows -> deficits of R (source capacity 15p + sigma_W per window stub, sink def+(R)), with a certified min-cut; certificate = flow-cut duality | T14 | #25, #26, #39, #45, #47, #50, #52, #82, #83, #92 | 10 |
| 6 | G04 Dominant or repetitive local type | `gap` | |R| | fact 88 gives full rank, the type coordinate exists at G; decided only in extras X9-X13 | size of the dominant/repetitive radius-2 rooted type fibre of G[R]; certificate = bound \|R\| <= c*(dominant fibre) + o(n) (the lowWedge arm's fact X14 is an instance) | T12 + T16 | #84, #85, #86, #87, #88, #89, #64, #68, #90 | 9 |
| 7 | B06 Boundaried graph type | `~` | |dR| | the cut dR is the boundary of R | boundaried type of (R, dR): ordered terminals, boundary degrees, incidence; certificate = classification | T05 | #9, #10, #25, #39, #45, #82, #92 | 7 |
| 8 | C01 Simple paths and attainable lengths | `~` | |R| | forced paths exist (19,20,22) | set of simple path lengths in G[R] between cut vertices | T08 | #19, #20, #22, #35, #48, #49, #61 | 7 |
| 9 | G08 Asymptotic versus finite-order behavior | `~` | |R| (via p) and slack | facts 91 and 80 carry 'sufficiently large' hypotheses; extras X16, X18 handle the small arm only in subtypes | explicit N0 and the small-order arm n < N0 of the net cap (fact 91) and the density cap (fact 80); certificate = exact small-order residual | T17 + T12 | #17, #65, #80, #91, #92, #2, #60 | 7 |
| 10 | H04 Feasibility of a local discharge | `~` | |dR| | the Rate's discharge s=4 appears in facts 2, 91, 92; the entries are not on this ledger | transfer rule of the Rate: entries -> supply with core in supply, and its feasibility; certificate = feasible discharge | T13 + T14 | #2, #25, #26, #82, #83, #91, #92 | 7 |
| 11 | A12 Cycle rank | `~` | |R| | fact 52 gives slack(R) = 4\|R\|-6-2e(R) exactly; fact 8 gives only global beta(G) | cycle rank of G[R] and of the cut: beta(G[R]) = e(R) - \|R\| + c(R); certificate = identity tied to slack(R) of fact 52 | T01 + T08 | #8, #34, #36, #51, #52, #53 | 6 |
| 12 | C07 Cycle-space interaction | `gap` | |R|/|dR| | beta(G) >= n/2+1 (fact 8) and cycle counts (34, 36) show a nontrivial cycle space | binary incidence vectors of the cycles through the cut edges of R; certificate = rank/independence bound in the cycle space | T08 + T11 | #8, #24, #34, #36, #51, #52 | 6 |
| 13 | D04 Matching-versus-star concentration | `~` | |dR| | fact 29 gives matching for G[N(h)] only | incidence graph of demands (deficit stubs of R) against resources (window stubs); certificate = classification matching vs star | T14 | #25, #26, #29, #39, #45, #82 | 6 |
| 14 | D06 Minimal connected overlap obstruction | `~` | |R| | witness minimality exists for sparse witnesses (fact 23) | smallest connected family of private carriers on which the Rate fails; certificate = minimal obstruction | T10 | #23, #45, #48, #49, #81, #92 | 6 |
| 15 | D07 Symmetry and equal response | `gap` | |R|,|dR| | P0 is chosen canonically (fact 14) | invariance of \|R\|, \|dR\| and the Rate under the choice of maximum packing; certificate = equal-response classification | T16 | #14, #17, #23, #52, #82, #92 | 6 |
| 16 | E08 Peelability | `gap` | |R| | windows are removable units | peel step preserving 13\|dR\|+3slack >= 3\|R\| | T19 | #14, #55, #17, #52, #53, #92 | 6 |
| 17 | G05 Additivity versus correlation | `~` | |R| | fact 90 disjunction | joint vs conditional count of window and remainder | T12 | #68, #71, #73, #74, #80, #90 | 6 |
| 18 | A04 Minimum and maximum degree | `~` | slack | hubs are the only high-degree vertices | maximum degree bound Delta <= 3+sigma <= 3+T(n) | T01 | #32, #56, #58, #63, #65 | 5 |
| 19 | B03 Cut vertices, blocks, and separators | `~` | |dR| | single-vertex boundaries occur (fact 28) | block-cut structure of G[R] joined to W | T04 | #28, #33, #35, #45, #48 | 5 |
| 20 | B07 Contextual response equivalence | `~` | |dR| | same | (G-only form is fact 10) combined with the R cut | T05 | #9, #10, #16, #23, #45 | 5 |
| 21 | H10 Finite demand descent | `gap` | |R| | same | well-founded demand measure with one-unit peel steps | T19 | #14, #17, #52, #53, #92 | 5 |
| 22 | B04 Multiple disjoint connections | `~` | |dR| | bridgeless (fact 24) | Menger number between terminals of R | T14 | #20, #24, #51, #45 | 4 |
| 23 | C11 Serial corridors and path increments | `~` | |R| | chain (fact 38) | corridor increments along the cut | T09 | #38, #76, #77, #78 | 4 |
| 24 | D02 Finite local type | `~` | |R| | types decided in extras | radius-2 rooted types of G[R] | T07 + T17 | #39, #40, #68, #88 | 4 |
| 25 | E07 Canonical descent under neutral moves | `gap` | |R| | same choice | neutral-move descent order on maximum packings | T16 + T19 | #14, #23, #17, #52 | 4 |
| 26 | B08 Locality of a witness or obstruction | `~` | |R| | fact 23 | support locality of the failing entries | T04 + T10 | #23, #48, #49 | 3 |
| 27 | C06 Ear structure | `~` | |R| | chords (fact 49) | ears of G[R] over G[W] | T08 + T04 | #35, #49, #48 | 3 |
| 28 | D09 Gluing realizability | `~` | |dR| | actualGlue (fact 10) | reconstruction of G from (R,dR) and W | T05 | #10, #16, #45 | 3 |
| 29 | F04 Geometric support of dependence | `~` | |R| | fact 87 | support of dependence relations | T11 | #87, #88, #23 | 3 |
| 30 | F08 Periodicity of a response family | `~` | |R| | mod-4 residue (fact 35) | periodic response family | T09 | #35, #38, #88 | 3 |
| 31 | G02 Number of legal local states | `~` | |R| | legal labels (fact 40) | census of labels realized on G's windows | T12+T17 | #39, #40, #68 | 3 |
| 32 | G06 Injective reconstruction from local data | `~` | |R| | fact 64 | injective reconstruction at G | T12+T11 | #64, #68, #90 | 3 |
| 33 | I01 Finite configuration space | `~` | |R| | bounded | explicit finite list | T17 | #48, #49, #50 | 3 |
| 34 | I02 Isomorphism and canonical representative | `~` | |R| | canonical | orbit representatives | T16+T17 | #14, #23, #70 | 3 |
| 35 | I04 Small-order residual | `~` | |R| | fact 91 | small-order residual | T17 | #91, #80 | 2 |

Ranking by the currency each gap feeds (sorted by number of combining facts within the group; B01 and H03 feed both |R| and |dR| and are listed under |R|):

- |dR| (supply side of the Rate): H06 (12), H07 (10), B06 (7), H04 (7), D04 (6), B03 (5), B07 (5), B04 (4), D09 (3)
- |R| (remainder size, and |R| against |dR| per component): B01 (14), H03 (12), G04 (9), C01 (7), G08 (7), A12 (6), C07 (6), D06 (6), D07 (6), E08 (6), G05 (6), H10 (5), C11 (4), D02 (4), E07 (4), B08 (3), C06 (3), F04 (3), F08 (3), G02 (3), G06 (3), I01 (3), I02 (3), I04 (2)
- slack (bridgeMassFactor*discharge*T(n)): H08 (15), A04 (5)

## Non-G facts

| # | Key | Non-G object | G-constructed replacement (missing accounting) |
|---|---|---|---|
| 1 | `selection` | second conjunct of SelectionMinimality: every strictly smaller baseline object avoids/does not have the property (other graphs) | E01: proper subgraphs of G fail the baseline (#5) together with the no-accepted-cycle conjunct (#1, G-part) |
| 11 | `replacementExclusion` | replacement piece X' and glue(X', G-Z): a graph other than G | E05: swap of G at Z inside G's own rest (as in #10, #16) and its canonical degree deficit at dZ measured against def+(R) |
| 12 | `uncompressible` | compressed representative X' glued to G-Z | same as #11 |
| 15 | `localAlgebra` | label alphabet census of a fixed window order (no guard over G's windows) | G02/I05: verified census of the labels realized by G's own windows P0, with generator and verifier |
| 18 | `noSuppressionChordViolation` | cycle certificate on the suppressed graph tvs.suppressed | E04: the un-suppressed walk in G with its chord count; use G-local switch facts #19, #20, #22 |
| 21 | `highCentreSplitForced` | cycle in G join M_h (edges not in G) | E04/D03: the cycle obtained from the G-local switch facts #19-#22 in subgraphs of G |
| 67 | `barrierEnumeration` | stored barrier-table row (safe/flat counts): presentation data, no object | I05/G02: table row recomputed from the label multiset realized on G's windows |
| 69 | `skeletonDominates` | class of labelled skeletons Skeleton(n,m) and every state map on it | G01/G06: the count of skeleton codes of G's own canonical decomposition and injectivity of G's own code map |
| 80 | `densityCap` | second conjunct: every state map on the skeleton class (other graphs); the first conjunct (density cap) is G-only and counts | G01: same as #69 |

Extras: none of X1-X18 uses an object outside G (each is an inequality or classification in G's own n, p, |R|, sigma, T(n), or a fact about G's canonical dominant root). Facts with a hypothesis that is a non-G quantifier were treated as mixed (#1, #80) and only their G conjunct earns marks. Facts #10 and #16 quantify contexts but only G's own rest (`actualGlue`), which is G-only and marked.

Effect on the Rate: none of the non-G facts is a Rate currency; marks lost are E01, E04, E05, G01 and I05, plus a share of G02/G06.

## Cross-check results

1. Every coordinate code in Table 2 has status x or ~ in Table 1 and lists that fact: PASS. Offending rows: none.
2. Every x or ~ in Table 1 cites at least one Table-2 row (and every nonG row cites a nonG fact): PASS. Offending rows: none.
3. Every Table-2 row accounts for at least one coordinate or is labelled bookkeeping: PASS. Offending rows: none. (Facts #1, #2, #3, #4, #5 are entry/spine laws but each accounts for coordinates; no row is pure routing; facts #11, #12, #15, #18, #21, #67, #69 account only nonG coordinates, which is recorded, not counted.)
4. No fact counted twice for the same demand in different currencies: PASS with one caveat recorded. Currencies are kept distinct: #82 (cap on |dR|) and #26 (window stub capacity) state the same inequality chain from the two ends of the manuscript's `lem:surplus-aware-window-stub`; #82 contains #25 and #26 as its two conjuncts and #83 spends #82's second link against T(n). They are recorded as one demand (deficit vs stub supply) accounted once under B09/H05, with #25 credited for A11/H06, #26 for H05 and #82/#83 credited for the same currency B09 only as restatements. Likewise #72 (cold Rate form) and #92 are the same test with different supply (`stubs*p + T` versus the true |dR|); only #92 counts for the Rate. #84/#89 use W2(R) and r_Omega(R) as a second currency (tests), not a second payment of the same deficit.

Coordinates of Table 1 not ranked in the gap table: none (every gap and ~ row is ranked).

## Outside the register

- The three-way split of the Rate into (private essential carriers per entry) / (supply |dR| via `Route8.cutEdges`) / (Type B bridge mass F*s*T(n)) has no register coordinate for the entry census itself: entries `entriesOfComponents R` with their `essentialCore` lie in `Route8Census` and the facts that publish them (route8CarrierCore, route8Rate, typeBBridgeMass) are upstream of this residual and are not on its 92-fact ledger. Observable: number of essential private carriers per entry and per component of R; certificate: bound `<= (delta-1)` per entry (`def:typeA-terminal-two-carrier`). It is the entry-level counterpart of the rate and is the accounting the top gaps B01/H03/H06 need.

## After the G audit (keys 8250-8252)

Facts added to the generic residual (now 95): #93 `route8RateFailsJoin` (exact window join identity at P0 with the cross-window incidences X, and the failed rate against it; about G; accounts A10, B05, H05, H01; bound + identity; consumed by #95), #94 `route8RateFailsPiece` (canonical pieces of G[R] partition |R| and |dR| exactly; for nonempty R a piece with m*delta*|X| <= m*(delta*s+1)*|dX| + delta*F*s*T(n); about G; accounts B01, H03; decomposition + witness; unconsumed), #95 `route8RateFailsCrossBound` (join against density cap #80: 2rL(delta n + (delta s+1)X) <= A(L+1)(delta n+T) + L T (A S + 2rD); about G; A10, H05, G08; bound; consumes #93 and #80's density-cap conjunct).

Table 1 delta: H03 `gap` -> `~` (witness piece exists; not consumed by any other fact, no per-piece stub bound); B01 stays `~` (pieces named with their |X|, |dX| now; still no per-piece bound); A10, H05 stay `x` (cross-window currency X now enters the rate inequality). Counts: x 45, ~ 29, gap 6 (C07, D07, E07, E08, G04, H10), n/a 3, nonG 5.

## Second pass (keys 8253-8255) and re-marking by user ruling

Re-marking (user ruling): #1 (SelectionMinimality: minimality is how the contradiction with G is reached), #11/#12 (replacement X' glued into G - Z, the replacement/compression form) and #69/#80 (skeleton-class count, a class built from G's data whose conclusion is an aggregate count consumed at G's parameters (n, m), never "some member fails X") are LEGITIMATE, not nonG. E01 nonG -> `x` (#1, #5, #11 combined), G01 nonG -> `x` (#69 and #80 enter the density cap that #95 combines with the rate), E05 nonG -> `~` (#11/#12 certify exclusion of smaller equivalents but are not combined with a rate currency). Remaining nonG: E04 (#18, #21: suppressed graph and G join M_h) and I05 (#15, #67: label census and barrier table row), not covered by the ruling.

New facts: #96 `route8RateFailsFlow` (H07: def+(X) <= |dX| <= def+(X)+sigma(X) for R and every piece; window stub capacity delivered to deficit and surplus of R up to X; failed rate in deficit currency; about G; A10 A11 B05 H05 H07; identity + bound; consumes #93), #97 `route8CarrierInjection` (H06: cores of the canonical route-8 entries of P0 lie in the cut and private cores total at most |dR|; about G; H06 A10; injection/bound; unconsumed), #98 `route8RateExactSlack` (H08: exact-sigma(G) rate or its exact negation, with sigma(G) < T(n) on the holding arm; about G; H08; bound; unconsumed).

Table 1 delta: H07 `~` -> `x`, H06 `~` (certified, not combined), H08 `~` (exact form published, downstream consumers still on the ceiling), G04 `gap` (not hoistable: decided only on the 8 low subtypes, see register). Final counts: x 48, ~ 29, gap 6 (C07, D07, E07, E08, G04, H10), n/a 3, nonG 2.

## Third pass (keys 8256-8258, `route8BasinBurden` hoisted) and final re-marking

Re-marking (user ruling): #18 (suppressed graph G - x + ab) and #21 (G join M_h) are graphs built from G with conclusions about G, legitimate: E04 `nonG` -> `~` (chord/cycle exclusions certified at graphs built from G; not combined with a rate currency). #15 (label alphabet census) and #67 (barrier table row) are parameter tables (constants), bookkeeping, not nonG: they account for no coordinate; I05 `nonG` -> `n/a` (the residual has no computational certificate whose input is G; constants only).

New generic facts: #99 `route8BasinBurden` (hoisted from the route-8 ledger; `s*D_A(X_A) <= N_basin`; needs only #5x remainderNormalized and cubicBaseline, before and independent of the rate; H06 H08), #100 `route8StubDeficit` (e(R,W) + exc(R) = sigma(R) + def+(R), exc <= sigma(R), deficit units inject into cut incidences, def+ + X + sigma(R) + 2(order-1)p = delta*order*p + sigma_W + exc; A10 A11 B05 H07; identity), #101 `route8DeficitVsStubs` (def+ reaches the stub capacity and then X + sigma(R) <= sigma_W + exc, def+ <= beta*p + sigma_W, or falls short and sigma_W + exc < X + sigma(R); H07 B05; classification with quantities), #102 `route8EntryLowerBound` (N_basin >= D_A; either the [113] test holds and |R| + s(X + 2(order-1)p) <= N_basin + s(delta*order*p + sigma_W) + slack, or D_A + s|dR| + slack < |R|; H06 A10; bound).

Table 1 delta: H06 `~` -> `x` (entry count combined with join, deficit and the [113] test). Final counts: x 49, ~ 29, gap 6 (C07, D07, E07, E08, G04, H10), n/a 4, nonG 0.

