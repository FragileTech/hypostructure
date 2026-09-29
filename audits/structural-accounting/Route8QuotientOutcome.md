# Structural accounting: `Route8QuotientOutcome`

Facts on the residual: 114. Structural coordinates: 88.

Status legend: `x` accounted · `~` partially accounted · `gap` present at G but unaccounted · `n/a` absent at G (reason required) · `nonG` accounted only through an object outside G (does not count).

## Table 1 — Structural coordinates (same for every residual)

### Size, degree, sparsity, and local incidence (`size-degree`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| A01 | Order | Number of vertices. |  |  |  |  |  |
| A02 | Size and edge density | Number of edges and density relative to order. |  |  |  |  |  |
| A03 | Degree sequence and classes | Degree multiset and threshold degree classes. |  |  |  |  |  |
| A04 | Minimum and maximum degree | Extremal vertex degrees. |  |  |  |  |  |
| A05 | Excess above a degree baseline | Degree sum above a fixed regular baseline. |  |  |  |  |  |
| A06 | Distribution of high-degree vertices | Adjacency and distances inside a threshold degree class. |  |  |  |  |  |
| A07 | Core number and degeneracy | Largest nonempty minimum-degree core and a peeling order. |  |  |  |  |  |
| A08 | Degree-two chains and subdivision storage | Maximal paths with degree-two internal vertices. |  |  |  |  |  |
| A09 | Length-two path or wedge supply | Count of two-edge paths, possibly with endpoint restrictions. |  |  |  |  |  |
| A10 | Incidence between two regions | Crossing-edge counts and their bipartite incidence graph. |  |  |  |  |  |
| A11 | Boundary degree deficit | Missing internal degree at marked boundary vertices. |  |  |  |  |  |
| A12 | Cycle rank | Dimension of the binary cycle space. |  |  |  |  |  |
| A13 | Global sparsity slack | Linear edge-count slack, globally or over every subgraph. |  |  |  |  |  |
| A14 | Near-regularity | Small degree excess or a bounded exceptional set. |  |  |  |  |  |

### Connectivity, cuts, and interfaces (`connectivity`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| B01 | Connected-component structure | Components of the graph or an induced remainder. |  |  |  |  |  |
| B02 | Bridges and edge cuts | Bridges, bonds, and edge connectivity. |  |  |  |  |  |
| B03 | Cut vertices, blocks, and separators | Block–cut tree and components behind a separator. |  |  |  |  |  |
| B04 | Multiple disjoint connections | Maximum internally disjoint paths between terminals. |  |  |  |  |  |
| B05 | Boundary of a region | Marked vertex/edge boundary, terminal labels, and degrees. |  |  |  |  |  |
| B06 | Boundaried graph type | Ordered terminals with degree and incidence data. |  |  |  |  |  |
| B07 | Contextual response equivalence | Agreement of two boundaried graphs in every compatible context. |  |  |  |  |  |
| B08 | Locality of a witness or obstruction | Smallest connected support carrying the witness. |  |  |  |  |  |
| B09 | Interface demand and supply | Relation between boundary demands and legal supporting incidences. |  |  |  |  |  |

### Paths, cycles, and length structure (`paths-cycles`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| C01 | Simple paths and attainable lengths | Set of simple path lengths between marked vertices. |  |  |  |  |  |
| C02 | Edge-rooted return lengths | Return-path lengths after removing a marked edge. |  |  |  |  |  |
| C03 | Cycle-length spectrum | Set of lengths of simple cycles. |  |  |  |  |  |
| C04 | Arithmetic class of lengths | Parity, residues, translated targets, or periodic responses. |  |  |  |  |  |
| C05 | Two-path and theta structure | Internally disjoint paths with common endpoints. |  |  |  |  |  |
| C06 | Ear structure | A path attached to a base subgraph only at its ends. |  |  |  |  |  |
| C07 | Cycle-space interaction | Binary incidence vectors and symmetric differences. |  |  |  |  |  |
| C08 | Induced paths and hereditary exclusion | Presence of an induced path or membership in a path-free class. |  |  |  |  |  |
| C09 | Packing number of a fixed pattern | Maximum disjoint family of pattern copies. |  |  |  |  |  |
| C10 | Structure of a packing remainder | Graph left after deleting a maximal packed family. |  |  |  |  |  |
| C11 | Serial corridors and path increments | Ordered path alternatives with base lengths and increments. |  |  |  |  |  |
| C12 | Endpoint and attachment constraints | Allowed external contacts at path endpoints and interiors. |  |  |  |  |  |
| C13 | Simultaneous path realizability | Joint disjointness, endpoint compatibility, and simplicity. |  |  |  |  |  |

### Local configurations, overlap, decomposition, and symmetry (`local-structure`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| D01 | Attachment pattern to a fixed motif | Marked motif vertices met by an outside vertex or path. |  |  |  |  |  |
| D02 | Finite local type | Marked isomorphism class with degrees and local responses. |  |  |  |  |  |
| D03 | Star, fan, and high-degree neighborhood | A center, typed neighbors, ports, and pair compatibilities. |  |  |  |  |  |
| D04 | Matching-versus-star concentration | Auxiliary incidence graph on demands and resources. |  |  |  |  |  |
| D05 | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports. |  |  |  |  |  |
| D06 | Minimal connected overlap obstruction | Smallest connected family where realization or additivity fails. |  |  |  |  |  |
| D07 | Symmetry and equal response | Automorphisms, equal increments, or identical signatures. |  |  |  |  |  |
| D08 | Canonical structural decomposition | Deterministic ordering of pieces and attachment data. |  |  |  |  |  |
| D09 | Gluing realizability | Compatibility and uniqueness of reconstructed boundaried pieces. |  |  |  |  |  |
| D10 | Bounded exceptional configuration | A fixed-size marked graph satisfying residual hypotheses. |  |  |  |  |  |

### Criticality, reduction, and replacement (`criticality`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| E01 | Extremal counterexample status | Minimality under a well-founded graph order. |  |  |  |  |  |
| E02 | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses. |  |  |  |  |  |
| E03 | Deletion criticality | Effect of deleting each edge or vertex. |  |  |  |  |  |
| E04 | Safe suppression and simplification | Invariance under a local graph reduction. |  |  |  |  |  |
| E05 | Replacement irreducibility | Absence of a smaller context-equivalent boundaried representative. |  |  |  |  |  |
| E06 | Quotient distinguishability | Whether identifying states changes a contextual response. |  |  |  |  |  |
| E07 | Canonical descent under neutral moves | A secondary order on equal-size decompositions. |  |  |  |  |  |
| E08 | Peelability | A removable unit preserving the residual invariant. |  |  |  |  |  |
| E09 | Completion or target defect | Whether a partial structure completes the target or fails a response coordinate. |  |  |  |  |  |

### Independence, dependence, and support (`dependence`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| F01 | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors. |  |  |  |  |  |
| F02 | Rank of a local-test family | Rank of response vectors or a maximum independent subfamily. |  |  |  |  |  |
| F03 | Minimal dependence circuit | An inclusion-minimal dependent subfamily. |  |  |  |  |  |
| F04 | Geometric support of dependence | Vertices, edges, contexts, and coordinates used by a relation. |  |  |  |  |  |
| F05 | Separation of testers | Disjoint supports or contexts distinguishing coordinates. |  |  |  |  |  |
| F06 | Cancellation and repair structure | Composite response relations and their repair network. |  |  |  |  |  |
| F07 | Full rank versus structured rank loss | Dichotomy between independent tests and localized dependence. |  |  |  |  |  |
| F08 | Periodicity of a response family | Repeated boundary or length response under additive increments. |  |  |  |  |  |

### Counting, information, and exact reconstruction (`counting`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| G01 | Size of a labelled graph class | Count at fixed order, size, degree data, or decomposition. |  |  |  |  |  |
| G02 | Number of legal local states | Cardinality of attachment, interface, or neighborhood types. |  |  |  |  |  |
| G03 | Conditional information of local tests | Logarithm of conditional fibre sizes. |  |  |  |  |  |
| G04 | Dominant or repetitive local type | Largest fibre in a finite partition. |  |  |  |  |  |
| G05 | Additivity versus correlation | Joint state count compared with conditional products. |  |  |  |  |  |
| G06 | Injective reconstruction from local data | Map from decomposition states to labelled graphs. |  |  |  |  |  |
| G07 | Resource multiplicity and double counting | Demands charged to each vertex, edge, token, or incidence. |  |  |  |  |  |
| G08 | Asymptotic versus finite-order behavior | Error terms, thresholds, and exact small orders. |  |  |  |  |  |
| G09 | Density of a packed pattern | Packing number normalized by graph order. |  |  |  |  |  |

### Potentials, discharging, demand, and descent (`potentials`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| H01 | Deficiency–surplus balance | Linear combination of boundary deficit, excess, and order. |  |  |  |  |  |
| H02 | Additive or superadditive charge | A potential compatible with support decomposition. |  |  |  |  |  |
| H03 | Connected negative support | A connected region with negative charge. |  |  |  |  |  |
| H04 | Feasibility of a local discharge | Transfer rules from suppliers to deficits. |  |  |  |  |  |
| H05 | Load and saturation | Load compared with certified capacity. |  |  |  |  |  |
| H06 | Incidence payment of deficits | Assignment to distinct or bounded-multiplicity resources. |  |  |  |  |  |
| H07 | Flow–cut structural support | Integral flow in the demand–support network. |  |  |  |  |  |
| H08 | Total exceptional mass | Sum of deficits or charges over an exceptional family. |  |  |  |  |  |
| H09 | Competition between two budgets | Required tests compared with available states or supply. |  |  |  |  |  |
| H10 | Finite demand descent | A well-founded measure and one-unit peel steps. |  |  |  |  |  |

### Finite and externally certified structure (`certification`)

| Code | Property | Observable | Status | Accounting facts | Certificate obtained | Techniques used | Missing accounting |
|---|---|---|---|---|---|---|---|
| I01 | Finite configuration space | Explicit bounded graphs, labels, attachments, or states. |  |  |  |  |  |
| I02 | Isomorphism and canonical representative | Canonical labels or orbit representatives. |  |  |  |  |  |
| I03 | Exact collision or compatibility | Integer equalities, endpoint conflicts, or unrealizable packages. |  |  |  |  |  |
| I04 | Small-order residual | Finite orders outside an asymptotic argument. |  |  |  |  |  |
| I05 | Reproducible computational certificate | Input schema, generator, verifier, and semantic theorem. |  |  |  |  |  |
| I06 | External structure theorem | Exact hypotheses and conclusion of an imported result. |  |  |  |  |  |

## Table 2 — Facts of the residual → structural coordinates

| # | Key | idx | Statement at G (one line) | About G only? | Coordinates accounted | Certificate type | Consumed by |
|---|---|---|---|---|---|---|---|
| 1 | `selection` | 0 |  |  |  |  |  |
| 2 | `cubicBaseline` | 221 |  |  |  |  |  |
| 3 | `minDegreeBaseline` | 2850 |  |  |  |  |  |
| 4 | `returnAvoidance` | 1 |  |  |  |  |  |
| 5 | `noProperBaseline` | 2 |  |  |  |  |  |
| 6 | `slackIndependent` | 4 |  |  |  |  |  |
| 7 | `tightEndpoint` | 3 |  |  |  |  |  |
| 8 | `cycleRankConstraint` | 425 |  |  |  |  |  |
| 9 | `degreeProfileFibres` | 2300 |  |  |  |  |  |
| 10 | `targetCompleteContextUniversality` | 2301 |  |  |  |  |  |
| 11 | `replacementExclusion` | 223 |  |  |  |  |  |
| 12 | `uncompressible` | 5 |  |  |  |  |  |
| 13 | `windowPresent` | 608 |  |  |  |  |  |
| 14 | `maximalPacking` | 6 |  |  |  |  |  |
| 15 | `localAlgebra` | 7 |  |  |  |  |  |
| 16 | `everyWitnessSpectrumSplit` | 6702 |  |  |  |  |  |
| 17 | `packingOrderBound` | 6611 |  |  |  |  |  |
| 18 | `noSuppressionChordViolation` | 6620 |  |  |  |  |  |
| 19 | `twoSwitchForcedPath` | 6800 |  |  |  |  |  |
| 20 | `crossSwitchFamily` | 6802 |  |  |  |  |  |
| 21 | `highCentreSplitForced` | 6801 |  |  |  |  |  |
| 22 | `sameVertexSwitchForcedPath` | 6803 |  |  |  |  |  |
| 23 | `specWitnessStructure` | 6677 |  |  |  |  |  |
| 24 | `remainderDeficiencyBelowCut` | 6663 |  |  |  |  |  |
| 25 | `windowCutCapacity` | 6664 |  |  |  |  |  |
| 26 | `primitiveCarrierCount` | 6666 |  |  |  |  |  |
| 27 | `singleBoundaryShape` | 6627 |  |  |  |  |  |
| 28 | `neighbourhoodPairCount` | 6900 |  |  |  |  |  |
| 29 | `starCycleConstraint` | 6901 |  |  |  |  |  |
| 30 | `meetingCycleConstraint` | 6902 |  |  |  |  |  |
| 31 | `highDegreePairSum` | 6903 |  |  |  |  |  |
| 32 | `vertexDeletionComponents` | 6904 |  |  |  |  |  |
| 33 | `cyclesThroughVertex` | 6905 |  |  |  |  |  |
| 34 | `cutVertexBlockPaths` | 6906 |  |  |  |  |  |
| 35 | `cycleDoubleCount` | 6907 |  |  |  |  |  |
| 36 | `threeRouteFan` | 7100 |  |  |  |  |  |
| 37 | `threeRouteChain` | 7101 |  |  |  |  |  |
| 38 | `windowPositionStubs` | 7102 |  |  |  |  |  |
| 39 | `windowAttachmentGap` | 7103 |  |  |  |  |  |
| 40 | `portEndDegree` | 7233 |  |  |  |  |  |
| 41 | `hubLinkStructure` | 7217 |  |  |  |  |  |
| 42 | `hubClassCounts` | 7218 |  |  |  |  |  |
| 43 | `slotRelation` | 7219 |  |  |  |  |  |
| 44 | `closedClasses` | 7220 |  |  |  |  |  |
| 45 | `hubTwoHopLinks` | 7221 |  |  |  |  |  |
| 46 | `slotLinear` | 7222 |  |  |  |  |  |
| 47 | `remainderPathBounds` | 7211 |  |  |  |  |  |
| 48 | `windowFreeGeometry` | 7212 |  |  |  |  |  |
| 49 | `inducedPathAttachment` | 7213 |  |  |  |  |  |
| 50 | `densityExcess` | 7207 |  |  |  |  |  |
| 51 | `remainderSlack` | 7208 |  |  |  |  |  |
| 52 | `hubWindowBudget` | 7209 |  |  |  |  |  |
| 53 | `windowHubBounds` | 7210 |  |  |  |  |  |
| 54 | `cubicNeighbourSupply` | 7200 |  |  |  |  |  |
| 55 | `hubCountBound` | 7201 |  |  |  |  |  |
| 56 | `lowEdgeParity` | 7202 |  |  |  |  |  |
| 57 | `bigHubBound` | 7203 |  |  |  |  |  |
| 58 | `bigHubVShapes` | 7204 |  |  |  |  |  |
| 59 | `highSurplusBound` | 7205 |  |  |  |  |  |
| 60 | `hubLengthThreePairs` | 7206 |  |  |  |  |  |
| 61 | `surplusDartIdentity` | 6607 |  |  |  |  |  |
| 62 | `highDegreeCountBound` | 6608 |  |  |  |  |  |
| 63 | `admissibleQuotientsLabelInjective` | 6626 |  |  |  |  |  |
| 64 | `surplusAtOrBelow` | 9 |  |  |  |  |  |
| 65 | `sparseSurplusSurvivor` | 119 |  |  |  |  |  |
| 66 | `barrierEnumeration` | 211 |  |  |  |  |  |
| 67 | `windowPackageSeparated` | 35 |  |  |  |  |  |
| 68 | `skeletonDominates` | 206 |  |  |  |  |  |
| 69 | `hotColdPartition` | 200 |  |  |  |  |  |
| 70 | `barrierCap` | 10 |  |  |  |  |  |
| 71 | `coldHotEntropyCap` | 215 |  |  |  |  |  |
| 72 | `coldMass` | 216 |  |  |  |  |  |
| 73 | `coldAmbientCubic` | 217 |  |  |  |  |  |
| 74 | `coldStubExcess` | 218 |  |  |  |  |  |
| 75 | `coldAmbientCubicStubExcess` | 180 |  |  |  |  |  |
| 76 | `coldSelectedBranchExcess` | 179 |  |  |  |  |  |
| 77 | `remainderNormalized` | 13 |  |  |  |  |  |
| 78 | `boundaryDemand` | 14 |  |  |  |  |  |
| 79 | `stubSupply` | 15 |  |  |  |  |  |
| 80 | `wedgeSupply` | 16 |  |  |  |  |  |
| 81 | `curvatureTargetRank` | 18 |  |  |  |  |  |
| 82 | `exactResponseProfile` | 207 |  |  |  |  |  |
| 83 | `targetRankCircuit` | 210 |  |  |  |  |  |
| 84 | `curvatureFullRank` | 20 |  |  |  |  |  |
| 85 | `forcedCurvatureCost` | 37 |  |  |  |  |  |
| 86 | `largeBudgetResidual` | 42 |  |  |  |  |  |
| 87 | `netDeficiencyCap` | 222 |  |  |  |  |  |
| 88 | `route8Rate` | 264 |  |  |  |  |  |
| 89 | `bridgeless` | 226 |  |  |  |  |  |
| 90 | `coldReturnCorridors` | 227 |  |  |  |  |  |
| 91 | `coldCorridorState` | 30 |  |  |  |  |  |
| 92 | `coldFirstFailureOccurrence` | 404 |  |  |  |  |  |
| 93 | `coldFailureCycle` | 64 |  |  |  |  |  |
| 94 | `coldFailureCompression` | 66 |  |  |  |  |  |
| 95 | `coldHandoffTransfer` | 69 |  |  |  |  |  |
| 96 | `netChargeLocalization` | 46 |  |  |  |  |  |
| 97 | `typeBAbsorbedCharge` | 2800 |  |  |  |  |  |
| 98 | `highCentreNormalForm` | 72 |  |  |  |  |  |
| 99 | `sameCenterOpenPortCompatibility` | 354 |  |  |  |  |  |
| 100 | `triangularShoulderCompletion` | 426 |  |  |  |  |  |
| 101 | `triangularPortReturn` | 427 |  |  |  |  |  |
| 102 | `route8BasinBurden` | 161 |  |  |  |  |  |
| 103 | `route8CarrierCore` | 163 |  |  |  |  |  |
| 104 | `typeBBridgeMass` | 85 |  |  |  |  |  |
| 105 | `typeBBridgeSublinear` | 189 |  |  |  |  |  |
| 106 | `route8UnifiedNegative` | 336 |  |  |  |  |  |
| 107 | `typeAExclusion` | 343 |  |  |  |  |  |
| 108 | `typeBBridgeReduction` | 344 |  |  |  |  |  |
| 109 | `route8PiecesClassified` | 266 |  |  |  |  |  |
| 110 | `route8ExtractedEntryCensus` | 350 |  |  |  |  |  |
| 111 | `typeBSublinearLedger` | 345 |  |  |  |  |  |
| 112 | `route8UnifiedDeficit` | 339 |  |  |  |  |  |
| 113 | `route8QuotientResidual` | 348 |  |  |  |  |  |
| 114 | `route8QuotientEntriesAtG` | 8150 |  |  |  |  |  |

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
