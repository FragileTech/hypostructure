# Graph structural properties and the techniques used to evaluate them

## Purpose and verdict

This document is a property-first companion to
[`structural_survey.md`](./structural_survey.md). It separates the structure of
a graph from the proof devices used to study that structure. Its source
baseline is the architecture and invariant ledger in the current
[`erdos_64_proof.tex`](../to_formalize/erdos_64_proof.tex).

The tables in `structural_survey.md` are an effective navigation aid for the
Erdős–Gyárfás (EG) manuscript. They are not yet a general structural survey.
There are four reasons.

1. Their columns are broad bundles. For example, degree distribution,
   surplus, and near-cubicity are distinct properties with different
   observables and different failure modes.
2. They mix intrinsic graph properties, hypotheses imposed by a
   minimal-counterexample proof, artifacts of the chosen decomposition, and
   terminal closure procedures.
3. Their rows name exact manuscript moves. A reader cannot directly transfer
   a row such as "run the Type A receiver ladder" to another graph problem.
4. An `X` records incidence, but not the test performed, the certificate
   produced, or the information still missing.

The current matrix also omits several structures that the manuscript's own
invariant ledger uses: bridges, cores, cycle and sparsity ranks, suppression of
degree-two chains, theta and ear completions, cycle-space symmetric difference,
and the locality of dependence supports. Its first table has inconsistent
column counts, and its net-charge formula is split by an unescaped vertical
bar.

The master survey below is exhaustive relative to the structural content of
the EG manuscript. Section 8 records major families of graph structure that
the EG proof does not exercise. Thus the document is a reusable starting point
for graph problems, rather than a claim to catalogue all of graph theory.

## 1. What counts as a property and what counts as a technique

The distinction is easiest to maintain through five layers.

| Layer | Meaning | Example |
| --- | --- | --- |
| **Graph property** | Isomorphism-invariant structure of a graph or a marked graph | The set of vertices of degree at least four is independent |
| **Observable** | A number, set, relation, or finite state that records the property | Degree sequence; cycle-length set; boundary response table |
| **Proof state** | A hypothesis introduced by the argument rather than intrinsic structure | The graph is a lexicographically minimal counterexample |
| **Technique** | A reusable operation or theorem applied to an observable | Edge deletion, maximal packing, uncrossing, rank, discharging |
| **Certificate** | The output that allows the proof to advance | A target cycle, a separator, a smaller equivalent piece, or a numerical bound |

Some properties below are marked **predicate-relative**. They describe how a
boundaried graph behaves with respect to an arbitrary graph predicate
\(\mathcal Q\), such as containing a cycle of an allowed length. They are
problem-independent as interface notions, although their concrete state space
depends on \(\mathcal Q\).

For a new problem, use the tables from left to right:

1. choose the structural property actually needed;
2. choose an observable that retains enough information;
3. apply one or more listed techniques;
4. state the certificate produced;
5. check the final column before treating that certificate as decisive.

## 2. Textbook technique families

These codes keep the master tables compact. The descriptions, rather than the
codes, are the reusable content.

| Code | Technique family | Standard move |
| --- | --- | --- |
| **T01** | Direct invariant calculation | Apply the handshake identity, degree sums, incidence identities, or rank identities |
| **T02** | Extremal selection | Choose a smallest or lexicographically minimal counterexample and exploit strict descent |
| **T03** | Local graph modification | Delete an edge or vertex, suppress a degree-two vertex, split, glue, or replace a subgraph |
| **T04** | Core and connectivity decomposition | Peel low-degree vertices; decompose into components, blocks, cuts, ears, or separators |
| **T05** | Boundary-interface analysis | Mark a boundary, record terminal data, and compare compatible outside contexts |
| **T06** | Maximal packing | Choose a maximal vertex- or edge-disjoint family and study the excluded remainder |
| **T07** | Local configuration analysis | Classify neighborhoods, attachments, fans, paths, or bounded-radius types |
| **T08** | Path–cycle and cycle-space analysis | Root a cycle at an edge, combine two paths, add an ear, or take symmetric difference |
| **T09** | Arithmetic of lengths | Use parity, congruences, sumsets, interval filling, or periodicity of attainable lengths |
| **T10** | Uncrossing and minimal obstruction | Select an inclusion-minimal failure and uncross intersecting supports into a simpler form |
| **T11** | Linear-algebraic rank | Represent local tests as coordinates; extract a basis or a minimal dependent circuit |
| **T12** | Counting and information | Use labelled enumeration, pigeonhole, conditional counting, or entropy |
| **T13** | Potential and discharging | Define a charge, redistribute it locally, and isolate overloaded or negative supports |
| **T14** | Demand–supply and flow | Build an incidence network; apply matching, alternating paths, or flow–cut reasoning |
| **T15** | Double counting and injection | Partition contributions, prevent duplicate charges, or reconstruct objects injectively |
| **T16** | Symmetry and canonicalization | Quotient by isomorphism, choose canonical representatives, and break equal-size ties |
| **T17** | Finite exact certification | Enumerate a finite state space and retain an independently checkable certificate |
| **T18** | External structural theorem | Invoke a proved classification or exclusion theorem as a black box |
| **T19** | Peeling and finite descent | Remove one certified unit at a time while preserving the invariant needed for iteration |

No single technique family is a universal evaluator. The decisive step in a
structural proof is often the composition of two techniques: maximal packing
with a remainder theorem, rank with support localization, or discharging with
an interface replacement argument.

## 3. Master property–technique survey

### 3.1 Size, degree, sparsity, and local incidence

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **A01** | Order | \(n=\lvert V(G)\rvert\) | T01, T02 | Induction parameter; finite-size threshold | Order alone contains no incidence information; pair with A02–A04 |
| **A02** | Size and edge density | \(m=\lvert E(G)\rvert\), \(m/n\), or edge density | T01, T12 | Sparse/dense branch; counting budget | Equal density permits very different topology; pair with degree distribution and cuts |
| **A03** | Degree sequence and degree classes | Multiset \(\{d(v):v\in V(G)\}\) and sets \(V_i,V_{\ge i}\) | T01, T07, T15 | Degree-class counts; local case split | The degree sequence does not determine adjacency among classes |
| **A04** | Minimum and maximum degree | \(\delta(G)\), \(\Delta(G)\) | T01, T02, T04 | Core existence; bounded- or high-degree branch | Extremal degrees do not control where exceptional vertices occur |
| **A05** | Excess above a degree baseline | \(\sigma_r(G)=\sum_v(d(v)-r)=2m-rn\) | T01, T13, T15 | Quantitative distance from \(r\)-regularity; supply of excess incidences | Aggregate excess can be concentrated; pair with A06 and D03 |
| **A06** | Distribution of high-degree vertices | Induced graph \(G[V_{\ge r+1}]\), distances between high-degree vertices | T02, T03, T07 | Independence, bounded clustering, or a fan configuration | A global excess bound does not imply separation without a criticality argument |
| **A07** | Core number and degeneracy | Largest \(k\) for which a nonempty \(k\)-core exists; peeling order | T04, T19 | A core, a low-degree elimination order, or core exclusion | A core certificate records minimum degree, not target cycles or boundary behavior |
| **A08** | Degree-two chains and subdivision storage | Maximal paths whose internal vertices have degree two | T03, T04, T08 | Safe suppression, a long corridor, or a critical-cycle witness | Suppression can change prescribed lengths and must preserve the target predicate |
| **A09** | Length-two path or wedge supply | \(W_2(G)=\sum_v\binom{d(v)}2\), with endpoint restrictions if needed | T01, T07, T15 | A lower bound on local path testers | Wedges can overlap heavily; pair with F02–F05 before treating them as independent |
| **A10** | Incidence between two regions | \(e(X,Y)\), attachment multiplicities, or a bipartite incidence graph | T01, T14, T15 | Exact join identity, capacity bound, or overload | A count does not determine the geometry of attachments |
| **A11** | Boundary degree deficit | \(q_X(v)=r-d_X(v)\) on marked boundary vertices, often with positive part | T01, T05, T13 | Required external incidence or unpaid local demand | The baseline \(r\) and boundary convention must remain fixed under replacement |
| **A12** | Cycle rank | \(\beta(G)=m-n+c(G)\), the dimension of the binary cycle space | T01, T04, T11 | Number of independent cycles; lower or upper rank bound | Cycle-space rank does not record the lengths of its cycles |
| **A13** | Global sparsity slack | A linear form such as \(an-b-m\), or a family \(m(H)\le a\lvert V(H)\rvert-b\) | T01, T02, T12 | Edge-count envelope or violation subgraph | A single global slack does not certify hereditary sparsity over all subgraphs |
| **A14** | Near-regularity | Small \(\sigma_r(G)\), a bounded exceptional set, or concentration of degrees near \(r\) | T01, T12, T13 | Reduced counting class and controlled local exceptions | Near-regular graphs may still contain large separators or correlated neighborhoods |

### 3.2 Connectivity, cuts, and interfaces

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **B01** | Connected-component structure | Components of \(G\) or of an induced remainder | T04, T13 | Reduction to one component; localization of a negative sum | Componentwise conclusions may lose constraints carried through the deleted region |
| **B02** | Bridges and edge cuts | Bridges, bonds, and \(\lambda(G)\) | T02, T03, T04 | Bridgelessness, a cut, or decomposition into edge-connected blocks | Edge connectivity does not control vertex bottlenecks |
| **B03** | Cut vertices, blocks, and vertex separators | Block–cut tree, separators \(S\), and components of \(G-S\) | T04, T05, T10 | A bounded interface or decomposition tree | Target behavior may depend on how paths pair across the separator |
| **B04** | Multiple disjoint connections | Maximum number of internally vertex- or edge-disjoint paths between terminals | T04, T08, T14 | Disjoint paths or a separating cut | Menger-type existence does not prescribe path lengths |
| **B05** | Vertex and edge boundary of a region | \(\partial_V X\), \(\partial_E X\), terminal labels, and boundary degrees | T01, T05 | A finite interface and exact external-incidence count | Boundary size alone omits terminal pairing and attainable lengths |
| **B06** | Boundaried graph type | A graph with ordered terminals, terminal degrees, and marked incidence data | T05, T16 | A composable local object for gluing or dynamic programming | The chosen interface must retain every datum used by outside contexts |
| **B07** | Contextual response equivalence **(predicate-relative)** | Two boundaried graphs give the same truth value for \(\mathcal Q\) in every compatible context | T03, T05, T16 | Safe replacement or a distinguishing outside context | Universal context equivalence may have an infinite state space |
| **B08** | Locality of a witness or obstruction | Smallest connected vertex/edge support carrying the witness | T05, T10, T11 | Proper local support, bounded interface, or a whole-graph obstruction | Minimal support need not be bounded without a separate localization theorem |
| **B09** | Interface demand and supply | Bipartite relation between boundary demands and legal supporting incidences | T14, T15 | Matching/flow, deficient cut, overload, or uncovered demand | Abstract feasible flow must correspond to graph-realizable paths or attachments |

### 3.3 Paths, cycles, and length structure

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **C01** | Simple path existence and attainable lengths | \(L_G(x,y)=\{\ell:\text{a simple }x\text{–}y\text{ path of length }\ell\}\) | T04, T07, T08 | A path of prescribed length or an exclusion interval | Walk-length information cannot be substituted for simple-path information |
| **C02** | Edge-rooted return lengths | For oriented \(uv\), lengths of simple \(v\)-to-\(u\) paths in \(G-uv\) | T03, T08 | A cycle-length certificate rooted at one edge | This is an equivalence transform, not a forcing theorem for the return path |
| **C03** | Cycle-length spectrum | \(\mathcal L(G)=\{\lvert C\rvert:C\text{ is a cycle of }G\}\) | T08, T09, T11 | A target length, an avoided set, girth, or circumference bound | Cycle-space addition does not preserve individual cycle lengths automatically |
| **C04** | Parity, congruence, or arithmetic class of lengths | \(\mathcal L(G)\bmod q\), translated target sets, or periodic response classes | T08, T09 | Modular hit, arithmetic obstruction, or eventual periodicity | Congruence is coarser than exact length and may create false candidate hits |
| **C05** | Two-path and theta structure | Two or three internally disjoint paths with common endpoints | T08, T09 | Several cycles whose lengths are sums of path lengths | Paths counted separately must be compatible and internally disjoint |
| **C06** | Ear structure | A path whose internal vertices lie outside a base subgraph and whose ends lie inside | T04, T08 | Ear decomposition, new cycle, or interface completion | Ear addition controls connectivity more directly than exact cycle lengths |
| **C07** | Cycle-space interaction | Binary incidence vectors and symmetric differences of cycles or paths | T08, T11 | A new cycle-space element, cancellation relation, or support decomposition | A symmetric difference may be a disjoint union rather than one simple cycle |
| **C08** | Induced paths and hereditary exclusion | Presence of an induced \(P_t\); membership in an induced-\(P_t\)-free class | T06, T07, T18 | A fixed induced pattern or a hereditary remainder class | An induced-subgraph theorem may be highly specific to \(t\) and the target family |
| **C09** | Packing number of a fixed pattern | Maximum number of vertex- or edge-disjoint copies | T06, T12, T15 | Packed pieces, packing density, and an excluded remainder | Maximal and maximum packings give different quantitative information |
| **C10** | Structure of a packing remainder | Graph obtained after deleting a maximal packed family | T04, T06, T07 | Exclusion of another packed pattern; componentwise restrictions | The remainder can retain long-range dependence through its attachments to the packing |
| **C11** | Serial corridors and path increments | Ordered alternatives with base lengths and increments \(\Delta_i\) | T08, T09, T10 | Sumset interval, modular orbit, or prescribed-length path | Branching or cyclic overlaps must be reduced to serial form before using additivity |
| **C12** | Endpoint and attachment constraints on paths | Which internal or endpoint vertices may meet the outside graph | T07, T08, T17 | Forced endpoint attachment, forbidden chord, or local cycle | Length data alone cannot determine endpoint compatibility |
| **C13** | Simultaneous realizability of paths | Vertex-disjointness, compatible endpoints, and preservation of simplicity | T07, T10, T15 | A jointly realized path package or a concrete collision | Independent existence statements do not imply joint realization |

### 3.4 Local configurations, overlap, decomposition, and symmetry

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **D01** | Attachment pattern to a fixed motif | Subsets or ordered tuples of motif vertices adjacent to an outside vertex/path | T07, T17 | Legal label, forbidden local cycle, or finite state | A bounded motif sees only bounded-radius geometry |
| **D02** | Finite local type | Isomorphism class with marked terminals, degrees, and local response data | T07, T16, T17 | Finite alphabet for counting or case analysis | The type must include every datum later used for gluing |
| **D03** | Star, fan, and high-degree neighborhood structure | Center, ordered or typed neighbors, ports, and pair compatibilities | T03, T07, T15 | Fan certificate, forced local configuration, or bounded deficit | Different fans can overlap and reuse the same paying incidence |
| **D04** | Matching-versus-star concentration | Auxiliary incidence graph on demands and shared resources | T07, T14, T15 | Large matching, large star, or bounded load | The auxiliary pattern must lift to the intended graph configuration |
| **D05** | Overlap pattern of local witnesses | Intersection graph or hypergraph of supports | T10, T11, T15 | Disjoint subfamily, connected cluster, or overload | Pairwise overlap data may miss higher-order intersections |
| **D06** | Minimal connected overlap obstruction | Inclusion-minimal connected family where additivity or realization fails | T10, T16 | A bounded obstruction, serial system, or separating interface | Minimality gives structure but not automatically bounded size |
| **D07** | Symmetry and equal-response configurations | Automorphisms, equal length increments, or identical boundary signatures | T09, T16, T17 | Orbit reduction, symmetric alternative, or canonical swap | Symmetry can preserve the obstruction instead of resolving it |
| **D08** | Canonical structural decomposition | Deterministic ordering of pieces, supports, and attachment data | T04, T16 | Unique ledger, strict tie-breaker, or no-overcount partition | Canonicality must be invariant under relabelling or explicitly label-relative |
| **D09** | Gluing realizability | Compatibility of two boundaried pieces and uniqueness of reconstructed labelled graph | T05, T15, T16 | Injective reconstruction or proof that a state tuple is unrealizable | Local state counts cannot be multiplied without this compatibility check |
| **D10** | Bounded exceptional configuration | A fixed-size marked graph satisfying the residual hypotheses | T07, T17 | Exact closure certificate or explicit surviving case | Finite closure is only as exhaustive as the encoded state space |

### 3.5 Criticality, reduction, and replacement

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **E01** | Extremal counterexample status **(proof state)** | Minimality under \((n,m)\) or a refined well-founded order | T02, T16 | Every strictly smaller admissible graph satisfies the theorem | Equal-size transformations require a refined order or canonical potential |
| **E02** | Proper-subgraph exclusion | No proper subgraph retains all counterexample hypotheses | T02, T03, T04 | Core exclusion, edge/vertex criticality, or connectedness | The retained hypotheses must be verified after deletion |
| **E03** | Edge- or vertex-deletion criticality | Effect of deleting each edge or vertex on the defining property | T02, T03 | Tight endpoint degree, essential edge, or restored target | Criticality for one operation need not imply criticality for another |
| **E04** | Safe suppression and local simplification | Invariance of the hypotheses and target under a local reduction | T03, T05, T08 | Smaller graph, forced cycle, or proof that suppression is forbidden | Exact-length problems make suppression especially delicate |
| **E05** | Replacement irreducibility **(predicate-relative)** | No proper boundaried piece has a smaller context-equivalent representative | T02, T03, T05 | Smaller equivalent piece or proof of local irreducibility | Requires a complete response signature and compatible boundary degrees |
| **E06** | Quotient distinguishability **(predicate-relative)** | Whether identifying states or terminals changes some contextual response | T05, T11, T16 | Distinguishing context, defective quotient, or valid quotient | A quotient that preserves local tests may fail in a global context |
| **E07** | Canonical descent under neutral moves | A well-founded secondary order on equal-size decompositions or signatures | T02, T16 | Strict decrease for same-size replacement | The order must be preserved by all surrounding contexts used in the proof |
| **E08** | Peelability | Existence of a removable local unit whose deletion preserves the residual invariant | T03, T19 | Shorter ledger and terminating descent | Every peel needs a preservation lemma and a monotone measure |
| **E09** | Completion or defect relative to a target **(predicate-relative)** | A partial structure either extends to \(\mathcal Q\) or exposes a failed response coordinate | T05, T07, T08 | Target witness, target-defective interface, or unresolved state | Route each defect to replacement, counting, or another stated closure |

### 3.6 Independence, dependence, and support

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **F01** | Supply of local structural tests | Family of wedges, attachments, pairs, or corridors that can test the target predicate | T07, T08, T15 | Lower bound on candidate tests | Candidate supply is not independent-test supply |
| **F02** | Rank of a local-test family | Rank of incidence/response vectors or maximum independent subfamily | T11 | Basis, rank bound, or full-rank certificate | Rank depends on the chosen representation of responses |
| **F03** | Minimal dependence circuit | Inclusion-minimal dependent subfamily | T10, T11 | Circuit relation with connected or controlled support | Algebraic minimality does not by itself imply geometric locality |
| **F04** | Geometric support of dependence | Union of vertices, edges, contexts, or boundary coordinates used by a relation | T05, T10, T11 | Proper local support, enlarged repair support, or whole-graph dependence | Dependence can smear over the whole graph without a localization theorem |
| **F05** | Separation of testers | Disjoint supports or outside contexts that distinguish different coordinates | T05, T10, T11 | Independent translates or polarized test family | Disjoint contexts must still be simultaneously compatible with the graph |
| **F06** | Cancellation and repair structure | Composite relations in which local responses cancel, together with a repair network | T08, T10, T11 | Smaller support, structured corridor, or exact global profile | Cancellation may hide in a larger support and defeat naive local rank counting |
| **F07** | Full-rank versus structured rank loss | Dichotomy between many independent tests and a localized dependence | T10, T11, T12 | Information cost or a structural obstruction | The dichotomy needs an explicit route for whole-support dependence |
| **F08** | Periodicity of a response family | Repetition of boundary or length responses under additive increments | T09, T16 | Finite response class, arithmetic hit, or compressible repetition | Eventual periodicity must be proved at the interface resolution actually used |

### 3.7 Counting, information, and exact reconstruction

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **G01** | Size of a labelled graph class | Number of graphs with fixed \(n,m\), degree constraints, or marked decomposition | T12 | Global description budget | A coarse superset count may leave too much room for a contradiction |
| **G02** | Number of legal local states | Cardinality of attachment, interface, or neighborhood types | T07, T12, T17 | Bits saved per constrained local piece | Local counts multiply only after dependence and gluing are controlled |
| **G03** | Conditional information of local tests | Logarithm of fibre sizes or conditional state counts | T11, T12 | Additive information cost or detected correlation | Entropy notation does not create probabilistic independence |
| **G04** | Dominant or repetitive local type | Largest fibre in a finite partition of vertices or pieces | T12 | Linear homogeneous subfamily by pigeonhole | A frequent type can remain geometrically concentrated or mutually overlapping |
| **G05** | Additivity versus correlation of constraints | Comparison between joint state count and product of conditional counts | T10, T11, T12 | Valid product bound or connected overlap obstruction | Pairwise independence need not imply joint independence |
| **G06** | Injective reconstruction from local data | Map from decomposition states to labelled graphs | T05, T15 | No-overcounting theorem and valid global count | Surjectivity and injectivity answer different counting obligations |
| **G07** | Resource multiplicity and double counting | Maximum number of demands charged to one vertex, edge, token, or incidence | T14, T15 | Capacity bound, partition identity, or overload witness | A bounded average multiplicity permits exceptional high-load fibres |
| **G08** | Asymptotic versus finite-order behavior | Error terms, explicit thresholds, and exact small-\(n\) ranges | T12, T17 | Large-order contradiction plus finite residual list | An asymptotic inequality cannot close unverified small orders |
| **G09** | Density of a packed pattern | Packing number divided by \(n\), with local label costs | T06, T12 | Density cap or dense residual | Dense residuals are precisely where independence assumptions are most fragile |

### 3.8 Potentials, discharging, demand, and descent

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **H01** | Deficiency–surplus balance of a region | Linear combination of boundary deficit, internal excess, and order | T01, T13 | Numerical surplus, deficit, or zero-balance identity | The chosen coefficients must match the later local transfer rules |
| **H02** | Additive or superadditive charge | Potential \(\mathcal N(X)\) compatible with a decomposition of \(X\) | T04, T13 | Global-to-local reduction of a negative total | Cross-boundary terms must be assigned exactly once |
| **H03** | Connected negative support | Component or inclusion-minimal connected region with negative charge | T04, T10, T13 | Concrete local obstruction for structural analysis | Localization forgets correlations crossing the selected boundary |
| **H04** | Feasibility of a local discharge | Transfer rules from suppliers to deficit vertices or pieces | T13, T15 | Nonnegative final charge or an overloaded receiver | A discharge proves only the inequality encoded by its rules |
| **H05** | Load and saturation | Load \(L(w)\) compared with capacity \(c(w)\) | T13, T14, T15 | Unsaturated global bound or saturated local witness | Saturation usually starts a new structural case rather than ending the proof |
| **H06** | Incidence payment of deficits | Assignment of each positive deficit to distinct or bounded-multiplicity resources | T14, T15 | Injection, matching, half-credit ledger, or unpaid unit | Overlapping certificates can invalidate distinctness |
| **H07** | Flow–cut structure of structural support | Integral flow or matching in the demand–support network | T10, T14 | Covering flow, alternating path, or deficient cut | The auxiliary cut needs a graph-theoretic interpretation and bounded interface |
| **H08** | Total exceptional mass | Sum of deficits or charges over an exceptional family | T13, T15 | Sublinear or bounded exceptional contribution | A small total does not identify which individual configurations close |
| **H09** | Competition between two budgets | Lower bound on required tests versus upper bound on graph states or supply | T01, T11, T12, T13 | Counting contradiction or narrow residual regime | Both budgets must use the same class and non-overlapping accounting |
| **H10** | Finite demand descent | Well-founded measure on unresolved demands and one-unit peel steps | T14, T19 | Termination at an empty or explicitly classified terminal state | Each step must preserve interface response and cannot create new unrecorded demand |

### 3.9 Finite and externally certified structure

| ID | Structural property | Observable or formulation | Textbook techniques | Certificate or conclusion | Limitation and usual companion |
| --- | --- | --- | --- | --- | --- |
| **I01** | Finite configuration space | Explicit list of bounded graphs, labels, attachments, or response states | T07, T17 | Exhaustive table of legal and illegal cases | The encoding and generation rules are part of the theorem |
| **I02** | Isomorphism and canonical representative | Canonical label or orbit representative of each finite state | T16, T17 | Duplicate-free enumeration | Marked boundaries and orientations must be included in isomorphism tests |
| **I03** | Exact collision or compatibility condition | Integer equalities, endpoint conflicts, or jointly unrealizable state packages | T15, T17 | Exact contradiction or surviving finite list | Floating-point or asymptotic substitutes are insufficient |
| **I04** | Small-order residual | Finite set of graph orders or parameter values outside an asymptotic proof | T17 | Direct enumeration, explicit theorem, or separate proof | The threshold connecting asymptotic and finite regimes must be explicit |
| **I05** | Reproducible computational certificate | Input schema, generator, verifier, output hash/table, and semantic theorem | T17 | Independently checkable finite lemma | Source code without a semantic link to the mathematical objects is not a certificate |
| **I06** | Dependence on an external structure theorem | Exact hypotheses and conclusion of the imported theorem | T18 | Certified reduction to a restricted graph class | The proof inherits the theorem's scope, conventions, and verification status |

## 4. Reverse technique index

This index answers the inverse question: given a familiar proof move, which
properties can it evaluate?

| Technique | Principal property IDs | Typical output |
| --- | --- | --- |
| Handshake and incidence identities | A02–A05, A09–A14, H01 | Exact numerical relation |
| Minimal-counterexample selection | E01–E03, E05, E07 | Criticality or strict descent |
| Deletion and suppression | A07–A08, B02, C02, E02–E04 | Smaller graph or restored witness |
| Core, component, block, and ear decomposition | A07, B01–B04, C06, H02–H03 | Structured piece or separator |
| Boundary signatures and contextual equivalence | B05–B09, E05–E06, E09 | Replacement, defect, or distinguishing context |
| Maximal packing | C08–C10, G09 | Pattern-free remainder |
| Local attachment and neighborhood classification | A03, A08–A10, C12, D01–D04 | Finite local type or forced configuration |
| Rooted returns, theta graphs, ears, and cycle space | C01–C07, E09 | Cycle or path certificate |
| Congruences, sumsets, and periodicity | C04–C05, C11, F08 | Length hit or periodic response |
| Uncrossing and minimal-obstruction extraction | B08, C11, D05–D06, F03–F07 | Serial support or bounded obstruction |
| Rank and circuit analysis | A12, F01–F07, G03, H09 | Independent family or dependence certificate |
| Counting, entropy, and pigeonhole | A02, A14, G01–G09, H09 | State-space contradiction or homogeneous family |
| Discharging and potential localization | A11, H01–H05, H08 | Nonnegative charge or overloaded support |
| Matching, flow, and demand–supply accounting | B09, D04, H05–H07, H10 | Assignment, deficient cut, or terminal demand |
| Double counting and injective reconstruction | A09–A10, D09, G06–G07, H06 | Exact capacity or no-overcount theorem |
| Symmetry and canonicalization | D07–D08, E07, F08, I02 | Orbit reduction or strict tie-break |
| Finite exact enumeration | D01–D02, D10, G08, I01–I05 | Machine-checkable finite closure |
| External structure theorem | C08, I06 | Entry into a restricted class |

## 5. Translation of the current EG technique rows

The following table converts the manuscript-specific row names in
`structural_survey.md` into reusable moves. The rightmost column gives the
properties that the move actually evaluates, rather than every invariant it
uses as a hypothesis.

| Current EG row | Problem-independent textbook formulation | Direct property IDs |
| --- | --- | --- |
| Edge-rooted Mersenne returns | Root a cycle at an edge and translate the allowed cycle-length set by one | C02–C04 |
| Lexicographically minimal counterexample | Extremal selection followed by deletion-criticality and proper-subgraph exclusion | E01–E03, A06 |
| Boundaried target response and replacement | Compare finite interfaces in all compatible contexts and replace an equivalent piece | B05–B07, E05–E07 |
| \(P_{13}\)-free theorem and maximal packing | Apply a forbidden-induced-subgraph theorem, pack maximal witnesses, and analyze the excluded remainder | C08–C10, I06 |
| Finite attachment-label algebra | Enumerate attachment types to a fixed induced motif and reject types with immediate local witnesses | D01–D02, C12, I01–I03 |
| Degree-surplus routing and near-cubic reduction | Measure excess above regularity; extract concentrated neighborhoods or enter a near-regular class | A05–A06, A14, D03–D04 |
| Skeleton counting and entropy | Bound the labelled ambient class and charge independent local constraints against it | G01–G05, G09 |
| Hot/cold split | Split local tests according to whether they contribute conditional information | F07, G03–G05 |
| Overlap uncrossing, corridors, and increment arithmetic | Extract a minimal dependence, uncross it into serial paths, and analyze the sumset of length increments | C11, D05–D06, F03–F08 |
| Deficiency, stub supply, and wedge counting | Convert degree requirements into boundary incidence and local path-test supply | A09–A11, H01 |
| Obstruction tensor and rank split | Encode local tests as response coordinates and split into a basis case or a circuit case | F01–F07 |
| Two-budget routing | Compare the information demanded by local tests with the state or incidence budget available globally | G01–G07, H09 |
| Net charge and localization | Define an additive potential and pass from a negative total to a connected negative piece | H01–H03 |
| Type A receiver analysis | Discharge a subcubic piece; an overloaded receiver exposes a bounded local obstruction | H04–H06, D10 |
| Type B fan analysis | Decompose high-degree neighborhoods into marked fans and charge their deficits by incidences | D03, H06, H08 |
| Route-8 demand descent | Form a demand–support network, peel canonical units, and classify the terminal low-support obstruction | B09, E08, H07, H10 |
| Dense-residual exact closures | Replace asymptotic independence by exact collision, symmetry, canonicalization, and injective gluing | C12–C13, D07–D10, G06, I01–I04 |

## 6. Exhaustive EG invariant crosswalk

The manuscript lists 38 invariants in its reverse impact index. Every entry is
accounted for below. "Proof state" means that the item governs the argument
rather than defining an intrinsic unmarked-graph invariant. "Derived response"
means that it is structural only after a target predicate and interface
encoding have been fixed.

| Inv. | Manuscript invariant | General property IDs | Classification and textbook reading |
| ---: | --- | --- | --- |
| 1 | Mersenne-return target algebra | C02–C04 | Rooted cycle completion and arithmetic translation of a length set |
| 2 | Minimal proper-subgraph condition | A07, E01–E02 | Proof state yielding core exclusion |
| 3 | Edge-deletion criticality | E03 | Criticality under a local graph modification |
| 4 | High-degree independence | A06 | Adjacency structure inside an exceptional degree class |
| 5 | No passive degree-two storage | A08, E04 | Suppression and control of subdivided corridors |
| 6 | Replacement dominance | B07, E05, E07 | Derived response plus well-founded replacement order |
| 7 | Lumpability defect | B07, E06 | Derived response; failure of quotient states to be context-equivalent |
| 8 | Hereditary target-uncompressibility | E05 | Predicate-relative irreducibility inherited by proper supports |
| 9 | Minimum edge count | A01–A04 | Direct extremal size bound from minimum degree |
| 10 | Sparse upper envelope | A02, A13 | Global edge-count or hereditary sparsity bound |
| 11 | Cycle-rank constraint | A12 | Binary cycle-space dimension |
| 12 | Laman slack identity | A12–A13, H09 | Linear relation between cycle rank, size, and sparsity slack; not a claim of full Laman sparsity |
| 13 | Surplus–rank relation | A05, A12, H01 | Conversion between degree excess, cycle rank, and potential |
| 14 | High-degree surplus bound | A05–A06, A14, H08 | Near-regularity or controlled exceptional mass |
| 15 | Near-cubic edge count | A02, A14, G01 | Size of a near-regular labelled graph class |
| 16 | Certificate-marked fan degree | A08, D03, I05 | Finite neighborhood certificate at a high-degree center |
| 17 | Spectral feasibility mask | C01, C04, D02 | Feasibility of connector-length states; this is not adjacency-eigenvalue spectral graph theory |
| 18 | Spectral equality branch | C01, D07 | Equal connector-length response and symmetry |
| 19 | Spectral surplus branch | A05, C01 | Connector feasibility with excess-degree supply |
| 20 | Low \(P_{13}\) density | C08–C09, G09 | Density of a packed forbidden induced pattern |
| 21 | Forced remainder | C09–C10 | Size and existence of the excluded remainder |
| 22 | \(P_{13}\)-free piece condition | C08, C10 | Hereditary induced-subgraph exclusion in remainder pieces |
| 23 | Window stub capacity | A10, B09 | Cross-region incidence capacity |
| 24 | Remainder deficiency density | A11, H01 | Boundary deficit per remainder vertex |
| 25 | Legal \(P_{13}\) labels | D01–D02, I01–I02 | Finite attachment algebra to a fixed motif |
| 26 | Two-step obstruction density | A09, F01 | Density of wedge-based local testers |
| 27 | Flatness entropy cost | G02–G03 | Conditional information consumed by an independent test |
| 28 | Raw piece-obstruction supply | A09, F01 | Candidate-test lower bound before rank correction |
| 29 | Obstruction-rank compression ratio | F02, F07, H09 | Ratio of independent tests to raw test supply |
| 30 | Two-path criterion | C05 | Target cycle formed from compatible internally disjoint paths |
| 31 | Theta closure | C05 | Cycle alternatives inside a theta subgraph |
| 32 | Ear closure | C06 | Target response under ear addition |
| 33 | Symmetric difference | C07 | Cycle-space cancellation and recombination |
| 34 | Rank-one target support | F03–F04 | Minimal dependence and its geometric support |
| 35 | Composite cancellation | F06 | Higher-order response cancellation and repair support |
| 36 | Odd response support nonempty | C04, F01 | Parity-sensitive response tester |
| 37 | No common response support | F05 | Separation of tester contexts |
| 38 | Polarized response-support transport | F05, F07 | Transport of separated coordinates to an independent family or dependence obstruction |

The crosswalk is a completeness audit of the structures asserted and used by
the manuscript. Mathematical validation of the lemmas producing those
invariants is a separate task. The implementation-status questions are tracked
in [`Assembly_node_audit.md`](../Assembly_node_audit.md).

## 7. What the exhaustive map says about the EG architecture

The proof uses four interacting structural channels.

1. **Length structure.** Rooted returns, two-path configurations, theta
   subgraphs, ears, and corridor increments test the prescribed cycle-length
   set.
2. **Interface structure.** Boundary degree data and contextual response
   determine whether a local piece can be distinguished, replaced, or
   compressed.
3. **Information structure.** Local attachment and wedge tests either have
   sufficient rank to consume the labelled graph budget or have a dependence
   with geometric support.
4. **Degree-flow structure.** Deficiency and surplus are localized by a
   potential, then resolved through receivers, fans, incidence payments, and
   finite descent.

The hard compatibility obligations occur between channels. A path-length
certificate must be simple and jointly realizable. A rank circuit must have a
usable geometric support. A local state count must glue injectively. A charge
payment must use distinct or bounded-multiplicity incidences. A replacement
must preserve the complete boundary response. These obligations explain why a
single binary coverage matrix is too coarse for this proof.

## 8. Major graph-structure families outside the EG survey

The following families are standard parts of a broader graph-problem survey,
but they are not materially evaluated by the EG architecture described above.
They should be added as separate modules when a new problem requires them.

| Family outside current scope | Typical properties | Standard techniques to add |
| --- | --- | --- |
| Planarity and surface topology | Planarity, genus, faces, crossings | Embeddings, Euler's formula, duality, discharging on faces |
| Minors and width | Excluded minors, treewidth, pathwidth, branchwidth | Minor operations, tree decompositions, dynamic programming, structure theorems |
| Coloring and perfectness | Chromatic number, list coloring, clique and independence numbers | Greedy/color-critical arguments, perfect graph methods, probabilistic bounds |
| Matchings and factors as primary structure | Matching number, perfect matchings, \(f\)-factors | Hall, Tutte, augmenting paths, blossom/factor theory |
| Covering and domination | Vertex cover, edge cover, domination, transversal parameters | LP duality, kernelization, local exchange, hypergraph transversals |
| Expansion and cuts at scale | Cheeger constants, separators, expansion profiles | Isoperimetry, multicommodity flow, separator theorems |
| Eigenvalue spectral graph theory | Adjacency/Laplacian spectra, spectral gap, interlacing | Rayleigh quotients, trace methods, interlacing, expander mixing |
| Random and pseudorandom structure | Concentration, quasirandomness, thresholds | First/second moment, martingales, regularity and containers |
| Homomorphisms and logical structure | Cores, homomorphism order, definability | Algebraic graph theory, finite model theory, constraint satisfaction |
| Directed, weighted, or temporal structure | Strong connectivity, flows, weighted distance, temporal reachability | Arborescences, min-cost flow, potential reweighting, time-expanded graphs |
| Algorithmic and parameterized complexity | Recognition, construction, fixed-parameter tractability | Reductions, kernelization, bounded-width algorithms, approximation |

These omissions provide the correct boundary of the present claim: the master
tables cover every structural coordinate used by the EG proof in generalized
language, while this final catalog identifies the principal directions needed
for a graph-theory-wide handbook.
