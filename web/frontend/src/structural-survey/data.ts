/**
 * Problem-independent structural coordinates, followed by the editorial
 * crosswalk that places the Erdős–Gyárfás manuscript on those coordinates.
 * Mathematical statements, nodes, result titles, and pages still come from the
 * extracted proof document; this file only names the comparison vocabulary.
 */

export const STRUCTURAL_TECHNIQUES = [
  { id: "T01", name: "Direct invariant calculation", move: "Apply degree sums, incidence identities, or rank identities." },
  { id: "T02", name: "Extremal selection", move: "Choose a smallest counterexample and exploit strict descent." },
  { id: "T03", name: "Local graph modification", move: "Delete, suppress, split, glue, or replace a local piece." },
  { id: "T04", name: "Core and connectivity decomposition", move: "Peel low-degree vertices or decompose into components, blocks, cuts, and ears." },
  { id: "T05", name: "Boundary-interface analysis", move: "Mark terminals, record boundary data, and compare outside contexts." },
  { id: "T06", name: "Maximal packing", move: "Pack disjoint witnesses and study the excluded remainder." },
  { id: "T07", name: "Local configuration analysis", move: "Classify bounded neighborhoods, attachments, fans, and paths." },
  { id: "T08", name: "Path–cycle and cycle-space analysis", move: "Root cycles, combine paths, add ears, or take symmetric differences." },
  { id: "T09", name: "Arithmetic of lengths", move: "Use parity, congruences, sumsets, intervals, or periodicity." },
  { id: "T10", name: "Uncrossing and minimal obstruction", move: "Choose a minimal failure and uncross its intersecting supports." },
  { id: "T11", name: "Linear-algebraic rank", move: "Encode local tests as coordinates and extract a basis or circuit." },
  { id: "T12", name: "Counting and information", move: "Use labelled enumeration, pigeonhole, conditional counting, or entropy." },
  { id: "T13", name: "Potential and discharging", move: "Define charge, redistribute it locally, and isolate overload or negative support." },
  { id: "T14", name: "Demand–supply and flow", move: "Use an incidence network, matching, alternating paths, or flow–cut." },
  { id: "T15", name: "Double counting and injection", move: "Partition contributions, control multiplicity, or reconstruct injectively." },
  { id: "T16", name: "Symmetry and canonicalization", move: "Choose canonical representatives and break equal-size ties." },
  { id: "T17", name: "Finite exact certification", move: "Enumerate a finite state space and retain a checkable certificate." },
  { id: "T18", name: "External structural theorem", move: "Invoke a fixed classification or exclusion theorem with exact hypotheses." },
  { id: "T19", name: "Peeling and finite descent", move: "Remove one certified unit while preserving a decreasing invariant." },
] as const;

export type TechniqueId = (typeof STRUCTURAL_TECHNIQUES)[number]["id"];

export interface StructuralProperty {
  id: string;
  name: string;
  observable: string;
  techniques: readonly TechniqueId[];
  certificate: string;
  caveat: string;
}

export interface StructuralPropertyGroup {
  id: string;
  title: string;
  properties: readonly StructuralProperty[];
}

export const STRUCTURAL_PROPERTY_GROUPS = [
  {
    id: "size-degree",
    title: "Size, degree, sparsity, and local incidence",
    properties: [
      { id: "A01", name: "Order", observable: "Number of vertices.", techniques: ["T01", "T02"], certificate: "An induction parameter or finite-size threshold.", caveat: "Order contains no incidence information." },
      { id: "A02", name: "Size and edge density", observable: "Number of edges and density relative to order.", techniques: ["T01", "T12"], certificate: "A sparse/dense branch or counting budget.", caveat: "Equal density permits different topology." },
      { id: "A03", name: "Degree sequence and classes", observable: "Degree multiset and threshold degree classes.", techniques: ["T01", "T07", "T15"], certificate: "Degree-class counts and local case splits.", caveat: "The sequence omits adjacency between classes." },
      { id: "A04", name: "Minimum and maximum degree", observable: "Extremal vertex degrees.", techniques: ["T01", "T02", "T04"], certificate: "A core or bounded/high-degree branch.", caveat: "Extremes do not locate exceptional vertices." },
      { id: "A05", name: "Excess above a degree baseline", observable: "Degree sum above a fixed regular baseline.", techniques: ["T01", "T13", "T15"], certificate: "Distance from regularity and a supply of excess incidences.", caveat: "Aggregate excess may be concentrated." },
      { id: "A06", name: "Distribution of high-degree vertices", observable: "Adjacency and distances inside a threshold degree class.", techniques: ["T02", "T03", "T07"], certificate: "Independence, bounded clustering, or a fan.", caveat: "A surplus bound alone gives no separation." },
      { id: "A07", name: "Core number and degeneracy", observable: "Largest nonempty minimum-degree core and a peeling order.", techniques: ["T04", "T19"], certificate: "A core, elimination order, or core exclusion.", caveat: "Core data does not record target cycles." },
      { id: "A08", name: "Degree-two chains and subdivision storage", observable: "Maximal paths with degree-two internal vertices.", techniques: ["T03", "T04", "T08"], certificate: "Safe suppression, a corridor, or a critical cycle.", caveat: "Suppression may change prescribed lengths." },
      { id: "A09", name: "Length-two path or wedge supply", observable: "Count of two-edge paths, possibly with endpoint restrictions.", techniques: ["T01", "T07", "T15"], certificate: "A lower bound on local path testers.", caveat: "Wedges may overlap heavily." },
      { id: "A10", name: "Incidence between two regions", observable: "Crossing-edge counts and their bipartite incidence graph.", techniques: ["T01", "T14", "T15"], certificate: "A join identity, capacity bound, or overload.", caveat: "Counts omit attachment geometry." },
      { id: "A11", name: "Boundary degree deficit", observable: "Missing internal degree at marked boundary vertices.", techniques: ["T01", "T05", "T13"], certificate: "Required external incidence or unpaid demand.", caveat: "The baseline and boundary must survive replacement." },
      { id: "A12", name: "Cycle rank", observable: "Dimension of the binary cycle space.", techniques: ["T01", "T04", "T11"], certificate: "The number of independent cycle coordinates.", caveat: "Rank does not record cycle lengths." },
      { id: "A13", name: "Global sparsity slack", observable: "Linear edge-count slack, globally or over every subgraph.", techniques: ["T01", "T02", "T12"], certificate: "An edge envelope or violating subgraph.", caveat: "One global value does not certify hereditary sparsity." },
      { id: "A14", name: "Near-regularity", observable: "Small degree excess or a bounded exceptional set.", techniques: ["T01", "T12", "T13"], certificate: "A reduced counting class with controlled exceptions.", caveat: "Near-regularity does not prevent large separators." },
    ],
  },
  {
    id: "connectivity",
    title: "Connectivity, cuts, and interfaces",
    properties: [
      { id: "B01", name: "Connected-component structure", observable: "Components of the graph or an induced remainder.", techniques: ["T04", "T13"], certificate: "A component reduction or localized negative sum.", caveat: "Deleted regions may carry interface constraints." },
      { id: "B02", name: "Bridges and edge cuts", observable: "Bridges, bonds, and edge connectivity.", techniques: ["T02", "T03", "T04"], certificate: "Bridgelessness, a cut, or an edge-block decomposition.", caveat: "Edge connectivity does not control vertex bottlenecks." },
      { id: "B03", name: "Cut vertices, blocks, and separators", observable: "Block–cut tree and components behind a separator.", techniques: ["T04", "T05", "T10"], certificate: "A bounded interface or decomposition tree.", caveat: "Targets may depend on terminal pairing across the cut." },
      { id: "B04", name: "Multiple disjoint connections", observable: "Maximum internally disjoint paths between terminals.", techniques: ["T04", "T08", "T14"], certificate: "Disjoint paths or a separating cut.", caveat: "Disjointness does not prescribe lengths." },
      { id: "B05", name: "Boundary of a region", observable: "Marked vertex/edge boundary, terminal labels, and degrees.", techniques: ["T01", "T05"], certificate: "A finite interface and exact incidence count.", caveat: "Boundary size omits pairing and path lengths." },
      { id: "B06", name: "Boundaried graph type", observable: "Ordered terminals with degree and incidence data.", techniques: ["T05", "T16"], certificate: "A composable local object.", caveat: "The interface must retain all downstream data." },
      { id: "B07", name: "Contextual response equivalence", observable: "Agreement of two boundaried graphs in every compatible context.", techniques: ["T03", "T05", "T16"], certificate: "Safe replacement or a distinguishing context.", caveat: "Universal response may have infinitely many states." },
      { id: "B08", name: "Locality of a witness or obstruction", observable: "Smallest connected support carrying the witness.", techniques: ["T05", "T10", "T11"], certificate: "A proper support, bounded interface, or whole-graph obstruction.", caveat: "Minimal support need not be bounded." },
      { id: "B09", name: "Interface demand and supply", observable: "Relation between boundary demands and legal supporting incidences.", techniques: ["T14", "T15"], certificate: "A flow, deficient cut, overload, or uncovered demand.", caveat: "Auxiliary flow must lift to graph structure." },
    ],
  },
  {
    id: "paths-cycles",
    title: "Paths, cycles, and length structure",
    properties: [
      { id: "C01", name: "Simple paths and attainable lengths", observable: "Set of simple path lengths between marked vertices.", techniques: ["T04", "T07", "T08"], certificate: "A prescribed-length path or excluded interval.", caveat: "Walk lengths cannot replace simple-path lengths." },
      { id: "C02", name: "Edge-rooted return lengths", observable: "Return-path lengths after removing a marked edge.", techniques: ["T03", "T08"], certificate: "A cycle-length certificate rooted at that edge.", caveat: "The transform does not force a return to exist." },
      { id: "C03", name: "Cycle-length spectrum", observable: "Set of lengths of simple cycles.", techniques: ["T08", "T09", "T11"], certificate: "A target length or an avoidance bound.", caveat: "Cycle-space addition need not preserve one cycle." },
      { id: "C04", name: "Arithmetic class of lengths", observable: "Parity, residues, translated targets, or periodic responses.", techniques: ["T08", "T09"], certificate: "A modular hit, obstruction, or periodic class.", caveat: "Congruence is coarser than exact length." },
      { id: "C05", name: "Two-path and theta structure", observable: "Internally disjoint paths with common endpoints.", techniques: ["T08", "T09"], certificate: "Several cycles with controlled length sums.", caveat: "Separately counted paths must be compatible." },
      { id: "C06", name: "Ear structure", observable: "A path attached to a base subgraph only at its ends.", techniques: ["T04", "T08"], certificate: "An ear decomposition or new cycle.", caveat: "Ears control connectivity more than exact length." },
      { id: "C07", name: "Cycle-space interaction", observable: "Binary incidence vectors and symmetric differences.", techniques: ["T08", "T11"], certificate: "A cancellation relation or support decomposition.", caveat: "A difference may be several disjoint cycles." },
      { id: "C08", name: "Induced paths and hereditary exclusion", observable: "Presence of an induced path or membership in a path-free class.", techniques: ["T06", "T07", "T18"], certificate: "A fixed induced pattern or restricted remainder.", caveat: "The input theorem may be target-specific." },
      { id: "C09", name: "Packing number of a fixed pattern", observable: "Maximum disjoint family of pattern copies.", techniques: ["T06", "T12", "T15"], certificate: "A packing, its density, and a remainder.", caveat: "Maximal and maximum packings differ." },
      { id: "C10", name: "Structure of a packing remainder", observable: "Graph left after deleting a maximal packed family.", techniques: ["T04", "T06", "T07"], certificate: "An excluded-pattern remainder with component restrictions.", caveat: "Attachments can retain long-range dependence." },
      { id: "C11", name: "Serial corridors and path increments", observable: "Ordered path alternatives with base lengths and increments.", techniques: ["T08", "T09", "T10"], certificate: "A sumset interval, orbit, or prescribed length.", caveat: "Branching overlaps must first become serial." },
      { id: "C12", name: "Endpoint and attachment constraints", observable: "Allowed external contacts at path endpoints and interiors.", techniques: ["T07", "T08", "T17"], certificate: "Forced endpoints, forbidden chords, or a local cycle.", caveat: "Length alone does not give compatibility." },
      { id: "C13", name: "Simultaneous path realizability", observable: "Joint disjointness, endpoint compatibility, and simplicity.", techniques: ["T07", "T10", "T15"], certificate: "A realized path package or exact collision.", caveat: "Separate existence does not imply joint existence." },
    ],
  },
  {
    id: "local-structure",
    title: "Local configurations, overlap, decomposition, and symmetry",
    properties: [
      { id: "D01", name: "Attachment pattern to a fixed motif", observable: "Marked motif vertices met by an outside vertex or path.", techniques: ["T07", "T17"], certificate: "A legal label or forbidden local cycle.", caveat: "A fixed motif has bounded-radius vision." },
      { id: "D02", name: "Finite local type", observable: "Marked isomorphism class with degrees and local responses.", techniques: ["T07", "T16", "T17"], certificate: "A finite alphabet for counting and cases.", caveat: "The type must retain all gluing data." },
      { id: "D03", name: "Star, fan, and high-degree neighborhood", observable: "A center, typed neighbors, ports, and pair compatibilities.", techniques: ["T03", "T07", "T15"], certificate: "A fan certificate or bounded deficit.", caveat: "Fans can reuse the same incidence." },
      { id: "D04", name: "Matching-versus-star concentration", observable: "Auxiliary incidence graph on demands and resources.", techniques: ["T07", "T14", "T15"], certificate: "A large matching, star, or bounded load.", caveat: "The auxiliary pattern must lift to the graph." },
      { id: "D05", name: "Overlap pattern of local witnesses", observable: "Intersection graph or hypergraph of supports.", techniques: ["T10", "T11", "T15"], certificate: "A disjoint family, connected cluster, or overload.", caveat: "Pairwise overlap misses higher-order intersection." },
      { id: "D06", name: "Minimal connected overlap obstruction", observable: "Smallest connected family where realization or additivity fails.", techniques: ["T10", "T16"], certificate: "A bounded obstruction, serial system, or interface.", caveat: "Minimality alone gives no size bound." },
      { id: "D07", name: "Symmetry and equal response", observable: "Automorphisms, equal increments, or identical signatures.", techniques: ["T09", "T16", "T17"], certificate: "Orbit reduction, symmetric alternative, or canonical swap.", caveat: "Symmetry may preserve the obstruction." },
      { id: "D08", name: "Canonical structural decomposition", observable: "Deterministic ordering of pieces and attachment data.", techniques: ["T04", "T16"], certificate: "A unique ledger, strict tie-break, or partition.", caveat: "Canonicality must respect relabelling." },
      { id: "D09", name: "Gluing realizability", observable: "Compatibility and uniqueness of reconstructed boundaried pieces.", techniques: ["T05", "T15", "T16"], certificate: "Injective reconstruction or unrealizability.", caveat: "Local counts cannot multiply before this check." },
      { id: "D10", name: "Bounded exceptional configuration", observable: "A fixed-size marked graph satisfying residual hypotheses.", techniques: ["T07", "T17"], certificate: "Exact closure or an explicit surviving case.", caveat: "Completeness depends on the encoded state." },
    ],
  },
  {
    id: "criticality",
    title: "Criticality, reduction, and replacement",
    properties: [
      { id: "E01", name: "Extremal counterexample status", observable: "Minimality under a well-founded graph order.", techniques: ["T02", "T16"], certificate: "Every smaller admissible graph satisfies the theorem.", caveat: "Neutral moves need a secondary order." },
      { id: "E02", name: "Proper-subgraph exclusion", observable: "No proper subgraph retains all counterexample hypotheses.", techniques: ["T02", "T03", "T04"], certificate: "Core exclusion, criticality, or connectedness.", caveat: "Deletion must preserve every retained hypothesis." },
      { id: "E03", name: "Deletion criticality", observable: "Effect of deleting each edge or vertex.", techniques: ["T02", "T03"], certificate: "A tight degree, essential edge, or restored target.", caveat: "Criticality depends on the operation." },
      { id: "E04", name: "Safe suppression and simplification", observable: "Invariance under a local graph reduction.", techniques: ["T03", "T05", "T08"], certificate: "A smaller graph or proof that reduction is forbidden.", caveat: "Exact-length targets make suppression delicate." },
      { id: "E05", name: "Replacement irreducibility", observable: "Absence of a smaller context-equivalent boundaried representative.", techniques: ["T02", "T03", "T05"], certificate: "A smaller equivalent piece or local irreducibility.", caveat: "Requires a complete response signature." },
      { id: "E06", name: "Quotient distinguishability", observable: "Whether identifying states changes a contextual response.", techniques: ["T05", "T11", "T16"], certificate: "A distinguishing context, defect, or valid quotient.", caveat: "Local preservation may fail globally." },
      { id: "E07", name: "Canonical descent under neutral moves", observable: "A secondary order on equal-size decompositions.", techniques: ["T02", "T16"], certificate: "Strict decrease for a neutral replacement.", caveat: "The order must survive surrounding contexts." },
      { id: "E08", name: "Peelability", observable: "A removable unit preserving the residual invariant.", techniques: ["T03", "T19"], certificate: "A shorter ledger and terminating descent.", caveat: "Each peel needs preservation and monotonicity." },
      { id: "E09", name: "Completion or target defect", observable: "Whether a partial structure completes the target or fails a response coordinate.", techniques: ["T05", "T07", "T08"], certificate: "A target witness, defective interface, or residual.", caveat: "Every defect needs a declared consumer." },
    ],
  },
  {
    id: "dependence",
    title: "Independence, dependence, and support",
    properties: [
      { id: "F01", name: "Supply of local structural tests", observable: "Family of wedges, attachments, pairs, or corridors.", techniques: ["T07", "T08", "T15"], certificate: "A lower bound on candidate tests.", caveat: "Candidate supply is not independent supply." },
      { id: "F02", name: "Rank of a local-test family", observable: "Rank of response vectors or a maximum independent subfamily.", techniques: ["T11"], certificate: "A basis or full-rank certificate.", caveat: "Rank depends on the response representation." },
      { id: "F03", name: "Minimal dependence circuit", observable: "An inclusion-minimal dependent subfamily.", techniques: ["T10", "T11"], certificate: "A circuit with controlled support.", caveat: "Algebraic minimality need not be geometric locality." },
      { id: "F04", name: "Geometric support of dependence", observable: "Vertices, edges, contexts, and coordinates used by a relation.", techniques: ["T05", "T10", "T11"], certificate: "A local support, repair support, or global obstruction.", caveat: "Dependence can smear across the graph." },
      { id: "F05", name: "Separation of testers", observable: "Disjoint supports or contexts distinguishing coordinates.", techniques: ["T05", "T10", "T11"], certificate: "Independent translates or a polarized test family.", caveat: "Contexts must remain jointly compatible." },
      { id: "F06", name: "Cancellation and repair structure", observable: "Composite response relations and their repair network.", techniques: ["T08", "T10", "T11"], certificate: "A smaller support, corridor, or exact global profile.", caveat: "Cancellation may hide in a larger support." },
      { id: "F07", name: "Full rank versus structured rank loss", observable: "Dichotomy between independent tests and localized dependence.", techniques: ["T10", "T11", "T12"], certificate: "Information cost or a structural obstruction.", caveat: "Whole-support dependence needs its own route." },
      { id: "F08", name: "Periodicity of a response family", observable: "Repeated boundary or length response under additive increments.", techniques: ["T09", "T16"], certificate: "A finite response class, hit, or compression.", caveat: "Periodicity must hold at the used resolution." },
    ],
  },
  {
    id: "counting",
    title: "Counting, information, and exact reconstruction",
    properties: [
      { id: "G01", name: "Size of a labelled graph class", observable: "Count at fixed order, size, degree data, or decomposition.", techniques: ["T12"], certificate: "A global description budget.", caveat: "A coarse superset count may leave too much room." },
      { id: "G02", name: "Number of legal local states", observable: "Cardinality of attachment, interface, or neighborhood types.", techniques: ["T07", "T12", "T17"], certificate: "Bits saved per constrained piece.", caveat: "Local counts need gluing and independence." },
      { id: "G03", name: "Conditional information of local tests", observable: "Logarithm of conditional fibre sizes.", techniques: ["T11", "T12"], certificate: "Additive cost or detected correlation.", caveat: "Entropy notation does not create independence." },
      { id: "G04", name: "Dominant or repetitive local type", observable: "Largest fibre in a finite partition.", techniques: ["T12"], certificate: "A linear homogeneous subfamily.", caveat: "A frequent type may remain concentrated." },
      { id: "G05", name: "Additivity versus correlation", observable: "Joint state count compared with conditional products.", techniques: ["T10", "T11", "T12"], certificate: "A product bound or overlap obstruction.", caveat: "Pairwise independence need not be joint." },
      { id: "G06", name: "Injective reconstruction from local data", observable: "Map from decomposition states to labelled graphs.", techniques: ["T05", "T15"], certificate: "A no-overcounting theorem and valid count.", caveat: "Surjectivity and injectivity are separate." },
      { id: "G07", name: "Resource multiplicity and double counting", observable: "Demands charged to each vertex, edge, token, or incidence.", techniques: ["T14", "T15"], certificate: "A capacity bound, partition, or overload.", caveat: "Average multiplicity permits exceptional fibres." },
      { id: "G08", name: "Asymptotic versus finite-order behavior", observable: "Error terms, thresholds, and exact small orders.", techniques: ["T12", "T17"], certificate: "A large-order contradiction plus a finite residual.", caveat: "Asymptotics do not close small orders." },
      { id: "G09", name: "Density of a packed pattern", observable: "Packing number normalized by graph order.", techniques: ["T06", "T12"], certificate: "A density cap or dense residual.", caveat: "Dense regimes weaken independence." },
    ],
  },
  {
    id: "potentials",
    title: "Potentials, discharging, demand, and descent",
    properties: [
      { id: "H01", name: "Deficiency–surplus balance", observable: "Linear combination of boundary deficit, excess, and order.", techniques: ["T01", "T13"], certificate: "A surplus, deficit, or balance identity.", caveat: "Coefficients must match local transfers." },
      { id: "H02", name: "Additive or superadditive charge", observable: "A potential compatible with support decomposition.", techniques: ["T04", "T13"], certificate: "A global-to-local negative reduction.", caveat: "Boundary terms must be assigned once." },
      { id: "H03", name: "Connected negative support", observable: "A connected region with negative charge.", techniques: ["T04", "T10", "T13"], certificate: "A local obstruction for structural analysis.", caveat: "Localization can lose crossing correlations." },
      { id: "H04", name: "Feasibility of a local discharge", observable: "Transfer rules from suppliers to deficits.", techniques: ["T13", "T15"], certificate: "Nonnegative charge or an overloaded receiver.", caveat: "A discharge proves only its encoded inequality." },
      { id: "H05", name: "Load and saturation", observable: "Load compared with certified capacity.", techniques: ["T13", "T14", "T15"], certificate: "A global bound or saturated local witness.", caveat: "Saturation begins a structural case." },
      { id: "H06", name: "Incidence payment of deficits", observable: "Assignment to distinct or bounded-multiplicity resources.", techniques: ["T14", "T15"], certificate: "An injection, matching, or unpaid unit.", caveat: "Overlapping certificates may break distinctness." },
      { id: "H07", name: "Flow–cut structural support", observable: "Integral flow in the demand–support network.", techniques: ["T10", "T14"], certificate: "A flow, alternating path, or deficient cut.", caveat: "The cut needs a graph-realizable interface." },
      { id: "H08", name: "Total exceptional mass", observable: "Sum of deficits or charges over an exceptional family.", techniques: ["T13", "T15"], certificate: "A sublinear or bounded exceptional contribution.", caveat: "Small total mass does not close each member." },
      { id: "H09", name: "Competition between two budgets", observable: "Required tests compared with available states or supply.", techniques: ["T01", "T11", "T12", "T13"], certificate: "A counting contradiction or narrow residual.", caveat: "Both budgets must count the same class." },
      { id: "H10", name: "Finite demand descent", observable: "A well-founded measure and one-unit peel steps.", techniques: ["T14", "T19"], certificate: "Termination at an empty or classified state.", caveat: "Every peel must preserve interface response." },
    ],
  },
  {
    id: "certification",
    title: "Finite and externally certified structure",
    properties: [
      { id: "I01", name: "Finite configuration space", observable: "Explicit bounded graphs, labels, attachments, or states.", techniques: ["T07", "T17"], certificate: "An exhaustive legal/illegal table.", caveat: "The generator is part of the theorem." },
      { id: "I02", name: "Isomorphism and canonical representative", observable: "Canonical labels or orbit representatives.", techniques: ["T16", "T17"], certificate: "Duplicate-free enumeration.", caveat: "Boundaries and orientations belong in isomorphism." },
      { id: "I03", name: "Exact collision or compatibility", observable: "Integer equalities, endpoint conflicts, or unrealizable packages.", techniques: ["T15", "T17"], certificate: "An exact contradiction or surviving finite list.", caveat: "Asymptotic substitutes are insufficient." },
      { id: "I04", name: "Small-order residual", observable: "Finite orders outside an asymptotic argument.", techniques: ["T17"], certificate: "Direct enumeration or a separate finite proof.", caveat: "The transition threshold must be explicit." },
      { id: "I05", name: "Reproducible computational certificate", observable: "Input schema, generator, verifier, and semantic theorem.", techniques: ["T17"], certificate: "An independently checkable finite lemma.", caveat: "Code needs a semantic link to graph objects." },
      { id: "I06", name: "External structure theorem", observable: "Exact hypotheses and conclusion of an imported result.", techniques: ["T18"], certificate: "Reduction to a restricted graph class.", caveat: "The proof inherits the theorem's scope." },
    ],
  },
] as const satisfies readonly StructuralPropertyGroup[];

export type PropertyId = (typeof STRUCTURAL_PROPERTY_GROUPS)[number]["properties"][number]["id"];

export type SurveyStructuralProperty = Omit<StructuralProperty, "id"> & { id: PropertyId };

export interface EGInvariantBinding {
  number: number;
  propertyIds: readonly PropertyId[];
  techniqueIds: readonly TechniqueId[];
  primaryItem: string;
}

const eg = (
  number: number,
  propertyIds: readonly PropertyId[],
  techniqueIds: readonly TechniqueId[],
  primaryItem: string,
): EGInvariantBinding => ({ number, propertyIds, techniqueIds, primaryItem });

export const EG_INVARIANT_BINDINGS = [
  eg(1, ["C02", "C03", "C04"], ["T08", "T09"], "lem:return-equivalence"),
  eg(2, ["A07", "E01", "E02"], ["T02", "T03", "T04"], "lem:no-proper-core"),
  eg(3, ["E03"], ["T02", "T03"], "lem:deletion-critical"),
  eg(4, ["A06"], ["T02", "T03", "T07"], "lem:deletion-critical"),
  eg(5, ["A08", "E04"], ["T03", "T04"], "lem:stub-positive"),
  eg(6, ["B07", "E05", "E07"], ["T02", "T03", "T05", "T16"], "lem:replacement"),
  eg(7, ["B07", "E06"], ["T05", "T16"], "lem:context-universality"),
  eg(8, ["E05"], ["T02", "T03", "T05"], "cor:uncompressible"),
  eg(9, ["A01", "A02", "A03", "A04"], ["T01"], "lem:cycle-rank"),
  eg(10, ["A02", "A13"], ["T01", "T02"], "lem:sparse-upper-envelope"),
  eg(11, ["A12"], ["T01", "T11"], "lem:cycle-rank"),
  eg(12, ["A12", "A13", "H09"], ["T01"], "lem:near-cubic-budget"),
  eg(13, ["A05", "A12", "H01"], ["T01", "T13"], "lem:netcharge-superadd"),
  eg(14, ["A05", "A06", "A14", "H08"], ["T01", "T12", "T13", "T14", "T15"], "prop:nonnear-cubic-sharp-overload-routing"),
  eg(15, ["A02", "A14", "G01"], ["T01", "T12"], "lem:near-cubic-budget"),
  eg(16, ["A08", "D03", "I05"], ["T07", "T13", "T17"], "lem:fan-certificate"),
  eg(17, ["C01", "C04", "D02"], ["T07", "T09", "T17"], "lem:fan-certificate"),
  eg(18, ["C01", "D07"], ["T09", "T16", "T17"], "lem:fan-certificate"),
  eg(19, ["A05", "C01"], ["T01", "T07", "T13", "T17"], "lem:fan-certificate"),
  eg(20, ["C08", "C09", "G09"], ["T06", "T12"], "prop:p13-density"),
  eg(21, ["C09", "C10"], ["T06", "T12"], "lem:stub-positive"),
  eg(22, ["C08", "C10"], ["T06"], "lem:remainder-empty-internal-3-core"),
  eg(23, ["A10", "B09"], ["T01", "T14", "T15"], "lem:stub-positive"),
  eg(24, ["A11", "H01"], ["T01", "T13"], "lem:stub-positive"),
  eg(25, ["D01", "D02", "I01", "I02"], ["T07", "T17"], "lem:labels"),
  eg(26, ["A09", "F01"], ["T01", "T07", "T17"], "lem:curv-enum"),
  eg(27, ["G02", "G03"], ["T11", "T12"], "cor:forced-curvature-cost"),
  eg(28, ["A09", "F01"], ["T01", "T07", "T15"], "lem:wedge-lower"),
  eg(29, ["F02", "F07", "H09"], ["T11", "T12"], "lem:full-rank"),
  eg(30, ["C05"], ["T08"], "lem:two-path-criterion"),
  eg(31, ["C05"], ["T08", "T09"], "lem:replacement"),
  eg(32, ["C06"], ["T04", "T08"], "lem:context-universality"),
  eg(33, ["C07"], ["T08", "T11"], "lem:context-universality"),
  eg(34, ["F03", "F04"], ["T10", "T11"], "lem:proper-smearing"),
  eg(35, ["F06"], ["T08", "T10", "T11"], "lem:smearing-support-repair"),
  eg(36, ["C04", "F01"], ["T08", "T09"], "lem:return-equivalence"),
  eg(37, ["F05"], ["T05", "T10", "T11"], "lem:separated-testers"),
  eg(38, ["F05", "F07"], ["T05", "T11"], "lem:separated-testers"),
] as const satisfies readonly EGInvariantBinding[];

export const ALL_STRUCTURAL_PROPERTIES: readonly SurveyStructuralProperty[] =
  STRUCTURAL_PROPERTY_GROUPS.flatMap(
    (group): readonly SurveyStructuralProperty[] => group.properties,
  );

export const STRUCTURAL_SURVEY_PART_ANCHOR = "methodology-survey";

export function techniqueAnchor(id: TechniqueId): string {
  return `methodology-technique-${id}`;
}

export function propertyAnchor(id: PropertyId): string {
  return `methodology-property-${id}`;
}
