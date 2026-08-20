# Erdős–Gyárfás manuscript: technique map, coverage matrix, and a second-generation proof strategy

## Scope and source normalization

This report analyzes the current `main`-branch manuscript *A Structural Exhaustion Proof of the Erdős–Gyárfás Conjecture on Power-of-Two Cycles*, with special attention to the dense-packing residual around explorer node 159.

There are three distinct notions of “finished” in the materials:

1. **The mathematical manuscript presents a complete proof.** Its dense-residual status remark says the dense regime has no open node after the canonical-replacement, symmetric-strand, endpoint, and remainder-glue arguments.
2. **The live explorer’s hand-written overview appears stale.** It describes surviving red outcomes even though the current manuscript source closes them.
3. **External acceptance is a separate question.** Public papers dated shortly before the repository update still describe the conjecture as open. That does not refute a newer manuscript, but the claimed resolution still requires independent checking.

For the mathematics below, the current manuscript source is authoritative. The explorer is used to understand the dependency structure and referee view; the repository audit is treated as implementation metadata.

## The proof in one paragraph

Assume a lexicographically minimal counterexample (G). Replace “a cycle of length (2^k)” by “an edge with a simple return path of Mersenne length (2^k-1).” Minimality makes (G) critical and makes every proper boundaried piece irreducible under target-preserving replacement.

The computer-assisted (P_{13})-free theorem forces an induced (P_{13}), so take a maximal packing of such paths—called windows—and let (R) be the remainder. The windows impose finite local restrictions. Either those restrictions contain enough independent information to exceed the number of near-cubic labelled skeletons, or their dependence creates a bounded overlap that can be uncrossed into alternative corridors. Arithmetic on the corridor lengths then gives a Mersenne return, a target-distinguishable quotient, or a target-equivalent compression.

Meanwhile, minimum degree forces (R) to supply boundary deficiency and many length-two paths. Either their cycle tests lose rank, again yielding defect or compression, or they have almost full rank and cost too much entropy. The surviving numerical case has small normalized net deficiency.

A discharging and localization argument then produces a connected negative-charge support. The Type A receiver analysis, Type B fan analysis, and route-8 descent show that such a support cannot exist. Exact collision tests, refined minimality, a two-strand check, endpoint structure, and a remainder-glue injection close the dense and finite residuals.

## 1. Technique audit

“Blind spot” means a structure the technique cannot see by itself and must pass to another part of the proof. It does not automatically mean the technique is faulty.

| Technique                                                             | Structural properties it accounts for                                                                                                                                    | Why it helps                                                                                                                                                             | Blind spots and proof obligations                                                                                                                                                                                                      |                                                                          |                                                                                                                                                                  |
| --------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **1. Edge-rooted Mersenne returns**                                   | Exact target length; an oriented edge plus a simple return path; arithmetic set ({2^k-1})                                                                                | Converts a global cycle question into a local path-completion test that can be attached to boundaries and corridors                                                      | It is an equivalence, not a forcing argument. It does not show that any required return exists or that separately counted returns are compatible and simple                                                                            |                                                                          |                                                                                                                                                                  |
| **2. Lexicographically minimal counterexample**                       | Proper-subgraph exclusion; edge criticality; domination by degree-3 vertices; independence of degree-(\ge4) vertices                                                     | Turns deletion and replacement into contradictions and forces a near-cubic local environment                                                                             | Applies only after selecting a global minimum. Equal-size swaps remain invisible until the order is refined using the canonical piece multiset (\Phi)                                                                                  |                                                                          |                                                                                                                                                                  |
| **3. Boundaried target response and replacement**                     | Boundary degree profiles; behavior under compatible outside contexts; target equivalence of pieces                                                                       | Makes local simplification logically sound: a smaller piece with the same complete boundary response would produce a smaller counterexample                              | “Same response in every context” is a very strong, potentially large state space. Whole-graph support dependence can escape ordinary proper-piece replacement                                                                          |                                                                          |                                                                                                                                                                  |
| **4. (P_{13})-free theorem and maximal packing**                      | Presence of long induced paths; decomposition into 13-vertex windows and a componentwise (P_{13})-free remainder                                                         | Creates a fixed-size interface whose attachments can be enumerated and gives the remainder a strong hereditary restriction                                               | Relies on a computer-assisted external theorem. Maximality controls the remainder but does not make different windows independent. Dense packings are the main exceptional regime                                                      |                                                                          |                                                                                                                                                                  |
| **5. Finite attachment-label algebra**                                | Attachment subsets to a (P_{13}); short outside paths; immediate (C_4), (C_8), and two-step obstructions; 399 local labels                                               | Converts local graph geometry into a finite alphabet and exact constraints                                                                                               | Has fixed-window and bounded-radius vision. It can miss long correlations, equal-length symmetries, and multi-window interactions. The finite computation must be reproducible                                                         |                                                                          |                                                                                                                                                                  |
| **6. Degree-surplus routing and near-cubic reduction**                | Total excess (\sigma(G)=\sum_v(d(v)-3)); high-degree ports; fan handoffs; capacity tokens                                                                                | Either closes high-surplus graphs structurally or reduces the main spine to (\sigma(G)=O(\sqrt n)), where sharp counting becomes possible                                | Aggregate surplus does not determine topology. Exceptional mass can concentrate in overlapping fans or corridors and must be charged without duplication                                                                               |                                                                          |                                                                                                                                                                  |
| **7. Skeleton counting and entropy**                                  | Number of labelled graphs with fixed (n,m); window density (\theta); remainder entropy; high/low entropy alternatives                                                    | Independent window and obstruction tests consume bits. If their certified demand exceeds skeleton capacity, the graph class is empty                                     | Counting works only if demanded information is genuinely independent or charged once. Conditional fibres, glue constraints, finite-order corrections, and realization statements must be exact                                         |                                                                          |                                                                                                                                                                  |
| **8. Hot/cold split**                                                 | Windows with live independent restrictions versus windows whose restrictions fail to add; linear cold mass after hot failure                                             | Separates the information-rich case from the structurally correlated case                                                                                                | The classification is proof-specific and duplicates analysis. Cold mass is useful only after bounded-overlap extraction and correct routing of high-degree configurations                                                              |                                                                          |                                                                                                                                                                  |
| **9. Overlap uncrossing, serial corridors, and increment arithmetic** | Correlation among windows; connected minimal overlaps; alternative path lengths; modular doubling orbits; periodic response classes                                      | Replaces an invalid independence assumption with a dichotomy: information adds, or dependence becomes a concrete corridor system that forces a dyadic hit or compression | Uncrossing must cover branching, cyclic, and nonserial intersections. Equal-length increments, endpoint-only pairs, and context-invisible periodicity require separate closures                                                        |                                                                          |                                                                                                                                                                  |
| **10. Deficiency, stub supply, and wedge counting**                   | Boundary shortfall (\partial_+); window–remainder incidences; absence of an internal 3-core; abundance of length-two paths (W_2(R))                                      | Translates minimum degree in (G) into quantitative supply inside the low-degree remainder                                                                                | Counts candidate tests rather than independent tests. Graphs with equal deficiency and wedge counts can have different dependence and boundary behavior                                                                                |                                                                          |                                                                                                                                                                  |
| **11. Obstruction tensor and rank split**                             | Independence of local two-step cycle tests; rank-drop support; full-rank cost                                                                                            | Prevents correlated tests from being charged as independent information. Rank loss becomes a certificate of defect, compression, or support dependence                   | Independence depends on the exact target-response representation. Dependence can smear across a large or whole-graph support                                                                                                           |                                                                          |                                                                                                                                                                  |
| **12. Two-budget routing**                                            | Skeleton capacity; remainder entropy; obstruction cost; window density; net deficiency                                                                                   | Forces each survivor into an entropy contradiction, an obstruction-budget contradiction, or a small-net-deficiency case                                                  | Sensitive to counted class definitions and constants. Several logically different cases are compressed into inequalities whose injections and non-double-counting must be verified                                                     |                                                                          |                                                                                                                                                                  |
| **13. Net charge and localization**                                   | (\mathcal N(X)=\partial_+(X)-\sigma(X)-                                                                                                                                  | X                                                                                                                                                                        | /4); additive decomposition; connected negative support                                                                                                                                                                                | Converts a global numerical imbalance into a concrete connected subgraph | Localization forgets some cross-boundary correlations. The (1/4) threshold is tailored to the later discharge and must agree with the exact collision inequality |
| **14. Type A receiver and discharging analysis**                      | Subcubic supports; boundary deficits; receiver loads; saturation; eight exits; cubic switches                                                                            | Either a basic discharge pays every deficit or an overloaded receiver exposes a bounded target, defect, compression, or handoff configuration                            | Exhaustiveness is the burden. Saturated exits may pass the problem onward; route 8 and the terminal two-carrier case are the delicate residue                                                                                          |                                                                          |                                                                                                                                                                  |
| **15. Type B fan certificates and mass ledger**                       | Independent high-degree centers; cubic fan neighbours; degree-4 and higher profiles; B1/B2 disjointness; bridge mass                                                     | Controls how high degree can concentrate and shows failed or overlapping fans cannot carry linear negative mass                                                          | Fan overlaps and decorated handoffs create double-counting risks. Aggregate sublinear mass does not identify an individual closure without the bridge ledger                                                                           |                                                                          |                                                                                                                                                                  |
| **16. Route-8 demand descent and two-carrier no-go**                  | Private response supports; basins; demand versus supply; peeling; finite descent                                                                                         | Closes the last Type A escape by showing that many demands need too many private supports, while the two-support exception is peeled or impossible                       | Must distinguish essential supports from an arbitrary support enumeration. Termination and preservation of interface response during every peel are central                                                                            |                                                                          |                                                                                                                                                                  |
| **17. Dense-residual exact closures**                                 | Failure of joint-package realization; exact deficiency collision; equal-length symmetry; same-size canonical swap; two-strand cycles; endpoint stubs; all-cold injection | Repairs the regime where entropy independence is weakest and removes asymptotic and small-order ambiguity                                                                | The canonical order must make same-size swaps strictly smaller. The two-strand check does not close every pair by length alone; endpoint structure removes the survivors. The glue class must preserve exactly the counted constraints |                                                                          |                                                                                                                                                                  |

## 2. Move-by-property coverage matrix

### Structural-property columns

| Code  | Structural property                              |
| ----- | ------------------------------------------------ |
| **T** | Exact dyadic/Mersenne target arithmetic          |
| **M** | Minimality, criticality, and irreducibility      |
| **B** | Boundary interfaces and outside-context response |
| **P** | Induced (P_{13}) windows and remainder structure |
| **D** | Degree distribution, surplus, and near-cubicity  |
| **A** | Local attachments, stubs, paths, and corridors   |
| **R** | Independence, dependence, and obstruction rank   |
| **E** | Global density, labelled counts, and entropy     |
| **C** | Deficiency, charge, and demand/supply flow       |
| **O** | Overlap, correlation, and symmetry               |
| **F** | Finite and exact exceptional-case closure        |

An `X` means the move directly evaluates or constrains the property, rather than merely using it as a hypothesis.

| Mathematical move                                                               |  T  |  M  |  B  |  P  |  D  |  A  |  R  |  E  |  C  |  O  |  F  |
| ------------------------------------------------------------------------------- | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| Convert a (2^k)-cycle into a Mersenne return                                    |  X  |     |     |     |     |  X  |     |     |     |     |     |
| Choose a lexicographically minimal counterexample                               |     |  X  |     |     |     |     |     |     |     |     |     |
| Delete edges and derive degree-3 incidence and high-degree independence         |     |  X  |     |     |  X  |  X  |     |     |     |     |     |
| Compare target-complete boundaried pieces and replace                           |  X  |  X  |  X  |     |  X  |     |     |     |     |  X  |     |
| Invoke the (P_{13})-free theorem and take a maximal packing                     |  X  |     |     |  X  |     |  X  |     |     |     |     |  X  |
| Enumerate window attachments and local labels                                   |  X  |     |  X  |  X  |     |  X  |     |     |     |     |  X  |
| Route large surplus or enter the near-cubic spine                               |     |  X  |  X  |     |  X  |  X  |     |     |  X  |  X  |     |
| Count labelled skeletons and split hot/cold windows                             |     |     |     |  X  |  X  |  X  |     |  X  |     |  X  |     |
| Uncross overlap supports into serial corridor systems                           |  X  |  X  |  X  |  X  |     |  X  |     |  X  |     |  X  |  X  |
| Count remainder deficiency, stubs, and wedges                                   |     |     |  X  |  X  |  X  |  X  |     |     |  X  |     |     |
| Split on obstruction-rank loss versus full rank                                 |  X  |  X  |  X  |     |     |  X  |  X  |  X  |     |  X  |     |
| Apply the two-budget entropy/obstruction comparison                             |     |     |     |  X  |  X  |     |  X  |  X  |  X  |     |     |
| Localize negative net charge to a connected support                             |     |     |  X  |     |  X  |     |     |     |  X  |     |     |
| Run the Type A receiver ladder and discharging exits                            |  X  |  X  |  X  |     |  X  |  X  |     |     |  X  |  X  |  X  |
| Run the Type B fan certificate and bridge ledger                                |  X  |  X  |  X  |  X  |  X  |  X  |     |     |  X  |  X  |  X  |
| Descend route 8 and exclude a terminal two-carrier                              |  X  |  X  |  X  |     |     |  X  |  X  |     |  X  |  X  |  X  |
| Close the dense residual through exact collision, symmetry, endpoints, and glue |  X  |  X  |  X  |  X  |  X  |  X  |     |  X  |  X  |  X  |  X  |

### What the matrix reveals

Three observations explain the manuscript’s length.

1. **No early move sees arithmetic, correlation, and degree flow simultaneously.**

   Mersenne returns see the target but not its supply. Entropy sees capacity but not topology. Charge sees supply but not the target response.

2. **Boundary and context equivalence are the universal escape catcher.**

   Whenever rank, entropy independence, uncrossing, or local discharge fails, the proof attempts to turn that failure into a target-defective quotient or a target-equivalent replacement.

3. **The main complexity is not the initial (P_{13}) enumeration.**

   The difficult part is proving that correlations among local tests cannot hide globally. The hot/cold analysis, rank routing, Type A and Type B handoffs, route 8, and the dense residual are manifestations of the same correlation problem.

## 3. A more intuitive compressed explanation

Think of a minimal counterexample as a **lossless circuit**.

* Every oriented edge asks a family of questions: “Can the rest of the graph return to me in (2^k-1) steps?” A counterexample answers no to every such question.
* A boundaried subgraph behaves like a component with an input/output signature. Its signature records which Mersenne-return questions become true in every legal outside context.
* Minimality says that no proper component can be replaced by a smaller component with the same signature.
* Each induced (P_{13}) window is a bank of local sensors. Its possible attachments are finite, and many attachment patterns immediately create a 4- or 8-cycle.
* Therefore every surviving window restricts the outside graph.
* If many window restrictions are independent, they encode more bits than a near-cubic graph can store. This is impossible.
* If the restrictions are dependent, the dependence is not free. A minimal dependence becomes a connected overlap of completion paths.
* Uncrossing the overlap produces a serial choice among paths of different lengths.
* Those choices either hit a power of two, are distinguished by an outside context, or are indistinguishable and permit compression.
* The remainder cannot be passive. Because the original graph has minimum degree at least three but the remainder has no internal 3-core, the remainder owes many edges to the windows and contains many length-two paths.
* Those paths are another bank of cycle sensors. They are either dependent and compressible or independent and too expensive in entropy.
* The only numerical escape leaves a small amount of unpaid degree deficit.
* Discharging localizes that unpaid deficit to a connected bottleneck.
* A subcubic bottleneck is handled using receiver loads. A high-degree bottleneck is handled using fans.
* Both ultimately reduce to the impossibility of preserving the target response using only two private boundary carriers.

The proof’s recurring engine is therefore:

> **Many local tests either carry independent information, exceeding the global description budget, or they correlate, and the correlation exposes a smaller target-equivalent interface.**

The entropy, rank, overlap, replacement, and discharging layers make this engine valid in different structural regimes.

## 4. Second-generation proof strategy

The best simplification is not to shorten every local lemma. It is to replace several parallel ledgers with two general dichotomies.

### 4.1 Target-response interfaces

For a boundaried graph (X), define its **dyadic response signature** (\Sigma(X)) to record:

* boundary degree demands;
* pairs of boundary terminals;
* attainable simple path lengths, at the resolution needed to determine whether a context creates a (2^k)-cycle;
* the finite attachment state to any root (P_{13}) window.

Two pieces are equivalent when they have the same signature.

A minimal counterexample contains no proper piece with a smaller equivalent representative.

This reframes target completeness as a Myhill–Nerode-style equivalence: two pieces are equivalent exactly when no legal context distinguishes them with respect to the language of dyadic cycles.

The difficult point is proving that the relevant signatures are effectively finite or eventually periodic for the bounded interfaces that arise. The manuscript already contains the ingredients:

* finite (P_{13}) attachment labels;
* bounded corridor offsets;
* modular doubling orbits;
* periodic response classes.

### 4.2 Macro-lemma I: information or compression

**Proposed lemma.** Let (\mathcal U) be a finite family of local dyadic tests supported on windows, wedges, or bounded corridors of a minimal counterexample. Then one of the following holds:

1. A test is realized, giving a power-of-two cycle.
2. The joint conditional information of the tests is at least the sum of their certified local contributions, minus a boundary term.
3. A connected subfamily has a bounded interface and two distinct realizations with the same dyadic response signature, one strictly smaller in the canonical order.

Outcome 3 contradicts minimality. Outcome 2 is the only remaining counting case.

This lemma would replace most of:

* the window product bound;
* the hot/cold split;
* the barrier-overlap obstruction;
* local uncrossing and serial additivity;
* obstruction-rank-drop routing;
* the whole-support smearing argument.

The natural language is submodular entropy.

If the tests fail to contribute their expected conditional information, their mutual information is large. Choose a minimal connected support carrying that mutual information. The two conditioned realizations on that support are then either:

* context-distinguishable, producing a target hit or defect; or
* context-equivalent, producing a compression.

Serial increment arithmetic would be used only to establish finiteness or periodicity of the response signature, rather than as a separate top-level branch.

### 4.3 Macro-lemma II: supply or small cut

Construct a bipartite incidence network:

* left nodes represent units of positive deficiency in the remainder;
* right nodes represent window stubs and high-degree surplus units;
* an edge represents a legal response support or corridor that can carry one unit of payment.

**Proposed lemma.** For every connected admissible remainder piece, one of the following holds:

1. There is a feasible payment flow covering all deficiency at the (1/4) rate.
2. An alternating path in the support network realizes a dyadic cycle.
3. A minimum deficient cut has a bounded dyadic-response interface and admits a smaller equivalent representative.

Outcome 1 gives nonnegative charge. Outcome 2 gives the target cycle. Outcome 3 contradicts minimality.

This lemma would replace the separate:

* Type A receiver ladder;
* Type B fan certificate and bridge ledger;
* route-8 demand descent.

The receiver loads, fan incidences, private supports, and two-carrier obstruction would become certificates for the three outcomes rather than independent proof architectures.

### 4.4 One potential function

Define

[
\Psi
====

## B_{\mathrm{skel}}

## I_{\mathrm{local}}

## c_{\Omega}r_{\Omega}

\lambda\bigl(\partial_+(R)-\sigma(R)\bigr),
]

where:

* (B_{\mathrm{skel}}) is the exact labelled-skeleton description budget;
* (I_{\mathrm{local}}) is the certified joint information of all window and corridor tests;
* (r_{\Omega}) is the remaining independent obstruction rank;
* (\partial_+(R)-\sigma(R)) is the unpaid degree demand;
* (c_{\Omega}) and (\lambda) come from the finite local optimization.

The current proof maintains these quantities in different ledgers. A second-generation proof should make them one invariant.

* If (\Psi<0), no labelled graph can realize the demanded states.
* If a local family fails to reduce (\Psi) by the expected amount, information-or-compression produces a smaller equivalent piece.
* If unpaid demand remains, supply-or-small-cut produces a target cycle or compression.

This explains why entropy and discharging cooperate: they are dual ways of accounting for the same missing degrees of freedom.

### 4.5 Compressed proof conditional on the macro-lemmas

1. Assume a minimal counterexample (G).

   Edge-rooted target algebra forbids every Mersenne return. Interface irreducibility forbids smaller equivalent proper pieces.

2. Apply the (P_{13})-free theorem.

   Choose a maximal induced-(P_{13}) packing and let (R) be the remainder.

3. Apply information-or-compression to all window tests.

   A target cycle or compression is impossible, so the tests contribute their certified information. The exact skeleton comparison gives the required density bound.

   The dense case is included because failure of additivity is already an outcome of the same lemma.

4. Use minimum degree and maximality.

   These give the exact stub and deficiency supply and a linear family of wedge tests in (R).

5. Apply information-or-compression to the wedge tests.

   Rank loss produces compression. Full information exhausts the skeleton budget unless normalized net deficiency is less than (1/4).

6. Apply supply-or-small-cut to a connected negative-charge component.

   * A covering flow contradicts negative charge.
   * An alternating target path gives a power-of-two cycle.
   * A deficient cut produces a smaller equivalent piece.

   Every outcome is impossible.

7. Therefore the minimal counterexample does not exist.

This version has four visible ideas:

1. Mersenne target algebra;
2. interface irreducibility;
3. information or compression;
4. supply or small cut.

### 4.6 What must still be proved

The compressed strategy is not a replacement for the following obligations.

1. **Finite or periodic interface theorem**

   Prove that every bounded interface appearing after uncrossing has a finite canonical dyadic-response signature, including equal-length and odd-modulus periodic cases.

2. **Information localization theorem**

   Prove that a deficit in conditional information is supported on a bounded connected overlap rather than being delocalized across the entire graph.

3. **Exact skeleton injection**

   Define the counted class so every retained remainder and window state glues injectively into a labelled graph with the exact degree and edge constraints, without double counting.

4. **Flow integrality and cut interpretation**

   Show that the response-support network has sufficient integrality and uncrossing for a failed payment flow to produce a graph-realizable bounded cut—not merely an abstract fractional obstruction.

5. **Canonical strict decrease**

   Define a canonical decomposition and order under which every response-equivalent replacement is strictly smaller, including same-size neutral swaps.

6. **Finite local certification**

   Retain a small and reproducible finite computation for the (P_{13}) attachment constants and bounded-interface base cases.

These are the real research obligations. If they can be proved cleanly, the structural-exhaustion proof becomes an implementation of two general theorems rather than something that must be understood branch by branch.

## 5. Bottom line

The manuscript’s deepest idea is not any particular constant, fan table, or entropy threshold. It is the repeated conversion

[
\text{failure of local independence}
\Longrightarrow
\text{bounded structural dependence}
\Longrightarrow
\text{target hit, context defect, or compression}.
]

The cleanest second-generation proof would establish that conversion once and combine it with a single flow/cut formulation of the deficit argument.

The current hot/cold, rank-drop, Type A, Type B, route-8, and dense-residual branches would then become verification cases for two meta-lemmas rather than separate conceptual stages.

## Sources

* [Live referee view at node 159](https://fragiletech.github.io/hypostructure/#/erdos-gyarfas/explore?step=159&mode=referee)
* [Current manuscript source](https://github.com/FragileTech/hypostructure/blob/main/to_formalize/erdos_64_proof.tex)
* [Hypostructure repository overview](https://github.com/FragileTech/hypostructure/blob/main/README.md)
* [Hegde–Sandeep–Shashank: the computer-assisted (P_{13})-free theorem](https://arxiv.org/abs/2410.22842)
* [Carr: structural restrictions on a minimal counterexample](https://arxiv.org/abs/2605.22844)
* [A 60-vertex lower-bound paper dated 2 August 2026](https://arxiv.org/abs/2608.02675)
