# Node [181]: structural accounting and implemented first reduction

This document lists every fact that holds for the minimal counterexample $G$
when the proof reaches node [181], the arm taken at every diamond on the way,
the technique (register T01–T19) that produced each fact and the register
property (A01–I06) it evaluated, and the exact typed data at the leaf. Nothing
is projected, summarized, or dropped. Section 0 records the implemented
strict transition from [181] to [124] or [183]. Sections 6–12 retain the earlier
trace--ear attempt and its audit because several of its local identities are
correct and useful. They are not used in the implemented transition. Sections
13–20 retain a superseded block--cut draft for audit history only. That draft
incorrectly treated every unpaid unified entry as silent, whereas the live
`route8UnifiedEntries` family contains both visible-first and silent-excess
loads. No assertion from §§13–20 is part of the proof DAG.

Sources: `to_formalize/erdos_64_proof.tex` (labels in backticks; node numbers
in brackets), `closure_proofs.md` (Theorems 1.3–1.5, 3.1–3.4), the live
statement types in `HypostructureErdos64EG/StrategyDag.lean` and
`Graph/Strategy/SpineVocabulary.lean`, and the register
`web/frontend/src/structural-survey/data.ts`.

---

## 0. Implemented transition: maximal-ledger augmentation

The first new textbook move on the literal node-[181] residual is a
**one-entry augmentation of a lexicographically maximal finite packing**. It
uses no silence assumption, does not rerun the demand construction, and does
not pass to another graph or another support.

Let `entries` be the retained unified entry family, let
`core(ξ)` be its canonical essential-carrier set, and let

\[
  \operatorname{priv}(\xi)
   :=\{c\in\operatorname{core}(\xi):
       c\notin\operatorname{core}(\eta)
       \text{ for every }\eta\in\texttt{entries},\ \eta\ne\xi\}.
\]

The incoming demand fact supplies a partition

\[
       P=(\Xi_3(P),\Xi_2(P),\Xi_{\rm res}(P);A_P)
\]

which is lexicographically maximal in
\((|\Xi_3(P)|,|\Xi_2(P)|)\), subject to the pinned-entry condition. Put

\[
       \Xi_{\rm un}(P):=\Xi_2(P)\mathbin{\dot\cup}\Xi_{\rm res}(P).
\]

### Theorem 0.1 (unpaid entries have at most two private carriers)

For every \(\xi\in\Xi_{\rm un}(P)\),

\[
                         |\operatorname{priv}(\xi)|\le2. \tag{0.1}
\]

#### Proof

Suppose instead that some unpaid \(\xi\) has at least three private carriers,
and choose a three-element set
\(D\subseteq\operatorname{priv}(\xi)\). Define a new ledger \(Q\) by

\[
 \Xi_3(Q)=\Xi_3(P)\cup\{\xi\},\qquad
 \Xi_2(Q)=\Xi_2(P)\setminus\{\xi\},\qquad
 \Xi_{\rm res}(Q)=\Xi_{\rm res}(P)\setminus\{\xi\},
\]

set \(A_Q(\xi)=D\), and leave every other assignment unchanged. The three
classes still form a disjoint partition of `entries`. The new assignment is
available because \(D\subseteq\operatorname{core}(\xi)\), and has cardinality
three. Every old size-two or size-three assignment is unchanged.

For disjointness, if \(\eta\ne\xi\), then the old assignment
\(A_P(\eta)\) lies in \(\operatorname{core}(\eta)\). Privacy of every
\(c\in D\) therefore gives \(c\notin A_P(\eta)\). Thus \(D\) is disjoint
from every old assignment, while old assignments remain pairwise disjoint.
Finally, a pinned entry different from \(\xi\) keeps its assignment. The
entry \(\xi\) itself cannot be pinned: every pinned entry already belongs to
\(\Xi_3(P)\), whereas \(\xi\in\Xi_2(P)\cup\Xi_{\rm res}(P)\). Hence \(Q\)
is an admissible pinned ledger and

\[
                    |\Xi_3(Q)|=|\Xi_3(P)|+1,
\]

contradicting the first coordinate of maximality. This proves (0.1). ∎

In Lean this exchange is proved anonymously inside
`route8UnpaidExitFourDichotomy`. The decision reads the incoming demand
partition, constructs the comparison partition \(Q\), verifies every
partition, availability, disjointness, cardinality, and pinned-assignment
clause there, and contradicts the first coordinate of the retained
maximality statement. No detached helper theorem or stronger intermediate
API is introduced.

### Theorem 0.2 (exhaustive exit-(4) split)

Exactly one of the following occurs.

1. Some \(\xi\in\Xi_{\rm un}(P)\) has no exit-(4) witness. Then the retained
   unified census makes \(\xi\) target-complete-minimal, gives
   \(\alpha(\xi)\ge2\), and Theorem 0.1 gives its two-carrier bound. These are
   exactly the inputs of the existing node-[124] proposition, so this arm
   closes there.
2. Every \(\xi\in\Xi_{\rm un}(P)\) has an exit-(4) witness. Together with
   Theorem 0.1 this is the exact residual fact at node [183].

#### Proof

Choose an unpaid entry with no witness if one exists. The unified census says
that its basin is either target-complete-minimal, or target-defective together
with an exit-(4) witness for the same indexed load. The second alternative
contradicts the choice. Thus the entry is target-complete-minimal. The census
also supplies \(\alpha\ge2\), and (0.1) supplies the two-carrier condition.
The retained no-witness statement is therefore literally
`route8UnifiedTrueTwoCarrierEntry`; its unique existing consumer
`route8UnifiedTerminalNoGoRow` closes node [124].

If no such entry exists, classical negation gives a witness for every unpaid
entry, and (0.1) holds for each of them. This is precisely
`Route8UnpaidExitFourResidualStatement`. ∎

For quantitative accounting define

\[
 H_{181}(P)=\{\xi\in\Xi_{\rm un}(P):
                   |\operatorname{priv}(\xi)|\ge3\},\qquad
 N_{181}(P)=\{\xi\in\Xi_{\rm un}(P):
                   \xi\text{ has no exit-(4) witness}\}.
\]

Theorem 0.1 proves \(|H_{181}(P)|=0\) on both arms. A positive value of
\(|N_{181}(P)|\) closes at [124]; the only surviving arm [183] has

\[
              (|H_{181}(P)|,|N_{181}(P)|)=(0,0). \tag{0.2}
\]

Thus the residual predicate has strictly fewer admissible structural profiles,
while the entry family, demand units, assignments, peel chain, absorption,
window blockers, unified census, and every earlier ledger key are retained.
The Lean decision is `route8UnpaidExitFourDichotomy`; the assembly consumer is
`selectedRouteEightUnpaidExitFourReduction`.

---

## 1. The path from the root to [181]

Each row: node(s) → arm taken → fact retained on the branch state → technique → register rows evaluated.

| Node(s) | Arm taken | Fact retained | Technique | Rows |
|---|---|---|---|---|
| [1]–[2] | yes | $G$ finite simple, $\delta(G)\ge3$, no cycle of length $2^j$ (`def:counterexample`) | — | A04, C03 |
| [4] | — | $G$ is the lexicographically minimal counterexample: minimum $\lvert V\rvert$,then $\lvert E\rvert$, then lexicographic order | T02 | E01 |
| [5]–[7] | no Mersenne return | $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every orientededge $e$, $\mathrm{Mers}=\{2^k-1:k\ge2\}$ (`lem:return-equivalence`) | T08 | C02 |
| [8] | — | every proper subgraph $H\subsetneq G$ has $\delta(H)\le2$ (`lem:no-proper-core`) | T02 | E02, A07 |
| [9]–[10] | — | every edge has an endpoint of degree $3$; $V_{\ge4}(G)$ is independent (`lem:deletion-critical`) | T03, T02 | E03, A06 |
| — | — | $G$ is bridgeless (`lem:bridgeless`, by contraction of a bridge) | T03, T02 | B02 |
| [11] | — | boundaried pieces $X\oplus_TY$ with boundary degree profile $\mathbf d_\partial$ (`def:boundaried-gluing`, `lem:degree-profile-fibres`) | T05 | B05, B06 |
| [12] | — | context universality: a target-complete identification agrees against every $T$-context; an identification valid only for the actual outside is target-defective (`lem:context-universality`) | T05 | B07, E06 |
| [13] | — | replacement: no $T$-boundaried $X'\preceq_TX$ with the same $\mathbf d_\partial$, no internal power-of-two cycle, internal degrees $\ge3$, strictly smaller (`lem:replacement`) | T02, T03 | E05 |
| [14] | — | hereditary target-uncompressibility: no proper boundaried piece admits a nontrivial target-complete compression (`cor:uncompressible`) | T02, T05 | E05 |
| retained spine facts | — | contraction criticality and all four gadget-closure clauses remain in the exact ledger: a contractible edge has an actual severed return of length $2^k$ ($k\ge2$); smaller target-free cubic two-terminal pieces have the one-piece, doubled-piece, paired-piece, and complementary Mersenne/power path conclusions stated in §2.C | T02,T03, T08 | E03, C01, C02 |
| [15]–[16] | no | $G$ contains an induced $P_{13}$ (`cor:p13-exists`, via the black box `thm:p13free`: $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle) | T18 | I06, C08 |
| [17] | — | $\mathcal P$: a **maximum-cardinality** family of vertex-disjoint induced $P_{13}$'s, $p_{13}=\lvert\mathcal P\rvert=\theta n$, chosen lexicographically first among maximum ones; $W=\bigcup V(P)$, $R=G-W$ | T06, T16 | C09, C10 |
| [18] | — | $P_{13}$ label algebra: $399$ legal labels (sizes $13,60,122,122,63,17,2$), relations $C_s$, obstruction tensor $\Omega_2$ (`lem:labels`) | T17 | D01, G02 |
| [19]/[20]; [125]–[144] | no non-near-cubic surplus survives | near-cubic spine: $m=\tfrac32n+O(\sqrt n)$, $\sigma(G)=2m-3n=O(\sqrt n)$, $\lvert V_{\ge4}\rvert\le\sigma(G)$ (`def:near-cubic-spine`, `prop:nonnear-cubic-sharp-overload-routing`, `thm:tokenized-surplus-accounting-closure`) | T13, T14, T15 | A02, A05, A14 |
| [21] | — | finite constants: $c_\Omega=2.28922315244$, $c_{13}=118.108581006$; two-stepobstruction enumeration $543958,432672,111286$ (`lem:curv-enum`, `lem:p13-window-package`)| T17 | I05, A09, G02 |
| [158] | yes | the joint window package of $\mathcal P$ is realized by the labelled skeleton class: $\ge2^{c_{13}p_{13}\log_2n}$ target-complete states assigned canonically to skeletons in $\mathcal G_{n,m}$ (`def:window-realization-test`) | T12 | G01, G03, G06 |
| [22]/[145]–[157] | the live-hot entropy comparison does not close; the cold machinery returns to [24] on its bounded arm | `thm:cold-branch-quantitative-closure` is stated *conditional on absence of node [181]* (clause (v) of `def:surviving-cold-branch`); on the [181]branch its outputs are not available as facts. What is retained is only the return at [24] | T12, T13 | G03, H08 |
| [24] | — | the original window-only bound is $\theta\le\theta_{\rm win}+o(1)$, $\theta_{\rm win}=1.5/c_{13}=0.0127002$; the retained relabelling-orbit facts `remainderRelabelingEntropy` (key 501) and `relabelingDensityCap` (key 502), specialized to the realized hot window state, give Theorem 1.5: $\theta\le\theta^\ast+o(1)$ and $\tau\le\tau^\ast+o(1)$ | T12, T16 | G09, G04, I02 |
| [25]–[27] | — | $\lvert R\rvert\ge(1-13\theta)n$; every component of $R$ is $P_{13}$-free, hence of diameter $\le11$ and $\le6142$ vertices, and has empty internal $3$-core: every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ (`lem:remainder-empty-internal-3-core`, black box) | T06, T18, T04 | C10, C08, A07 |
| [28]–[29] | — | $\defp(X)=\sum_v\max(0,3-d_X(v))$; $\defp(R)\le e(R,W)\le15p_{13}+o(n)$;exact split $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; $(\defp(R)-\sigma_R)/\lvert R\rvert\le15\theta/(1-13\theta)+o(1)$, hence the live $\tau_{\rm win}=0.2281749\ldots$ bound | T01, T15 | A10, A11, H01 |
| [30] | — | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$ per component; $W_2(R)\ge\omega_{\rmwin}\lvert R\rvert-o(\lvert R\rvert)$, $\omega_{\rm win}=2.54365$ (high entropy $2.57407$)(`lem:wedge-lower`) | T01 | A09, F01 |
| [31]–[47] | no rank drop | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$; every rank-reducing dependence is target-defective, a proper compression (forbidden), a proper-support dependence (forbidden, `lem:proper-smearing`), or a whole-graph dependence that is target-defective, has a smaller closed representative, or is exact on labels (`lem:no-silent-global-smearing`); repair identity $s=p-2+2\beta_Z-\sigma_Z$ (`lem:smearing-support-repair`); separated identical wedges are context-universal or defective (`lem:separated-testers`) | T11, T10, T05 | F01–F07, A12 |
| [48] | — | forced obstruction cost $c_\Omega r_\Omega(R)\ge K_{\rm win}\lvert R\rvert-o(\lvert R\rvert)$, $K_{\rm win}=5.82298$ (high entropy $K=5.89263$) (`cor:forced-curvature-cost`) | T12 | G03, H09 |
| [49]–[50] | high entropy | $\eta(R)=\log_2\lvert\mathcal G(R)\rvert/\lvert R\rvert\ge(1-\tau)\log_2\lvert R\rvert-O(1)>\tfrac1{10}\log_2n$: the low-entropy arms (b),(c) of `prop:two-budget` are empty (Corollary 1.4, relabeling orbits) | T12, T16 | G01, G04, I02 |
| [51]–[53] | remaining non-obstruction budget not $<K\lvert R\rvert$ | large-budget branch: the skeleton budget minus the forced obstruction cost is at least $K\lvert R\rvert$; the entropy cap `prop:entropy-high-theta` ($\theta>\Theta(n)$) does not apply; $\Theta(n)=(1.4-K/\log_2n)/(116.808581006-13K/\log_2n)$ | T12 | H09, G08 |
| [55]–[56]; [173] | — | Residual C: $\Delta_{\rm net}(R)=(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau_{\rm win}+o(1)<\tfrac14$, with the manuscript's stated collision decided exactlyat [173] (`lem:exact-collision-test`) | T01, T13 | H01, I03 |
| [57]–[61] | $\No(R)<0$ | net charge $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; $\sum_i\No(X_i)=\defp(R)-\sigma(R)-\tfrac14\lvert R\rvert\le-(\tfrac14-\tau)\lvert R\rvert$; some connected canonical support has $\No(X)<0$ (`def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge`); canonical decomposition of $R$ into components withsurplus assigned to the piece containing the high-degree vertex (`def:canonical-decomp`) |T13, T04 | H01–H03, D08 |
| [62]; [64]–[85] | Type B closed | high-degree supports: centers independent, fan neighbours cubic, certificate-marked cap $d_G(h)\le8$, the fan-window ledger, B2 disjointness; every Type B support with $\No<0$ outside the bridge residual has a route-8 profile or a positive-deficit fan residual; the bridge residual mass is $M_B\le16\sigma(G)=o(\lvert R\rvert)$ (`lem:typeB-exclusion`, `prop:typeB-bridge-sublinear`, `thm:branch-kill`(b)) | T07, T13, T14, T15 | D03, D04, H05, H06, H08 |
| [63], [86]–[88] | Type A | the negative supports of linear mass are Type A: $\sigma(X)=0$, so every $v\in V(X)$ has $d_G(v)=3$; $X$ is connected, subcubic, $P_{13}$-free, $\operatorname{diam}X\le11$, $\lvert X\rvert\le6142$, empty internal $3$-core, contextually target-safe, hereditarily uncompressible, every deficient vertex supplied from $W$; $\defp(X)<\lvert X\rvert/4$; receivers $w$ with $d_X(w)\le2$, $q(w)=3-d_X(w)$ ports; canonical traces$T_u$ and loads $L(w)$ (`def:typeA-support`, `def:typeA-receiver-load`) | T04, T05, T07 |A03, A11, B05, C08, D08 |
| [89] | some receiver saturated | $L(w)\ge4q(w)$ for some receiver (else `lem:typeA-unsaturated-discharge`: $\defp(X)\ge\tfrac14\lvert X\rvert$, $n_3\le3n_2+7n_1+11n_0$, closing)| T13 | H04, H05 |
| before [93] | — | the live `portPowerReturn` key retains its witness selected Type A piece; at every completion port of every receiver of **that piece**, absence of a common ambient-cubic neighbour supplies an actual anchored return of length $2^k$, $k\ge2$.  It is not silently generalized to every member of $\tilde{\mathcal X}$ | T03, T08 | E03, C01, C02|
| [93] | no | no completion port carries four visible receiver-entry returns (else exits (1)–(7), `lem:typeA-visible-entry`) | T07, T08 | C01, C02 |
| [94] | — | visible-first excess: $S^{\rm exc}_{\rm sil}(X)=\sum_w\lvert\mathcal U(w)\rvert\ge n_3-3n_2-7n_1-11n_0=4D_A(X)$, $D_A(X)=\tfrac14\lvert X\rvert-\defp(X)$ (`lem:typeA-silent-excess-count`, `def:typeA-excess-basin`) | T13, T15 | H05, G07 |
| [95]–[108] | exits (1),(2),(3),(5),(6) closed; (7) absent; (4) peels | at every saturated receiver of every $X\in\tilde{\mathcal X}$: no anchored return of Mersenne length through a port; no two internally disjoint receiver-entry returns through one port with lengthssumming to a power of two (`lem:typeA-common-port-return-cycle`); no violated label relation $C_s$ on a shared window; no nontrivial target-complete response compression; no delocalizing response equality; no decorated handoff fan (exit (7)) since $X\in\tilde{\mathcal X}$ produces none; continuation routing at a port gives exits (4)–(6) or a surviving firstseparator of degree $\ge4$ (`lem:typeA-continuation-routing`, `lem:typeA-cubic-switch-absorption`, `lem:typeA-high-degree-handoff`) | T08, T09, T05, T07 | C01–C05, D01, E05, E06, D03 |
| [109]–[113] | — | the unified negative collection $\tilde{\mathcal X}=\{X:\sigma(X)=0,\No(X)<0,\text{no handoff}\}$ with $\tilde D_A=\sum(\tfrac14\lvert X\rvert-\defp(X))\ge(\tfrac14-\tau)\lvert R\rvert-o(\lvert R\rvert)$; entries $\tilde\Xi=\{(X,w,u,B_u):u\in\mathcalU_X(w)\}$, $\tilde N\ge4\tilde D_A$ (`def:typeA-unified-negative`, `lem:typeA-unified-deficit`, `lem:typeA-unified-burden`) | T13, T15 | H03, H08, G07 |
| [114]–[116] | — | every entry passes to its canonical minimal target-complete response-support core $\mathcal C_{\rm ess}(\xi)\subseteq\partial_EX$, $\alpha(\xi)=\lvert\mathcal C_{\rm ess}\rvert\ge2$ (`lem:typeA-unified-carriers`; entries with $\alpha\le1$ realize exits (4)–(7)) | T11, T05 | F02, F04, B08 |
| [117]; [119]–[122] | two-support entry exists | if every entry had $\pi(\xi)\ge3$ private essential incidences then $3\tilde N\le\defp(R)$ against $\tilde N\ge12(\tfrac14-\tau)\lvert R\rvert$, impossible; so some $\xi$ has $\pi(\xi)\le2$ (`prop:typeA-unified-reduction`) | T15, T01 | G07, H06 |
| [118], [124] | route-8 two-support closed | no terminal two-support route-8 obstruction(`thm:typeA-two-carrier-nogo`); Theorem 3.2: every two-support entry realizes exit (4), soroute-8 two-support entries do not occur | T05, T11 | E06, F05 |
| [101]–[102], [123] | target-defect two-support: peel | each such entry is peeled: its load leaves the receiver sum, $\Lambda_4=\sum_w\lvert\mathcal L(w)\setminus P_4(w)\rvert$ decreases by one, the deficit by $\tfrac14$, no invariant weakened (`lem:typeA-exit4-discharge`, `lem:typeA-exit4-finite-descent`); iterate while $\tilde D_A^{P_4}\ge(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$ | T19 | E08, H10 |
| [181] | the reduced-rate test fails | the leaf (§4) | — | — |

Arms not on the path (for completeness): [3] not a counterexample; [16] $P_{13}$-free; [20] non-near-cubic surplus (routed back to the spine); [23] live-hot overflow; [159]–[172] dense-packing residual ($\theta>\theta_{\rm win}$, the no-arm of [158]) and its nodes [163]–[172], [178]–[180], [182]; [60] net-cap contradiction; [90]–[92] unsaturated; [96], [98],[100], [104], [106] closed exits; [108] handoff; [124] closed.

---

## 2. The complete hypothesis ledger, by register category

Every unqualified fact below is on the branch state $\mathcal B_{181}$.
Rows explicitly labelled “candidate” or “exploratory” are included only to
audit the attempted closure and are not incoming live-ledger facts. “Produced
by” names the technique; “Row” the register property it evaluates.

### A — size, degree, sparsity, local incidence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| A-1 | $\delta(G)\ge3$; $n=\lvert V(G)\rvert\to\infty$ along the branch | `def:counterexample` | — | A04, A01 |
| A-2 | $m=\tfrac32n+O(\sqrt n)$; $\sigma(G)=2m-3n=O(\sqrt n)$; $\lvert V_{\ge4}(G)\rvert\le\sigma(G)$ | `def:near-cubic-spine` | T13/T14/T15 (surplus ledger) | A02, A05, A14 |
| A-3 | $m\ge\lceil3n/2\rceil$, $m\le2n-2$; $\beta=m-n+1\ge n/2+1$; $\beta+\lambda=n-2$; $\sigma=2\beta-n-2$ | invariants 9–13 | T01 | A02, A12, A13 |
| A-4 | $V_{\ge4}(G)$ independent; every edge has a degree-3 endpoint | `lem:deletion-critical` | T03/T02 | A06, E03 |
| A-5 | every vertex of every Type A support has $d_G=3$; a vertex of internal degree $3-q$ has $q$ stubs to $W$; $\defp(X)=\sum q$; $\defp(X)<\lvert X\rvert/4$ on $\tilde{\mathcalX}$ | `def:typeA-support` | T05 | A03, A11 |
| A-6 | $\defp(R)\le e(R,W)\le15p_{13}+o(n)$; $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; each window carries at most $15$ stubs (interior vertex one, end two) | `lem:stub-positive` |T01/T15 | A10, A11 |
| A-7 | $(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau^\ast+o(1)$, where $\theta^\ast=\frac{3/4}{c_{13}-39/4-15}$ and $\tau^\ast=\frac{15\theta^\ast}{1-13\theta^\ast}=0.13456\ldots<1/7$ | `prop:p13-density`; `closure_proofs.md`, Theorem 1.5; live orbit keys 501–502 | T12/T16 | A11, H01 |
| A-8 | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$; $W_2(R)\ge2.54365\lvert R\rvert-o(\lvertR\rvert)$ | `lem:wedge-lower` | T01 | A09 |
| A-9 | every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ | `lem:remainder-empty-internal-3-core` | T18 | A07 |
| A-10 | every component of $G-V(X)$ sends $\ge2$ edges to $X$; $\defp(X)\ge2$ | `lem:bridgeless` | T03/T02 | A11, B02 |

### B — connectivity, cuts, boundaries, contexts

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| B-1 | $G$ is bridgeless; every edge lies on a cycle | `lem:bridgeless` | T03/T02 | B02 |
| B-2 | every proper subgraph has $\delta\le2$ | `lem:no-proper-core` | T02 | E02, B01 |
| B-3 | $R=G-W$; its components are the canonical supports; no edges of $R$ between distinct components; surplus units of $V_{\ge4}\cap V(R)$ assigned to their component | `def:canonical-decomp` | T04 | B01, D08 |
| B-4 | boundaried pieces, boundary degree profiles, gluing $X\oplus_TY$; quotients fibrewise over $\mathbf d_\partial$ | `def:boundaried-gluing`, `lem:degree-profile-fibres` | T05| B05, B06 |
| B-5 | context universality (target-complete identifications agree against every context)| `lem:context-universality` | T05 | B07 |
| B-6 | trace basins $B_u$: lexicographically first inclusion-minimal trace-complete connected subgraph containing $T_u$; trace-response state $\rho_u(B_u)=(\mathbf d_\partial(B_u),\mathcal R_u(B_u),\profile)$ | `def:typeA-trace-basin` | T05/T10 | B08, B06 |
| B-7 | boundary incidences $\partial_EX$, $\lvert\partial_EX\rvert=\defp(X)$; every $u$-supported coordinate leaving $X$ records one | `def:typeA-route8-carriers` | T05 | B05, B09|
| B-8 | the demand ledger on $\tilde\Xi$: partition $\Xi_3\sqcup\Xi_2\sqcup\Xi_{\rm res}$with disjoint incidence sets $A(\xi)$ ($3$ or $2$ per entry), lexicographically first maximizing $N_3$ then $N_2$; $\mathsf P_{\rm ext}=N_2+3N_{\rm res}$; $3N_3+2N_2\le\defp(R)$ |`def:typeA-pressure-ledger`, `lem:typeA-pressure-ledger-no-overcount` | T14/T15 | B09, H06|
| B-9 | absorbers: (A1) unused boundary incidences of the same support, (A2) profile-dependence certificates; $\mathsf P_{\rm open}=\lvert\mathcal U_{\rm press}\setminus\mathcal U_{\rm abs}\rvert$; $3\tilde N-\mathsf P_{\rm open}\le\defp(R)$ once (A2) has routed | `def:typeA-pressure-absorbers`, `lem:typeA-pressure-absorber-no-overcount` | T14/T15 | B09, H06|
| B-10 | window blockers: each open unit is assigned one incidence $c(\upsilon)$ and its unique window $P(\upsilon)$; $\mathsf P_{\rm open}=\sum_PB_{\rm open}(P)$ | `def:typeA-open-window-blocker`, `lem:typeA-open-window-blocker-count` | T15 | B09, A10 |
| B-11 | $\mathsf P_{\rm open}\ge(3-13\tau)\lvert R\rvert-o(\lvert R\rvert)$ and $\mathsfP^{+}_{\rm zero}\ge\varepsilon_{\rm prim}\lvert R\rvert-o(\lvert R\rvert)$ on the branch (so the offered consumers of [181] are vacuous) | Theorem 3.1 | T01 | B09, H09 |

### C — paths, cycles, lengths

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| C-1 | no cycle of $G$ has length in $\mathrm{Pow}=\{2^j\}$; $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every oriented edge | `lem:return-equivalence` | T08 | C02, C03 |
| C-2 | every completion port has at least one actual anchored return | `lem:typeA-port-return` | T08 | C02 |
| C-3 | receiver-entry returns are actual simple connector–channel paths, and the finite schedule contains every such return | `def:typeA-visible-load`; `VisibleReceiverEntry.lean`| T08/T16 | C01, C02 |
| C-4 | connector/channel arithmetic: for a receiver-entry return $\Gamma\circ Q$ through$(w,h)$ with connector length $g$, $g+\lambda\notin\mathrm{Mers}$ for all $\lambda\in\Lambda_X(r,w)$; interval form with $I_X(r,w)$ | `lem:typeA-spectral-pressure`, `def:typeA-channel-spectrum` | T09 | C01, C04 |
| C-5 | theta closure: all branch-pair sums in a theta avoid $\mathrm{Pow}$; ear closure;symmetric difference of overlapping cycles avoids $\mathrm{Pow}$ | invariants 31–33 | T08/T09 | C05–C07 |
| C-6 | two-path criterion: two internally disjoint returns through one port with lengthssumming to $2^k$ give a forbidden cycle | `lem:typeA-common-port-return-cycle`, invariant30 | T08 | C05 |
| C-7 | every cycle length has an odd prime divisor; no single odd prime divides all cyclelengths; overlap formula $q_p(E)=q_p(C)+q_p(D)-2t$ flat and non-killing | invariants 36–38 | T09/T11 | C04 |
| C-8 | $G$ has an induced $P_{13}$; $R$ has none; every component of $R$ has diameter $\le11$ and $\le6142$ vertices | `cor:p13-exists`, `lem:remainder-empty-internal-3-core` | T18/T06 | C08 |
| C-9 | $p_{13}$ is the **maximum** number of vertex-disjoint induced $P_{13}$'s; the incoming live rate is $\theta=p_{13}/n\le\theta_{\rm win}+o(1)$ | [17], `prop:p13-density` | T06/T12 | C09, G09 |
| C-10 | gadget closure, one-piece and doubled: if $K$ is a smaller target-free cubic two-terminal piece with terminals $a,b$, then closing $a,b$ produces an actual $a$--$b$ path of length $2^e-1$; if $2|K|<|G|$, closing two copies produces two such paths whose lengthssum to $2^e-2$ | live key `gadgetClosure`, clauses 2 and 3 | T02/T03/T08 | C01, C02, E03 |
| C-11 | gadget closure, paired and complementary: two smaller target-free cubic two-terminal pieces whose closed gluing has minimum degree $3$ supply terminal paths whose lengths,plus the two joining edges, sum to a power of two; a complementary closure supplies an outside terminal path of length $2^e-1$ | live key `gadgetClosure`, clauses 1 and 4 | T02/T03/T08 | C01, C02, E03 |

### D — local configurations, motifs, overlap, symmetry

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| D-1 | $399$ legal $P_{13}$ labels; relations $C_s$; the zero-defect quotient through path lengths $1,2,3$ is the identity | `lem:labels` | T17 | D01, G02 |
| D-2 | $0.795414$ of locally safe wedges are obstructing; $c_\Omega=2.2892$ bits per independent obstruction coordinate | `lem:curv-enum` | T17 | D02, G02 |
| D-3 | Type B: fan-safe graphs, certificate labellings, $d_G(h)\le8$ for certificate-marked fans, degree-4 profiles, B2 disjointness, bridge residual sublinear | [64]–[85] | T07/T13/T14 | D03, D04 |
| D-4 | canonical decomposition, canonical traces (lexicographically first receiver-reaching paths in $X_3$), canonical payable set $A(w)$ (visible-first order), lexicographicallyfirst ledgers and assignments | `def:canonical-decomp`, `def:typeA-receiver-load`, `def:typeA-excess-basin`, `def:typeA-pressure-ledger` | T16 | D08, I02 |
| D-5 | all auxiliary objects are functions of the labelled adjacency matrix under a fixedtie-break; states are $\mathrm{Sym}(R)$-invariant relative to $W$ | `lem:skeleton-dominates`, Theorem 1.3 | T16/T12 | D09, G06 |

### E — extremality, criticality, replacement, quotients

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| E-1 | lexicographic minimality of $G$ ($\lvert V\rvert$, then $\lvert E\rvert$, then lexicographic) | [4] | T02 | E01 |
| E-2 | no proper subgraph with $\delta\ge3$; deletion criticality | [8]–[9] | T02/T03 | E02, E03 |
| E-3 | replacement lemma and hereditary uncompressibility (I5) | `lem:replacement`, `cor:uncompressible` | T02/T05 | E05 |
| E-4 | a quotient is valid only if target-complete against every context; otherwise target-defective | `lem:context-universality` | T05 | E06 |
| E-5 | exit-(4) peeling is a well-founded descent on $\Lambda_4$ preserving every invariant | `lem:typeA-exit4-finite-descent` | T19 | E08, H10 |
| E-6 | exits (5) and (6) never occur at any saturated receiver of $\tilde{\mathcal X}$ (standing-invariant contradictions); exit (7) is absent | `lem:typeA-exits-discharged`, `lem:typeA-unified-burden` | T02/T05 | E05, E09 |
| E-7 | contraction criticality: for an oriented edge $xy$, if no common neighbour of $x,y$ has ambient degree $3$, then the severed graph contains an **actual** simple $x$--$y$ path of length $2^e$, $e\ge2$ | live key `contractionCritical` | T02/T03 | E03, C01 |

### F — local tests, rank, dependence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| F-1 | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$ | `lem:full-rank` | T11 | F02, F07 |
| F-2 | rank drop routes to target defect, proper compression, or support enlargement; proper enlargements $Z\subsetneq G$ are impossible; whole-graph dependence cannot silently reduce rank | `lem:curvature-dependence-routing`, `lem:proper-smearing`, `lem:no-silent-global-smearing` | T10/T11 | F03–F07 |
| F-3 | separated identical wedges are context-universal or target-defective | `lem:separated-testers` | T05/T11 | F05 |
| F-4 | every entry's trace basin fails target-complete-minimality only through alternative (a) — a trace-local quotient forgetting a coordinate on an internal edge of $B_u$ is distinguished by a compatible context; (b),(c),(d) do not occur | `def:typeA-trace-basin`, Theorem 3.2 | T05/T16 | F04, E06 |
| F-5 | $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$; every $c\in\mathcal C_{\rm ess}$ hasa declared deletion witness (internal/mixed) with boundary-incidence support | `lem:typeA-unified-carriers`, `def:typeA-carrier-deletion-witness`, `lem:typeA-deletion-witness-declared` | T05/T11 | F04, F05 |

### G — counting and information

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| G-1 | $\lvert\mathcal G_{n,m}\rvert=\binom{\binom n2}{m}$; skeleton budget $\tfrac32n\log_2n+o(n\log n)$ | `lem:skeleton-dominates`, `lem:near-cubic-budget` | T12 | G01 |
| G-2 | the joint window package is realized: $\ge2^{c_{13}p_{13}\log_2n}$ states | [158]yes | T12 | G03 |
| G-3 | $\log_2\lvert\Phi(\mathcal S)\rvert\le\log_2\lvert\mathcal S\rvert-(\tfrac34\lvertR\rvert-15p_{13})\log_2\lvert R\rvert+O(n)$; the finite orbit inequalities are registeredby `remainderRelabelingEntropy` and `relabelingDensityCap` | `closure_proofs.md` Theorem1.3; live keys 501–502 | T12/T16 | G01, G04 |
| G-4 | $\eta(R)\ge(1-\tau)\log_2\lvert R\rvert-O(1)$ and the specialization of G-3 on thehot arm gives $\theta\le\theta^\ast+o(1)$ | `closure_proofs.md` Corollary 1.4 and Theorem1.5 | T12/T16 | G04, G09 |
| G-5 | forced cost $c_\Omega r_\Omega\ge K_{\rm win}\lvert R\rvert$; the large-budget arm: remaining budget $\ge K\lvert R\rvert$ | [48], [53] | T12 | G03, H09 |
| G-6 | no double counting: demand incidences pairwise disjoint; absorbers single-use; theexact stage identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ | `lem:typeA-pressure-ledger-no-overcount`, `lem:typeA-peeling-stage-accounting` | T15 | G07 |
| G-7 | the exact collision actually stated at [173] is decided there; it does not exactify a newly introduced coefficient comparison | `lem:exact-collision-test` | T12/T17 | G08 |

### H — charging and discharging

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| H-1 | $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; superadditivity; some connected support has $\No<0$ | `def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge` | T13 | H01–H03 |
| H-2 | Type A: each cubic vertex charges $\tfrac14$ to its receiver; receiver charge $q(w)-\tfrac14-\tfrac14L(w)$; unsaturated receivers ($L\le4q-1$) pay; thresholds $H_0\le4,H_1\le8,H_2\le12$ | `lem:typeA-threshold-algebra`, `lem:typeA-unsaturated-discharge`, `lem:typeA-exit4-peeling-charge` | T13 | H04, H05 |
| H-3 | saturated receivers with silent excess: $S^{\rm exc}_{\rm sil}\ge4D_A(X)$; the unified deficit $\tilde D_A\ge(\tfrac14-\tau)\lvert R\rvert$; $\tilde N\ge4\tilde D_A$ | [94], [111]–[113] | T13/T15 | H05, H08 |
| H-4 | private-support budget: three private incidences per entry would force $3\tilde N\le\defp(R)$, contradiction; hence two-support entries exist | `prop:typeA-unified-reduction` | T15 | H06 |
| H-5 | the demand ledger, absorbers and blockers (B-8–B-11) | — | T14/T15 | H06 |
| H-6 | Type B bridge mass $o(\lvert R\rvert)$ | `prop:typeB-bridge-sublinear` | T13/T15 |H08 |
| H-7 | with the retained cap $\tau^\ast<1/7$, the local inequality $\lvert X\rvert\le7\defp(X)$ on every negative Type A support is sufficient for a global contradiction | `closure_proofs.md` Theorems 1.5 and 3.4 | T13 | H09 |
| H-8 | finite descent $\Lambda_4$ | `lem:typeA-exit4-finite-descent` | T19 | H10 |

### I — finite certification and external inputs

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| I-1 | the black box `thm:p13free` (HSS): $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle; consumed as A-9 and C-8 | [15]–[16] | T18 | I06 |
| I-2 | Bondy--Vince: except for $K_1,K_2$, a graph with at most two vertices of degree below $3$ contains two cycles whose lengths differ by $1$ or $2$.  Only this exact theorem is used below; neither the appendix's quiet-block estimate nor a Gao--Ma consequence is assumed | [Bondy--Vince, *Cycles in a graph whose lengths differ by one or two*](https://people.clas.ufl.edu/avince/files/Cycles.pdf) | T18 | I06 |
| I-3 | finite constants $c_\Omega$, $c_{13}$, label counts; the $91$-barrier computation;the two-strand table | `app:curv-code`, `lem:labels`, [167] | T17 | I05, I01 |
| I-4 | exact small-order collision decided on the object | [173] | T17 | I03, I04 |

---

## 3. Techniques already used upstream, and the structural properties each one consumed

| Technique | Where used | Properties consumed (register rows) | What it left behind |
|---|---|---|---|
| T01 Direct invariant calculation | [28]–[30], [56], [119]–[122], Theorems 3.1, 3.4 | A02, A09–A12, H01, H06, H09 | the inequalities of A-3, A-6–A-8, H-3, H-4, B-11 |
| T05 Boundary-interface analysis | [11]–[14], trace basins, response states, cores, deletion witnesses, contexts | B05–B08, E05, E06, F04, F05 | B-4–B-7, E-3, E-4, F-4, F-5 |
| T08 Path–cycle and cycle-space analysis | [5]–[7], invariants 30–33, `lem:typeA-port-return`, `lem:typeA-common-port-return-cycle` | C02, C03, C05–C07 | C-1, C-3, C-5, C-6 |
| T10 Uncrossing and minimal obstruction | [31]–[47] (dependence localization), trace-basin minimality, continuation routing | F03–F07, B08, D05 (cold branch only) | F-2; on the [181] branch the corridor/overlap consumers of [169]–[172] are **not** available (they liveon the dense-packing residual) |
| T11 Linear-algebraic rank | [31]–[47], response-support cores | F01–F07, A12 | F-1, F-2,F-5 |
| T12 Counting and information | [21], [48]–[55], [158], Theorems 1.3–1.5, Corollary 1.4 |G01–G09, H09 | G-1–G-5, A-7, C-9; the low-entropy arms are empty |
| T13 Potential and discharging | [56]–[62], Type A charging, Type B ledger | H01–H05, H08| H-1–H-3, H-6 |
| T14 Demand–supply and flow | Type B B1/B2, the $2/3$-demand ledger, absorbers, surplus token ledger | B09, H05, H06, D04 | B-8–B-10; the failure of the matching is the leaf |
| T16 Symmetry and canonicalization | lexicographic tie-breaks everywhere, $\mathrm{Sym}(R)$-invariance (Theorem 1.3), canonical traces/ledgers | D08, I02, E07, G04 | D-4, D-5, G-3; the refined-order swap [165]–[166] is used only on the dense residual |
| T18 External structural theorem | [15]–[16] (HSS) | I06, C08 | I-1; Bondy--Vince is notinvoked upstream and is consumed locally in Lemma 9.1; no Gao--Ma consequence is used |
| T19 Peeling and finite descent | [101]–[102], [123] | E08, H10 | E-5, H-8, and the leaf's identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ |

---

## 4. The leaf: the typed data of [181]

`def:typeA-peeled-demand-residual`, after the procedure of `thm:large-budget-route8-only`:

In the live vocabulary its proposition is definitionally
\[
\begin{gathered}
\texttt{Route8StageRateFailedFact}\;\wedge\;
\texttt{Route8DemandLedgerStatement}\;\wedge\\
\texttt{Route8DemandAbsorptionStatement}\;\wedge\;
\texttt{Route8WindowBlockersStatement}.
\end{gathered}                                      \tag{4.1}
\]
The four conjuncts are retained together with, rather than substituted for,
the incoming `ExactLedger` facts.

- **(R1)** a valid family \(P_4=(P_4(w))_w\) of exit-(4) peeling sets at
  which
  \(\tilde D_A^{P_4}<(\tfrac14-\tau_{\rm win})|R|-o(|R|)\);
- **(R2)** the disjoint partition
  \(\tilde\Xi=\tilde\Xi^{P_4}\mathbin{\dot\cup}\tilde P_4\),
  \(p_4=|\tilde P_4|=\sum_w|P_4^{\rm un}(w)|\), the exact identity
  \(4\tilde D_A=4\tilde D_A^{P_4}+p_4\), and the recorded exit-(4) witness
  for every index actually occurring in the peel chain;
- **(R3)** the maximal \(2/3\)-demand ledger on the full unified entry
  family \(\tilde\Xi\), its maximal absorption ledger, and the unique-window
  blocker partition
  \(\mathsf P_{\rm open}=\sum_P B_{\rm open}(P)\).

The full unified family is not the peeled list and is not a purely silent
family. An index \(\xi=(X,w,u)\in\texttt{route8UnifiedEntries}\) consists of
a retained Type A support \(X\), a saturated receiver \(w\), and an unpaid
load \(u\in E_X(w)\), where \(E_X(w)\) is the visible-first excess basin.
Thus the family contains both unpaid visible-first loads and silent-excess
loads. For every such index the retained unified census supplies the
selected basin \(B_u\), the bound
\(|\mathcal C_{\rm ess}(\xi)|=\alpha(\xi)\ge2\), and exactly the alternative

\[
 \text{target-complete-minimal}\quad\text{or}\quad
 \bigl(\text{trace-local target defect with the other three failures absent
 and a canonical exit-(4) witness for }u\bigr).          \tag{4.2}
\]

Neither silence, the two-private-carrier bound, nor the target-defect arm is
asserted for every unified entry at node [181]. The two-private-carrier
bound for entries unpaid by the selected maximal partition is the new
conclusion of Theorem 0.1; the witness-free part of the first arm in (4.2)
is what routes to [124] in Theorem 0.2.

The assertion \(q(w)\in\{1,2\}\) is a consequence, not an extra hypothesis.
If a connected negative Type A support contained a receiver of internal
degree \(0\), that vertex would be an isolated vertex of \(X\), hence
\(X=\{w\}\). Then \(\defp(X)=3>1/4=|X|/4\), contrary to \(\No(X)<0\).
Thus \(n_0(X)=0\), and every receiver has internal degree \(1\) or \(2\), so
\(q(w)=2\) or \(1\).

For an unpaid index on the target-defect arm, the demand ledger supplies a
`CanonicalDemandRecord`. Its alternative realization, outside context, and
profile event are certificate data, not paths of \(G\). The record must be in
its **profile** disjunct: its actual disjunct would be a target cycle in
\[
 \operatorname{glue}(\operatorname{piece}(B_u),
                     \operatorname{outside}(B_u)).
\]
The owned-decomposition isomorphism
`SupportAtom.decomposition.reconstructionIso` identifies this gluing with
\(G\), and the target predicate is invariant under isomorphism; the actual
disjunct would therefore contradict C-1. A profile event is retained as
certificate data but is never used as an actual path of \(G\).

Derived facts at the leaf: Theorem 3.1 (the offered consumers are vacuous); Theorem 3.2 (every two-support entry realizes exit (4); no true route-8 two-support entry; at least onepeel is performed); Corollary 3.3 ([181] is the only exit of [123]); Theorem 3.4 (diagnostic rate).

---

## 5. The unconsumed rows and the attempted move

Before the closure below, the unconsumed local rows are B02–B04 beyond the
bare statement of bridgelessness (cyclic edge cuts, blocks and disjoint
connections), A08 (degree-two chains), D05 (overlap of traces and basins), E04
(safe suppression), and I06 (Bondy--Vince with its exact hypotheses).  The
demand and Hall rows H06–H07 locate the marks to which those local structures
belong.  C04/F08, C09 and D07 remain available on the monotonically growing
ledger, but the selected move does not need them.  In particular none is
deleted or replaced by a weaker statement.

The attempted move is T10 followed by T18: uncross the **actual canonical
traces** of all silent marks into a trace--ear forest, and apply Bondy--Vince
only to the terminal two-pole shells produced by that forest.  The move is on
the complete state $\mathcal B_{181}$; $X$, a full-vertex component of $X$,
and a shell are active regions on which the move acts, not replacements for
the residual. The intended recursive measure and terminal arms are written in
§8. Section 12 identifies the unhandled multi-boundary cyclic arm, so this
move is not an admitted structural-exhaustion transition. It nevertheless
isolates the exact new accounting that would be needed: no upstream row counted
how many silent marks can survive in the cyclic part of a cubic support.

---

## 6. The target closure statement for [181] (not established)

**Target statement [181].** Let \(G\) be a finite simple graph and suppose that all
facts of §2 (A-1 through I-4), with the arms of §1 as stated, and all leaf data
(R1)–(R3) of §4 hold. Then \(G\) contains a cycle whose length is a power of
two.

Equivalently, the complete declared-support residual routed from [123] after
[124] is empty. The proof must act on the target-defect two-support entries
themselves; it may not replace their declared carriers by the weaker
event-carrier implementation.

Sections 7–11 give the attempted derivation. Section 7 fixes the actual
objects and the monotone ledger, §8 states the proposed local trace--ear
exhaustion, §9 proves the valid finite shell estimate, §10 records the
conditional local and global inequalities, and §11 records the intended
implementation interface. Section 12 audits every step and explains why the
derivation does not prove this target statement.

---

## 7. Fixing the object: full vertices, actual traces and boundary half-edges

Throughout §§7–10 the ambient object is still the complete branch state
$\mathcal B_{181}$.  Fix one member $X$ of the unified negative Type A
collection only as the active region of the next move.  Put
\[
 n_i=n_i(X):=|\{x\in X:d_X(x)=i\}|,
 \qquad d:=\defp(X)=n_2+2n_1+3n_0.
\]
By the argument in §4, $n_0=0$, so
\[
 d=n_2+2n_1.                                        \tag{7.1}
\]
Let
\[
 U_X:=\mathop{\dot\bigcup}_{w\in\operatorname{Rec}(X)}\mathcal U_X(w)
\]
be the **original**, visible-first silent excess.  This is the collection
before any exit-(4) peel.  The partition and witnesses (R1)–(R3) remain
attached to its members; passing back from the peeled list to $U_X$ is not a
loss of data.  The exact support-level count at [94] gives
\[
 |U_X|\ge n_3-3n_2-7n_1.                            \tag{7.2}
\]

Let $X_3=X[\{x:d_X(x)=3\}]$, and let $F$ run over the connected components of
$X_3$.  Write $b(F)$ for the number of edges of $X$ with one end in $F$ and
the other end a receiver.  Attach a formal leaf to the $F$-end of each such
edge; these are the boundary half-edges of $F$.  Put
\[
 U(F)=U_X\cap V(F),\qquad b_X=\sum_F b(F).
\]
Then the sets $U(F)$ partition $U_X$.  Moreover,
\[
 b_X\le2n_2+n_1.                                    \tag{7.3}
\]
Indeed a degree-two receiver has at most two neighbours in $X_3$, and a
degree-one receiver at most one; receiver--receiver edges only decrease the
left side.

There is no ambiguity about the routing inside $F$.  From any two vertices of
$F$, exactly the same receivers are reachable by a path whose nonterminal
vertices have internal degree three: they are precisely the receiver
neighbours of $F$.  Since `traceReceiver?` scans the fixed vertex order, it
therefore chooses one and the same receiver $r(F)$ for every full vertex of
$F$.  The selected path `tracePath?` stays in $F$ until its last edge to
$r(F)$.  Thus the marks $U(F)$, their canonical paths and their terminal
receiver are all actual objects of $G$.

Finally, every **completion port** used below has an actual return.  Delete
its port edge.  Since $G$ is bridgeless, its ends remain joined; shortening
the joining walk gives a simple anchored path $P$ from the outside endpoint
$h$ to the receiver $w$. Let $r$ be the first vertex of $X$ on $P$ and let
$\Gamma$ be the prefix from $h$ to $r$. Every vertex of $\Gamma$ before $r$
is outside $X$. Since $X$ is connected, choose a simple path $Q$ inside $X$
from $r$ to $w$. The supports of $\Gamma$ and $Q$ meet only at $r$, so
$\Gamma Q$ is simple. It avoids the deleted port: $\Gamma$ is a prefix of the
anchored path, while $Q$ lies in $X$ and the other endpoint $h$ of the port
does not. Thus $(\Gamma,Q)$ is an actual receiver-entry return. This is the
elementary content needed from C-2. The
$b(F)$ half-edges are only the formal terminals at which such a channel may
enter or leave $F$; they are not silently identified with completion ports.
If an exposure enters a two-pole region whose two outside ends have
coalesced, its two inside terminal incidences are kept distinct and the
lexicographically first simple path between the two inside terminals is used
as an internal exposed route.  Such a path exists by connectedness.  If the
two incidences have the same inside endpoint, that cubic vertex is a branch
vertex and the region is split there first.  The stronger spectral paths of
C-10 and C-11 remain on the ledger but are not needed for this elementary
exposure.  No profile context $Y$, alternative realization $S_1$, or profile
event $E$ is used in the construction.

---

## 8. The new local move: marked cubic trace--ear exhaustion

The point not accounted upstream is that many silent traces cannot occupy the
cyclic part of $F$ independently.  The following lemma records the exact
local statement needed by the count.

### Proposed Lemma 8.1 (marked trace--ear lemma; not proved)

For every component $F$ above there are

- pairwise vertex-disjoint connected induced subgraphs
  $K_1,\ldots,K_p\subseteq F$;
- a set $Z$ of $B$ distinct vertices of
  $F\setminus\bigcup_iV(K_i)$; and
- an injection
  \[
  \iota:U(F)\longrightarrow\{K_1,\ldots,K_p\}\mathbin{\dot\cup}Z
  \]

with the following properties.

1. Every $K_i$ is receiver-free and has exactly two boundary edges in $F$.
   Equivalently, every vertex of $K_i$ has ambient degree three and
   \[
   \sum_{x\in K_i}(3-d_{K_i}(x))=2.                 \tag{8.1}
   \]
2. After contracting each $K_i$ to a marked degree-two vertex, adjoining the
   $b(F)$ boundary leaves and suppressing every other degree-two vertex, the
   resulting connected multigraph $Q_F$ has $B$ cubic branch vertices and
   cycle rank $\beta_F\le p$.

Consequently
\[
 |U(F)|\le p+B,qquad |F|\ge8p+B,qquad B\le b(F)+2p.       \tag{8.2}
\]

### Attempted proof

The following is the attempted exhaustion. The audit in §12 shows that the
multi-boundary cyclic case is not exhausted and that the asserted injection
of rank tokens into terminal shells does not follow.

**The exposure state.**  Adjoin the $b(F)$ formal boundary leaves to $F$.
An exposed route is the $F$-part of an actual receiver-entry return from §7,
or a tagged lexicographically first internal terminal path when the two
exterior ends have coalesced.
At any stage let $D$ be the union of the routes already exposed.  The active
regions are the induced connected shores cut off by the first and last
contacts of a canonical trace with $D$; their interiors are chosen
inclusion-minimally.  Each active region carries precisely the still
unassigned members of $U(F)$ in its interior and all of their original
branch-state data.  We order active states by
\[
 \mu=(\#\hbox{ unassigned marks},
      \sum_A|V(A)|,
      \#\hbox{ unsuppressed active edges})           \tag{8.3}
\]
lexicographically.  When a region is replaced by several regions, the sums
in (8.3) are over their disjoint interiors.

**One exposure.**  Take the first unassigned mark $u$ in the fixed order and
read its canonical trace from $r(F)$ towards $u$.  Up to the last point at
which it follows $D$ there is nothing to decide.  At the next edge exactly
one of the following happens.

1. The trace never leaves $D$.  If the containing route is tagged as an
   actual receiver-entry channel, it is a terminal segment of that channel,
   so $u$ is visible.  This is excluded by the definition of $U(F)$ (and, at
   an overloaded port, is one of the already closed exits (1)–(3)).  If the
   containing route is an internal terminal route, its two ordered terminal
   incidences delimit a two-pole active region; the mark is passed to that
   region, where the two-mark argument below either splits it or leaves the
   unique terminal shell.  Thus the internal-route case does not pretend to
   prove visibility.
2. The new segment first returns to $D$ at a vertex different from its first
   contact.  Its first and last contacts bound an ear.  Add the ear to $D$
   and replace its shore by the inclusion-minimal induced shore with those
   two contact incidences.  If the shore has a third boundary incidence, use
   the first one in the fixed edge order: the first vertex at which the three
   routes separate is put in $Z$, a mark there (if any) is assigned to that
   vertex, and the remaining marks pass to the strict components after that
   vertex is deleted.  If there is no third incidence, the shore is a
   two-pole active region.
3. The new segment has no second contact with $D$.  Continue from its loose
   end through unused edges.  Finiteness gives either a first return to $D$
   (case 2), a boundary half-edge, or a repeated vertex.  A repeated vertex
   is shortened to its first repetition and again gives an ear.  At a
   boundary half-edge, let $C$ be the component of $G-X$ incident with that
   half-edge.  If $C$ is the component of the outside connector already in
   $D$, a path in $C$ closes the new segment to an actual receiver-entry
   return whose channel contains $T_u$, contrary to silence.  If it is a
   different component, that half-edge is retained as a new terminal of the
   active route diagram.  A region with only one retained boundary edge
   would make that edge a bridge of $G$, contrary to B-1.  Hence this case
   again gives either a branch vertex or a two-pole region.

This list is exhaustive because every vertex of $F$ has three incidences when
the formal boundary half-edges are counted.  Notice also that it handles the
apparently exceptional lobe whose two boundary edges meet the same outside
vertex: delete that outside vertex and regard the two incidences as distinct
ordered poles.  Connectedness supplies the terminal-to-terminal route used as $D$.
If that route and the current trace do not have distinct first and last
contacts, their first repeated contact is a cubic branch vertex; if they do,
they give case 2.  Thus a one-vertex attachment is not discarded as a new
residual.

**Why a two-pole region with two marks splits.**  Let $A$ be such a region and
let $u\ne v$ be its first two marks.  Compare the two canonical traces from
the receiver side.  If their first divergence has two different later
contacts, those contacts give the ear of case 2.  Otherwise one trace is a
terminal segment of the other until the first unused incidence.  Start at
the other pole and seek a path to that unused incidence avoiding the common
terminal segment.  If it exists, concatenating it with the common segment
has two readings, according to the tag of the parent route.  For an actual
receiver-entry route, adjoining the exposed outside connector makes a simple
actual channel containing one of $T_u,T_v$, so that mark is visible.  For an
internal terminal route, the new path and the tagged route have distinct
first and last contacts and hence give the strict ear of case 2; if their
contacts coincide, the common contact has three continuations and is the
branch case.  If the avoiding path does not exist, the elementary vertex form
of Menger's theorem gives a separating vertex on the common segment.  Its
three incident directions are the parent route and the two marked sides; it
is again the branch vertex of case 2, and deletion of it puts the two marks in
strict active regions.  This proves that a terminal two-pole region contains
exactly one unassigned mark.

This paragraph also covers overlap of more than two basins: take the first
pair in the canonical order.  It is precisely the D05 overlap consumer.
No target-defect event is substituted for either trace.  The only paths in
the Menger argument are subpaths of $F$ and of the actual exposed connector.

**Uncrossing.**  If two two-pole shores cross, edge-cut submodularity gives
\[
 |\delta(A\cap A')|+|\delta(A\cup A')|
 \le |\delta(A)|+|\delta(A')|=4.                    \tag{8.4}
\]
Neither nonempty shore has cut size zero, and cut size one is forbidden by
bridgelessness.  Hence both new shores have cut size two.  Replacing the
crossing pair by its intersection and union preserves every mark in the
union and makes the ordered pair laminar; marks outside the intersection stay
active in the corresponding difference region of the union.  Repeating this
finite uncrossing leaves pairwise disjoint terminal shores.  These are the
$K_i$.  A terminal shore receives its unique mark; a mark met at a cubic
separation vertex receives that vertex.  The preceding paragraph shows that
no two marks receive the same object, proving the injection.

**Termination and cycle rank.**  Assigning a mark decreases the first
coordinate of (8.3).  Replacing a shore by strict shores moves at least one
contact path into $D$, and therefore decreases the second coordinate or,
when the vertex sets agree, the third.  Thus every arm closes or strictly
decreases $\mu$, so the construction terminates.

Contract the terminal shores and suppress the unmarked degree-two chains.
Orient every exposed ear by its exposure time.  A tree extension does not
increase rank.  An ear whose two ends already lie in the same exposed
component increases rank by one and places one rank token on its
inclusion-minimal two-pole shore.  Tokens are followed down the laminar
family.  If two tokens were to reach the same active shore, compare the two
corresponding ears after their last common segment.  Their first distinct
contacts either give two disjoint strict shores, one for each token, or give
three continuations at their first common contact, in which case that contact
is retained as a branch vertex and deletion again puts the two ear interiors
in different strict regions.  This is the same first-divergence argument as
for two marks, now with the two ear interiors in place of $T_u,T_v$.
Consequently no terminal shore receives two rank tokens.  The number of rank
tokens is exactly the cycle rank left after contraction and suppression, so
$\beta_F\le p$.
All remaining nonleaf, nonshell vertices have degree three, and they are
exactly the vertices counted by $B$.  The handshake identity in the connected
multigraph $Q_F$ is
\[
 B=b(F)-2+2\beta_F\le b(F)+2p.                      \tag{8.5}
\]
The injection gives $|U(F)|\le p+B$. The shells are disjoint and the branch
vertices lie outside them; Lemma 9.1 below gives $|F|\ge8p+B$. This would
prove (8.2) if every preceding routing and the rank-token injection were
valid. They are not; see §12.

---

## 9. The terminal shell estimate

### Lemma 9.1 (a target-free cubic two-pole shell has at least eight vertices)

Let $K$ be a connected simple graph all of whose vertices have ambient degree
three and with exactly two edges leaving $K$.  If $K$ contains no cycle of
power-of-two length, then $|K|\ge8$.

### Proof

The degree sum is
\[
 2|E(K)|=3|K|-2,                                    \tag{9.1}
\]
so $|K|$ is even.  The case $|K|=2$ would require two parallel internal
edges and is impossible in a simple graph.  If $|K|=4$, then $|E(K)|=5$, so
$K=K_4-e$ and contains a $4$-cycle.

It remains to exclude $|K|=6$.  Equation (9.1) gives $|E(K)|=8$, and the
total internal deficiency is two; hence at most two vertices have degree
below three.  Bondy--Vince (I-2) supplies two cycles whose lengths differ by
one or two.  Since a $4$-cycle is already a target, in a target-free graph on
six vertices the possible cycle lengths are $3,5,6$, and every pair among
these differing by one or two contains a $5$-cycle.  Let $C$ be such a
$5$-cycle and let $x$ be the sixth vertex.  Besides the five edges of $C$
there are exactly three edges.  If $d_K(x)\le2$, at least one of them is a
chord of $C$; that chord together with the three-edge arc of $C$ is a
$4$-cycle.  If $d_K(x)=3$, the three neighbours of $x$ on $C$ include two at
cyclic distance two; their two edges to $x$ and the two-edge arc between them
again form a $4$-cycle.  Both cases contradict C-1.  Thus the next possible
even order is eight.  $\square$

This is the sole use of I-2.  In particular the proof does not assume the
appendix's quiet-block estimate and does not enumerate bounded graphs.

---

## 10. Conditional consequences of Proposed Lemma 8.1

### 10.1 The exact component inequality

Assume the conclusion of Proposed Lemma 8.1 and apply Lemma 9.1 to one $F$.
From (8.2) and (8.5),
\[
\begin{aligned}
 10|U(F)|
 &\le10(p+B)\\
 &=3(8p+B)+7(B-2p)\\
 &\le3|F|+7b(F).
\end{aligned}                                       \tag{10.1}
\]
Summing over the full-vertex components and using (7.3) gives
\[
 10|U_X|\le3n_3+7b_X
             \le3n_3+14n_2+7n_1.                  \tag{10.2}
\]
Combine this with the retained visible-first lower bound (7.2):
\[
 10(n_3-3n_2-7n_1)
 \le3n_3+14n_2+7n_1,
\]
and hence
\[
 7n_3\le44n_2+77n_1.                               \tag{10.3}
\]
Using (7.1),
\[
\begin{aligned}
 7|X|
 &=7(n_3+n_2+n_1)\\
 &\le51n_2+84n_1\\
 &\le51(n_2+2n_1)=51\defp(X).
\end{aligned}                                       \tag{10.4}
\]
Thus every negative, zero-surplus, no-handoff Type A component in the full
unified collection satisfies the exact estimate
\[
 |X|\le\frac{51}{7}\defp(X).                       \tag{10.5}
\]
The argument used the full $U_X$, including every member later recorded as a
peel.  Therefore (10.5) closes the original [123] continuation and, a
fortiori, its complete [181] descendant; it does not prove a surrogate about
the reduced list.

### 10.2 Summing without dropping a component

Use the canonical decomposition B-3.  A component with $\No(X)\ge0$ satisfies
$|X|\le4(\defp(X)-\sigma(X))\le4\defp(X)$ and hence (10.5).  A negative
zero-surplus no-handoff component satisfies (10.5) by §10.1.  A negative
handoff or positive-surplus component is already in the Type B ledger; all
of it is closed except the bridge residual of total mass
$M_B\le16\sigma(G)$.  Consequently the exact pre-asymptotic statement is
\[
 7|R|\le51\defp(R)+7M_B.                            \tag{10.6}
\]
This summation includes nonnegative components, the unified collection,
handoff pieces and the bridge residual exactly once.  No piece and no surplus
unit disappears.

Since $|R|=(1-13\theta)n=\Omega(n)$, A-2 gives
$M_B=o(|R|)$ and $\sigma_R\le\sigma(G)=o(|R|)$.  A-7 bounds
$\defp(R)-\sigma_R$; adding the preceding estimate for $\sigma_R$ gives
\[
 \defp(R)\le\tau^*|R|+o(|R|),
 \qquad
 \tau^*=\frac{15\theta^*}{1-13\theta^*}.            \tag{10.7}
\]
The margin is strict.  Indeed
\[
 \theta^*=\frac{3/4}{118.108581006-39/4-15}
           =0.008033\ldots <\frac7{856},
\]
and direct cross-multiplication shows
\[
 \frac{15\theta^*}{1-13\theta^*}<\frac7{51}
 \quad\Longleftrightarrow\quad 856\theta^*<7.       \tag{10.8}
\]
Substitution of (10.7) into (10.6) now gives
\[
 |R|\le\frac{51}{7}\tau^*|R|+o(|R|),               \tag{10.9}
\]
where $(51/7)\tau^*=0.9803\ldots<1$.  Dividing by
$|R|$ contradicts (10.9) on the branch.

The attempted exactification was to read G-7 and I-4 as deciding the exact
quantities behind the $o(|R|)$ notation and to reuse [173] for (10.8). That is
not justified. The sharpened rate has no producer in the incoming live ledger,
and [173] decides a different integer collision. The local estimates
(10.1)–(10.6) introduce no asymptotic error, but they do not provide either
missing global producer.

Thus, conditional on Proposed Lemma 8.1, on a valid producer for the sharpened
rate $\tau^*$, and on an exact finite comparison for the new threshold, the
display would contradict C-1. None of those three conditions may be silently
read as an incoming node-[181] fact; §12 records the failures. Consequently
this calculation does not close node [181].

---

## 11. Candidate exhaustion ledger (not an admitted proof DAG)

The following table records what the attempted proof intended to establish.
It is not a list of descendants that may be added to the proof graph.  A row
is admissible only when its status says that it is a certificate or a closed
arm; every conditional or failed row must remain outside the proof DAG.

| Move | Fact or claimed output | Required progress | Audited status |
|---|---|---|---|
| actual/profile record | every canonical demand record at [181] is profile-only | the actual disjunct contradicts reconstruction of $G$; append the profile-only consequence without creating a child | **valid certificate** |
| degree-zero receiver | $n_0(X)=0$ and $q(w)\in\{1,2\}$ | the $q=3$ case contradicts connectedness and negative charge | **valid certificate** |
| trace follows one exposed channel | the oriented trace is a terminal segment of one actual channel | visibility contradicts membership in $U(F)$ | **closed** |
| first divergence and rejoining | an actual ear and an induced shore | prove the shore proper and transport every mark before claiming fewer vertices or edges | **conditional** |
| three continuations | a distinct cubic articulation vertex | delete it and pass marks tostrict components | **failed when the multi-terminal region has no articulation** |
| dangling continuation | a same-component outside path, or a different-component terminal| the first must give a simple visible return; the second must have a consumer or shrinkthe shore | **closed on the first arm; failed on the second** |
| crossing two-pole shores | laminar intersection/union shores | preserve every mark and decrease a declared measure while obtaining disjoint terminal shores | **failed** |
| terminal two-pole shore | one mark assigned to one shell | decrease the unassigned-markcount | **conditional on producing the shore and uniqueness** |
| shell orders $2,4,6$ | impossible by simplicity, a $C_4$, or Bondy--Vince plus a $C_4$ |surviving shell has at least eight vertices | **valid certificate** |
| component/global sum | (10.5), then (10.6) | pay every component exactly once | **validconditional on the forest certificate** |
| final rate | coefficient strictly below one | prove the sharpened rate and exact comparison on this branch, then derive `False` | **missing two producers** |

The recursive measure (8.3) would certify termination only after every arm is
shown to decrease it. The union-of-routes arm, the multi-boundary cyclic arm,
the different-outside-component arm, the separator-of-order-at-least-two arm,
and the crossing-shore replacement do not have such a proof, so none may be
installed as a descendant and the displayed measure does not certify a
recursion.
The ledger is monotone: R1–R3, the profile tokens, essential cores and deletion
witnesses, demand/absorption/blocker assignments, window data, entropy and rank
facts, gadget and contraction facts, and every exit exclusion remain attached
throughout.  Some are not needed in the final numerical line, but none is
projected away.

For a future Lean implementation the intended mathematical interface would be
finite and local only after the missing producer is proved:

1. `canonicalDemandRecord_profile_only`, proved from the owned-decomposition
   reconstruction isomorphism and target invariance;
2. `negative_typeA_no_degree_zero`;
3. `markedTraceEarExhaustion`, which is **not yet available**: it would have to
   return $p,B,b$, the injection, disjoint two-pole shells and $\beta\le p$
   while taking the complete [181] ledger as its input;
4. `targetFreeTwoPole_eight_le`, the proof of §9;
5. `negativeTypeA_card_le_51_sevenths_defect` and the exact aggregate form
   (10.6).

The live [181] proposition remains exactly
`Route8StageRateFailedFact ∧ Route8DemandLedgerStatement ∧
Route8DemandAbsorptionStatement ∧ Route8WindowBlockersStatement`; the closing
row described above does not yet exist. The current implementation correctly
retains that conjunction on its full inherited `ExactLedger` and does not
return `False`.

---

## 12. Airtightness audit of the attempted closure

The full node-local red-team report is
[`audits/erdos-64-red-team/reports/node-181.md`](audits/erdos-64-red-team/reports/node-181.md).
Its verdict is **NONEXHAUSTIVE BRANCH**. The audit preserves all incoming
facts and separates the valid textbook consequences from the unsupported
structural producer.

### 12.1 What is valid

1. The live proposition (4.1) and the append-only `ExactLedger` reading are
   exact.
2. The arguments $n_0(X)=0$, (7.1), the silent-excess lower bound (7.2), and
   the boundary count (7.3) are valid on the stated Type A support.
3. Full vertices in one component $F$ have the same set of traceable receivers
   and hence the same receiver selected by the fixed order.
4. Lemma 9.1 is valid. Total internal deficiency two leaves at most two
   vertices of degree below three, exactly the hypothesis of Bondy--Vince
   Theorem 1; the orders $2,4,6$ are then excluded by the written elementary
   argument.
5. The algebra (10.1)–(10.5) is correct **conditional on** the conclusion of
   Proposed Lemma 8.1.

The port-return sentence in §7 has been repaired as follows. From an anchored
return, take the prefix ending at its first entry into $X$; every
earlier prefix vertex is outside $X$. Join that first-entry receiver to the
terminal receiver by a simple path inside connected $X$. The two paths meet
only at the first entry, their concatenation is simple, and it avoids the
deleted port. This produces a genuine receiver-entry return. The earlier
first/last-visit split did not ensure that the connector stayed outside $X$.

### 12.2 First unhandled residual

The first nonlocal inference is case 2 of “One exposure.” If an induced ear
shore has a third boundary incidence, the proof chooses that incidence and
asserts a “first vertex at which the three routes separate.” A two-connected
three-terminal cyclic region need not have a single vertex whose deletion
separates the three routes. Cubicity limits local degree; it does not create
an articulation vertex. No fact in (4.1), no retained exit exclusion, and no
ancestor of [181] supplies that articulation. The cold-branch overlap
consumers [169]–[172] are not on this branch.

This arm neither closes nor replaces the active region by strict active
regions. It can return the same cyclic region with the same unassigned marks,
so it does not decrease any coordinate of $\mu$ in (8.3). It is therefore a
literal violation of the residual-shrink rule, not a presentational omission.

### 12.3 Further failed inferences

- If a trace is contained in the **union** $D$ of exposed routes, it may switch
  between intersecting routes. Containment in the union does not make it a
  suffix of one actual receiver-entry channel, so case 1 does not establish
  visibility.
- In the two-mark paragraph, failure of a path avoiding an entire common
  segment says that the segment contains a separator. Vertex Menger does not
  imply that a separator of order one exists; a minimum separator can have two
  or more vertices.
- Cut submodularity can make crossing cut-two shores laminar under additional
  nonempty/proper checks. Intersection and union are nested, however, not
  pairwise disjoint, and the proof does not preserve and reassign all marks in
  the difference regions. Moreover, the number of crossings is not a
  coordinate of $\mu$; an uncrossing can leave all three coordinates in (8.3)
  unchanged.
- In the dangling-continuation case, retaining a terminal in a different
  outside component adds information to the route diagram but does not by
  itself replace the active shore by a strict shore or route it to a closed
  consumer.
- The rank-token paragraph assumes the missing conclusion. Independent ears
  can end in one multi-boundary cyclic core; first divergence does not give a
  distinct cut-two terminal shore for each ear. Thus $\beta_F\le p$ has no
  proof.

A minimal abstract stress test is a triangle with one formal boundary leaf at
each vertex. The reduced diagram has $b=3$, three cubic branch vertices,
cycle rank one, and no induced cut-two shore. Hence $p=0$ and the asserted
$\beta_F\le p$ would read $1\le0$. This is not claimed to be a realization of
the full node-[181] counterexample ledger; it isolates the exact topological
inference that the local argument lacks.

### 12.4 The valid conditional replacement

The textbook part can be retained in this exact form. Suppose there are
pairwise disjoint two-pole shells $K_1,\ldots,K_p$, a set $Z$ outside them, an
injection
\[
 U(F)\longrightarrow\{K_1,\ldots,K_p\}\mathbin{\dot\cup}Z,
\]
and an embedded forest whose leaves are among the $b(F)$ boundary leaves and
the two formal poles of each shell, with every member of $Z$ of forest degree
at least three. The forest leaf identity gives
\[
 |Z|\le b(F)+2p.
\]
Lemma 9.1 and disjointness give $|F|\ge8p+|Z|$, while injectivity gives
$|U(F)|\le p+|Z|$. Therefore
\[
 10|U(F)|
 \le10(p+|Z|)
 =3(8p+|Z|)+7(|Z|-2p)
 \le3|F|+7b(F).
\]
This proof is complete, local, and uses only textbook moves. What is not
proved is that the full node-[181] residual produces this forest certificate.
Splitting on its existence would not repair the proof: the negative arm can be
the same multi-boundary cyclic core and hence would not shrink the residual.

### 12.5 Global ledger check

Even after a future proof of the forest certificate, two global facts need
their own producers before the final line can be called exact.

1. The sharper $\theta^*,\tau^*$ estimate is proved only in the exploratory
   `closure_proofs.md`; it is not a new key in the live incoming [181]
   `ExactLedger`. It may be added only through a proved, branch-correct
   transition.
2. Node [173] decides the manuscript's existing exact collision. It does not
   automatically decide the new integer comparison $856\theta<7$ used in
   (10.8). That comparison requires its own exact finite arm and a consumer
   for its literal failure.

### 12.6 Transition-by-transition progress audit

For this audit a *child residual* means the complete state carried after a
case distinction, not merely the active shore drawn in the local picture.  A
deterministic construction may append a proved certificate without creating
a child.  Every genuine child must either be closed or carry the whole
incoming ledger together with a strict decrease of
\[
 \mu=(M,V,E),
 \qquad
 M=\#\text{unassigned marks},\quad
 V=\sum_A|V(A)|,\quad
 E=\#\text{unsuppressed active edges}.
\]
The following table checks every transition used in the attempted proof.

| Transition | Exact incoming predicate | Textbook move | Output on each arm | Progress verdict |
|---|---|---|---|---|
| Construct one port return | a completion-port edge of a connected support in bridgeless$G$ | delete the edge, shorten a return walk, take the prefix to the first entry into $X$,then join inside connected $X$ | an actual simple receiver-entry return, appended as a certificate; no child residual | **valid certificate step** |
| Trace already exposed | $T_u$ is an oriented terminal segment of one tagged actual channel | take the corresponding connector--channel subpath | $u$ is visible, contradicting $u\in U(F)$ | **closed** |
| Trace contained only in the union | $T_u\subseteq D$, but it is not an oriented terminalsegment of one tagged actual channel | none | the same active region and the same mark $u$ | **invalid: $\mu$ unchanged** |
| Proper two-contact ear | the new trace segment has two distinct contacts and its choseninduced shore is proper with exactly two boundary incidences | first/last-contact ear extraction | a strict two-pole active shore, carrying every inherited fact whose objects lie in it and retaining the ambient ledger | **valid only after properness and fact transport are proved; then $V$ or $E$ decreases** |
| Third incidence with a cut vertex | three relevant route sectors meet a vertex $z$ whosedeletion separates their marked interiors | articulation decomposition | assign at most the mark at $z$ to $z$ and pass all other marks to strict components of $A-z$ | **valid: $M$ decreases, or $V$ decreases by deletion of $z$** |
| Third incidence without such a cut vertex | the ear shore is a two- or three-connected multi-terminal cyclic region | cubicity alone gives no separator | the same cyclic region with the same marks and edges | **invalid: $\mu$ unchanged** |
| Loose end returns to $D$ or repeats | the continuation first meets $D$, or first repeatsa vertex | shorten at the first contact/repetition | the preceding two-contact-ear case |**inherits that case's conditional verdict** |
| Loose end reaches the same outside component | the outside connector and the new boundary incidence lie in one component and can be joined without meeting the channel internally| path shortening and concatenation | an actual channel containing $T_u$, hence visibility| **closed after the stated disjointness check** |
| Loose end reaches a different outside component | the new boundary incidence belongs toanother component of $G-X$ | retain the incidence as a terminal | the same active shore with one more terminal tag | **invalid: no coordinate of $\mu$ decreases** |
| One-edge shore | the retained incidence is the only edge from an actual nonempty propershore to its complement | bridge criterion | contradiction to B-1 | **closed**, but only for an actual cut of $G$, not for a formal route-diagram boundary |
| Two marks, avoiding path exists | the required path avoids the whole common trace segment, and its concatenation is simple | path concatenation / first--last contact | visibilityon an actual-route tag, or a strict ear on an internal tag | **closed or smaller after the simplicity and proper-shore checks** |
| Two marks, separator of order one | the avoiding path fails and a one-vertex separator $z$ is independently proved | vertex separation | strict components of $A-z$ | **valid: $V$decreases** |
| Two marks, separator of order at least two | the avoiding path fails but the minimum separator has size at least two | vertex Menger gives only the separator set | the same two-connected cyclic core | **invalid: the claimed one-vertex child does not exist** |
| Uncross two cut-two shores | both intersection and union are nonempty proper shores andall four cut lower bounds are established | cut submodularity | a laminar pair $A\cap A'\subseteq A\cup A'$ | **not yet admissible: the shores are nested, not disjoint; marks in the differences are unassigned; $\mu$ has no crossing coordinate** |
| Create a rank token | a new ear raises cycle rank | ear-decomposition rank identity | atoken is asserted to lie on a new terminal cut-two shore | **invalid in a multi-boundary cyclic core: no such shore follows** |
| Terminal shell | a receiver-free induced shore with exactly two leaving edges has been produced | degree sum and Lemma 9.1 | at least eight vertices paid to that shell | **closedcertificate** |
| Forest count | the disjoint shells, injection, and embedded forest of §12.4 have all been produced | the forest leaf identity | $10|U(F)|\le3|F|+7b(F)$ | **valid conditional certificate; it does not produce its own hypotheses** |

Thus the first failed child is not a later numerical edge: it is the
multi-terminal cyclic child in the third-incidence arm.  The same failure
reappears in the union-of-routes, different-outside-component,
higher-separator, uncrossing, and rank-token arms.  Adding any of those arms
as a descendant of [181] would violate monotonicity because its complete
state has the same $M,V,E$ as its parent.

### 12.7 No retained fact removes the nonshrinking child

The Lean producer makes the retention check literal.  Its output index is
\[
 [\texttt{peeledResidual},\texttt{windowBlockers},
   \texttt{demandAbsorption},\texttt{demandLedger},
   \texttt{stageRateFailed},\texttt{peelingDescent}]
 \mathbin{+\!+}\texttt{known}.
\]
In particular the required keys `route8UnifiedNegative`, `typeAExclusion`,
`typeBBridgeReduction`, `route8PiecesClassified`, `typeBBridgeSublinear`,
`route8ExtractedEntryCensus`, `typeBSublinearLedger`,
`route8UnifiedDeficit`, `route8QuotientFree`, `typeAReceiverRouting`,
`route8UnifiedEntryCensus`, and `selection` remain in `known`.  The proposed
local proof is therefore not permitted to forget any of them.  Checking them
by mathematical content, rather than by name, gives:

| Retained ledger block | What it actually supplies on the cyclic child | Why it does notclose or shrink that child |
|---|---|---|
| A, B | subcubic/full-degree incidence, connectedness, bridgelessness, boundary profiles,and absence of a proper internal $3$-core | bridgelessness excludes cut size one but permits two- and three-connected multi-terminal cyclic regions; none of these facts creates anarticulation or cut-two shore |
| C | target avoidance, actual returns, length exclusions, and the gadget/contraction conclusions under their exact terminal hypotheses | visibility is available only after one actual simple channel containing the whole canonical trace is constructed; a union of routesor a profile context is not such a channel, and a multi-terminal core is not a two-terminal gadget |
| D | canonical choices, label data, and symmetry | a tie-break chooses among existing objects; it neither creates a separator nor turns a laminar family into disjoint marked shores |
| E | minimality, replacement exclusion, quotient rules, and the completed peel descent |minimality can be invoked only after constructing an admissible smaller target-complete representative; no such representative is produced from the cyclic child, while another peelonly re-encodes the already recorded mass |
| F | essential response supports, declared deletion witnesses, quotient-freeness, and thetrace-local target-defect alternative | these are statements about response coordinates and boundary-compatible realizations.  The surviving `CanonicalDemandRecord` is in its profile disjunct, whose outside context is explicitly non-actual; it supplies no path or separator in $G$ |
| G, H | the exact deficit, disjoint incidence ledger, failed stage rate, maximal absorption, and blocker partition | these facts prove how many unpaid units remain and prevent double counting; they do not inject those units into vertices or two-pole shells of the cyclic core |
| I | the $P_{13}$-free theorem, finite constants, exact previously registered collision,and Bondy--Vince | HSS applies to a graph of minimum degree at least three, not to the present multi-boundary piece; Bondy--Vince yields the proved eight-vertex bound only after acut-two shell has been produced; [173] decides a different comparison |

This table also rules out the tempting misuse of the demand token.  In the
live definition `TraceLocalTargetDefect` is a context-distinguishability
statement about a retained reading.  `CanonicalDemandRecord` is a disjunction
of an actual-exterior record and a record in a context unequal to the actual
exterior.  Target avoidance eliminates the first disjunct on this branch, so
only the second remains.  Treating its certificate, event, or corridor as a
path in $G$ would drop the inequality of contexts and hence drop an upstream
fact.

### 12.8 Final audit verdict for the trace--ear attempt

Accordingly, the honest present conclusion is: Lemma 9.1 and the conditional
coefficient calculation are sound, but Proposed Lemma 8.1 is nonexhaustive,
its supposed recursive residuals do not all shrink, and node [181] is not
closed by §§7–11.

---

## 13. Retired block--cut shore draft (not part of the proof)

**Audit status.** The material in §§13–20 is retained only to preserve any
independently useful shore identities. Its proposed transition is invalid for
the actual node-[181] input because Lemma 15.1 assumes every unpaid owner is
silent. The live unified family also contains visible-first excess entries.
Consequently Proposition 16.3 is unavailable, the block--cut recursion is not
exhaustive, and none of §§13–20 may be cited as closing [181] or [183]. The
implemented proof transition is Theorems 0.1–0.2 above.

**Reading convention for §§13–20.** Identities about an already given
ambient-cubic shore remain ordinary proved identities. Any statement using a
newly rebuilt shore ledger, the assertion that every unpaid or open owner is
silent, or recursive application of Proposition 16.3 is false as a
node-[181] transition and is labeled as such below. No extra hypothesis is
introduced to rescue it. The remaining calculations are retained only to
show what is independently correct and exactly where the implication breaks.

The conclusion of §12.8 concerns only the trace--ear proposal of §§7--11.
The retired draft below does not use Proposed Lemma 8.1 or a trace ear. It
attempted to enrich the node-[181] state at every stage to

\[
   \mathcal B_{181}[S,\mathscr L_S]
   :=(\mathcal B_{181};S,\delta_G(S),\mathscr L_S),       \tag{13.1}
\]

where the first coordinate would be the complete immutable ledger of §§1--4,
\(S\) is the current connected induced shore inside one member of
\(\widetilde{\mathcal X}\), and \(\mathscr L_S\) is the canonical local
restriction of the already established receiver, trace, response-support and
demand interfaces.  In particular, (R1)--(R3), every peel witness, every
closed exit, the relabelling cap, and the original support remain in the
state. This notation records the intended monotone bookkeeping; it does not
prove that \(\mathscr L_S\) exists with the claimed inherited properties.

For a nonempty vertex set \(S\subseteq V(G)\), write

\[
 b(S):=|\delta_G(S)|.
\]

Every vertex of every shore considered below has ambient degree three.
Consequently

\[
 b(S)=\sum_{v\in S}(3-d_S(v))=3|S|-2|E(G[S])|.          \tag{13.2}
\]

The draft proposed the following textbook move.

> **Retired block--cut transition.** Take the first open demand unit in the canonical
> shore ledger and its silent owner \((S,w,u,B_u)\).  Visibility forces
> \(d_S(w)=2\) and forces \(S-w\) to have exactly two components.  Replace
> the active shore \(S\) by those two components, retaining the whole parent
> ledger.

If a silent open owner on a transported shore ledger had been available, the
resulting split would use B03 and would have the exact progress measure

\[
        M(\mathscr F):=\sum_{S\in\mathscr F}|S|.          \tag{13.3}
\]

Such a block--cut move replaces \(S\) by \(K,H\) with
\(|K|+|H|=|S|-1\).  Hence it changes \(M\) to \(M-1\), not merely to a
lexicographically selected subproblem.  The removed separator vertex is not
discarded: it appears as the \(+1\) in the order identity and as the exact
\(+1\) in the boundary identity proved in §16.

The remainder of the retired draft attempted to establish the three facts
needed to iterate this move:

1. the local burden and pressure interfaces transport to every derived
   shore (§§14--15);
2. every open unit supplies the stated strict block--cut decomposition
   (§16);
3. a shore on which no unit is open either satisfies the required
   \(7b-8\) estimate or already contains a forbidden \(4\)- or \(8\)-cycle
   (§17).

The first item is not established on the incoming residual: rebuilding the
ledger on \(S\) neither preserves the original indexed family nor eliminates
its unpaid visible-first entries. Consequently the second and third items do
not form an exhaustive recursion. Sections 18–19 retain only the conditional
calculation that would follow from those unavailable premises.

---

## 14. Elementary shore identities and the claimed interface transport

### Definition 14.1 (derived shore)

Fix \(X\in\widetilde{\mathcal X}\).  A *derived shore of \(X\)* is obtained
recursively as follows.

- The root shore is \(V(X)\).
- If \(S\) is a derived shore and the block--cut move selects \(w\in S\),
  the two connected components of \(G[S]-w\) are its children.

The choice is canonical: use the first open unit in the retained demand-unit
order, then the first owner in the retained entry order.  Thus this is one
well-founded recursion, not an uncontrolled family of choices.

### Lemma 14.2 (elementary shore identities)

Every derived shore \(S\) has the following properties.

\[
\begin{array}{ll}
\text{(a)}&\varnothing\ne S\subseteq V(X),\quad G[S]\text{ is connected and induced};\\
\text{(b)}&d_G(v)=3\text{ for every }v\in S;\\
\text{(c)}&b(S)=3|S|-2|E(G[S])|\text{ and }b(S)\equiv |S|\pmod2;\\
\text{(d)}&b(S)\ge2;\\
\text{(e)}&G[S]\text{ is }P_{13}\text{-free and every nonempty induced}\
&\qquad\text{subgraph of }G[S]\text{ has a vertex of degree at most }2;\\
\text{(f)}&G[S]\text{ contains no power-of-two cycle.}
\end{array}                                                   \tag{14.1}
\]

#### Proof

The root has (a) and (b) by the definition of a Type A support.  A child is a
connected component after deleting one vertex from an induced graph, hence is
again a nonempty connected induced vertex set; ambient degrees do not change.
This proves (a) and (b) inductively.  Summing ambient degree three over \(S\)
gives

\[
 3|S|=2|E(G[S])|+|\delta_G(S)|,
\]

which proves the equality and parity assertion in (c).

The packing is nonempty because the counterexample contains an induced
\(P_{13}\), so \(S\subseteq R\subsetneq V(G)\).  Since \(G\) is connected,
\(b(S)>0\).  If \(b(S)=1\), the unique edge of \(\delta_G(S)\) disconnects
\(S\) from its complement and is a bridge of \(G\), contrary to B-1.  Hence
\(b(S)\ge2\), proving (d).

An induced subgraph of the \(P_{13}\)-free graph \(G[X]\) is
\(P_{13}\)-free.  By A-9, every nonempty \(P_{13}\)-free induced subgraph
of \(G\) has a vertex of internal degree at most two.  This proves (e),
including the empty internal \(3\)-core condition.  Finally any cycle of
\(G[S]\) is a cycle of \(G\), so C-1 proves (f). \(\square\)

### Failed Claim 14.3 (boundary-interface transport)

Let \(S\) be a derived shore. The draft claimed that every boundary and
response statement used by the Type A local ledger remains valid with \(S\)
in place of \(X\):

1. every edge of \(\delta_G(S)\) is an actual oriented completion incidence;
2. the outside context is the actual induced complement together with the
   boundary vertices, so gluing reconstructs \(G\);
3. a target-complete quotient on a proper subpiece of \(S\) is forbidden by
   hereditary target-uncompressibility;
4. a target-defective event meeting an internal edge of \(S\) and an edge
   outside \(S\) uses at least two distinct incidences of \(\delta_G(S)\);
5. the node-[124] two-carrier terminal accepts a target-complete-minimal shore
   entry with at most two private essential incidences;
6. a decorated handoff produced inside \(S\) is the same actual Type B
   handoff when the omitted vertices \(X-S\) are glued back.

#### Audit of the argument

Items 1–2 are elementary descriptions of the actual cut, and the cycle-cut
parity used in item 4 is independently valid. What is not supplied by the
incoming ledger is a new entry census on \(S\), target-complete-minimality for
those new entries, or transport of the closed alternatives and absorber
ownership to that census. Thus items 3–6 do not jointly establish the claimed
ledger transport. The following argument is retained to identify its valid
cut identities and invalid transport inferences; it is not a lemma.

Items 1 and 2 are definitions: no formal half-edge is introduced.  The
vertex partition

\[
  \partial S\ \dot\cup\ (S-\partial S)\ \dot\cup\ (V(G)-S)
\]

and the ownership of each internal or external edge give a canonical graph
isomorphism from the glued actual piece and actual outside to \(G\).

For item 3, a proper boundaried subpiece of \(S\) is also a proper
boundaried piece of \(G\).  The boundary degree profile is the actual one,
so `cor:uncompressible` applies without changing its fibre.  The same gluing
observation transports proper- and whole-support dependence to the already
closed rows E-3, F-2.

For item 4, add the root edge when the event is edge-rooted.  The result is a
simple cycle meeting both \(S\) and its complement.  A cycle crosses every
edge cut an even number of times.  It crosses this cut positively, and a
simple cycle cannot traverse one cut edge twice, so it uses at least two
distinct cut incidences.  This is precisely the proof of
`lem:typeA-pressure-token-two-carriers`; it does not require the cut edges to
end in \(W\).

For item 5, inspect the terminal contract of [124].  It asks for ambient
cubicity, contextual target-safety, a target-complete-minimal trace basin, an
essential core of size at least two, at most two private essential
incidences, and the declared deletion witnesses.  Ambient cubicity and
actual target-safety are Lemma 14.2(b),(f), while contextual target-safety is
the inherited boundaried-piece fact in \(\mathcal B_{181}\); the response-state
construction and its deletion witnesses use the actual boundary just
established; and the one-carrier case is excluded by the cut-parity argument
of item 4.  The terminal's smaller two-terminal-piece clauses are supplied by
the retained `gadgetClosure` fact (key 500), whose statement is uniform in the
chosen proper piece.  Thus all clauses of the [124] input interface, and no
stronger clause, hold.

For item 6, the handoff certificate consists of actual connector tails, their
first high-degree separator, and the decorated core.  Gluing \(X-S\) back
does not change any of those ambient vertices, edges, degrees, or return
tests.  Hence it is a handoff for the original branch state.  Members of
\(\widetilde{\mathcal X}\) have already taken the no-handoff arm, so it
cannot occur on a surviving derived shore. \(\square\)

The important point is that an edge of \(\delta_G(S)\) may end in
\(X-S\), rather than in a packed window.  None of items 1--6 uses a window
blocker.  The closing proof retains the blocker partition from (R3) but does
not spend it again.

---

## 15. Retired hereditary-shore ledger construction

The draft next reruns the receiver, trace, visible-first, demand, and
absorption constructions on \(G[S]\). This is not transport of the incoming
node-[181] ledger. That ledger is indexed by the original full unified family,
whose excess basins contain unpaid visible-first as well as silent loads; no
upstream statement identifies it with a newly constructed silent-only family
on every derived shore. The construction therefore stops here. The notation
below is retained as notation from the failed draft and creates no fact or
child residual.

Write

\[
 n_i(S):=|\{v\in S:d_S(v)=i\}|,
 \qquad N(S):=\text{number of indexed silent-excess entries on }S. \tag{15.1}
\]

The retired draft let \(o(S)\) be the number of open demand units after the
lexicographically
first maximal \(2/3\)-ledger and maximal same-shore type-(A1) absorption have
been formed on these entries and all type-(A2) conclusions have routed to
their already closed compression/support-dependence rows.  This is a derived
quantity. It is not supplied by the incoming residual.

### Failed Claim 15.1 (local burden)

The retired draft asserted

\[
 N(S)\ge n_3(S)-3n_2(S)-7n_1(S)-11n_0(S)
      =|S|-4b(S).                                      \tag{15.2}
\]

#### Audit

For a receiver \(w\), put \(q_S(w)=3-d_S(w)\) and
\(c_S(w)=4q_S(w)-1\).  The visible-first normalization first routes a
four-visible configuration through the exhaustive exits and repeats after
an exit-(4) record; finite peeling terminates because its integer load measure
decreases. The unavailable step is the next one: the draft transports all
closed exits and then concludes that every unpayable load in the rebuilt
family is silent. The live node-[181] family disproves that identification at
the level of available data, since it also contains unpaid visible-first
loads. Under \(\mathsf H_{\rm shore}\) one would have

\[
 |\mathcal U_S(w)|\ge L_S(w)-c_S(w),                   \tag{15.3}
\]

where the right side may be negative.  The exact peeling identity retains a
recorded load on the entry side when it is removed from a receiver sum, so
(15.3) is unchanged by each normalization step; this is the local form of
\(4D=4D^{P_4}+p_4\).

Every internal-degree-three vertex is routed exactly once, hence
\(\sum_wL_S(w)=n_3(S)\).  Receivers of degrees \(2,1,0\) have capacities
\(3,7,11\).  Summing (15.3) gives the first inequality.  Finally,

\[
 b(S)=3n_0(S)+2n_1(S)+n_2(S),
 \qquad |S|=n_0(S)+n_1(S)+n_2(S)+n_3(S),
\]

and direct subtraction gives

\[
 |S|-4b(S)=n_3(S)-3n_2(S)-7n_1(S)-11n_0(S).
\]

The last degree identity is correct, but the false silence step means that
the lower bound for \(N(S)\), and hence (15.2), has not been proved on the
incoming residual. \(\square\)

### Failed Claim 15.2 (local three-unit pressure)

The retired draft asserted

\[
             3N(S)-o(S)\le b(S).                      \tag{15.4}
\]

Moreover every open unit has a silent owner
\(\xi=(S,w,u,B_u)\) in the ledger of (15.1).

#### Proof

For each entry, the four trace-basin failure alternatives are exhaustive.
The compression and support-dependence alternatives are already closed, and
the handoff alternative is excluded by Lemma 14.3(6).  Thus an entry is
either target-complete-minimal or target-defective.

If it is target-complete-minimal and has at most two private essential
incidences, Lemma 14.3(5) routes it to [124].  Therefore every surviving
target-complete-minimal entry has three private incidences; these incidences
are pairwise disjoint by privacy.  If it is target-defective, Lemma 14.3(4)
gives a canonical token with at least two actual boundary incidences.  The
lexicographically first maximal ledger therefore partitions the \(N(S)\)
entries as

\[
  \Xi_3(S)\ \dot\cup\ \Xi_2(S)\ \dot\cup\ \Xi_{\rm res}(S),
\]

uses

\[
 a(S)=3N_3(S)+2N_2(S)                                 \tag{15.5}
\]

distinct incidences, and creates

\[
 d(S)=N_2(S)+3N_{\rm res}(S)                          \tag{15.6}
\]

demand units.  Equations (15.5)--(15.6) give the exact identity

\[
                 3N(S)=a(S)+d(S).                     \tag{15.7}
\]

Let \(A_1(S)\) be the number of these units absorbed by unused incidences of
the same shore.  These incidences are disjoint from the base assignment and
from one another.  Type-(A2) certificates have left through their closed
rows, so maximal absorption gives

\[
 o(S)=d(S)-A_1(S),
 \qquad a(S)+A_1(S)\le|\delta_G(S)|=b(S).              \tag{15.8}
\]

Substituting (15.8) into (15.7) proves (15.4).  Demand units exist only for
entries in \(\Xi_2(S)\cup\Xi_{\rm res}(S)\), all of which are members of the
silent-excess family used to define \(N(S)\).  Hence every open unit has the
stated silent owner. \(\square\)

### Invalid draft consequence 15.3 (no-open shore estimate)

If \(o(S)=0\), then

\[
                    |S|\le\frac{13}{3}b(S).           \tag{15.9}
\]

#### Proof

By Lemmas 15.1--15.2,

\[
 3(|S|-4b(S))\le3N(S)\le b(S).
\]

Rearranging gives \(3|S|\le13b(S)\). \(\square\)

The identities (15.5)--(15.8) are correct algebra for the newly defined draft
ledger, and the displayed boundary incidences are counted once. That ledger
is not the incoming one, while (15.2) is unproved. Therefore (15.9) is not a
node-[181] consequence and this section supplies no child.

---

## 16. An open unit forces the strict block--cut move

### Lemma 16.1 (an ambient cubic vertex is not a cut vertex of \(G\))

If \(d_G(v)=3\), then \(G-v\) is connected.

#### Proof

The minimal counterexample is connected: otherwise one connected component
would be a smaller graph of minimum degree at least three with no
power-of-two cycle.  Suppose \(G-v\) has \(k\ge2\) components.  Each such
component sends at least two edges to \(v\), because a component sending one
edge would make that edge a bridge.  Hence
\(d_G(v)\ge2k\ge4\), contrary to \(d_G(v)=3\). \(\square\)

### Lemma 16.2 (nonseparating receivers make every load visible)

Let \(S\) be a derived shore, \(w\) a receiver, and \(u\) a routed load whose
canonical trace ends with the edge \(tw\).  Fix a completion port \(wh\).
If \(t\) lies in a component of \(S-w\) that is reached by an actual
\(h\)-to-\(S\) connector avoiding \(w\), then \(u\) is visible through
\(wh\).  In particular this holds through every port if

\[
 d_S(w)=1,
 \quad\text{or}\quad
 d_S(w)=2\text{ and }S-w\text{ is connected}.          \tag{16.1}
\]

#### Proof

By Lemma 16.1, \(G-w\) is connected.  Choose a simple path in \(G-w\) from
\(h\) into the component of \(S-w\) containing \(t\), and stop it at its
first vertex \(r\) in \(S\).  Such a path is exactly the connector assumed
in the first sentence; in the two cases of (16.1), any \(h\)-to-\(t\) path
in \(G-w\) has its first entry in that unique component.  Its prefix
\(\Gamma:h\leadsto r\) has all internal vertices outside \(S\).  The entering
edge shows \(d_S(r)\le2\), so \(r\) is a receiver.  By the hypothesis, choose
an internal path \(Q_0:r\leadsto t\) in the relevant component of \(S-w\)
and append \(tw\).  The connector and this channel meet only at \(r\), so
\(\Gamma\circ Q_0\circ tw\) is a simple receiver-entry return avoiding
\(wh\).  Replacing \(Q_0\circ tw\) by the first scheduled channel with the
same terminal trace edge preserves these properties and satisfies the second
clause of `VisibleFor`.  Thus \(u\) is visible.

If \(d_S(w)=1\), deleting the leaf \(w\) leaves \(S-w\) connected.  The
second case of (16.1) states the same connectivity explicitly. \(\square\)

### Proposition 16.3 (open-owner split)

Let an open unit of \(\mathscr L_S\) have owner
\(\xi=(S,w,u,B_u)\).  Then

\[
 d_S(w)=2,
 \qquad S-w=K\mathbin{\dot\cup}H                         \tag{16.2}
\]

for exactly two nonempty connected components \(K,H\).  Both are proper
derived shores and

\[
 \begin{aligned}
 |S|&=|K|+|H|+1,\\
 b(K)+b(H)&=b(S)+1,\\
 b(K)&\ge2,\qquad b(H)\ge2.                             \tag{16.3}
 \end{aligned}
\]

#### Proof

By Lemma 15.2 the owner is a silent excess load, so its receiver is saturated.
The case \(d_S(w)=0\) is impossible: connectivity would give
\(S=\{w\}\), which has no internal-degree-three vertex and hence no routed
load.  If \(d_S(w)=1\), Lemma 16.2 makes every routed load visible through
both ports; saturation gives at least eight loads, so a port carries four.
If \(d_S(w)=2\) and \(S-w\) is connected, the same lemma makes every load
visible through the unique port; saturation gives at least four.  Either
conclusion contradicts that \(u\) is in the silent-excess family.

Therefore \(d_S(w)=2\) and \(S-w\) is disconnected.  Since \(S\) is
connected and \(w\) has exactly two neighbours in \(S\), deletion of \(w\)
has exactly two components, one containing each neighbour.  This proves
(16.2) and the order identity.

Let \(b_K^0\) and \(b_H^0\) count the original edges of \(\delta_G(S)\)
whose endpoint in \(S\) lies in \(K\) and \(H\), respectively.  The third
edge at \(w\) is the unique edge of \(\delta_G(S)\) incident with \(w\), so

\[
        b(S)=1+b_K^0+b_H^0.                            \tag{16.4}
\]

There is no edge between \(K\) and \(H\), and each has exactly one edge to
\(w\).  Hence

\[
        b(K)=1+b_K^0,\qquad b(H)=1+b_H^0.              \tag{16.5}
\]

Adding (16.5) and using (16.4) gives
\(b(K)+b(H)=b(S)+1\).  Finally a cut of size one in connected \(G\) is a
bridge, so Lemma 14.2(d) gives \(b(K),b(H)\ge2\). \(\square\)

### Quantitative progress

Replacing \(S\) by \(K,H\) changes the active vertex measure by

\[
 M_{\rm after}-M_{\rm before}
   =|K|+|H|-|S|=-1.                                   \tag{16.6}
\]

Every child is a proper subset of \(S\).  The separator \(w\) is accounted
once by the \(+1\) in the first line of (16.3), and the new interface cost is
accounted once by the \(+1\) in its second line.  Thus (16.6) is a genuine
residual decrease with no dropped owner, vertex, or boundary unit.

---

## 17. The boundary-two terminal is closed completely

The algebra (15.9) is already strong enough when \(b(S)\ge3\):

\[
 \frac{13}{3}b(S)\le7b(S)-8
 \quad\Longleftrightarrow\quad b(S)\ge3.               \tag{17.1}
\]

The only terminal not covered by (17.1) has \(b(S)=2\).  It is closed by the
following elementary lemma; no finite search is used.

### Lemma 17.1 (small two-boundary shore contains \(C_4\) or \(C_8\))

Let \(S\) be a connected induced ambient-cubic shore in a bridgeless simple
graph.  If \(b(S)=2\) and \(|S|\le8\), then \(G[S]\) contains a cycle of
length four or eight.

#### Proof

Because

\[
 2=b(S)=\sum_{v\in S}(3-d_S(v)),                       \tag{17.2}
\]

the degree deficit is either two degree-two vertices or one degree-one
vertex.  The latter is impossible.  Indeed both boundary edges would then be
incident with the degree-one vertex \(x\); its unique internal edge would be
the only edge joining \(S-\{x\}\) to \(x\) and the outside, hence a bridge
of \(G\).  Thus \(G[S]\) has exactly two vertices of degree two and every
other vertex has degree three.  The degree sum is \(3|S|-2\), so \(|S|\) is
even.  The case \(|S|=2\) is incompatible with (17.2).  It remains to treat
orders four, six and eight.

If \(|S|=4\), the graph has five edges and is \(K_4\) with one edge deleted;
it contains a \(4\)-cycle.

Let \(|S|=6\).  If the graph is triangle-free, take a cubic vertex \(v\).
Its three neighbours are independent.  Each needs a further neighbour among
the remaining two vertices, and two of them therefore share such a neighbour;
together with \(v\) they form a \(4\)-cycle.  Now suppose \(abc\) is a
triangle, and let \(k\) of its vertices be the two degree-two terminals.  A
cubic triangle vertex has one spoke to the remaining three vertices.  In the
absence of a \(4\)-cycle, spoke endpoints of distinct triangle vertices are
distinct and nonadjacent.  The graph has eight edges, so the graph induced by
the three outside vertices has \(2+k\) edges.  If \(k=0\), the three spoke
endpoints would have to support two edges, contrary to their required
nonadjacency.  If \(k=1\), the outside graph has three edges and is a triangle,
again joining the two spoke endpoints.  If \(k=2\), it would have four edges
on three vertices.  All cases are impossible without a \(4\)-cycle.

Let \(|S|=8\).  First suppose the graph is triangle-free.  For a cubic
vertex \(v\), let \(A\) be its three independent neighbours and let \(B\)
be the other four vertices.  A vertex of \(B\) has at most one neighbour in
\(A\), otherwise it and \(v\) give a \(4\)-cycle.  If \(t\) terminals lie
in \(A\), the vertices of \(A\) require \(6-t\) edges to \(B\).  Hence
\(6-t\le4\), so \(t=2\) and equality holds.  Every vertex of \(B\) then has
one neighbour in \(A\); all terminals have already been used, so every vertex
of \(B\) has two neighbours in \(B\).  The induced graph on four vertices is
therefore a \(4\)-cycle.

It remains that \(abc\) is a triangle.  Let \(F=S-\{a,b,c\}\) and let
\(k\) terminals lie on the triangle.  There are \(3-k\) spokes and, since
the whole graph has eleven edges,

\[
                  |E(F)|=5+k.                         \tag{17.3}
\]

In the absence of a \(4\)-cycle, distinct spoke endpoints are distinct and
nonadjacent.

- If \(k=2\), the degree sequence in \(F\) is
  \((3,3,3,3,2)\).  Its complement has degree sequence
  \((2,1,1,1,1)\), hence is a three-vertex path plus a disjoint edge.  If
  its edges are \(xa,xb,cd\), then \(a-c-b-d-a\) is a \(4\)-cycle in
  \(F\).
- If \(k=1\) and the outside terminal is a spoke endpoint, \(F\) has degree
  sequence \((3,3,3,2,1)\).  Deleting its degree-one vertex leaves five
  edges on four vertices, a \(K_4\) minus one edge, and hence a
  \(4\)-cycle.  If the outside terminal is not a spoke endpoint, the degree
  sequence is \((3,3,2,2,2)\).  Call the degree-three vertices \(p,q\).
  If they are nonadjacent they share the three remaining vertices and give a
  \(4\)-cycle.  If they are adjacent, each has two neighbours among the
  remaining three.  Their two neighbour sets meet in exactly one vertex;
  the two noncommon vertices must be adjacent to complete their degree two,
  and these four vertices with \(pq\) give a \(4\)-cycle.
- If \(k=0\), let \(d,e,f\) be the three independent spoke endpoints and
  let \(g,h\) be the other vertices of \(F\).  If \(gh\notin E(F)\), all
  five edges of \(F\) lie in \(K_{3,2}\); two of \(d,e,f\) then meet both
  \(g,h\), giving a \(4\)-cycle.  Hence \(gh\in E(F)\).  The other four
  edges have degree pattern \((2,1,1)\) on \(d,e,f\): each spoke endpoint
  needs at least one edge in \(F\).  They have pattern \((2,2)\) on
  \(g,h\), since each already uses \(gh\), has degree at most three, and
  the four cross edges must all be counted.  Relabel so the cross edges are
  \(dg,dh,eg,fh\), and relabel the triangle so its spokes are
  \(ad,be,cf\).  Then
  \[
       a-b-e-g-d-h-f-c-a
  \]
  is an \(8\)-cycle.

Thus every case contains \(C_4\) or \(C_8\). \(\square\)

### Corollary 17.2 (the \(b=2\) no-open arm is empty)

If \(o(S)=0\) and \(b(S)=2\), Corollary 15.3 gives
\(|S|\le26/3\), hence \(|S|\le8\).  Lemma 17.1 gives a cycle of length four
or eight, contradicting C-1.  Thus this arm is closed.

Notice also that an open-owner split cannot start at \(b(S)=2\): (16.3)
would give \(b(K)+b(H)=3\) while each summand is at least two.  This is an
independent exact check on the terminal.

---

## 18. The seven-deficit theorem

### Theorem 18.1 (sharp shore estimate)

On the node-[181] branch, every surviving derived shore satisfies

\[
                       |S|\le7b(S)-8.                  \tag{18.1}
\]

In particular, every original support
\(X\in\widetilde{\mathcal X}\) satisfies

\[
                       |X|\le7\defp(X)-8.              \tag{18.2}
\]

#### Proof

Use strong induction on \(|S|\).  By Lemma 14.2, \(b(S)\ge2\).

If \(o(S)=0\), Corollary 15.3 gives
\(|S|\le13b(S)/3\).  When \(b(S)\ge3\), (17.1) gives (18.1).  When
\(b(S)=2\), Corollary 17.2 closes the branch; hence no target-free
counterexample shore remains in this case.

Suppose \(o(S)>0\).  Proposition 16.3 gives two proper children \(K,H\).
They retain the shore interface by Lemmas 14.2--15.2, so the induction
hypothesis applies to each.  Using (16.3),

\[
\begin{aligned}
 |S|
   &=|K|+|H|+1\\
   &\le (7b(K)-8)+(7b(H)-8)+1\\
   &=7(b(S)+1)-15\\
   &=7b(S)-8.
\end{aligned}                                         \tag{18.3}
\]

This proves (18.1).  For a root Type A support,
\(b(X)=\defp(X)\) by ambient cubicity, giving (18.2). \(\square\)

### 18.2 Exact decomposition-tree balance

The induction can be audited without hiding any charge.  Let a completed
shore-exhaustion tree have \(\ell\) no-open leaves and \(t\) split vertices.
It is a full binary tree, so \(t=\ell-1\).  Repeated use of (16.3) gives the
literal identities

\[
 |S|=\sum_{L\text{ leaf}}|L|+t,
 \qquad
 \sum_{L\text{ leaf}}b(L)=b(S)+t.                    \tag{18.4}
\]

Every surviving leaf has \(b(L)\ge3\) and satisfies
\(|L|\le7b(L)-8\).  Therefore

\[
\begin{aligned}
 |S|
 &\le\sum_L(7b(L)-8)+t\\
 &=7(b(S)+t)-8\ell+t\\
 &=7b(S)+8(\ell-1)-8\ell\\
 &=7b(S)-8.
\end{aligned}                                         \tag{18.5}
\]

Thus each separator is paid exactly once; the \(+1\) boundary increment is
neither lost nor charged twice.  At the transition level, (16.6) says the
active residual loses exactly one vertex per split.  At the completed-tree
level, (18.4)--(18.5) account for every original vertex and every newly
exposed boundary incidence.

---

## 19. Global summation and contradiction

Put

\[
                  Q(Y):=\defp(Y)-\sigma(Y).            \tag{19.1}
\]

Let \(\mathcal E_B\) be the Type B bridge/envelope residual family.  The
incoming Type B ledger gives

\[
 M_B:=\sum_{Y\in\mathcal E_B}|Y|=o(|R|),
 \qquad \sigma(G)=o(|R|).                              \tag{19.2}
\]

Every canonical support outside \(\mathcal E_B\) is accounted as follows.

- If \(\No(Y)\ge0\), then
  \[
       |Y|\le4Q(Y)\le7Q(Y).                            \tag{19.3}
  \]
- If \(\No(Y)<0\) and it is Type A with no handoff, then
  \(\sigma(Y)=0\) and Theorem 18.1 gives
  \[
       |Y|\le7\defp(Y)-8<7Q(Y).                        \tag{19.4}
  \]
- Every other negative support has already routed through the Type B
  handoff/bridge ledger; its only surviving mass is included in
  \(\mathcal E_B\).

The canonical supports partition \(R\), and their deficits and assigned
surpluses add.  Moreover

\[
 \left|\sum_{Y\in\mathcal E_B}Q(Y)\right|
 \le3M_B+\sigma(G)=o(|R|),                             \tag{19.5}
\]

because positive deficiency is at most three per vertex and all assigned
surplus is bounded by the global surplus.  Summing (19.3)--(19.4), using
(19.2)--(19.5), gives

\[
\begin{aligned}
 |R|-M_B
   &\le7\sum_{Y\notin\mathcal E_B}Q(Y)\\
   &=7Q(R)-7\sum_{Y\in\mathcal E_B}Q(Y),
\end{aligned}
\]

and hence

\[
             |R|\le7(\defp(R)-\sigma(R))+o(|R|).       \tag{19.6}
\]

It remains to compare (19.6) with the retained cap.  Theorem 1.5 gives

\[
 \frac{\defp(R)-\sigma(R)}{|R|}\le\tau^\ast+o(1),
 \qquad
 \theta^\ast=\frac{3}{4c_{13}-99},
 \qquad
 \tau^\ast=\frac{45}{4c_{13}-138}.                    \tag{19.7}
\]

The registered finite constant satisfies
\(c_{13}=118.108581006\ldots>453/4\).  Therefore

\[
 7\tau^\ast<1,
 \qquad
 1-7\tau^\ast
   =\frac{4c_{13}-453}{4c_{13}-138}
   =0.0581\ldots>0.                                   \tag{19.8}
\]

Divide (19.6) by \(|R|\) and use (19.7):

\[
                    1\le7\tau^\ast+o(1).              \tag{19.9}
\]

For sufficiently large \(|R|\), the \(o(1)\) term is smaller than half the
positive margin in (19.8), contradicting (19.9).  Hence

\[
                         \boxed{\mathcal B_{181}\Longrightarrow\bot}. \tag{19.10}
\]

This closes node [181].

For completeness, the cap used here is itself an accumulated upstream fact,
not a new assumption.  On the hot arm, the realized window state supplies
\((c_{13}-o(1))p_{13}\log_2n\) bits.  The relabelling-orbit inequality of
keys 501--502 and the \(\tfrac32n\log_2n+O(n)\) skeleton budget give

\[
 c_{13}\theta+\frac34(1-13\theta)-15\theta
 \le\frac32+o(1),
\]

so \((c_{13}-99/4)\theta\le3/4+o(1)\), which is the first
formula in (19.7).  The stub identity then gives the second.  Thus the
numerical contradiction uses no fact introduced after [181].

---

## 20. Closure and implementation audit

### 20.1 Monotone residual ledger

| Step | Incoming residual | Exhaustive outcomes | Quantitative result |
|---|---|---|---|
| Shore-interface transport, §§14–15 | \(\mathcal B_{181}[S]\) | no split; derives \(N(S)\ge|S|-4b(S)\) and \(3N(S)-o(S)\le b(S)\) | all parent facts retained; no currency spent |
| Open-unit test | same shore and ledger | \(o(S)=0\) or \(o(S)>0\) | zero arm closes by (15.9), (17.1), Cor. 17.2; positive arm feeds Prop. 16.3 |
| Block--cut move | \(o(S)>0\) with its actual silent owner | exactly the two components of \(S-w\) | \(M\mapsto M-1\); \(|S|=|K|+|H|+1\); \(b(K)+b(H)=b(S)+1\) |
| Boundary-two terminal | \(o(S)=0,b(S)=2\) | orders \(4,6,8\) after parity | actual \(C_4\) or \(C_8\), so target hit |
| Shore induction | all smaller children closed or bounded | no residual child remains | \(|S|\le7b(S)-8\) |
| Global sum | complete canonical support partition | nonnegative / negative Type A / TypeB bridge residual | \(|R|\le7(\defp(R)-\sigma(R))+o(|R|)\) |
| Density collision | (19.6) plus retained (19.7) | one arithmetic outcome | \(1\le7\tau^\ast+o(1)<1\), contradiction |

The only repeated operation is the newly selected block--cut move, and every
repetition has the strict integer decrease (16.6).  The pressure ledger is not
selected again as a closing move; Lemma 15.2 proves that its already
established interface transports to a child shore.  The trace ear, Hall
projection, same-window cap, and gadget closure are not used in the closing
chain.  Their correct upstream statements remain in the immutable ledger.

### 20.2 No dropped fact and no double charge

- The state at every descendant has \(\mathcal B_{181}\) as its first
  coordinate; all facts in §§1--4 remain queryable.
- A split deletes no graph vertex from the proof account: its receiver appears
  once in (16.3) and (18.4).
- Each boundary incidence used by the base demand ledger or a type-(A1)
  absorber is single-use; equation (15.8) is the complete capacity account.
- Each new child boundary contains exactly one edge to the separator; the two
  such edges replace the separator's one old exterior edge, producing the
  exact net increment one.
- Type B exceptional mass is retained explicitly as \(M_B\), and both its
  vertex mass and its possible \(Q\)-contribution are absorbed only into the
  displayed \(o(|R|)\) term in (19.2), (19.5).
- The sharpened cap is derived from the registered orbit inequalities; it is
  not inserted as a branch assumption.

### 20.3 Lean implementation contract

The following is a retired implementation sketch and must not be implemented
below the existing
`route8PeeledDemandResidual` row without changing node [123] or the original
manuscript.  The implementation should add, at the next unused keys, exactly
these interfaces:

1. `route8ShoreLedgerTransport`: reads the complete [181] ledger and publishes
   (14.1), (15.2), (15.4) for a derived shore; this row also exposes the
   manuscript's same-support ownership clause for type-(A1) absorbers, which
   the current weaker live absorber schema does not store explicitly;
2. `route8OpenOwnerBlockCut`: reads an open unit and publishes the two actual
   children with (16.2)--(16.3) and the strict measure equality (16.6);
3. `route8BoundaryTwoTerminal`: publishes `False` from the no-open
   \(b=2\) arm using Lemma 17.1;
4. `route8SevenDeficit`: well-founded recursion on the active-vertex measure,
   publishing (18.1);
5. `route8Node181Closure`: reads the canonical support partition, the Type B
   sublinear ledger, `relabelingDensityCap`, and the shore estimate, and
   publishes `False` by (19.6)--(19.9).

Each row must read through `FactInputs.get`, append one literal fact through
`AtomicCT.run`, and retain the complete incoming key list.  The recursive row
uses the natural-valued measure (13.3); it needs no callback, detached theorem,
surrogate residual, or strengthened node-[123] statement.

The original LaTeX paper now records the implemented Theorems 0.1–0.2 as
`thm:typeA-unpaid-exit4-reduction` and routes [181] to [124] or [183].
