# The graph at node [181]: complete structural accounting

This document lists every fact that holds for the minimal counterexample $G$ when the proof reaches node [181], the arm taken at every diamond on the way, the technique (register T01–T19) that produced each fact and the register property (A01–I06) it evaluated, and the exact typed data at the leaf. Nothing is projected, summarized, or dropped; the closure of [181] is the theorem in §6, whose hypotheses are exactly the facts listed here.

Sources: `to_formalize/erdos_64_proof.tex` (labels in backticks; node numbers in brackets), `closure_proofs.md` (Theorems 1.3–1.5, 3.1–3.4), and the register `web/frontend/src/structural-survey/data.ts`.

---

## 1. The path from the root to [181]

Each row: node(s) → arm taken → fact retained on the branch state → technique → register rows evaluated.

| Node(s) | Arm taken | Fact retained | Technique | Rows |
|---|---|---|---|---|
| [1]–[2] | yes | $G$ finite simple, $\delta(G)\ge3$, no cycle of length $2^j$ (`def:counterexample`) | — | A04, C03 |
| [4] | — | $G$ is the lexicographically minimal counterexample: minimum $\lvert V\rvert$, then $\lvert E\rvert$, then lexicographic order | T02 | E01 |
| [5]–[7] | no Mersenne return | $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every oriented edge $e$, $\mathrm{Mers}=\{2^k-1:k\ge2\}$ (`lem:return-equivalence`) | T08 | C02 |
| [8] | — | every proper subgraph $H\subsetneq G$ has $\delta(H)\le2$ (`lem:no-proper-core`) | T02 | E02, A07 |
| [9]–[10] | — | every edge has an endpoint of degree $3$; $V_{\ge4}(G)$ is independent (`lem:deletion-critical`) | T03, T02 | E03, A06 |
| — | — | $G$ is bridgeless (`lem:bridgeless`, by contraction of a bridge) | T03, T02 | B02 |
| [11] | — | boundaried pieces $X\oplus_TY$ with boundary degree profile $\mathbf d_\partial$ (`def:boundaried-gluing`, `lem:degree-profile-fibres`) | T05 | B05, B06 |
| [12] | — | context universality: a target-complete identification agrees against every $T$-context; an identification valid only for the actual outside is target-defective (`lem:context-universality`) | T05 | B07, E06 |
| [13] | — | replacement: no $T$-boundaried $X'\preceq_TX$ with the same $\mathbf d_\partial$, no internal power-of-two cycle, internal degrees $\ge3$, strictly smaller (`lem:replacement`) | T02, T03 | E05 |
| [14] | — | hereditary target-uncompressibility: no proper boundaried piece admits a nontrivial target-complete compression (`cor:uncompressible`) | T02, T05 | E05 |
| [15]–[16] | no | $G$ contains an induced $P_{13}$ (`cor:p13-exists`, via the black box `thm:p13free`: $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle) | T18 | I06, C08 |
| [17] | — | $\mathcal P$: a **maximum-cardinality** family of vertex-disjoint induced $P_{13}$'s, $p_{13}=\lvert\mathcal P\rvert=\theta n$, chosen lexicographically first among maximum ones; $W=\bigcup V(P)$, $R=G-W$ | T06, T16 | C09, C10 |
| [18] | — | $P_{13}$ label algebra: $399$ legal labels (sizes $13,60,122,122,63,17,2$), relations $C_s$, obstruction tensor $\Omega_2$ (`lem:labels`) | T17 | D01, G02 |
| [19]/[20]; [125]–[144] | no non-near-cubic surplus survives | near-cubic spine: $m=\tfrac32n+O(\sqrt n)$, $\sigma(G)=2m-3n=O(\sqrt n)$, $\lvert V_{\ge4}\rvert\le\sigma(G)$ (`def:near-cubic-spine`, `prop:nonnear-cubic-sharp-overload-routing`, `thm:tokenized-surplus-accounting-closure`) | T13, T14, T15 | A02, A05, A14 |
| [21] | — | finite constants: $c_\Omega=2.28922315244$, $c_{13}=118.108581006$; two-step obstruction enumeration $543958,432672,111286$ (`lem:curv-enum`, `lem:p13-window-package`) | T17 | I05, A09, G02 |
| [158] | yes | the joint window package of $\mathcal P$ is realized by the labelled skeleton class: $\ge2^{c_{13}p_{13}\log_2n}$ target-complete states assigned canonically to skeletons in $\mathcal G_{n,m}$ (`def:window-realization-test`) | T12 | G01, G03, G06 |
| [22]/[145]–[157] | the live-hot entropy comparison does not close; the cold machinery returns to [24] on its bounded arm | `thm:cold-branch-quantitative-closure` is stated *conditional on absence of node [181]* (clause (v) of `def:surviving-cold-branch`); on the [181] branch its outputs are not available as facts. What is retained is only the return at [24] | T12, T13 | G03, H08 |
| [24] | — | $\theta\le\theta_{\rm win}+o(1)$, $\theta_{\rm win}=1.5/c_{13}=0.0127002$; sharpened on the hot arm to $\theta\le\theta^\ast+o(1)$, $\theta^\ast=0.75/(c_{13}-39/4-15)=0.0080335$ (Theorem 1.5) | T12, T16 | G09, I02 |
| [25]–[27] | — | $\lvert R\rvert\ge(1-13\theta)n$; every component of $R$ is $P_{13}$-free, hence of diameter $\le11$ and $\le6142$ vertices, and has empty internal $3$-core: every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ (`lem:remainder-empty-internal-3-core`, black box) | T06, T18, T04 | C10, C08, A07 |
| [28]–[29] | — | $\defp(X)=\sum_v\max(0,3-d_X(v))$; $\defp(R)\le e(R,W)\le15p_{13}+o(n)$; exact split $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; $(\defp(R)-\sigma_R)/\lvert R\rvert\le15\theta/(1-13\theta)+o(1)$, i.e. $\le\tau_{\rm win}=0.2281749$, sharpened to $\tau^\ast=0.13456$ (`lem:stub-positive`, Theorem 1.5) | T01, T15 | A10, A11, H01 |
| [30] | — | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$ per component; $W_2(R)\ge\omega_{\rm win}\lvert R\rvert-o(\lvert R\rvert)$, $\omega_{\rm win}=2.54365$ (high entropy $2.57407$) (`lem:wedge-lower`) | T01 | A09, F01 |
| [31]–[47] | no rank drop | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$; every rank-reducing dependence is target-defective, a proper compression (forbidden), a proper-support dependence (forbidden, `lem:proper-smearing`), or a whole-graph dependence that is target-defective, has a smaller closed representative, or is exact on labels (`lem:no-silent-global-smearing`); repair identity $s=p-2+2\beta_Z-\sigma_Z$ (`lem:smearing-support-repair`); separated identical wedges are context-universal or defective (`lem:separated-testers`) | T11, T10, T05 | F01–F07, A12 |
| [48] | — | forced obstruction cost $c_\Omega r_\Omega(R)\ge K_{\rm win}\lvert R\rvert-o(\lvert R\rvert)$, $K_{\rm win}=5.82298$ (high entropy $K=5.89263$) (`cor:forced-curvature-cost`) | T12 | G03, H09 |
| [49]–[50] | high entropy | $\eta(R)=\log_2\lvert\mathcal G(R)\rvert/\lvert R\rvert\ge(1-\tau)\log_2\lvert R\rvert-O(1)>\tfrac1{10}\log_2n$: the low-entropy arms (b),(c) of `prop:two-budget` are empty (Corollary 1.4, relabeling orbits) | T12, T16 | G01, G04, I02 |
| [51]–[53] | remaining non-obstruction budget not $<K\lvert R\rvert$ | large-budget branch: the skeleton budget minus the forced obstruction cost is at least $K\lvert R\rvert$; the entropy cap `prop:entropy-high-theta` ($\theta>\Theta(n)$) does not apply; $\Theta(n)=(1.4-K/\log_2n)/(116.808581006-13K/\log_2n)$ | T12 | H09, G08 |
| [55]–[56]; [173] | — | Residual C: $\Delta_{\rm net}(R)=(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau_{\rm win}+o(1)<\tfrac14$ (now $\le\tau^\ast$), decided exactly on the object at [173] (`lem:exact-collision-test`) | T01, T13 | H01, I03 |
| [57]–[61] | $\No(R)<0$ | net charge $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; $\sum_i\No(X_i)=\defp(R)-\sigma(R)-\tfrac14\lvert R\rvert\le-(\tfrac14-\tau)\lvert R\rvert$; some connected canonical support has $\No(X)<0$ (`def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge`); canonical decomposition of $R$ into components with surplus assigned to the piece containing the high-degree vertex (`def:canonical-decomp`) | T13, T04 | H01–H03, D08 |
| [62]; [64]–[85] | Type B closed | high-degree supports: centers independent, fan neighbours cubic, certificate-marked cap $d_G(h)\le8$, the fan-window ledger, B2 disjointness; every Type B support with $\No<0$ outside the bridge residual has a route-8 profile or a positive-deficit fan residual; the bridge residual mass is $M_B\le16\sigma(G)=o(\lvert R\rvert)$ (`lem:typeB-exclusion`, `prop:typeB-bridge-sublinear`, `thm:branch-kill`(b)) | T07, T13, T14, T15 | D03, D04, H05, H06, H08 |
| [63], [86]–[88] | Type A | the negative supports of linear mass are Type A: $\sigma(X)=0$, so every $v\in V(X)$ has $d_G(v)=3$; $X$ is connected, subcubic, $P_{13}$-free, $\operatorname{diam}X\le11$, $\lvert X\rvert\le6142$, empty internal $3$-core, contextually target-safe, hereditarily uncompressible, every deficient vertex supplied from $W$; $\defp(X)<\lvert X\rvert/4$; receivers $w$ with $d_X(w)\le2$, $q(w)=3-d_X(w)$ ports; canonical traces $T_u$ and loads $L(w)$ (`def:typeA-support`, `def:typeA-receiver-load`) | T04, T05, T07 | A03, A11, B05, C08, D08 |
| [89] | some receiver saturated | $L(w)\ge4q(w)$ for some receiver (else `lem:typeA-unsaturated-discharge`: $\defp(X)\ge\tfrac14\lvert X\rvert$, $n_3\le3n_2+7n_1+11n_0$, closing) | T13 | H04, H05 |
| [93] | no | no completion port carries four visible receiver-entry returns (else exits (1)–(7), `lem:typeA-visible-entry`) | T07, T08 | C01, C02 |
| [94] | — | visible-first excess: $S^{\rm exc}_{\rm sil}(X)=\sum_w\lvert\mathcal U(w)\rvert\ge n_3-3n_2-7n_1-11n_0=4D_A(X)$, $D_A(X)=\tfrac14\lvert X\rvert-\defp(X)$ (`lem:typeA-silent-excess-count`, `def:typeA-excess-basin`) | T13, T15 | H05, G07 |
| [95]–[108] | exits (1),(2),(3),(5),(6) closed; (7) absent; (4) peels | at every saturated receiver of every $X\in\tilde{\mathcal X}$: no anchored return of Mersenne length through a port; no two internally disjoint receiver-entry returns through one port with lengths summing to a power of two (`lem:typeA-common-port-return-cycle`); no violated label relation $C_s$ on a shared window; no nontrivial target-complete response compression; no delocalizing response equality; no decorated handoff fan (exit (7)) since $X\in\tilde{\mathcal X}$ produces none; continuation routing at a port gives exits (4)–(6) or a surviving first separator of degree $\ge4$ (`lem:typeA-continuation-routing`, `lem:typeA-cubic-switch-absorption`, `lem:typeA-high-degree-handoff`) | T08, T09, T05, T07 | C01–C05, D01, E05, E06, D03 |
| [109]–[113] | — | the unified negative collection $\tilde{\mathcal X}=\{X:\sigma(X)=0,\No(X)<0,\text{no handoff}\}$ with $\tilde D_A=\sum(\tfrac14\lvert X\rvert-\defp(X))\ge(\tfrac14-\tau)\lvert R\rvert-o(\lvert R\rvert)$; entries $\tilde\Xi=\{(X,w,u,B_u):u\in\mathcal U_X(w)\}$, $\tilde N\ge4\tilde D_A$ (`def:typeA-unified-negative`, `lem:typeA-unified-deficit`, `lem:typeA-unified-burden`) | T13, T15 | H03, H08, G07 |
| [114]–[116] | — | every entry passes to its canonical minimal target-complete response-support core $\mathcal C_{\rm ess}(\xi)\subseteq\partial_EX$, $\alpha(\xi)=\lvert\mathcal C_{\rm ess}\rvert\ge2$ (`lem:typeA-unified-carriers`; entries with $\alpha\le1$ realize exits (4)–(7)) | T11, T05 | F02, F04, B08 |
| [117]; [119]–[122] | two-support entry exists | if every entry had $\pi(\xi)\ge3$ private essential incidences then $3\tilde N\le\defp(R)$ against $\tilde N\ge12(\tfrac14-\tau)\lvert R\rvert$, impossible; so some $\xi$ has $\pi(\xi)\le2$ (`prop:typeA-unified-reduction`) | T15, T01 | G07, H06 |
| [118], [124] | route-8 two-support closed | no terminal two-support route-8 obstruction (`thm:typeA-two-carrier-nogo`); Theorem 3.2: every two-support entry realizes exit (4), so route-8 two-support entries do not occur | T05, T11 | E06, F05 |
| [101]–[102], [123] | target-defect two-support: peel | each such entry is peeled: its load leaves the receiver sum, $\Lambda_4=\sum_w\lvert\mathcal L(w)\setminus P_4(w)\rvert$ decreases by one, the deficit by $\tfrac14$, no invariant weakened (`lem:typeA-exit4-discharge`, `lem:typeA-exit4-finite-descent`); iterate while $\tilde D_A^{P_4}\ge(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$ | T19 | E08, H10 |
| [181] | the reduced-rate test fails | the leaf (§4) | — | — |

Arms not on the path (for completeness): [3] not a counterexample; [16] $P_{13}$-free; [20] non-near-cubic surplus (routed back to the spine); [23] live-hot overflow; [159]–[172] dense-packing residual ($\theta>\theta_{\rm win}$, the no-arm of [158]) and its nodes [163]–[172], [178]–[180], [182]; [60] net-cap contradiction; [90]–[92] unsaturated; [96], [98], [100], [104], [106] closed exits; [108] handoff; [124] closed.

---

## 2. The complete hypothesis ledger, by register category

Every fact below is on the branch state $\mathcal B_{181}$. "Produced by" names the technique; "Row" the register property it evaluates.

### A — size, degree, sparsity, local incidence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| A-1 | $\delta(G)\ge3$; $n=\lvert V(G)\rvert\to\infty$ along the branch | `def:counterexample` | — | A04, A01 |
| A-2 | $m=\tfrac32n+O(\sqrt n)$; $\sigma(G)=2m-3n=O(\sqrt n)$; $\lvert V_{\ge4}(G)\rvert\le\sigma(G)$ | `def:near-cubic-spine` | T13/T14/T15 (surplus ledger) | A02, A05, A14 |
| A-3 | $m\ge\lceil3n/2\rceil$, $m\le2n-2$; $\beta=m-n+1\ge n/2+1$; $\beta+\lambda=n-2$; $\sigma=2\beta-n-2$ | invariants 9–13 | T01 | A02, A12, A13 |
| A-4 | $V_{\ge4}(G)$ independent; every edge has a degree-3 endpoint | `lem:deletion-critical` | T03/T02 | A06, E03 |
| A-5 | every vertex of every Type A support has $d_G=3$; a vertex of internal degree $3-q$ has $q$ stubs to $W$; $\defp(X)=\sum q$; $\defp(X)<\lvert X\rvert/4$ on $\tilde{\mathcal X}$ | `def:typeA-support` | T05 | A03, A11 |
| A-6 | $\defp(R)\le e(R,W)\le15p_{13}+o(n)$; $e(R,W)+2e_\times(W)=15p_{13}+\sigma_W$; each window carries at most $15$ stubs (interior vertex one, end two) | `lem:stub-positive` | T01/T15 | A10, A11 |
| A-7 | $(\defp(R)-\sigma_R)/\lvert R\rvert\le\tau^\ast+o(1)$, $\tau^\ast=15\theta^\ast/(1-13\theta^\ast)=0.13456$ | Theorem 1.5 | T12/T16 | A11, H01 |
| A-8 | $W_2(C)\ge3\lvert V(C)\rvert-2\defp(C)$; $W_2(R)\ge2.54365\lvert R\rvert-o(\lvert R\rvert)$ | `lem:wedge-lower` | T01 | A09 |
| A-9 | every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ | `lem:remainder-empty-internal-3-core` | T18 | A07 |
| A-10 | every component of $G-V(X)$ sends $\ge2$ edges to $X$; $\defp(X)\ge2$ | `lem:bridgeless` | T03/T02 | A11, B02 |

### B — connectivity, cuts, boundaries, contexts

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| B-1 | $G$ is bridgeless; every edge lies on a cycle | `lem:bridgeless` | T03/T02 | B02 |
| B-2 | every proper subgraph has $\delta\le2$ | `lem:no-proper-core` | T02 | E02, B01 |
| B-3 | $R=G-W$; its components are the canonical supports; no edges of $R$ between distinct components; surplus units of $V_{\ge4}\cap V(R)$ assigned to their component | `def:canonical-decomp` | T04 | B01, D08 |
| B-4 | boundaried pieces, boundary degree profiles, gluing $X\oplus_TY$; quotients fibrewise over $\mathbf d_\partial$ | `def:boundaried-gluing`, `lem:degree-profile-fibres` | T05 | B05, B06 |
| B-5 | context universality (target-complete identifications agree against every context) | `lem:context-universality` | T05 | B07 |
| B-6 | trace basins $B_u$: lexicographically first inclusion-minimal trace-complete connected subgraph containing $T_u$; trace-response state $\rho_u(B_u)=(\mathbf d_\partial(B_u),\mathcal R_u(B_u),\profile)$ | `def:typeA-trace-basin` | T05/T10 | B08, B06 |
| B-7 | boundary incidences $\partial_EX$, $\lvert\partial_EX\rvert=\defp(X)$; every $u$-supported coordinate leaving $X$ records one | `def:typeA-route8-carriers` | T05 | B05, B09 |
| B-8 | the demand ledger on $\tilde\Xi$: partition $\Xi_3\sqcup\Xi_2\sqcup\Xi_{\rm res}$ with disjoint incidence sets $A(\xi)$ ($3$ or $2$ per entry), lexicographically first maximizing $N_3$ then $N_2$; $\mathsf P_{\rm ext}=N_2+3N_{\rm res}$; $3N_3+2N_2\le\defp(R)$ | `def:typeA-pressure-ledger`, `lem:typeA-pressure-ledger-no-overcount` | T14/T15 | B09, H06 |
| B-9 | absorbers: (A1) unused boundary incidences of the same support, (A2) profile-dependence certificates; $\mathsf P_{\rm open}=\lvert\mathcal U_{\rm press}\setminus\mathcal U_{\rm abs}\rvert$; $3\tilde N-\mathsf P_{\rm open}\le\defp(R)$ once (A2) has routed | `def:typeA-pressure-absorbers`, `lem:typeA-pressure-absorber-no-overcount` | T14/T15 | B09, H06 |
| B-10 | window blockers: each open unit is assigned one incidence $c(\upsilon)$ and its unique window $P(\upsilon)$; $\mathsf P_{\rm open}=\sum_PB_{\rm open}(P)$ | `def:typeA-open-window-blocker`, `lem:typeA-open-window-blocker-count` | T15 | B09, A10 |
| B-11 | $\mathsf P_{\rm open}\ge(3-13\tau)\lvert R\rvert-o(\lvert R\rvert)$ and $\mathsf P^{+}_{\rm zero}\ge\varepsilon_{\rm prim}\lvert R\rvert-o(\lvert R\rvert)$ on the branch (so the offered consumers of [181] are vacuous) | Theorem 3.1 | T01 | B09, H09 |

### C — paths, cycles, lengths

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| C-1 | no cycle of $G$ has length in $\mathrm{Pow}=\{2^j\}$; $R_e(G)\cap\mathrm{Mers}=\varnothing$ for every oriented edge | `lem:return-equivalence` | T08 | C02, C03 |
| C-2 | every non-triangle edge lies on a $(2^k+1)$-cycle, $k\ge2$; every completion port $(w,h)$ not in a triangle with a degree-3 third vertex has an anchored return of length exactly $2^k$ | Theorem 2.1, Corollary 2.2 | T03/T02 | C02, C05 |
| C-3 | every completion port has at least one anchored return | `lem:typeA-port-return` | T08 | C02 |
| C-4 | connector/channel arithmetic: for a receiver-entry return $\Gamma\circ Q$ through $(w,h)$ with connector length $g$, $g+\lambda\notin\mathrm{Mers}$ for all $\lambda\in\Lambda_X(r,w)$; interval form with $I_X(r,w)$ | `lem:typeA-spectral-pressure`, `def:typeA-channel-spectrum` | T09 | C01, C04 |
| C-5 | theta closure: all branch-pair sums in a theta avoid $\mathrm{Pow}$; ear closure; symmetric difference of overlapping cycles avoids $\mathrm{Pow}$ | invariants 31–33 | T08/T09 | C05–C07 |
| C-6 | two-path criterion: two internally disjoint returns through one port with lengths summing to $2^k$ give a forbidden cycle | `lem:typeA-common-port-return-cycle`, invariant 30 | T08 | C05 |
| C-7 | every cycle length has an odd prime divisor; no single odd prime divides all cycle lengths; overlap formula $q_p(E)=q_p(C)+q_p(D)-2t$ flat and non-killing | invariants 36–38 | T09/T11 | C04 |
| C-8 | $G$ has an induced $P_{13}$; $R$ has none; every component of $R$ has diameter $\le11$ and $\le6142$ vertices | `cor:p13-exists`, `lem:remainder-empty-internal-3-core` | T18/T06 | C08 |
| C-9 | $p_{13}$ is the **maximum** number of vertex-disjoint induced $P_{13}$'s; $\theta=p_{13}/n\le\theta^\ast+o(1)$ | [17], Theorem 1.5 | T06/T12 | C09, G09 |
| C-13 | a component with $\ge2^{\ell+1}$ vertices has an induced path on $\ell+2$ vertices from each receiver; a window with two attached induced $R$-paths at positions $i<j$ of lengths $\ge12-i$, $\ge j$, disjoint, non-adjacent, avoiding stubs into the retained segments, gives $p_{13}+1$ windows | Lemmas 3.15, 3.16 | T06/T15 | C08, C09 |

### D — local configurations, motifs, overlap, symmetry

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| D-1 | $399$ legal $P_{13}$ labels; relations $C_s$; the zero-defect quotient through path lengths $1,2,3$ is the identity | `lem:labels` | T17 | D01, G02 |
| D-2 | $0.795414$ of locally safe wedges are obstructing; $c_\Omega=2.2892$ bits per independent obstruction coordinate | `lem:curv-enum` | T17 | D02, G02 |
| D-3 | Type B: fan-safe graphs, certificate labellings, $d_G(h)\le8$ for certificate-marked fans, degree-4 profiles, B2 disjointness, bridge residual sublinear | [64]–[85] | T07/T13/T14 | D03, D04 |
| D-4 | canonical decomposition, canonical traces (lexicographically first receiver-reaching paths in $X_3$), canonical payable set $A(w)$ (visible-first order), lexicographically first ledgers and assignments | `def:canonical-decomp`, `def:typeA-receiver-load`, `def:typeA-excess-basin`, `def:typeA-pressure-ledger` | T16 | D08, I02 |
| D-5 | all auxiliary objects are functions of the labelled adjacency matrix under a fixed tie-break; states are $\mathrm{Sym}(R)$-invariant relative to $W$ | `lem:skeleton-dominates`, Theorem 1.3 | T16/T12 | D09, G06 |

### E — extremality, criticality, replacement, quotients

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| E-1 | lexicographic minimality of $G$ ($\lvert V\rvert$, then $\lvert E\rvert$, then lexicographic) | [4] | T02 | E01 |
| E-2 | no proper subgraph with $\delta\ge3$; deletion criticality | [8]–[9] | T02/T03 | E02, E03 |
| E-3 | replacement lemma and hereditary uncompressibility (I5) | `lem:replacement`, `cor:uncompressible` | T02/T05 | E05 |
| E-4 | a quotient is valid only if target-complete against every context; otherwise target-defective | `lem:context-universality` | T05 | E06 |
| E-5 | exit-(4) peeling is a well-founded descent on $\Lambda_4$ preserving every invariant | `lem:typeA-exit4-finite-descent` | T19 | E08, H10 |
| E-6 | exits (5) and (6) never occur at any saturated receiver of $\tilde{\mathcal X}$ (standing-invariant contradictions); exit (7) is absent | `lem:typeA-exits-discharged`, `lem:typeA-unified-burden` | T02/T05 | E05, E09 |

### F — local tests, rank, dependence

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| F-1 | full obstruction rank $r_\Omega(R)\ge W_2(R)-o(W_2)$ | `lem:full-rank` | T11 | F02, F07 |
| F-2 | rank drop routes to target defect, proper compression, or support enlargement; proper enlargements $Z\subsetneq G$ are impossible; whole-graph dependence cannot silently reduce rank | `lem:curvature-dependence-routing`, `lem:proper-smearing`, `lem:no-silent-global-smearing` | T10/T11 | F03–F07 |
| F-3 | separated identical wedges are context-universal or target-defective | `lem:separated-testers` | T05/T11 | F05 |
| F-4 | every entry's trace basin fails target-complete-minimality only through alternative (a) — a trace-local quotient forgetting a coordinate on an internal edge of $B_u$ is distinguished by a compatible context; (b),(c),(d) do not occur | `def:typeA-trace-basin`, Theorem 3.2 | T05/T16 | F04, E06 |
| F-5 | $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$; every $c\in\mathcal C_{\rm ess}$ has a declared deletion witness (internal/mixed) with boundary-incidence support | `lem:typeA-unified-carriers`, `def:typeA-carrier-deletion-witness`, `lem:typeA-deletion-witness-declared` | T05/T11 | F04, F05 |

### G — counting and information

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| G-1 | $\lvert\mathcal G_{n,m}\rvert=\binom{\binom n2}{m}$; skeleton budget $\tfrac32n\log_2n+o(n\log n)$ | `lem:skeleton-dominates`, `lem:near-cubic-budget` | T12 | G01 |
| G-2 | the joint window package is realized: $\ge2^{c_{13}p_{13}\log_2n}$ states | [158] yes | T12 | G03 |
| G-3 | orbit count: $\log_2\lvert\Phi(\mathcal S)\rvert\le\log_2\lvert\mathcal S\rvert-(\tfrac34\lvert R\rvert-15p_{13})\log_2\lvert R\rvert+O(n)$ | Theorem 1.3 | T12/T16 | G01, G04 |
| G-4 | $\eta(R)\ge(1-\tau)\log_2\lvert R\rvert-O(1)$; high-entropy arm of `prop:two-budget` | Corollary 1.4 | T12 | G04 |
| G-5 | forced cost $c_\Omega r_\Omega\ge K_{\rm win}\lvert R\rvert$; the large-budget arm: remaining budget $\ge K\lvert R\rvert$ | [48], [53] | T12 | G03, H09 |
| G-6 | no double counting: demand incidences pairwise disjoint; absorbers single-use; the exact stage identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ | `lem:typeA-pressure-ledger-no-overcount`, `lem:typeA-peeling-stage-accounting` | T15 | G07 |
| G-7 | asymptotics: all bounds with $o(n)$, $o(\lvert R\rvert)$ error terms; exact collision decided at [173] | `lem:exact-collision-test` | T12/T17 | G08 |

### H — charging and discharging

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| H-1 | $\No(X)=\defp(X)-\sigma(X)-\tfrac14\lvert V(X)\rvert$; superadditivity; some connected support has $\No<0$ | `def:net-charge`, `lem:netcharge-superadd`, `prop:negative-net-charge` | T13 | H01–H03 |
| H-2 | Type A: each cubic vertex charges $\tfrac14$ to its receiver; receiver charge $q(w)-\tfrac14-\tfrac14L(w)$; unsaturated receivers ($L\le4q-1$) pay; thresholds $H_0\le4,H_1\le8,H_2\le12$ | `lem:typeA-threshold-algebra`, `lem:typeA-unsaturated-discharge`, `lem:typeA-exit4-peeling-charge` | T13 | H04, H05 |
| H-3 | saturated receivers with silent excess: $S^{\rm exc}_{\rm sil}\ge4D_A(X)$; the unified deficit $\tilde D_A\ge(\tfrac14-\tau)\lvert R\rvert$; $\tilde N\ge4\tilde D_A$ | [94], [111]–[113] | T13/T15 | H05, H08 |
| H-4 | private-support budget: three private incidences per entry would force $3\tilde N\le\defp(R)$, contradiction; hence two-support entries exist | `prop:typeA-unified-reduction` | T15 | H06 |
| H-5 | the demand ledger, absorbers and blockers (B-8–B-11) | — | T14/T15 | H06 |
| H-6 | Type B bridge mass $o(\lvert R\rvert)$ | `prop:typeB-bridge-sublinear` | T13/T15 | H08 |
| H-7 | the required rate: with $\tau^\ast$, a single-use charging of $c$ incidence-units per entry contradicts iff $c>0.2914$; the branch is empty if every component has $\lvert X\rvert\le7\defp(X)$ (diagnostic) | Theorem 3.4 | T13 | H09 |
| H-8 | finite descent $\Lambda_4$ | `lem:typeA-exit4-finite-descent` | T19 | H10 |

### I — finite certification and external inputs

| # | Fact | Source | Produced by | Row |
|---|---|---|---|---|
| I-1 | the black box `thm:p13free` (HSS): $P_{13}$-free $+\ \delta\ge3\Rightarrow$ power-of-two cycle; consumed as A-9 and C-8 | [15]–[16] | T18 | I06 |
| I-2 | Bondy–Vince / Gao–Ma are citable with exact hypotheses; the appendix's derived input "$\lvert Y\rvert<5b(Y)^2$ for quiet almost-cubic blocks" is *assumed*, not proved (`lem:app-typeA-quiet-bound`, `lem:app-dense-window-closure`) | appendix | T18 (not yet invoked) | I06 |
| I-3 | finite constants $c_\Omega$, $c_{13}$, label counts; the $91$-barrier computation; the two-strand table | `app:curv-code`, `lem:labels`, [167] | T17 | I05, I01 |
| I-4 | exact small-order collision decided on the object | [173] | T17 | I03, I04 |

---

## 3. Techniques already used upstream, and the structural properties each one consumed

| Technique | Where used | Properties consumed (register rows) | What it left behind |
|---|---|---|---|
| T01 Direct invariant calculation | [28]–[30], [56], [119]–[122], Theorems 3.1, 3.4 | A02, A09–A12, H01, H06, H09 | the inequalities of A-3, A-6–A-8, H-3, H-4, B-11 |
| T05 Boundary-interface analysis | [11]–[14], trace basins, response states, cores, deletion witnesses, contexts | B05–B08, E05, E06, F04, F05 | B-4–B-7, E-3, E-4, F-4, F-5 |
| T08 Path–cycle and cycle-space analysis | [5]–[7], invariants 30–33, `lem:typeA-port-return`, `lem:typeA-common-port-return-cycle` | C02, C03, C05–C07 | C-1, C-3, C-5, C-6 |
| T10 Uncrossing and minimal obstruction | [31]–[47] (dependence localization), trace-basin minimality, continuation routing | F03–F07, B08, D05 (cold branch only) | F-2; on the [181] branch the corridor/overlap consumers of [169]–[172] are **not** available (they live on the dense-packing residual) |
| T11 Linear-algebraic rank | [31]–[47], response-support cores | F01–F07, A12 | F-1, F-2, F-5 |
| T12 Counting and information | [21], [48]–[55], [158], Theorems 1.3–1.5, Corollary 1.4 | G01–G09, H09 | G-1–G-5, A-7, C-9; the low-entropy arms are empty |
| T13 Potential and discharging | [56]–[62], Type A charging, Type B ledger | H01–H05, H08 | H-1–H-3, H-6 |
| T14 Demand–supply and flow | Type B B1/B2, the $2/3$-demand ledger, absorbers, surplus token ledger | B09, H05, H06, D04 | B-8–B-10; the failure of the matching is the leaf |
| T16 Symmetry and canonicalization | lexicographic tie-breaks everywhere, $\mathrm{Sym}(R)$-invariance (Theorem 1.3), canonical traces/ledgers | D08, I02, E07, G04 | D-4, D-5, G-3; the refined-order swap [165]–[166] is used only on the dense residual |
| T18 External structural theorem | [15]–[16] (HSS) | I06, C08 | I-1; Bondy–Vince/Gao–Ma present but not invoked (I-2) |
| T19 Peeling and finite descent | [101]–[102], [123] | E08, H10 | E-5, H-8, and the leaf's identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ |

---

## 4. The leaf: the typed data of [181]

`def:typeA-peeled-demand-residual`, after the procedure of `thm:large-budget-route8-only`:

- **(R1)** a valid family $P_4=(P_4(w))_w$ of exit-(4) peeling sets at which $\tilde D_A^{P_4}<(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$;
- **(R2)** the disjoint partition $\tilde\Xi=\tilde\Xi^{P_4}\mathbin{\dot\cup}\tilde P_4$, $p_4=\lvert\tilde P_4\rvert=\sum_w\lvert P_4^{\rm un}(w)\rvert$, the exact identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$ (so $p_4\ge4\tilde D_A-(1-4\tau_{\rm win})\lvert R\rvert+o(\lvert R\rvert)$, linear), and for each peeled entry its recorded exit-(4) witness;
- **(R3)** the maximal $2/3$-demand ledger on $\tilde\Xi$, its maximal absorption ledger, and the unique-window blocker partition $\mathsf P_{\rm open}=\sum_PB_{\rm open}(P)$.

Each peeled entry $\xi=(X,w,u,B_u)$ carries: a Type A support $X\in\tilde{\mathcal X}$ with all of §2; a saturated receiver $w$ ($L(w)\ge4q(w)$, $q(w)\in\{1,2\}$); a silent unpaid routed load $u$ (cubic; its trace $T_u$ ends at $w$; no receiver-entry return through a port of $w$ has a channel containing $T_u$); its trace basin $B_u$ with state $\rho_u(B_u)$; two-support: $\pi(\xi)\le2$ private essential incidences, $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$, declared deletion witnesses for each $c\in\mathcal C_{\rm ess}$; alternative (a) only: a trace-local quotient $q$ forgetting a $u$-supported coordinate on an internal edge of $B_u$, with the demand token $(\xi,q,S_0,S_1,Y,E)$ — $S_0$ the actual realization, $S_1$ an alternative in the same boundary-degree fibre with $q(S_0)=q(S_1)$, $Y$ a compatible outside context in which $S_0\oplus Y$ and $S_1\oplus Y$ differ in target predicate, $E$ the first witnessing event, using an internal edge of $B_u$ and at least two boundary incidences of $X$ ($K(\mathfrak t)$, $\lvert K\rvert\ge2$).

What each certificate does and does not say: the token and the deletion witnesses certify that specific quotients are not target-complete; $S_1$, $Y$, $E$ are hypothetical; only $S_0$, $u$, $T_u$, $B_u$, the ports and their actual returns are objects of $G$.

Derived facts at the leaf: Theorem 3.1 (the offered consumers are vacuous); Theorem 3.2 (every two-support entry realizes exit (4); no true route-8 two-support entry; at least one peel is performed); Corollary 3.3 ([181] is the only exit of [123]); Theorem 3.4 (diagnostic rate).

---

## 5. Present rows not consumed by any step of §1

From the inventory (`repair_and_closure.md` §4.7): B02–B04 beyond bridgelessness (cyclic edge cuts, blocks, disjoint connections); A08 (chains of degree-2 receivers); C04/F08 on this branch (arithmetic class and periodicity of the entries' actual channel and connector lengths); C09 (cardinality maximality, consumed only through $P_{13}$-freeness); D05/D07 for entries (overlap of the basins of one receiver's loads; equal response states among linearly many entries over a bounded alphabet); E04 (safe suppression of degree-2 receivers); H07 (the Hall obstruction of the demand ledger as a located set of entries and ports); I06 (Bondy–Vince/Gao–Ma with exact hypotheses). The consumers of D05/D06/C11 ([169]–[172]) and of D07/E07 ([163]–[166]) are stated on the dense-packing residual and are not available on this branch.

---

## 6. The closure theorem for [181]

**Theorem [181].** Let $G$ be a finite simple graph and suppose that all of the following hold: the facts of §2 (A-1 through I-4), with the arms of §1 as stated, and the leaf data (R1)–(R3) of §4 with $p_4=\Theta(\lvert R\rvert)$ peeled two-support target-defect entries carrying the data listed there. Then $G$ contains a cycle whose length is a power of two.

Equivalently, the conjunction of §1–§4 is unsatisfiable. Any proof must consume at least one row of §5, because every other present row is already accounted by the step named in §1–§3, and re-applying an accounted row returns a fact already on the ledger.
