# Closure proofs for nodes [181] and [182]

Structural-exhaustion proofs on the two open nodes of `to_formalize/erdos_64_proof.tex`. Every cited statement is a displayed statement of the manuscript (by `\label`) or a definition of the Lean sources (by file and name). Notation is the manuscript's: $G$ the lexicographically minimal counterexample, $n=\lvert V(G)\rvert$, $R$ the $P_{13}$-free remainder, $W=V(\mathcal P)$ the packed-window vertex set, $p_{13}=\lvert\mathcal P\rvert$, $\theta=p_{13}/n$, $\defp,\sigma,\No$ as there, $\mathrm{Pow}=\{2^k\}$.

---

## 1. The density cap through relabeling entropy

**Lemma 1.1.** Let $H$ be a graph on $[n]$ with $m$ edges and minimum degree $\ge3$, $\sigma_H:=2m-3n$. Let $W\subseteq[n]$, $R:=[n]\setminus W$, $\mathrm{Aut}_W(H)$ the automorphisms of $H$ fixing $W$ pointwise, and $K_H$ the number of components of $H-W$. Then
$$\log_2\lvert\mathrm{Aut}_W(H)\rvert\ \le\ K_H\log_2K_H+6\lvert R\rvert+4\sigma_H\log_2n .$$

*Proof.* An automorphism fixing $W$ pointwise permutes the components of $H-W$ (at most $K_H!\le K_H^{K_H}$ ways) and acts on each component $C$ as an automorphism of a connected graph, which is determined by the image of one vertex and, along a breadth-first order, a bijection between each vertex's neighbourhood and its image's; so $\lvert\mathrm{Aut}(C)\rvert\le\lvert C\rvert\prod_{v\in C}\deg(v)!$ and $\log_2\lvert\mathrm{Aut}(C)\rvert\le\lvert C\rvert+\sum_{v\in C}\deg(v)\log_2\deg(v)$. Vertices of degree $3$ contribute at most $3\log_23\,\lvert R\rvert\le4.76\lvert R\rvert$ in total. Since $\sum_v(\deg v-3)=\sigma_H$ with all degrees $\ge3$, the vertices of degree $\ge4$ have total degree at most $4\sigma_H$, each of degree $\le n$. $\square$

**Lemma 1.2.** If in Lemma 1.1 the set $W$ is the vertex set of $p_{13}$ vertex-disjoint induced paths on $13$ vertices of $H$, then $K_H\le\tfrac14\lvert R\rvert+15p_{13}+\sigma_H$.

*Proof.* A component of $H-W$ with no edge to $W$ has minimum degree $\ge3$, hence $\ge4$ vertices. A component with an edge to $W$ uses one of the $W$–$R$ edges, whose number is at most $\sum_{w\in W}\deg(w)-2e(H[W])\le39p_{13}+\sigma_H-24p_{13}$. $\square$

**Theorem 1.3 (orbit count).** Let $\mathcal S$ be the near-cubic labelled skeletons on $[n]$ with $m=\tfrac32n+O(\sqrt n)$ edges in which the fixed packing $\mathcal P$ consists of induced paths, and let $\Phi:\mathcal S\to\Sigma$ be invariant under all permutations of $[n]$ fixing $W$ pointwise. Then, with $\lvert R\rvert=n-13p_{13}$,
$$\log_2\lvert\Phi(\mathcal S)\rvert\ \le\ \log_2\lvert\mathcal S\rvert-\bigl(\tfrac34\lvert R\rvert-15p_{13}\bigr)\log_2\lvert R\rvert+O(n).$$

*Proof.* For each $s\in\Phi(\mathcal S)$ choose $H_s\in\Phi^{-1}(s)$. Its orbit under $\mathrm{Sym}(R)$ lies in $\Phi^{-1}(s)$ and has $\lvert R\rvert!/\lvert\mathrm{Aut}_W(H_s)\rvert$ elements; orbits of distinct states are disjoint. Lemmas 1.1–1.2 with $\sigma_H=O(\sqrt n)$ and $\log_2\lvert R\rvert!\ge\lvert R\rvert\log_2\lvert R\rvert-1.45\lvert R\rvert$ give $\log_2\lvert\Phi^{-1}(s)\rvert\ge(\tfrac34\lvert R\rvert-15p_{13})\log_2\lvert R\rvert-O(n)$; sum over $s$. $\square$

**Corollary 1.4 (the low-entropy arms of node [50] are empty).** On the near-cubic spine, $\eta(R)\ge(1-\tau)\log_2\lvert R\rvert-O(1)$ with $\tau=\defp(R)/\lvert R\rvert$; hence $\eta(R)>\tfrac1{10}\log_2n$ for large $n$ and branches (b), (c) of `prop:two-budget` do not occur.

*Proof.* The class $\mathcal G(R)$ of `def:remainder-entropy` is closed under relabeling of $V(R)$ and contains $R$, so $\lvert\mathcal G(R)\rvert\ge\lvert R\rvert!/\lvert\mathrm{Aut}(R)\rvert$. Every component of $R$ has empty internal $3$-core (`lem:remainder-empty-internal-3-core`), hence a vertex of internal degree $\le2$, hence $\defp\ge1$; so $K_R\le\defp(R)\le\tau\lvert R\rvert$. Apply Lemma 1.1 with $\sigma=0$. $\square$

**Theorem 1.5 (sharpened cap).** On the hot branch (yes-arm of node [158]) under `def:near-cubic-spine`,
$$\theta\le\theta^\ast+o(1),\qquad\theta^\ast:=\frac{3/4}{c_{13}-\tfrac{39}{4}-15}=0.0080335\ldots,\qquad
\frac{\defp(R)-\sigma(R)}{\lvert R\rvert}\le\tau^\ast+o(1),\qquad\tau^\ast:=\frac{15\theta^\ast}{1-13\theta^\ast}=0.13456\ldots$$

*Proof.* Take $\Phi$ = the window-package state relative to $W$; its barrier states $(S,A,T)$ (`lem:p13-window-package`) are window labels and outside path lengths, hence $\mathrm{Sym}(R)$-invariant. On the hot branch $\log_2\lvert\Phi(\mathcal S)\rvert\ge(c_{13}-o(1))p_{13}\log_2n$; by `lem:near-cubic-budget`, $\log_2\lvert\mathcal S\rvert\le\tfrac32n\log_2n+O(n)$. Theorem 1.3 with $\lvert R\rvert=(1-13\theta)n$ and division by $n\log_2n$ gives $c_{13}\theta+\tfrac34(1-13\theta)-15\theta\le\tfrac32+o(1)$. The second display is `lem:stub-positive` as in `prop:p13-density`. $\square$

(Not in the manuscript; stated and proved here only.)

---

## 3. Node [181]

### 3.1 What the node carries

(The complete accounting — path, arms, every fact with source and technique, leaf data, closure theorem — is `node_181_structure.md`.)


Standing statements, all on the large-budget branch: (S1) $\frac{\defp(R)-\sigma(R)}{\lvert R\rvert}\le\tau+o(1)$ with $\tau=\tau^\ast$ by Theorem 1.5; (S2) `lem:typeA-unified-deficit`: $\tilde D_A\ge\tfrac14\lvert R\rvert-(\defp(R)-\sigma(R))-o(\lvert R\rvert)$; (S3) `lem:typeA-unified-burden`: $\tilde N\ge4\tilde D_A$; (S4) `lem:typeA-pressure-absorber-no-overcount`: $3\tilde N-\mathsf P_{\rm open}\le\defp(R)$ once the (A2) certificates have routed; (S8) `prop:typeA-unified-reduction`; (S9) `lem:typeA-unified-carriers`: $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$ for every entry; (S10)–(S12) `lem:typeA-essential-deletion-witness`, `lem:typeA-deletion-witness-declared`, `def:typeA-exit4-family` (Q5), `lem:typeA-carrier-deletion-exit`; (S13) `def:typeA-true-route8-residual` (R2); (S15) `lem:typeA-exit4-discharge`; (S16) `lem:typeA-peeling-stage-accounting`, `lem:typeA-peeling-reduced-reduction`; (S17) `thm:large-budget-route8-only`.

**Theorem 3.1.** On the large-budget branch, once the (A2) certificates have routed, $\liminf\mathsf P_{\rm open}/\lvert R\rvert\ge\varepsilon_{\rm press}:=12(\tfrac14-\tau)-\tau$ and $\liminf\mathsf P^{+}_{\rm zero}/\lvert R\rvert\ge\varepsilon_{\rm prim}$. Hence the hypotheses of `prop:typeA-exit4-closure-from-open-pressure`, `cor:typeA-large-budget-closure-open-pressure`, `prop:typeA-exit4-closure-from-window-blockers` and `prop:typeA-exit4-closure-from-zero-shadow` never hold on the branch.

*Proof.* (S4), (S3), (S2), (S1): $\mathsf P_{\rm open}\ge3\tilde N-\defp(R)\ge12\tilde D_A-\defp(R)\ge3\lvert R\rvert-13\defp(R)-o(\lvert R\rvert)\ge(3-13\tau)\lvert R\rvert-o(\lvert R\rvert)$, and $3-13\tau=\varepsilon_{\rm press}$. For the second display use `lem:typeA-open-pressure-zero-shadow-excess`, $\mathsf P_{\rm open}\le2p_{13}+\mathsf P^{+}_{\rm zero}$, and $\limsup2p_{13}/\lvert R\rvert\le2\theta/(1-13\theta)$. $\square$

**Theorem 3.2.** (i) Every two-support entry $\xi\in\tilde\Xi$ ($\pi_{\mathcal X}(\xi)\le2$) realizes exit (4) at its receiver. (ii) No two-support entry is a true route-8 residual entry; the terminal obstruction of `thm:typeA-two-carrier-nogo` is empty by definition. (iii) The procedure of (S17) performs at least one peel and terminates at node [181].

*Proof.* (i) If $B_u$ is not target-complete-minimal, alternatives (b),(c),(d) of `def:typeA-trace-basin` are exits (5),(6),(7), excluded on $\tilde{\mathcal X}$; so (a) holds, which is exit (4) through a (Q3) quotient. If $B_u$ is target-complete-minimal, (S9) gives $c\in\mathcal C_{\rm ess}(\xi)$, (S10) a declared $c$-deletion witness, (S11)–(S12) $q_{\xi,c}\in\mathcal Q_4(w)$ and exit (4). (ii) (S13) requires exit (4) absent through $\mathcal Q_4(w)$; contradiction with (i). (iii) (S2) makes the initial reduced-rate test hold; (S16) gives a two-support entry; by (i),(ii) it is peeled (S15), decreasing $\tilde D_A^{P_4}$ by $\tfrac14$ and $\Lambda_4$ by one; iterate; the integer $\Lambda_4$ stops the loop only when the reduced-rate test fails, which is [181] by (S17). $\square$

**Corollary 3.3.** Node [181] is the only exit of node [123]. Any closure of the large-budget branch through the unified ledger must show that a two-support entry realizes an exit other than (4).

**Theorem 3.4 (the required rate).** With $\tau=\tau^\ast$, a single-use charging giving each unified entry $c$ boundary-incidence units yields a contradiction iff $c>\tau^\ast/(1-4\tau^\ast)=0.2914$. Equivalently, the large-budget branch is empty as soon as every component $X$ of $R$ satisfies $\lvert V(X)\rvert\le7\,\defp(X)$.

*Proof.* Disjoint units total at most $\defp(R)\le\tau^\ast\lvert R\rvert$, while $\tilde N\ge(1-4\tau^\ast)\lvert R\rvert$ by (S2)–(S3). For the second statement: $\sum_X\lvert V(X)\rvert=\lvert R\rvert$ and $\sum_X\defp(X)=\defp(R)\le\tau^\ast\lvert R\rvert<\lvert R\rvert/7$. $\square$

Theorem 3.4 is a diagnostic only. The residual of [181] is the branch state $\mathcal B_{181}$ below, never a projection of it.

**The branch state $\mathcal B_{181}$ (Rule 0).** Every step below is a statement about the conjunction of: the minimal counterexample $G$ (cubic on the near-cubic spine, `def:near-cubic-spine`, no power-of-two cycle, bridgeless); the maximum-cardinality packing $\mathcal P$ of induced $P_{13}$'s with $p_{13}=\theta n$ (`cor:p13-exists` ff.) and the remainder $R$ with $P_{13}$-free $2$-degenerate components (`lem:remainder-empty-internal-3-core`, black box `thm:p13free` consumed there); the hot arm of [158] with its state count $\log_2\lvert\Phi(\mathcal S)\rvert\ge(c_{13}-o(1))p_{13}\log_2n$ and the cap $\theta\le\theta^\ast$, $\tau\le\tau^\ast$ (Theorem 1.5); the large-budget arm; the standing statements (S1)–(S17) of §3.1; the exits (1)–(3), (5), (6) closed and (7) absent at every saturated receiver of every $X\in\tilde{\mathcal X}$ (`lem:typeA-unified-burden`); the typed data (R1)–(R3) of `def:typeA-peeled-demand-residual` — the peeled entries $\xi=(X,w,u,B_u)$, two-support ($\pi_{\mathcal X}(\xi)\le2$) with essential core $\mathcal C_{\rm ess}(\xi)$, $\lvert\mathcal C_{\rm ess}\rvert\ge2$, declared deletion witnesses (S9)–(S12), their demand tokens, the $2/3$-demand ledger, absorbers and window blockers; Theorems 3.1–3.4 and Corollary 3.3 as derived facts. A step that names a sub-object (a component, a ball) is a step about $\mathcal B_{181}$ in which the move acts on that sub-object; the rest of the state is carried unchanged.

### 3.2 The record on a component of $\tilde{\mathcal X}$ carrying a peeled entry

| | Invariant | Source |
|---|---|---|
| I1 | every vertex has $G$-degree $3$; a vertex of internal degree $3-q$ has $q$ stubs into $W$; $\defp(X)=\sum q$ | `def:typeA-support`, `def:canonical-decomp` |
| I2 | $X$ is $P_{13}$-free; $\operatorname{diam}X\le11$; $\lvert V(X)\rvert\le6142$ | `lem:remainder-empty-internal-3-core`, §"Type A" |
| I3 | every $P_{13}$-free induced subgraph of $G$ has a vertex of degree $\le2$ (the black box, fully consumed) | `thm:p13free`, `lem:remainder-empty-internal-3-core` |
| I4 | no cycle of $G$ meeting $X$ has length in $\mathrm{Pow}$ | `def:target-safe` |
| I5 | no proper boundaried piece of $G$ has a smaller representative with the same boundary-degree profile and sub-profile | `lem:replacement`, `cor:uncompressible` |
| I6 | $\defp(X)\ge2$; every component of $G-V(X)$ sends $\ge2$ edges to $X$ | `lem:bridgeless` |
| I8 | on the branch some component has $\lvert V(X)\rvert>7\,\defp(X)$ (diagnostic; not the residual) | Theorem 3.4 |
| I9 | $p_{13}$ is maximum: no vertex-disjoint family of induced $P_{13}$'s has $p_{13}+1$ members | `cor:p13-exists` ff. |
| I10 | $\xi$ is two-support: $\pi_{\mathcal X}(\xi)\le2$, $\lvert\mathcal C_{\rm ess}(\xi)\rvert\ge2$, each $c\in\mathcal C_{\rm ess}$ has a declared deletion witness; $B_u$ fails target-complete-minimality through alternative (a) only | (S9)–(S12), Theorem 3.2 |
| I11 | $u$ is silent: no receiver-entry return through a port of $w$ has a channel containing $T_u$ | `def:typeA-visible-load`, `def:typeA-excess-basin` |

### 3.4 The residual

The residual of [181] is $\mathcal B_{181}$ as stated in §3.1, with no further arms.

**Proposition 3.7 (O7: two-support target-defect no-go).** *On the large-budget branch, let $\xi=(X,w,u,B_u)$ be a peeled entry with demand token $\mathfrak t=(\xi,q,S_0,S_1,Y,E)$. Then one of exits (1), (2), (3), (5), (6), (7) of `def:typeA-saturated-exits` occurs at $w$ or at the window interfaces of $E$.* With Proposition 3.7, no peel is ever performed and [181] is empty (Theorem 3.2(iii) with its loop body replaced by the exit).

## 4. Node [182]

### 4.1 Definitions

From `hypostructure/Hypostructure/Graph/SparseEntropySandwich.lean`: `Skeleton n m` = labelled graphs on $[n]$ with $m$ edges; `portReturns` $=\bigcup_\pi\text{pairSeed}(\pi)$; `outsideEdges H I` = edges of $H$ not contained in $I$; `outsideCode H` = (outside edges, baseline word); `conditionalFibre H₀` = same outside code; `response H π` = (boundary of $H[X_\pi]$, the predicate $Y\mapsto$ [glue$(H[X_\pi],Y)$ has a power-of-two cycle]); `conditionalValues family order H₀ i` = responses at index $i$ over candidates in the fibre agreeing with $H_0$ on earlier indices; `RealizingOrder` $=\exists$ order, $\forall H_0$, $\forall i$, $2\le\mathrm{Nat.card}(\ldots)$; `Overlaps`, `PairwiseSeparated`, `ConditionalFactorization` = `separated` $\wedge$ `concatenate`. Constructor 1 of `PairUncoveredResidual` (`Graph/Strategy/SpineVocabulary.lean`) is $\neg$`ConditionalFactorization`.

### 4.2 The predicate and its correction

**Theorem 4.1.** (a) If some support $X_\pi$ contains two vertices outside portReturns and two inside, then `separated` fails at the singleton family $\{\pi\}$ for a reference skeleton carrying a $4$-cycle on those four vertices. (b) If a seed vertex $s\in X_\pi$ has no neighbour outside $X_\pi$ in $H_0$ and a free non-edge $st$ to a portReturns vertex outside $X_\pi$ exists, together with a removable free edge preserving the baseline word, then `conditionalValues` at $\{\pi\}$ has $\ge2$ elements regardless of target responses.

*Proof.* (a) The four edges of the $4$-cycle have an endpoint outside portReturns, so they are outside edges and lie in every member of the fibre; the piece $H[X_\pi]$ then has a $4$-cycle for all $H$ in the fibre and the `response` field is constantly true; choosing $H_0$ so that every seed vertex of $X_\pi$ has a fixed outside neighbour makes the boundary field constant too, so $\mathrm{Nat.card}=1$. (b) $H=H_0-e+st$ has the same outside edges and edge count; $s$ enters the boundary field, so the two `response` structures differ. $\square$

**Corrected predicate.** `RealizingOrder_G`: reference fixed to the object's own skeleton (`BlockedClass.objectSkeletonMember`), candidates required to have the same piece boundary as the reference, responses compared on the `response` field. Everything below is for `RealizingOrder_G`.

### 4.3 The switch

**Theorem 4.2.** Let $\pi=\{p,q\}$, let $x_0x_1x_2x_3$ be four consecutive vertices of $T(p)$, and $e$ an edge of $G$ inside pairSeed$(\pi)$ not among $x_0x_1,x_1x_2,x_2x_3$. Put $H=G-e+x_0x_3$. Then $H$ is a skeleton with the outside edges of $G$; $H[X_\pi]$ contains the $4$-cycle $x_0x_1x_2x_3$, so its response is constantly true; $G[X_\pi]$ has no power-of-two cycle, so its response is false on the empty context; hence `response H π` $\ne$ `response G π`, and $H$ lies in the fibre of $G$ iff the baseline word is unchanged.

*Proof.* $x_0x_3\notin E(G)$ by I4; both modified edges have both endpoints in portReturns; the rest is as stated. $\square$

**Theorem 4.3.** Let (R2) every switch of a free pair preserve the baseline word, and (R3) every pairwise-separated family admit an order in which each $\pi_i$ has a switch inside pairSeed$(\pi_i)$ avoiding $\bigcup_{j<i}X_{\pi_j}$. Then `separated` and `concatenate` hold for `RealizingOrder_G`. Conversely, if no switch of some $\pi$ preserves the baseline word, `separated` fails at $\{\pi\}$.

*Proof.* Under (R2),(R3), the switch for $\pi_i$ changes no edge with an endpoint in an earlier support, so earlier responses are unchanged and Theorem 4.2 gives the second value; for `concatenate` order the left family first. Conversely, the only fibre members with a different response are switches, all outside the fibre. $\square$

**Proposition 4.4 (residual of constructor 1).** *(R2) and (R3) hold.* (R2) is a constraint on the baseline family $\mathcal I_{\rm spine}$, which `def:baseline-spine-demand` leaves unspecified; it holds if no coordinate of $\mathcal I_{\rm spine}$ has declared support meeting $\bigcup_{\pi\in\Pi_{\rm free}}\text{pairSeed}(\pi)$, at a cost of $O(\lvert\Pi_{\rm free}\rvert)$ in $E_{\rm spine}(n)$. (R3) is the geometry of `lem:pair-failure-overlap`.

### 4.4 Constructors 2 and 3

**Theorem 4.5.** The proofs of `lem:pair-system-realizability` and `lem:pair-system-increment-arithmetic` use `lem:cold-corridor-first-failure`, `lem:cold-germ-extraction`, `lem:cold-bounded-germ-trichotomy` and `lem:cold-increment-arithmetic`, each stated under `def:surviving-cold-branch`, whose clause (v) requires that no peeled target-defect demand residual be active. Hence constructors 2 and 3 of [182] are closed only after [181].

*Proof.* By the cited statements. $\square$

**Proposition 4.6 (residual of constructors 2–3).** *Under Proposition 3.7, for every minimal connected pair overlap obstruction on the strict branch one of the five outcomes of `lem:pair-system-realizability` occurs, and for every scale-spanning serial demand system the arithmetic or a routed periodic outcome of `lem:pair-system-increment-arithmetic` occurs.* The transfer from `lem:window-system-realizability` requires: connectors of $X_\pi$ are internally disjoint paths (vertex-minimality; a branching connector is outcome (iv)); the uncrossing preserves the fibre (Theorem 4.2's locality); the two-strand check re-run at return parameters; the cold machinery available by Proposition 3.7.

---

## 5. Status

| Statement | Status |
|---|---|
| Lemmas 1.1–1.2, Theorem 1.3, Corollary 1.4, Theorem 1.5 | proved |
| Theorems 3.1, 3.2, 3.4; Corollary 3.3 | proved |
| Proposition 3.7 (O7) | open — closes [181]; proof route fixed by the inventory selection |
| Theorem 4.1, Theorem 4.2, Theorem 4.3, Theorem 4.5 | proved |
| Proposition 4.4 (R2, R3) | open — closes constructor 1 of [182] |
| Proposition 4.6 | open — closes constructors 2–3 of [182], after Proposition 3.7 |

## 6. Corrections to the manuscript (recorded here; the tex is not edited)

1. **Density constants.** `prop:p13-density` proves $\theta\le\theta_{\rm win}=1.5/c_{13}=0.0127002$ and $\tau\le\tau_{\rm win}=0.2281749$ using only the skeleton budget. The class $\mathcal G(R)$ is closed under relabeling of $V(R)$ and the window-package states are $\mathrm{Sym}(R)$-invariant, so the orbit count of Theorem 1.3 applies and gives, on the hot arm of [158], $\theta\le\theta^\ast=0.75/(c_{13}-39/4-15)=0.0080335$ and $\tau\le\tau^\ast=0.13456$ (Theorem 1.5). Consequences: the low-entropy arms (b), (c) of `prop:two-budget` are empty (Corollary 1.4), and every constant derived below node [55] from $\theta_{\rm win},\tau_{\rm win}$ ($\omega_{\rm win}$, $K_{\rm win}$, $\varepsilon_{\rm press}$, $\varepsilon_{\rm prim}$, the [56] collision, the rate of `lem:typeA-peeling-reduced-reduction`) should be re-derived from $\theta^\ast,\tau^\ast$. The sharper values are not needed for correctness of any existing step; they change which arms are live.

2. **The offered consumers of [181] are vacuous on their own branch.** `lem:typeA-pressure-absorber-no-overcount` ($3\tilde N-\mathsf P_{\rm open}\le\defp(R)$), `lem:typeA-unified-burden`, `lem:typeA-unified-deficit` and `lem:stub-positive` force $\mathsf P_{\rm open}\ge(3-13\tau)\lvert R\rvert-o(\lvert R\rvert)=\varepsilon_{\rm press}\lvert R\rvert-o(\lvert R\rvert)$ on the large-budget branch (Theorem 3.1). Hence the hypotheses of `prop:typeA-exit4-closure-from-open-pressure`, `cor:typeA-large-budget-closure-open-pressure`, `prop:typeA-exit4-closure-from-window-blockers` and `prop:typeA-exit4-closure-from-zero-shadow` never hold there; `def:typeA-same-window-open-blocker-cap` is false on the branch, not merely unproved; and `rem:typeA-zero-shadow-numerics` ($\mathsf P^{+}_{\rm zero}\ge0.217p_{13}$) describes every case, not a hard case. These statements are true but cannot close [181]; the text presenting them as the route to closure should say so.

3. **Two-support entries and node [124].** Every two-support entry of $\tilde\Xi$ realizes exit (4) (Theorem 3.2(i)): for a target-defect entry through its (Q3) quotient, for a route-8 entry through the (Q5) deletion quotient of `lem:typeA-carrier-deletion-exit`. So no two-support entry is a true route-8 residual entry and the terminal obstruction of `thm:typeA-two-carrier-nogo` is empty by definition (Theorem 3.2(ii)); the theorem is correct but its role is definitional, and the routing at [123] always performs at least one peel and always terminates at [181] (Theorem 3.2(iii), Corollary 3.3). The manuscript's description of [123] as "finite exact descent terminates in true route 8?" with a live yes-arm is therefore misleading: the yes-arm is empty and the whole large-budget branch flows to [181].

4. **The cold-branch closure is conditional on [181].** `thm:cold-branch-quantitative-closure` and `def:surviving-cold-branch` (clause (v)) assume the absence of the peeled-demand residual; `lem:window-system-realizability`, `lem:serial-system-sumset` and `lem:system-increment-arithmetic` are stated on the dense-packing residual [169] (the no-arm of [158]). None of these is available as a fact on the [181] branch; any closure of [181] that cites them imports a hypothesis not on the branch.

5. **Appendix inputs are assumptions.** `lem:app-dense-window-closure` and `lem:app-typeA-quiet-bound` are stated under an assumed Bondy–Vince/Gao–Ma input ("quiet almost-cubic blocks satisfy $\lvert Y\rvert<5b(Y)^2$; exported close cycle lengths force a Mersenne return or a replacement"), which is not proved anywhere; the appendix says it bounds route 8 "but does not by itself close" it. The text should not list these as closures.

6. **Lean/manuscript mismatch at [182]** (Theorem 4.1): the formal `RealizingOrder` conditioned on the outside-edge fibre of a reference skeleton, which the manuscript's realized $(\text{baseline word},\text{prefix})$ signatures do not; the Lean definition was corrected (`conditionalValues` in `SparseEntropySandwich.lean`), the manuscript's statement is the one kept.

7. **Provenance of node [181] (trace against the Zenodo original, record 22019344, dated 2026-08-20).** The original manuscript has no node [181] and no [182]; `def:typeA-peeled-demand-residual` and `lem:typeA-peeling-stage-accounting` are the only labels present now and absent then. They were introduced in commit `4416c4c` (2026-08-25, "Route EG node 123 residual and sync proof artifacts", 269 changed lines of the tex, together with the red-team audit `audits/erdos-64-red-team/summary-nodes-157-180.md` and the Lean rows for node [123]). Every other statement in the [123]/[124] cluster — `def:typeA-true-route8-residual`, `prop:typeA-route8-carrier-reduction`, `lem:typeA-exit4-finite-descent`, `lem:typeA-pressure-is-exit4-peel`, `prop:typeA-route8-closure-from-nogo`, `thm:typeA-two-carrier-nogo`, the demand ledger, the absorbers, the blockers, the four exit-(4) closure propositions, `def:typeA-same-window-open-blocker-cap`, `rem:typeA-zero-shadow-numerics` — is byte-identical in the original and the current file. What changed is one paragraph of the proof of `thm:large-budget-route8-only` and the surrounding routing text.

   *The original proof's first step.* "If $\tilde D_A^{P_4}<(\tfrac14-\tau_{\rm win})\lvert R\rvert-o(\lvert R\rvert)$, then the still-unresolved negative mass is too small to realize the large-budget branch: all supports outside the $P_4$-reduced Type A ledger are nonnegative or belong to the Type B bridge ledger … Hence the large-budget net-deficiency cap and `thm:branch-kill` close that stage." This step is contradicted by the original's own text: (i) `thm:branch-kill` is stated for residuals *outside the target-defect exit*, and the peeled supports are exactly the target-defect exit; (ii) the introduction of `sec:exit4-closure` (original, unchanged) says: "Such a support has strictly negative net charge (a peeled routed load is a cubic vertex still carrying $-\tfrac14$), so it is neither a nonnegative support nor, in general, a route-8 residual nor a Type B bridge residual. Any partition that counts only those three classes omits the target-defect negative mass." The peel changes the ledger, not the graph (`lem:typeA-exit4-finite-descent`: "the operation changes only the bookkeeping ledger"), so the peeled deficit $p_4/4$ is still negative mass of $G$ and the reduced-rate test failing does not close anything. The original's exit-(4) accounting section then offers closure only *conditionally* — on $\mathsf P_{\rm open}=o(\lvert R\rvert)$, on the same-window two-blocker cap (a *definition*, never proved), or on $\mathsf P^{+}_{\rm zero}<\varepsilon_{\rm prim}\lvert R\rvert$ — and its own `rem:typeA-zero-shadow-numerics` states that the criterion "leaves only residuals satisfying $\mathsf P^{+}_{\rm zero}\ge0.217p_{13}$". By Theorem 3.1 those conditional hypotheses are false on the branch.

   *The 2026-08-25 edit.* It replaced the false first step by the exact identity $4\tilde D_A=4\tilde D_A^{P_4}+p_4$, named the failed reduced-rate stage node [181], and marked the cold-branch closure as conditional on its absence. It did not remove or alter any closing lemma; it removed a claim that was inconsistent with two other unchanged statements of the same manuscript. The commit is authored `guillemdb <guillem@fragile.tech>`.

   *On [124].* Node [124] closes only route-8 two-support entries; it never closed the target-defect ones, which in both versions are peeled. Theorem 3.2 shows that under the unchanged definitions every two-support entry realizes exit (4), so no two-support entry is a true route-8 entry and [124]'s arm is empty in the original as well. Hence the original's large-budget closure rested entirely on the deleted step, and the gap at [181] is a gap of the original, made explicit on 2026-08-25, not one created by that edit.

