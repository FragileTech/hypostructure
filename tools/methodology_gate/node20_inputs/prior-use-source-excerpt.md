# Node 20 Stage 1 source scope

Verbatim excerpts from `to_formalize/erdos_64_proof.tex`; the original line ranges are retained for precise citations.

## Source lines 686–686

```tex
686: \node[box, right=of surplusq] (surplusclose) {\textbf{[20]}~surplus-pair\\accounting branch};
```

## Source lines 726–726

```tex
726: \caption[Proof-dependency diagram, Part I]{Proof-dependency diagram, Part I.  Rectangles are assertions or residual states, diamonds are exhaustive branch tests, ellipses are terminal outcomes, and edge labels state which branch is followed.  The bracketed numbers are unique diagram-node numbers used by the dependency table.  Nodes [19] and [20] record the non-near-cubic surplus accounting branch used before the normalized spine budget; node [20] is the continuation expanded in \cref{fig:proof-diagram-part-x}.  Node [158] is the exact finite form of the realization sentence of \cref{lem:p13-window-package,prop:p13-density}: it asks whether the joint window package of the fixed maximal packing is realized by the labelled skeleton class; its no-branch is the dense-packing residual expanded in \cref{fig:proof-diagram-part-xii}.  Node [22] creates the hot/cold dichotomy by splitting $\mathcal P$ into $\mathcal P_{\rm hot}$ and $\mathcal P_{\rm cold}$.  Its no-branch continues at [145] in \cref{fig:proof-diagram-part-xi}.  The bounded arm of [153] returns to [24] with the density cap, and only that live residual continues to [25] and \cref{fig:proof-diagram-part-ii}.}
```

## Source lines 1138–1196

```tex
1138: \draw[arrow] (in125)--node[right]{from [20]}(resid.north);
1139: \node[box] (slack) at (-1.55,6.55) {\textbf{[126]}~sparse envelope:\\\(m\le2n-2\), \(\sigma=n-6-2\lambda\)};
1140: \node[box] (extract) at (-1.55,4.90) {\textbf{[127]}~excess-port extraction:\\\(\mathcal A=\mathcal P_{\rm exc}\), \(|\mathcal A|=\sigma(G)\)};
1141: \node[box] (activate) at (-1.55,3.25) {\textbf{[128]}~canonical activation:\\returns \(R_p\); open \(Q_p\); triangular response};
1142: \node[box] (thin) at (-1.55,1.60) {\textbf{[129]}~full active family and baseline:\\\(\mathcal A_0=\mathcal P_{\rm exc}\), \(E_{\rm spine}\le C_E n\)};
1143: \node[dec] (rankq) at (-1.55,-0.35) {\textbf{[130]}~canonical pair split:\\blocker-free?};
1144: \node[box] (entropy) at (-7.40,-0.35) {\textbf{[131]}~free-pair entropy sandwich:\\\(|\Pi_{\rm free}|\le E_{\rm spine}+(\sigma/2+1)\log_2 n\)};
1145: \node[dec] (depend) at (5.70,-0.35) {\textbf{[132]}~blocked-pair routing:\\exit or canonical blocker?};
1146: \node[term] (exit) at (12.00,-4.45) {\textbf{[133]}~sparse surplus\\exit closes};
1147: \node[wide] (blockers) at (5.70,-3.05) {\textbf{[134]}~canonical blocker ledger:\\each blocked pair gets one \(B_\pi\)\\and one capacity token};
1148: \node[wide] (joinpress) at (5.70,-5.35) {\textbf{[135]}~exact window-join load:\\\(e(R,W)+2e_\times(W)=15p_{13}+\sigma_W\)};
1149: \node[wide] (supplyq) at (5.70,-7.55) {\textbf{[136]}~tokenized blocked-pair ledger:\\\(|\Pi_{\rm blk}|=\sum_{C,t,r}\ell(t,r)\),\\supplies \(15p_{13}+\sigma_W,\sigma_R,4n+2\sigma\)};
1150: \node[dec] (highload) at (5.70,-9.75) {\textbf{[137]}~coupled excess\\\(D_{\rm all}>0\)?};
1151: \node[term] (nearclose) at (11.90,-9.75) {\textbf{[138]}~no coupled overload:\\explicit quadratic bound on \(\sigma\);\\near-cubic spine};
1152: \node[dec] (wclass) at (5.70,-12.35) {\textbf{[139]}~token in\\\(\mathfrak T_W\)?};
1153: \node[box] (wres) at (11.90,-12.35) {\textbf{[140]}~window-incidence\\geometric audit:\\homogeneous matching/star};
1154: \node[dec] (rclass) at (5.70,-15.15) {\textbf{[141]}~token in\\\(\mathfrak T_R\)?};
1155: \node[box] (rres) at (11.90,-15.15) {\textbf{[142]}~remainder-surplus\\geometric audit:\\homogeneous matching/star};
1156: \node[box] (pres) at (5.70,-17.95) {\textbf{[143]}~primitive blocker-support\\geometric audit:\\homogeneous matching/star};
1157: \node[term] (capcontra) at (11.90,-17.95) {\textbf{[144]}~bottleneck discharge:\\sparse exit, Type B, or near-cubic spine};
1158: \node[wide] (pairunreal) at (-13.30,-3.05) {\textbf{[178]}~pair-code unrealized residual: conditional factorization gives a minimal connected pair overlap obstruction};
1159: \node[wide] (pairserial) at (-13.30,-6.35) {\textbf{[179]}~covered uncrossing: target/sparse-exit/Type B, or a graph-realized serial demand system};
1160: \node[wide] (pairclose) at (-13.30,-9.35) {\textbf{[180]}~covered increment split: periodic sparse-exit/Type B, or full-modulus arithmetic gives an actual power-of-two cycle};
1161: \node[open] (pairgap) at (-13.30,-12.35) {\textbf{[182]}~OPEN: the exact [178], [179], or [180] implication not supplied by the manuscript};
1162: \draw[arrow] (resid)--(slack);
1163: \draw[arrow] (slack)--(extract);
1164: \draw[arrow] (extract)--(activate);
1165: \draw[arrow] (activate)--(thin);
1166: \draw[arrow] (thin)--(rankq);
1167: \draw[arrow] (rankq.west)--node[above]{yes}(entropy.east);
1168: \draw[arrow] (rankq.east)--node[above]{no}(depend.west);
1169: \draw[arrow] (depend.east)--node[above,pos=0.35]{exit}(9.35,-0.35)|-($(exit.north)+(0,0.45)$)--(exit.north);
1170: \draw[arrow] (depend.south)--node[pos=0.40,right,xshift=2pt]{blocker}(blockers.north);
1171: \draw[arrow] (blockers)--(joinpress);
1172: \draw[arrow] (joinpress)--(supplyq);
1173: \draw[arrow] (supplyq)--(highload);
1174: \draw[arrow] (entropy.south)--(entropy.south|-highload.west)--node[below]{count holds: free pairs}(highload.west);
1175: \draw[arrow] (entropy.west)--node[above]{count fails}(pairunreal.east|-entropy.west)--(pairunreal.north);
1176: \coordinate (freeside) at ($(highload.south)+(-3.50,-0.40)$);
1177: \draw[arrow] (highload.south)|-node[below,pos=0.55]{count fails on the free side: continue at [178]}(freeside);
1178: \draw[arrow] (pairunreal)--node[right]{factorization}(pairserial);
1179: \draw[arrow] (pairserial)--node[right]{serial arm}(pairclose);
1180: \draw[arrow] (pairunreal.west)--++(-1.05,0)|-node[left,pos=0.20]{no factorization}(pairgap.west);
1181: \draw[arrow] (pairserial.west)--++(-0.70,0)|-node[left,pos=0.25]{no exhaustive uncrossing}(pairgap.west);
1182: \draw[arrow] (pairclose)--node[right]{uncovered increment response}(pairgap);
1183: \draw[arrow] (highload.east)--node[above]{no}(nearclose.west);
1184: \draw[arrow] (highload)--node[right]{yes}(wclass);
1185: \draw[arrow] (wclass.east)--node[above]{yes}(wres.west);
1186: \draw[arrow] (wclass)--node[right]{no}(rclass);
1187: \draw[arrow] (rclass.east)--node[above]{yes}(rres.west);
1188: \draw[arrow] (rclass)--node[right]{no}(pres);
1189: \coordinate (wto144) at ($(capcontra.north)+(0.75,0.65)$);
1190: \coordinate (rto144) at ($(capcontra.north)+(-0.75,0.65)$);
1191: \draw[arrow] (wres.east)--node[above,pos=0.25]{bottleneck}++(0.95,0)|-(wto144)--(capcontra.70);
1192: \draw[arrow] (rres.south)--node[right,pos=0.40]{bottleneck}(rto144)--(capcontra.110);
1193: \draw[arrow] (pres.east)--node[above]{bottleneck}(capcontra.west);
1194: \end{tikzpicture}%
1195: }
1196: \caption[Proof-dependency diagram, Part X]{Proof-dependency diagram, Part X.  This panel expands the sparse non-near-cubic branch [20].  Nodes [126]--[129] build the full active surplus family.  Node [130] splits canonical pairs.  Free pairs are charged by the entropy sandwich [131], while blocked pairs pass through the blocker route [132]--[136]; the role fibres in [136] partition \(\Pi_{\rm blk}\), so this ledger has no double counting.  Node [137] is the coupled single-graph test of \cref{cor:coupled-single-graph-overload-budget,cor:numerical-single-graph-budget,prop:single-graph-sparse-pressure-routing}: all three token classes use the same \(n,p_{13},\sigma_W,\sigma_R\).  If \(D_{\rm all}=0\), the explicit quadratic bound routes to [138].  If \(D_{\rm all}>0\), the role-fibre excess enters the window-incidence, remainder-surplus, or primitive blocker-support geometric audit [140], [142], [143].  Node [144] applies \cref{thm:homogeneous-overload-geometric-closure}: the bottleneck realizes a sparse surplus exit, produces Type B fan data, or is bounded by fixed homogeneous caps and routes to [138].  The entropy counts of [131] and of the free side of [137] are branch tests.  On the covered pair-code arm, [178] retains the exact conditional factorization and minimal connected overlap obstruction, [179] retains either an already routed outcome or the graph-realized serial system, and [180] retains either an already routed periodic outcome or the exact full-modulus arithmetic data from which an actual power-of-two cycle is constructed.  The manuscript does not prove that these three classifications are exhaustive on the retained residual.  Their literal failures therefore meet only at the explicit open node [182]; none is renamed as a blocker, quotient, exit, or Type B witness.}
```

## Source lines 1364–1368

```tex
1364: 45 & [19], [20] & Non-near-cubic surplus branch & every survivor of the sparse surplus exits has the full active-demand family and, after an \(O(n)\)-deficit baseline demand is fixed, satisfies the exact capacity-token budget; the geometric same-token bottleneck lemma gives fixed homogeneous caps unless the load realizes a sparse surplus exit or ordinary Type B fan data, and the caps give \(\sigma(G)=O(\sqrt n)\) & derives the near-cubic spine before the normalized entropy budget is used, except for branches that are already routed to sparse exits or to the Type B fan ledger; blocker-free pair responses are charged by the exact cubic-baseline sandwich and the spine lower-bound deficits, while blocked pairs are assigned to capacity tokens; the exact token-fibre budget gives the load forced by any attempted violation, and \cref{lem:same-token-bottleneck-routing} turns a large homogeneous fibre into a geometric first-separator/fan route & \cref{lem:sparse-upper-envelope}, \cref{lem:sparse-slack-surplus}, \cref{def:named-surplus-exits}, \cref{def:active-surplus-demands}, \cref{lem:surviving-active-family}, \cref{def:surplus-blockers}, \cref{def:canonical-blocker-ledger}, \cref{lem:canonical-blocker-ledger-no-overcount}, \cref{def:primitive-sparse-blocker-carrier}, \cref{lem:primitive-carrier-supply}, \cref{def:capacity-token-ledger}, \cref{lem:capacity-token-supply}, \cref{lem:token-ledger-no-overcount}, \cref{def:same-token-patterns}, \cref{def:same-token-blocker-roles}, \cref{def:same-token-routing-germs}, \cref{lem:same-token-matching-star}, \cref{lem:same-token-homogeneous-extraction}, \cref{lem:same-token-bottleneck-routing}, \cref{thm:homogeneous-overload-geometric-closure}, \cref{cor:homogeneous-same-token-caps-close}, \cref{def:baseline-spine-demand}, \cref{lem:exact-cubic-baseline-budget}, \cref{lem:incremental-skeleton-room}, \cref{prop:sparse-entropy-sandwich}, \cref{prop:sparse-entropy-sandwich-with-blockers}, \cref{thm:tokenized-surplus-accounting-closure}, \cref{def:window-remainder-surplus-split}, \cref{lem:exact-window-join-identity}, \cref{cor:global-window-join-pressure}, \cref{prop:nonnear-cubic-sharp-overload-routing} \\
1365: 46 & [125]--[129] & Sparse accounting setup & a sparse-load survivor yields the full active surplus family and an \(O(n)\)-deficit baseline demand & [129] fixes the common baseline used by the later sandwich & \cref{def:named-surplus-exits}, \cref{def:active-surplus-demands}, \cref{lem:surviving-active-family}, \cref{def:baseline-spine-demand} \\
1366: 47 & [130]--[132] & Free/blocked pair split & pair-response coordinates split into blocker-free and blocked pairs; free pairs are charged by the entropy sandwich & blocked-pair debt is the only branch passed to the token ledger & \cref{def:sparse-pair-response}, \cref{lem:sparse-pair-dependence-exit}, \cref{prop:sparse-entropy-sandwich-with-blockers} \\
1367: 48 & [132]--[136] & Blocker and token ledger & canonical blockers, primitive blocker supports, and capacity tokens count blocked pairs exactly once & [136] is the exact token-fibre partition and no-overcounting closure & \cref{def:surplus-blockers}, \cref{def:canonical-sparse-blocker-order}, \cref{def:canonical-blocker-ledger}, \cref{lem:canonical-blocker-ledger-no-overcount}, \cref{def:primitive-sparse-blocker-carrier}, \cref{lem:primitive-carrier-supply}, \cref{def:capacity-token-ledger}, \cref{lem:capacity-token-supply}, \cref{lem:token-ledger-no-overcount} \\
1368: 49 & [135], [136] & Window-join load & the exact packed-window join identity supplies \(15p_{13}+\sigma_W\) and the surplus-aware window-stub load & supplies the window/remainder capacity side of the token ledger & \cref{def:window-remainder-surplus-split}, \cref{lem:exact-window-join-identity}, \cref{cor:global-window-join-pressure}, \cref{rem:surplus-pair-sharp-frontier} \\
```
