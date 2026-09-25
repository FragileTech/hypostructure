# Node 20 Stage 5: bound-witness applicability review

This is a source-scope aid, not a new premise or a proof of impossibility. Check the reviewer-requested direct consumer inference on the SAME bound attempt, `reduced`, `full`, and `O`. In particular, determine whether the selected connected-cut output constrains their target responses, or only the support `S`. If only `S`, identify the earliest defective workflow decision for independent review; do not silently reopen an accepted stage.

## `hypostructure/Hypostructure/Graph/DeclaredRankQuotient.lean:61-105`

```lean
61: structure AttemptedQuotient (Baseline Target : FiniteObject.{u} → Prop)
62:     (object : FiniteObject.{u}) {Coordinate : Type u}
63:     (family : Finset Coordinate)
64:     (coordinateSupport : Coordinate → Finset object.Vertex) : Type (u + 2) where
65:   /-- The determination support `Z`. -/
66:   support : Finset object.Vertex
67:   /-- `Z` is connected: `def:admissible-rank-quotient` quantifies over families
68:   "carried by a connected support `X ⊆ G`". -/
69:   connected : SupportComponents.Connected.ConnectedOn object support
70:   /-- `Z` carries the coordinates under discussion. -/
71:   carries : ∀ coordinate ∈ family, coordinateSupport coordinate ⊆ support
72:   /-- The labelled coordinates of the quotient datum `Q`. -/
73:   Label : Type (u + 1)
74:   /-- Target-response values. -/
75:   Value : Type (u + 1)
76:   /-- The quotient map on the declared coordinate labels. -/
77:   label : Coordinate → Label
78:   /-- The target response a realization gives at a quotient label.  A
79:   realization is a boundaried graph that can occupy `Z`'s place. -/
80:   value : BoundaryPiece (SupportAtom.boundary object support) → Label → Value
81:   /-- `def:admissible-rank-quotient`, proper clause.  A rank-reducing quotient at
82:   a proper support is admissible **only when** it is target-complete, and then it
83:   is represented by a strictly smaller proper representative — the five
84:   hypotheses of `lem:replacement` at `Z`. -/
85:   properRepresentative : (∃ vertex, vertex ∉ support) →
86:     ¬ Set.InjOn label ↑family →
87:     (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
88:       (∀ coordinate ∈ family, value left (label coordinate) =
89:         value right (label coordinate)) →
90:       left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
91:         Response.ContextEquivalent Target left right) →
92:     ReplacementSupport Baseline Target object support
93:   /-- `def:admissible-rank-quotient`, closed clause.  Likewise at `Z = G`: only a
94:   target-complete rank-reducing quotient is admissible, and then it is
95:   represented by a strictly smaller admissible closed representative. -/
96:   closedRepresentative : (∀ vertex, vertex ∈ support) →
97:     ¬ Set.InjOn label ↑family →
98:     (∀ left right : BoundaryPiece (SupportAtom.boundary object support),
99:       (∀ coordinate ∈ family, value left (label coordinate) =
100:         value right (label coordinate)) →
101:       left.boundaryDegreeProfile = right.boundaryDegreeProfile ∧
102:         Response.ContextEquivalent Target left right) →
103:     ∃ representative : FiniteObject.{u},
104:       representative.LexicographicallySmaller object ∧
105:         Baseline representative ∧ (Target representative → Target object)
```

## `hypostructure/Hypostructure/Graph/DeclaredRankQuotient.lean:131-138`

```lean
131: /-- Two realizations the attempt does not separate on the declared family. -/
132: def Identifies (attempt : AttemptedQuotient Baseline Target object family
133:       coordinateSupport)
134:     (left right : BoundaryPiece (SupportAtom.boundary object attempt.support)) :
135:     Prop :=
136:   ∀ coordinate ∈ family,
137:     attempt.value left (attempt.label coordinate) =
138:       attempt.value right (attempt.label coordinate)
```

## `hypostructure/Hypostructure/Graph/NamedSurplusExits.lean:21-30`

```lean
21: > chord set violates the arithmetic conclusion of
22: > `lem:suppressed-family-critical-cycle`.
23: >
24: > A graph *survives the sparse surplus exits* when none of these conclusions
25: > occurs.
26: 
27: This module declares the five alternatives and their joint negation.  Node
28: `[125]` performs the manuscript's branch test through `ExactLedger`: an exit is
29: published on one arm, and `SurvivesSparseExits` is published on the other.  In
30: particular, this declaration does not claim that selection or replacement
```

## `hypostructure/Hypostructure/Graph/NamedSurplusExits.lean:59-74`

```lean
59:         coordinateSupport)
60:       (reducing : ¬ Set.InjOn attempt.label ↑family)
61:       (reduced full : BoundaryPiece
62:         (SupportAtom.boundary object attempt.support))
63:       (identified : attempt.Identifies reduced full)
64:       (defect : Response.TargetDefect Target reduced full)
65:   /-- (c) a nontrivial target-complete compression of a proper atom, recorded
66:   at the one-way `ReplacementSupport` strength used by `lem:replacement`. -/
67:   | compression (support : Finset object.Vertex)
68:       (replacement : ReplacementSupport Baseline Target object support)
69:   /-- (d) a proper or global delocalization coordinate: a strictly smaller
70:   representative meeting the baseline whose target transfers back. -/
71:   | delocalization (representative : FiniteObject.{u})
72:       (smaller : representative.LexicographicallySmaller object)
73:       (baseline : Baseline representative)
74:       (transfer : Target representative → Target object)
```

## `to_formalize/erdos_64_proof.tex:2692-2713`

```tex
2692: \begin{definition}[Sparse surplus exits]\label[definition]{def:named-surplus-exits}
2693: A \emph{sparse surplus exit} is one of the following conclusions, each of which
2694: is defined without invoking the near-cubic Type A/Type B branch machinery:
2695: \begin{enumerate}[label=(\alph*), leftmargin=2.2em]
2696: \item a direct power-of-two contradiction, equivalently a power-of-two cycle or a
2697: Mersenne return in the sense of \cref{lem:return-equivalence};
2698: \item a target-defective quotient, as defined by
2699: \cref{lem:context-universality};
2700: \item a nontrivial target-complete compression of a proper boundaried piece, forbidden by
2701: \cref{lem:replacement,cor:uncompressible};
2702: \item a proper or whole-graph support-dependence coordinate governed by
2703: \cref{lem:proper-smearing,lem:no-silent-global-smearing};
2704: \item an open-port suppression cycle whose chord set violates the arithmetic
2705: conclusion of \cref{lem:suppressed-family-critical-cycle}.
2706: \end{enumerate}
2707: A graph \emph{survives the sparse surplus exits} when none of these conclusions
2708: occurs for any selected surplus demand, any selected pair of surplus demands,
2709: or any baseline spine coordinate used in the entropy sandwich of
2710: \cref{def:baseline-spine-demand}.
2711: The label name \texttt{def:named-surplus-exits} is retained for references in
2712: the dependency diagram; the exits in this branch are precisely the sparse exits
2713: listed above.
```
