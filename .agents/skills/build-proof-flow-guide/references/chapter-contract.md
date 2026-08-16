# Proof-flow chapter contract

## 1. Mathematical authority

The target manuscript is the single source of truth. Read the cited definitions,
lemmas, theorem statements, and proofs. An earlier paper may supply visual style,
but it may not supply missing hypotheses, branches, labels, or closures.

The guide must preserve the final theorem exactly. In particular, do not replace
local compact-cylinder estimates with whole-space estimates, and do not turn an
unconditional conclusion into a conditional one.

## 2. Chapter contents

Place the guide after the introduction and before the proof. Use this order:

1. Architecture and reading guide: state the input, locality, source-of-truth
   rule, shape semantics, and how carried facts are represented.
2. Diagram map: list each part, node range, branch resolved, and principal
   internal sources.
3. Proof-dependency diagram: one logical directed graph, split across pages only
   for legibility.
4. Node-by-node audit table: node, state/test, exact proof source, successor or
   closure.
5. Monotone ledger: record hypotheses established upstream and retained through
   subsequences, reselection, and terminal extraction.
6. Branch-closure ledger: list every terminal class, diagram route, closure
   source, and terminal output.

## 3. Node semantics

- Rectangle (`box`): a state or interface with exactly one incoming and one
  outgoing live edge. The unique root has no incoming edge.
- Diamond/rhomboid (`dec`): an exhaustive decision. It has at least two outputs.
  Use it when some outputs close and others continue.
- Solid ellipse (`term`): a terminal closure justified by a cited proof. It has
  no outgoing edge.
- Dashed ellipse (`route`): an unnumbered visual copy of a numbered solid
  terminal ellipse located elsewhere. Its text names that terminal node. It is
  not a new proof state.

Never draw an ellipse with an outgoing edge. Never give a rectangle two outputs.
Never hide a real dichotomy inside an ellipse labelled “A or B closed.” Insert a
decision node and show the separate branches unless the body proves a genuinely
single named closure with no further live case distinction.

## 4. Routing contract

- Use one numbered root representing the paper's actual input.
- Every numbered node must be reachable from that root.
- Every nonterminal path must have a visible successor.
- A first-failure rectangle routes to the ordered classifier; naming a row does
  not close it.
- Each cross-page output such as “continue at [42]” must have a matching
  unnumbered incoming arrow or annotation at [42]. Aggregate several known
  sources in one annotation when they enter the same decision.
- Dashed closure copies must point only to solid terminal ellipses, never to a
  live state or decision.
- Carried hypotheses need not generate backward arrows. Record them in the
  monotone ledger, but continue drawing the live residual/state.
- If a theorem reselects a smaller member of a finite family, show the
  well-founded reselection test or cite the finite-rank termination explicitly;
  do not make the replacement branch vanish.

## 5. Numbering and labels

Number solid nodes consecutively in source order. Use each number exactly once
in the diagrams and once in the node audit table. Dashed proxy ellipses repeat
the target number but do not create a solid node or table row.

Use semantic LaTeX labels such as `fig:proof-flow-active-core` and
`lem:pressure-routing`. Remove labels whose only meaning is a deleted paper
number or obsolete document layout.

## 6. TikZ baseline

Use consistent styles throughout the chapter:

```tex
box/.style={rectangle,rounded corners,draw,align=center,inner sep=3pt},
dec/.style={diamond,draw,aspect=2.35,align=center,inner sep=1.5pt},
term/.style={ellipse,draw,align=center,inner sep=3pt},
route/.style={ellipse,draw,dashed,align=center,inner sep=2pt},
arrow/.style={-{Latex[length=2mm]},thick}
```

Adjust dimensions and coordinates for legibility. Keep edge text away from node
text. Prefer explicit coordinates for broad fans. Render the PDF page after any
nontrivial positioning change.

## 7. Source audit

For each decision, compare the outgoing labels with the exact enumerated cases
in the cited result. For each terminal, read the closure proof and confirm that
it does not merely route to another unresolved row. For each continuation,
confirm the target accepts the same state and retains all required hypotheses.

Check especially:

- entry and concentration-sequence construction;
- representation, gauge, and pressure interfaces;
- compactness and profile/residual exhaustion;
- reselection and finite-rank termination;
- first-failure classification versus later closure;
- local regularity contradictions;
- the final unconditional assembly and absence of circularity.

## 8. Mechanical and visual audit

Run the bundled checker, `git diff --check`, and the manuscript's normal LaTeX
build. Search the log for undefined references, multiply defined labels,
oversized floats, and overfull boxes. Inspect all diagram pages at readable
resolution; compilation alone does not reveal overlaps or misleading arrow
geometry.
