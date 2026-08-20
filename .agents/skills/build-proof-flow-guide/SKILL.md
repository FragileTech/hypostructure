---
name: build-proof-flow-guide
description: Create, repair, or audit an introductory proof-architecture chapter in a mathematical LaTeX manuscript, including TikZ proof-flow diagrams, a diagram map, node-by-node source ledger, monotone-hypothesis ledger, and branch-closure table. Use when Codex must reproduce the proof-first reading-guide style of type_II_regularity.tex or erdos_64_proof.tex for another paper; merge or expand proof diagrams; correct node shapes, cross-page routing, labels, or overlaps; or verify that a diagram is acyclic, exhaustive, local, unconditional, and faithful to the implemented proof.
---

# Build Proof Flow Guide

Create a referee-facing map of the proof without changing or replacing the
proof. Treat the manuscript's definitions, statements, and proofs as the only
mathematical source of truth.

## Required reading

Read [references/chapter-contract.md](references/chapter-contract.md) completely
before designing or editing a guide. Inspect the target manuscript itself; use
an existing guide only for presentation conventions, never for mathematical
content or labels.

## Workflow

1. Locate the introduction, the main unconditional conclusion, the ordered
   proof assembly, every routing lemma it invokes, and every terminal closure.
2. Record the actual proof states and alternatives before writing TikZ. Trace
   every branch from one unique input. Do not create an independent branch
   merely because a later theorem starts a new subsection.
3. Check dependency order. Separate row-producing lemmas from later row-closing
   theorems, and reject any edge that uses a closure to manufacture its own
   input.
4. Design the graph under the shape contract in the reference. Expand each
   genuine case split into a decision node and distinct outputs. Use a named
   terminal closure only when the cited proof truly closes that branch.
5. Split a large graph across pages only as parts of one logical DAG. Give every
   cross-part continuation a matching unnumbered input annotation. Use dashed
   ellipses only as references to numbered solid terminal ellipses drawn
   elsewhere.
6. Insert the guide after the introduction and before the proof, unless the
   user specifies another location. Keep the target paper self-contained and
   use meaningful labels that describe results rather than obsolete paper
   numbers.
7. Add, in order: a short architecture explanation, diagram map, proof-flow
   parts, node-by-node audit table, monotone retained-fact ledger when useful,
   and branch-closure audit table.
8. Cite the exact body statement supporting every node and every terminal
   edge. If the diagram would require a statement the paper does not prove,
   report the proof gap; do not conceal it with prose or weaken the theorem.
9. Run `scripts/audit_proof_flow.py` on the manuscript. Fix all numbering,
   shape, terminal-output, proxy, and table errors it reports.
10. Compile to PDF, inspect every diagram page visually, and check for undefined
    references, oversized floats, clipped nodes, crossed labels, or overlapping
    edges. Recompile after corrections.

## Proof-integrity rules

- Preserve the theorem's quantifiers, hypotheses, locality, and unconditional
  status. Never introduce a global bound to simplify a proof that is local.
- Do not alter the proof body unless the user separately authorizes a proof
  repair. The guide is an audit layer, not an alternate proof.
- Monotone ledger facts may remain implicit on later arrows, but the live state
  may not disappear, duplicate, or appear without an incoming route.
- A backward numerical reference is acceptable only when the directed graph is
  still acyclic and the target cannot route back to the source.
- Prefer several readable parts of one DAG over a compressed picture that hides
  alternatives. Do not call multiple panels a single diagram when the user asks
  for one continuous drawing.

## Validation command

Run from the skill directory or use the absolute script path:

```bash
python3 scripts/audit_proof_flow.py path/to/paper.tex --first 1 --last N
```

The checker assumes the standard style names `box`, `dec`, `term`, and `route`.
Pass the corresponding style flags if the manuscript uses different names.
Treat a successful script run as structural evidence only; source-level proof
comparison and rendered-page inspection remain mandatory.

## Completion report

State what was added or corrected, whether the proof body changed, which graph
invariants were checked, the compilation result, and the paths to the source
and PDF. If any diagram edge remains unsupported by the proof, identify it
plainly instead of declaring the audit complete.
