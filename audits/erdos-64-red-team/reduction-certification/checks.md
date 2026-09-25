# Reproduction and check results

These checks concern the current implementation, not a proof of the missing
three-endpoint theorem. Run from the repository root unless specified.

## Completed

- The canonical ExactLedger, FactManifest and ExactExecution modules and 12
  execution/ledger fixtures built successfully: **8573 jobs**.
  See `framework-build.log` for the exact results.
- `python3 .agents/skills/eg-proof-expansion/scripts/audit_tables.py check --repo-root .`
  passes after correcting the root audit row and removing the obsolete
  `cor:conditional-conjecture` fact row. This checks table structure only.
- In `proofs/hypostructure_erdos_64_eg`,
  `lake env lean ../../audits/erdos-64-red-team/reduction-certification/InputAxiomAudit.lean`
  prints the transitive axioms of the freshly built `spineData`.
  Result: **472 axioms: 468 generated `native_decide` axioms, `propext`,
  `Classical.choice`, `Quot.sound`, and the explicit HSS axiom**.
  No `sorryAx` occurs in that output. See `input-axioms.log`.

The native computation results have compiler/runtime trust in addition to
the external HSS theorem. They are not 468 unfinished mathematical lemmas,
but they must not be described as kernel-reduced computation without that
trust boundary. This input audit is not a substitute for checking the axioms
of the final root theorem.

## Full-library and API checks

The full-library command is `lake build HypostructureErdos64EG`, run in
`proofs/hypostructure_erdos_64_eg`. At the report cutoff (2026-09-21 15:51 UTC), this build was still running,
with no final success/failure result. `library-build-in-progress.log` is a
snapshot, not a completed build certificate. The live log is
`/tmp/eg-reduction-build.log`. Consequently the full-root axiom diagnostic
`AxiomAudit.lean` has not been certified against a completed fresh build.

The API catalog check initially failed because `SpineRows.olean` was missing;
a subsequent attempt progressed to a missing `SpineContinuationRun.olean`.
These are incomplete-build preconditions, not evidence of an API violation.
The command is
`python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py check --repo-root .`.

## Scope limitations

No LaTeX or Lean mathematical source was edited by this audit. The source
tree already contained changes and `Assembly.lean` also changed externally
while checking. The final source hashes are recorded, with the initial hashes
kept separately. A later successful build is evidence only for the sources it
actually read. The exact three-endpoint theorem remains absent regardless
of the broader library's build result.

The report is a complete inventory of the root's returned alternatives and
an evidenced rejection of current certification. It is not a completed
independent proof check of every mathematical lemma in the manuscript.
