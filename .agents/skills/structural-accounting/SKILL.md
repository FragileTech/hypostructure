---
name: structural-accounting
description: Perform a complete structural accounting check of one open residual of the Erdős–Gyárfás Hypostructure proof (or any residual built on the same ExactLedger). Produces two tables using the methodology page's structural register (groups A–I, 88 coordinates) as the template. Table 1 lists every structural property, marked with an x where the residual correctly accounts for it. Table 2 maps every fact of the residual to the structural properties it accounts for. Use when asked to account structure on a residual, audit which structure a residual has or has not used, find unaccounted ("free") structure before a closure attempt, or re-run the Stage 1/2 accounting of the methodology workflow as a standalone task.
---

# Structural accounting of one residual

This skill carries out the accounting that the methodology workflow (repair_and_closure.md, stages 1–2) was meant to do: record exactly which structure of G the residual already measures, and exhibit every structural coordinate that is present at G but still unmeasured. The output is a fixed, problem-independent grid (Table 1) and a complete fact-by-fact map (Table 2). The two are cross-checked, so an omission in either table is visible.

It is read-only analysis. **Never edit Lean, never build, never commit.** The only file you write is the report.

## The rule that governs every mark

**Only what is constructed for G counts.** G is the selected minimal counterexample, and it is the whole object. The residual's region Z, its piece G[Z] and its rest G − Z are all parts of G. An object that is not part of G never accounts for anything, however useful it looks. Such objects include:
- an arbitrary outside context O glued at a boundary;
- a cycle in "reading glued to O";
- "some context separates", or "every context agrees";
- a witness on another graph.

A fact whose statement depends on such an object gets the status `nonG` for the coordinates it touches, and it never earns an `x`. Where one exists, record the G-constructed reformulation (for example, the swap of G at Z and its canonical degree deficit) as the missing accounting.

## Template: the structural register

The coordinates are the methodology page's structural survey ("Techniques and structural invariants"), stored in `tools/methodology_gate/policy/structural-register.json`:
- 9 groups: size-degree (A), connectivity (B), paths-cycles (C), local-structure (D), criticality (E), dependence (F), counting (G), potentials (H), certification (I);
- 88 properties, each with its observable, admissible techniques (T01–T19) and certificate type.

Table 1 always contains all 88 rows, in register order, for every residual. The grid is the same for every problem; only the marks change.

Generate the blank template first:

```
python3 .agents/skills/structural-accounting/scripts/structural_template.py <ResidualName> \
  --out <report path>
```

`<ResidualName>` is the residual's `abbrev`: a generic residual in `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly/Residuals.lean` (for example `Node144aOutcome`, `Node54ResidualOutcome`), or one of the subtypes that the root type `SelectedLedgerBoundaryResult` (`Assembly/Final.lean`) actually returns, stated in `Assembly/Residuals/*.lean` (for example `Node144aOutcome_windowFails`, `BlockedBarrierOverlapOutcome_DeficiencyAtOrAbove`). The script extracts every fact key of that residual in ledger order, expanding a subtype's generic residual in place, and the register rows. For a product path (for example `Route8JointBalanceOutcome_product`) it lists the disjunctive arm blocks without expanding them; add the keys of the arm the path took. It never marks anything.

## Required reading, before marking

1. The register JSON, all of it: observables, techniques, certificates and caveats.
2. The methodology page's account of accounting: `web/frontend/src/components/MethodologySection.tsx`, parts "Cost as constraint", "Cost as quantity: structural accounting" and "Cost as compression". These define what "accounted" means: demands, payers, canonical assignment, certified capacity, distinct currencies, and the moves × budgets check.
3. The residual's `abbrev` in `Residuals.lean` or `Residuals/*.lean`, and for **every** key the exact `Holds` statement. Follow `Holds` in `hypostructure/Hypostructure/Graph/Strategy/SpineVocabulary.lean` to its Statement in `hypostructure/Hypostructure/Graph/Statements/*.lean`. Read the proposition itself, not its docstring.
4. The residual's entry in `audits/erdos-64-red-team/lean-vs-paper-discrepancies.md` and the manuscript node (`to_formalize/erdos_64_proof.tex`), to know the canonical objects and the test whose failure defines the residual.

## Procedure

1. **Name the residual's defining failure.** State in one sentence which test or inequality failed to produce this residual, and at which canonical objects of G. Every later judgement is relative to that object.
2. **Table 2 first, fact by fact.** For each key, in ledger order, fill in:
   - the statement at G, in one line of mathematics;
   - whether it is about G only (`yes` / `no: <the non-G object>`);
   - the coordinates it accounts for, as register codes, possibly several;
   - the certificate type it delivers: bound, identity, witness, decomposition, obstruction, replacement, exclusion or classification;
   - what consumes it: the other keys or the decision that read it, or `unconsumed`.

   A fact accounts for a coordinate only if it gives that coordinate's observable a certificate of the register's type, at G's canonical objects of this residual. A fact that merely mentions an object does not account for its structure.
3. **Table 1 from Table 2.** For each of the 88 coordinates, choose exactly one status:
   - `x` (accounted): at least one Table-2 fact about G gives the certificate at this residual's canonical objects, quantitatively where the observable is a quantity, **and** it is combined with the other currencies it interacts with (it enters an inequality, decision or identity together with them). List the fact numbers.
   - `~` (partially accounted): certified only on a sub-object; or an existence claim where a quantity is available; or proved but never combined or consumed. Say what is missing.
   - `gap` (present at G, unaccounted): the structure provably occurs at G on this residual (name the fact or canonical object that shows it occurs), but no fact measures it. State the missing accounting as a concrete observable and certificate.
   - `n/a` (absent): the structure is provably absent at G on this residual, or excluded by a named fact. Give the reason and the excluding fact. "Not relevant" is not a reason.
   - `nonG`: only non-G facts touch it. Also give the G-constructed accounting that should replace them.
4. **Cross-check the two tables:**
   - every coordinate code in Table 2 has status `x` or `~` in Table 1, and lists that fact;
   - every `x` or `~` in Table 1 cites at least one Table-2 row;
   - every Table-2 row accounts for at least one coordinate, or is labelled `bookkeeping` (a pure routing or tag fact) with a reason;
   - no fact is counted twice for the same demand in different currencies (the methodology page's unit rule).
5. **Joint check.** For each `gap` and `~`, name the facts already on the residual that would combine with that coordinate once it is measured, and the technique (T-code) that would measure it. Rank the gaps by how many existing facts each would be combined with. The top of that ranking is the structure a closure attempt should use next.

## Report format (the file you write)

1. Header: the residual, its defining failure, the fact count, and counts per status (`x`, `~`, `gap`, `n/a`, `nonG`).
2. **Table 1**: all 88 rows grouped as in the register, with the columns from the template.
3. **Table 2**: all facts, with the columns from the template.
4. **Gaps ranked**: coordinate, why it is present at G, the missing observable and certificate, the technique, and the existing facts it would combine with.
5. **Non-G facts**: each fact that uses an object outside G, with its G-constructed replacement.
6. **Cross-check results**: the four checks of step 4, pass or fail, with the offending rows.

## Discipline

- Mark from the Lean statements, never from summaries, register prose or earlier reports.
- Do not invent coordinates; the register is the template. If some structure really fits no coordinate, put it in a final section "Outside the register", with its observable, and do not force it into a row.
- Never present a feasible numerical point as G's structure. A coordinate is `gap` because the structure is present and unmeasured, not because some assignment of numbers is consistent.
- No "unbounded" or "free" claims: if nothing measures a coordinate, the status is `gap` together with the missing accounting.
- Complete every row. A blank cell is a failed check, never an implicit `n/a`.
