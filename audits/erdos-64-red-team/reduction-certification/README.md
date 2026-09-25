# Certification audit of the three-residual reduction

Date: 2026-09-21. Target: `thm:main` in `to_formalize/erdos_64_proof.tex`.
The source hashes in this directory identify the final inspected mathematical sources.
`Assembly.lean` changed externally during the audit; the root alternatives were
rechecked after that change. Declaration names are the authoritative locators;
some line references describe the initial inspected revision.

## Verdict

**The stated three-residual reduction is not currently certified.** The live
Lean root proves a broader disjunction. Two specific statement/composition
defects also occur in the LaTeX argument. This is a failed certification audit,
not a counterexample to the reduction or the conjecture, and not a certification
of all the manuscript's individual lemmas. A complete independent verification
of every local mathematical argument remains outstanding.

Proving the emptiness of [172a], [182], and [186] is **not** a prerequisite for
publishing a correct reduction to those three residuals. Proving that every
other branch reaches one of them, with its full incoming state, is required.

## Method and evidence boundary

1. Read the exact theorem and its proof, including the retained-state clause.
2. Inspect the actual root definition, recursively expand every returned
   disjunction, and inspect the underlying `Holds` propositions.
3. Trace each extra return to a live producer/return site and compare the
   manuscript's proposed consumer and its hypotheses.
4. Inspect the three intended endpoint predicates separately from their
   unresolved emptiness claims.
5. Build the canonical execution fixtures and the current EG library; inspect
   transitive axioms rather than relying on green audit cells.
6. Record both established discrepancies and remaining certification work.

The complete root-output inventory below is exhaustive for the current return
type. It is not an assertion that all 186 diagram nodes have undergone a new
line-by-line semantic audit. Existing node-table verdicts are not adopted as
evidence merely because they are green. UI, graph-extraction, and PDF tests do
not certify mathematics.

## Exact root-output inventory

Source: `proofs/hypostructure_erdos_64_eg/HypostructureErdos64EG/Assembly.lean`.
`selectedLedgerBoundary` (9250) accepts a selected input and its selection
ledger. `SelectedLedgerBoundaryResult` (9241) expands through definitions at
1653, 2708, 6785, 7148, 7753, and 9191 to **nine distinct propositions**:

| Output key | Intended endpoint? | What must be certified |
|---|---|---|
| `blockedBarrierOverlap` | [172a] | First failed conditional graph-count inequality, its prefix/outside fibre, and retained incoming state. |
| `pairConditionalFactorizationResidual` | [182] | One of three explicitly recorded uncovered implications, with its literal witness/input. |
| `route8JointBalance` | [186] | Same-family visible-overload residual, joint balances, silent exclusion, and retained ancestry. |
| `sparseTargetDefectResidual` | No | Construct the applicable target-defect continuation on the actual sparse ledger; close it or route it to an allowed endpoint. |
| `typeBFanEntry` | No | Continue the strict-surplus Type B handoff without borrowing the near-cubic sibling hypothesis. |
| `typeBSublinearResidual` | No | Prove the required Type B charging/absorption hypotheses on the incoming ledger, or route their failure using an established implication. |
| `route8QuotientResidual` | No | Discharge or route failure of the precise quotient-free statement before the route-8 census/descent uses it. |
| `route8RateFails` | No | Route the failed exact private-carrier inequality on every arm, including the finite-order cases. |
| `coldBranchClosed` | No | Consume the local exclusion with an actual surviving terminal witness, or route its remaining alternatives. A negated local terminal predicate alone is not `False`. |

These are possible conclusions of a proved disjunction, not nine proven
nonempty graph classes. Some extra outputs may be removable by connecting
existing mathematics; the inventory does not prove six new mathematical gaps.

## Specific certification obligations

### R1. Sparse target-defect exit

The root's sparse-exit arm returns the target-defect fact directly
(`Assembly.lean:9258–9266`; producer `selectedSparseSurplusExitContinuation`).
Its meaning (`SpineVocabulary.lean:11154`) is existence of an attempted quotient
whose labels are not injective and an identified pair with a target defect.
This is not itself a power-of-two cycle or any of [172a], [182], [186].

The main proof says “that sparse exit closes in the sparse branch”
(`erdos_64_proof.tex:365`). Certification requires the actual closure or
continuation from this incoming ledger, including the construction that makes
the defect applicable to the later exit-(4)/peeling machinery. Identifying a
target defect is not that construction. Do not substitute a downstream
near-cubic peeling theorem without establishing all of its prerequisites.

### R2. Strict-surplus Type B handoff: a LaTeX composition gap

`prop:nonnear-cubic-sharp-overload-routing` (`tex:5719`) has three outcomes:
near-cubic estimate, sparse exit, or decorated Type B handoff. It does not
prove that the third outcome reaches the first. Nevertheless `thm:main`
(`tex:364–373`) concludes that every survivor reaches the near-cubic spine.

The live continuation confirms the missing consumption:
`StrictSurplusTypeBOutcome` is `Holds .typeBFanEntry`, and
`selectedStrictSurplusTypeBContinuation` ends by projecting that fact
(`Assembly.lean:2708–2760`). The root returns it unchanged.

The cited bridge sublinearity proposition (`tex:14893`) explicitly assumes
`def:near-cubic-spine` and uses it to obtain `16 σ(G)=O(√n)=o(|R|)`.
It cannot establish that same prerequisite on the strict-surplus arm.
Required: an unconditional continuation from the strict-surplus handoff's
actual retained hypotheses, terminating in contradiction or a stated endpoint,
or deriving the near-cubic estimate without this circular use. Merely drawing
the arrow into the Type B ledger is insufficient.

### R3. Type B sublinearity prerequisites

`SpineVocabulary.lean:9839` defines the residual as
`¬ TypeBSublinearHypotheses data object` (definition at 5645).
The positive statement includes quantified bridge-component conditions and
existence of handoff pieces, high-degree centres, fan envelopes, absorbed
subsets, receiver assignments/capacity inequalities, and the total absorption
bound. The relevant quantification includes every maximum packing; proving
only a selected-packing instance does not prove that statement.

`selectedRouteEightResidual` returns the negative arm at
`Assembly.lean:1886–1903` (also 2050ff). The manuscript uses
`prop:typeB-bridge-sublinear` and the envelope/bridge lemmas to eliminate this
mass. Required: check each premise against the actual incoming state, prove
the positive hypothesis package there, and wire its use. Alternatively prove
a manuscript-supported route for its literal failure. Failure alone supplies
no geometric overlap construction.

### R4. Quotient exclusion before the route-8 census

`SpineVocabulary.lean:9843` defines the output as
`¬ Route8QuotientFreeStatement data object` (definition at 5733).
That positive statement excludes trace-response quotients for selected basins
of unified entries and of specified extracted positive-surplus cores.
The same continuation returns this negative arm before entering the later
route-8 census and descent (`Assembly.lean:1893ff`, 2050ff).

Required: prove quotient exclusion, or its appropriate closure/routing, on
these actual basins. Audit properness, baseline preservation, target-response
preservation and strict progress before invoking minimality. An arbitrary
trace-response quotient cannot be treated as a smaller admissible
counterexample by naming it a quotient. No supplied raw failure-to-endpoint
implication is present at the root.

### R5. Private-carrier rate, including a LaTeX hypothesis mismatch

The exact positive predicate (`Graph/Route8Census.lean:218`) is

`(threshold * discharge + 1) * |supply| + threshold * slack < threshold * |R|`.

Its negation is the output at `SpineVocabulary.lean:10843`. It is returned
at `Assembly.lean:8102,8568,9023`; `selectedRouteEightRateFailure` (7137)
only returns its incoming ledger.

There is a concrete source-level routing mismatch. `lem:dense-deficiency-routing`
(`tex:7586`) sends **either** failed rate test to [162]. But the stated
`lem:dense-cold-pass` (`tex:7613`) assumes `τ≥1/4`. A failure of `τ<3/13`
after success of `τ<1/4` does not imply that assumption. The interval
`3/13 ≤ τ < 1/4` is not covered by the stated receiving lemma. Its proof says
the density sentence is unused, which suggests a possible repair, but a
broader exact statement and its proof must actually be supplied and checked.

Required: consume each failed exact rate on its correct incoming state.
The small-order repair [173]–[177] decides a different collision; it cannot
be applied just because some rate fails. Explicitly verify finite allowances
and both comparison complements. No asymptotic estimate can replace an
unproved inequality for the particular finite minimal counterexample.

### R6. Local cold exclusion versus global branch closure

`coldBranchClosed` (`SpineVocabulary.lean:9216`) means
`¬ TerminalColdResidual ... object`. `TerminalColdResidual`
(`Graph/ColdCorridor.lean:1914`) is a disjunction of terminal length-changing
families, terminal table rows, and terminal self-returns.

The root continuation returns this exclusion (`Assembly.lean:9011`, also
through `SelectedAbsorbedGermBoundary`). A proof of `¬ T` does not close a
counterexample branch without a proof of `T` on that branch, or an exhaustive
route for its alternatives. The LaTeX `thm:cold-branch-quantitative-closure`
(`tex:7493`) claims that all its outcomes are excluded.

Required: certify extraction of a terminal witness or the full alternative
continuation from the literal cold ledger, consume the local exclusions,
and prove that every handoff/defect/compression is actually discharged.
Check the finite positivity of the configuration count; the displayed
asymptotic lower bound alone does not cover every finite input.

In particular, `def:surviving-cold-branch` (`tex:6920`) includes absence of
unpaid exit-(4) peels and of the [181] demand residual, as well as the
near-cubic estimate. These are substantive entry requirements. A local cold
theorem under that definition does not establish that every earlier cold
branch has those properties; the complementary cases must be routed through
the reduction as well.

## The intended endpoints and [171]

The inspected endpoint definitions contain substantial, concrete mathematical
content; they are not merely three unnamed assumptions:

- [172a]: `BlockedBarrierFailureStatement` (`SpineVocabulary.lean:2574`)
  includes all local state-fibre/monotonicity bounds, earlier-ranked relative
  bounds, and a strict failed conditional graph-count inequality.
- [182]: `PairUncoveredResidual` (7930) has three constructors retaining the
  overlap system, demand returns, or serial system and the corresponding
  negated implication/outcome.
- [186]: `Route8JointBalanceStatement` (6364) contains visible-overload data,
  absence of silent unpeeled excess, a peel chain, stage accounting, maximal
  demand partition/absorption, and simultaneous balances on the same entries.

The root nevertheless projects semantic facts and returns a disjunction,
rather than returning each complete terminal ExactLedger. The manuscript
expressly promises all inherited facts and objects. Certification must check
that a final theorem preserves or reconstructs the complete branch history;
the inspected payloads alone are not a proof of that universal retention
claim. Use the existing canonical ledger machinery, not new assumptions.

[171] is not a fourth open leaf. On [170]'s positive graph-count arm it uses
the established bounds, blocked membership and the retained dense overflow
to contradict the skeleton budget. The intended [172a] residual is precisely
the negative arm. The broad blocked-class estimate in the old Zenodo version
must not be used unconditionally in this certification.

## Entry, trust, and the actual finish line

`openSelectedCounterexample` (`Assembly.lean:1095`) constructs the selected
scope using refined minimality. The current root starts from the selected
ledger. The final reduction must connect the finite-simple-graph existence
assumption to this scope and then to **exactly** the three retained endpoints.
The old names `erdos_64_of_selectedLedgerClosure` and
`target_closure_of_selectedLedgerClosure` listed in audit rows [1]–[3] are
absent from the current EG source; those rows cannot certify the new theorem.

The EG source has an explicit external axiom
`WindowAlgebra.p13Free_hasPowerOfTwoCycle`. The cited result is consistent with
Hegde–Sandeep–Shashank, *Erdős–Gyárfás conjecture on graphs without long induced
paths*, https://arxiv.org/abs/2410.22842. A journal reduction can cite this
external theorem. Calling the whole result Lean-certified without disclosing
that trust boundary would be inaccurate. Transitive axiom checks, including
computational trust, are recorded separately in the build evidence.

The acceptance conditions for certification are:

1. Resolve R1–R6 on their actual incoming histories, without new assumptions
   or a silently enlarged endpoint list.
2. State and prove the exact three-endpoint root theorem and its entry
   selection, preserving the retained-state claim.
3. Audit every transitively used local proposition against its LaTeX
   quantifiers, objects, hypotheses and conclusion. A successful Lean build
   establishes only the encoded propositions, not their fidelity to prose.
4. Check all finite/asymptotic transitions and exact counted classes on those
   paths, including integer rounding and injection/decoding assumptions.
5. Produce a successful build and transitive axiom inventory of that exact
   root, then synchronize the source, audit tables, app and final PDF.

Until these conditions are met, the manuscript should not be represented as
a verified reduction to only three residuals. Independent mathematical
refereeing remains valuable even after formal certification.
