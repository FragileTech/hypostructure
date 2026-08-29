# Proof status after red-team review of nodes [157]–[180]

Audit date: 2026-08-25

Implementation status updated: 2026-08-29

Scope: the cumulative residuals and routing contracts at nodes [157]–[180] of the Erdős–Gyárfás structural-exhaustion proof.

Sources: the live manuscript, directed proof graph, node ledgers, current Lean declarations where present, and the 24 canonical reports in [`reports/`](reports/). The campaign ledger is [`coverage.json`](coverage.json).

## Post-audit implementation status

The verdicts below record what the red-team campaign found in the 2026-08-25
snapshot. A 2026-08-29 code-first recheck confirms that the node-`[177]`
**WRONG ROUTING DESTINATION** verdict still applies to manuscript fidelity,
although its earlier mechanical projection failures are fixed.

The repairs through `[157]`, `[160]`–`[161]`, `[165]`–`[171]`, and
`[173]`–`[176]` are implemented on the literal incoming `ExactLedger`. In
particular:

- `[175]` partitions the retained incidence family without losing the heavy
  complement on mixed families;
- `[176]` runs the registered `[154]`–`[157]`, `[163]`, and `[165]`–`[168]`
  owners on the selected local residual;
- `[177]` constructs a cold heavy-centre corridor witness and its seven former
  projection failures are repaired, but the implementation then weakens
  `TypeBFanEntryStatement` by adding that witness as a new disjunct. No theorem
  constructs the manuscript's assigned Type-B support/decorated envelope, so
  `[177]` remains an implementation bug;
- `[171]` executes the additive compression closure, while the exact
  nonadditive fibre is retained only at `[172a]`;
- the covered arms of `[178]`–`[180]` are implemented, and only their precise
  negative complements are retained at `[182]`.

The same-token `[144]` route, although outside this report's node range, now
executes the shared `[68]`–`[85]` continuation mechanically. That continuation
still omits the manuscript's shoulder-completion, port-return, first-landing,
cross-shoulder, and fan-closed routing facts, so its successful build is not a
proof of the Type-B chain. The remaining bugs are therefore not limited to
`[172a]`, `[181]`, and `[182]`; see
[`../../EG_incomplete_nodes_repair_plan.md`](../../EG_incomplete_nodes_repair_plan.md).

The remainder of this document preserves the original findings and proposed
repairs for audit provenance.

## Original executive conclusion

The audit found no graph satisfying the complete accumulated hypotheses that disproves the Erdős–Gyárfás theorem. It also found no `VALID LOCAL COUNTEREXAMPLE`. Many attractive counterexamples fail an earlier minimum-degree, target-avoidance, packing, or branch-selection invariant.

Nevertheless, the audited part of the manuscript is not yet a complete proof as written. Of the 24 nodes, two are sound, six need precise wording, and sixteen contain a local proof or routing obligation that is not discharged by their incoming residual. Those sixteen findings reduce to nine recurring mathematical defects: a missing graph representative, a density-threshold mismatch, an undeclared same-size minimality order, an incompatible stub selection, a missing entropy baseline, incomplete modular lifting, a missing positivity split, an ill-typed Type B handoff, and a nonexhaustive pair-obstruction analysis.

The current situation is therefore:

- the overall proof strategy remains recognizable and most repairs preserve its existing routes;
- several corrections are editorial or finite decision splits;
- several central steps require actual new lemmas or constructions, especially [157], [165]–[166], [171], [175]–[177], and [178]–[179];
- the theorem has not been refuted, but this audited terminal portion should not be described as closed until those obligations are proved.

## Verdict totals

| Verdict | Nodes | Meaning for the proof |
|---|---:|---|
| `NO ISSUE FOUND` | 2 | The exact accumulated contract and routing survived the audit. |
| `PROSE AMBIGUITY` | 6 | The intended claim is recoverable from nearby definitions or retained facts, but the current wording states a different or underspecified contract. |
| `MISSING REPRESENTATIVE` | 3 | An abstract quotient, equivalent piece, or equal-size exchange is not yet an actual strictly smaller counterexample in the declared minimality order. |
| `MISSING RANGE OR DIVISIBILITY CHECK` | 5 | A threshold, positivity, 2-adic compatibility, or finite central-range condition is omitted. |
| `WRONG ROUTING DESTINATION` | 6 | A live residual does not satisfy the complete entry contract of its advertised destination. |
| `NONEXHAUSTIVE BRANCH` | 2 | The stated alternatives leave a real abstract residual unassigned. |

The verdict count is a node count, not a count of independent errors. For example, [160] and [161] are two manifestations of one threshold defect, while [172] and [180] repeat the same modular-lifting error in different systems.

## Where the proof is sound

Two nodes survived all required counterexample tests.

- [Node 158](reports/node-158.md) is a valid exact cardinality decision provided it is read as the budget test
  \[
  2^{c_{13}p_{13}\log_2 n}\le |\mathcal G_{n,m}|.
  \]
  Its two arms are literal complements. A prescribed noninjective semantic response map is not part of that predicate.
- [Node 169](reports/node-169.md) correctly places the selected graph in the blocked class. The needed window positions, vertex and edge counts, minimum degree, and global target avoidance have already accumulated.

These findings are local. They do not validate their predecessors or successors.

## The nine substantive proof obligations

### 1. Neutral finite-table compression lacks a graph representative — [157]

[Node 157](reports/node-157.md) correctly handles a length-changing row when one same-interface representative is strictly shorter. It does not close a neutral equal-length row merely from boundary data, response equivalence, and completion truth values. The cited admissible-rank definition excludes an abstract quotient that has no smaller representative; it does not construct the missing representative.

Correction:

- compress only when an explicit proper graph representative satisfying the replacement lemma has been constructed;
- route a neutral row with no such representative to the neutral-symmetry analysis at [163];
- retain the actual support, interface, boundary degrees, baseline, response equivalence, and absence of the earlier realizing/distinguishing exits.

Completion criterion: either enumerate the finite table and construct a valid smaller representative in every neutral row, or prove that every unrepresented row enters [163] with its full contract.

### 2. The dense threshold is too weak for route 8 — [160]–[161]

[Nodes 160](reports/node-160.md) and [161](reports/node-161.md) use a net-deficiency estimate equivalent to \(\tau<1/4\), but the later private-carrier route requires \(\tau<3/13\). The interval
\[
\frac{3}{13}\le \tau<\frac14
\]
is nonempty and is already identified elsewhere in the manuscript as belonging to the hot/cold pass. The present edge sends this interval into a destination whose hypotheses it does not satisfy.

Correction: insert an exact route-8 rate decision after the \(1/4\) comparison. Send only the \(\tau<3/13\) arm to the ordinary Type A/Type B continuation; send the complementary interval to [162] with its dense-packing ledger intact. This decision already has a recognizable analogue in the Lean vocabulary, but the manuscript and graph must state and use it.

### 3. Same-size replacement has no declared decreasing order — [165]–[166]

[Nodes 165](reports/node-165.md) and [166](reports/node-166.md) replace a piece while preserving both \(|V|\) and \(|E|\). The minimal counterexample at [4] was selected only by \((|V|,|E|)\), so the new graph is tied, not smaller. A third coordinate \(\Phi\) is introduced locally without a prior graph-level definition or a proof that recomputing the canonical decomposition changes exactly the exchanged entry.

Correction:

- define at the initial selection a fixed well-founded order \((|V|,|E|,\Psi)\) on canonically labelled graph presentations;
- prove a swap-locality lemma showing that every allowed \(Q\to E\) exchange strictly decreases \(\Psi\) while preserving simplicity, minimum degree, target avoidance, and all boundary responses;
- if no such order is available, retain the equal-size distinct replacement as an open residual rather than concluding \(Q=E\).

Isomorphism invariance is not required; a fixed labelled canonical graph code is enough. What is required is a globally declared order and a proved strict decrease.

### 4. Selected interior-stub closure — [168], [176]

The manuscript and Lean select the same family before corridor extraction: the eleven one-stub interior incidences of each ambient-cubic induced \(P_{13}\), with the first two absorbed corridor incidences dropped.

The resulting supply is exactly \(9C-o(n)\), and the greedy extraction gives \(9C/D_{\rm cold}-o(n)\).

[Node 168](reports/node-168.md) retains the selected interior origin through
the graph-realized two-strand branch. A genuine pair needs two distinct
external stubs at each attachment and therefore attaches at endpoints, whereas
the selected occurrence lies at a one-stub interior vertex. The corresponding
facts are incompatible and close through the sealed executor. [Node
176](reports/node-176.md) applies this continuation to each surviving [175]
part on its literal monotone ledger.

### 5. Barrier compression subtracts an uncharged entropy baseline — [171]

[Node 171](reports/node-171.md) has conditional bounds \(F_c\) on surviving barrier-state values out of nominal sets of size \(W_c\). Coding a graph by its outside record and surviving states proves at most
\[
|\mathcal B|\le D\prod_c F_c.
\]
The manuscript then subtracts the savings \(\sum_c\log(W_c/F_c)\) as if it had also proved
\[
D\prod_c W_c\le |\mathcal G_{n,m}|.
\]
That baseline is absent. Bounding \(D\) alone by \(|\mathcal G_{n,m}|\) does not license subtracting the unused \(W_c\)-capacity, because conditional state cardinality does not control how many graphs lie over each state.

Correction: construct either the missing fibrewise baseline or a direct switching injection
\[
\mathcal B\times\prod_c A_c
\hookrightarrow
\mathcal G_{n,m}\times\prod_c F_c
\]
with all reconstruction overhead counted. If such a switching map fails, retain its first minimal support-dependence witness and prove that it satisfies the connected overlap contract before sending it to [172].

This is one of the main unresolved mathematical steps. The report does not prove that no such injection exists; it proves that the current argument does not supply one.

### 6. Odd-part orbit hits do not automatically lift to realized powers — [172], [180]

[Nodes 172](reports/node-172.md) and [180](reports/node-180.md) infer a power-of-two length from an orbit hit modulo the odd part of an increment gcd. Write
\[
g=2^a u,\qquad u\text{ odd}.
\]
A valid hit requires all of the following for one retained residue \(r\):
\[
2^a\mid L+r,
\qquad
2^{k-a}\equiv \frac{L+r}{2^a}\pmod u,
\qquad
t=\frac{2^k-L-r}{g}\in[C_{\rm sys},T_r-C_{\rm sys}].
\]
An orbit hit modulo \(u\) alone does not establish the first condition, and scale-spanning does not establish the residue-specific central range.

Correction: replace each terminal shortcut by an exact full-modulus-and-range decision. Route exact hits to the target-cycle closure, bounded exponent or end-range cases to the finite table, and exact no-hit states according to their retained full phase: context distinction, proper-support replacement, support dependence, route 8, or a typed Type B continuation. A raw no-hit state is not itself a contradiction.

### 7. Collision failure does not imply a nonempty cold family — [173]–[174]

[Node 173](reports/node-173.md) correctly rearranges failure of the strict collision inequality to
\[
73C\ge n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R).
\]
The right-hand side can be zero. Hence the no-arm may have \(C=0\); it need not contain one cold window, an eligible selected half-edge, or linearly many cold corridors. [Node 174](reports/node-174.md) consumes precisely such a corridor without first establishing its existence.

Correction: split the no-arm exactly on nonemptiness. Send only \(C>0\), together with an actual eligible selected half-edge, corridor, and first-failure support, to [175]. Send \(C=0\), or a nonempty cold family with no eligible incidence, to a separately proved all-hot or finite budget-edge residual. The current named budget-edge frontier is a useful destination shape, not yet a proof of this closure.

### 8. A high cold-corridor centre is not yet a Type B envelope — [175], [177]

[Node 175](reports/node-175.md) obtains a high-degree vertex, cubic neighbours, and two corridor tails. [Node 177](reports/node-177.md) routes these data directly to the decorated Type B entry [65]. That destination additionally requires a counted connected \(P_{13}\)-free core, declared response coordinates through a common completion port, a surviving first separator, boundary-profile compatibility, fan-safe alternatives, and the exact charge-transfer identity. None of these follows merely from one high centre and two tails.

Correction: insert a conversion decision. Route to [65] only when an actual decorated envelope and assigned ledger have been constructed. Route a bounded graph-realized germ without that envelope to [176] when its contract fits; otherwise retain a distinct cold-handoff localization residual. A Lean-only disjunct for a weaker cold-corridor witness is not a proof that the manuscript's existing Type B contract is met.

### 9. The pair-overlap obstruction is defined in the wrong direction and is not exhaustive — [178]–[179]

[Node 178](reports/node-178.md) starts from failure to realize one binary bit per pair. Such a failure means some conditional coordinate has at most one extension. Its stated obstruction uses the opposite condition: no ordering makes every coordinate have at most one extension. Consequently a constant coordinate can be a genuine code failure with no stated obstruction, while the full binary product satisfies the displayed obstruction predicate.

[Node 179](reports/node-179.md) then defines minimal obstruction so that it is necessarily a singleton, yet begins its proof by choosing two intersecting supports. Even with two supports, connected minimum-vertex supports need not be paths, a high-degree intersection need not be a same-token bottleneck, and no uniform port-return bound supplies the claimed finite constant.

Correction:

- define a minimal binary code defect using the conditional inequality in the failure direction;
- prove fixed-\((n,m)\), boundary-profile-preserving factorization before concluding that a minimal defect has connected overlap support;
- separate baseline-realization failure, disconnected compatibility failure, singleton/nonserial geometry, and a verified serial uncrossing certificate;
- send only the last typed certificate to [180].

The singleton and nonserial complements currently need new mathematics or new residuals. They cannot be routed to [180] merely by naming them overlap obstructions.

## The six prose and contract corrections

These are important because later nodes consume the exact branch predicate, but they do not by themselves require a new proof strategy.

| Node | Present ambiguity | Required wording |
|---|---|---|
| [159](reports/node-159.md) | “Canonical realization” can mean a prescribed semantic response map, whose failure does not imply cardinal overflow. | Define [158]–[159] as the exact budget decision \(Q\le|\mathcal G_{n,m}|\) and its negation. If semantic realization is intended, add the third residual \(\neg\mathrm{Real}_{\rm can}\land Q\le B\). |
| [162](reports/node-162.md) | The box says [157] closes, while its outgoing edge retains a neutral [157] row. | State that only realizing, distinguishing, handoff, and explicitly represented compression rows close; retain the neutral equal-length no-representative row for [163]. |
| [163](reports/node-163.md) | Provenance, graph realization, and equality \(E=Q\) are conflated. | Decide literal internally-disjoint graph realization, then on the no-arm decide \(E\ne Q\) versus \(E=Q\), retaining the same selected germ. |
| [164](reports/node-164.md) | The remainder class used earlier is not explicitly fixed to one edge count, but the glue injection assumes it. | Define \(\mathcal G(R)\) as the exact inherited-edge slice \(e(H)=e(G[R])\) at its first use. |
| [167](reports/node-167.md) | The survivor shorthand says \(\ell\notin\mathrm{Pow}\), although the first closing length is \(2\ell\). | Use \(2\ell\notin\mathrm{Pow}\) and \(\ell+d\notin\mathrm{Pow}\). For example, \(\ell=2\) survives the old shorthand but creates a 4-cycle. |
| [170](reports/node-170.md) | “Condition on the other windows” can mean all-other-coordinate conditioning, which does not imply a product bound. | State the canonical prefix-exposure predicate used by the proof; its no-arm must retain a minimal nonempty no-order obstruction and its fixed fibre. |

## Node-by-node status

| Node | Reviewed verdict | Short disposition |
|---:|---|---|
| [157](reports/node-157.md) | Missing representative | Neutral finite-table data do not construct a smaller graph. |
| [158](reports/node-158.md) | No issue found | Exact package-budget decision is exhaustive. |
| [159](reports/node-159.md) | Prose ambiguity | Call the predicate a cardinal budget test, not semantic realization. |
| [160](reports/node-160.md) | Wrong routing destination | The \(1/4\) arm does not satisfy the later \(3/13\) route-8 threshold. |
| [161](reports/node-161.md) | Missing range check | The delicate interval must be sent to the hot/cold pass. |
| [162](reports/node-162.md) | Prose ambiguity | Carve out and retain the neutral no-representative row. |
| [163](reports/node-163.md) | Prose ambiguity | Split graph realization, provenance, and \(E=Q\) explicitly. |
| [164](reports/node-164.md) | Prose ambiguity | The entropy class must be the fixed-edge slice used by the glue map. |
| [165](reports/node-165.md) | Missing representative | Equal-size exchange has no declared third-coordinate decrease. |
| [166](reports/node-166.md) | Missing representative | \(Q=E\) does not follow without the global order and swap-locality lemma. |
| [167](reports/node-167.md) | Prose ambiguity | Replace \(\ell\notin\mathrm{Pow}\) by \(2\ell\notin\mathrm{Pow}\). |
| [168](reports/node-168.md) | Wrong routing destination | The selected stub is not known to be interior. |
| [169](reports/node-169.md) | No issue found | Blocked-class membership follows from accumulated facts. |
| [170](reports/node-170.md) | Prose ambiguity | Use prefix-exposure conditional fibres; Lean's bundled predicate is a separate fidelity issue. |
| [171](reports/node-171.md) | Wrong routing destination | Conditional state counts lack the baseline needed for relative entropy savings. |
| [172](reports/node-172.md) | Missing divisibility/range check | Odd-part hits need full 2-adic compatibility and an exact central coefficient. |
| [173](reports/node-173.md) | Missing range check | Failure permits \(C=0\). |
| [174](reports/node-174.md) | Missing range check | No actual eligible cold corridor has been produced. |
| [175](reports/node-175.md) | Wrong routing destination | High centre and two tails do not satisfy the decorated Type B contract. |
| [176](reports/node-176.md) | Wrong routing destination | The terminal endpoint contradiction inherits [168]'s selection mismatch. |
| [177](reports/node-177.md) | Wrong routing destination | No conversion theorem constructs the full Type B envelope. |
| [178](reports/node-178.md) | Nonexhaustive branch | The obstruction inequality is reversed and disconnected failure is unassigned. |
| [179](reports/node-179.md) | Nonexhaustive branch | Minimal obstruction is forced singleton; nonserial geometry remains live. |
| [180](reports/node-180.md) | Missing divisibility/range check | Odd-part orbit contact is not an exact realized central power. |

## Recommended repair order

The following order minimizes rework because later repairs depend on the exact objects produced upstream.

1. **Freeze the branch semantics.** Correct [159], [162]–[164], [167], [170], and the binary defect predicate at [178]. These edits determine what each later theorem is allowed to consume.
2. **Repair the early quantitative gates.** Add the \(3/13\) route-8 decision at [160]–[161] and the cold-family/eligible-incidence split at [173]–[174].
3. **Construct the missing structural witnesses.** Resolve the neutral representative at [157], define and prove the global same-size decrease at [165]–[166], rebuild the corridor extraction from the interior selected set for [168]/[176], and prove or replace the Type B conversion at [175]/[177].
4. **Repair the entropy handoff.** Supply the fibrewise baseline or switching injection at [171]. Only a typed minimal failure witness may enter [172].
5. **Rebuild the sparse pair obstruction.** Prove conditional factorization and connectedness at [178], then state a genuine serial uncrossing certificate at [179]. Retain singleton, disconnected, and nonserial complements until separately closed.
6. **Apply the exact modular decision twice.** Use full 2-adic compatibility and residue-specific central ranges at [172] and [180], with explicit routes for every no-hit and bounded case.
7. **Recompute constants and synchronize artifacts.** Recheck all thresholds affected by replacing 13 selected stubs with at least nine interior selected stubs. Then update the manuscript, proof-flow graph, table/ledger rows, Lean propositions and producers, and regression analogues together.

## What would count as a repaired proof segment

This part of the proof can be called closed only after all of the following are present in the mathematical source, not merely represented by Lean fact names:

- every decision has literal complementary arms and retains its witness or negation;
- every routing edge lists and proves the destination's full entry contract;
- every compression uses an actual graph representative that strictly decreases the declared global minimality order;
- every entropy saving is backed by an injective map or a charged baseline;
- every selected corridor has a retained originating incidence compatible with the later degree argument;
- every cold continuation first proves nonemptiness and eligibility;
- every Type B handoff constructs the full decorated envelope and transfer identity;
- every pair failure is either closed or retained in an explicitly typed residual;
- every modular hit satisfies divisibility, normalized congruence, integrality, and its exact finite coefficient range;
- all affected constants, finite tables, downstream analogues, graph edges, and Lean contracts are updated consistently.

## Residual uncertainty and limits of this summary

The audit covered only nodes [157]–[180]. Nodes [1]–[156] have not been certified by this campaign, even when their facts were used as accumulated hypotheses for a later node. The reports test whether each audited node follows from its incoming contract; they do not independently reprove every ancestor.

No complete minimum-degree-three, power-of-two-cycle-free graph realizing every accumulated fact was found. The strongest candidates generally expose an invalid implication, missing witness, or unassigned abstract residual and then fail some earlier graph invariant. Accordingly, the correct conclusion is not that the theorem is false. It is that the present manuscript has local obligations that must be filled before the proof is complete.

The main unresolved construction questions are:

1. whether every neutral finite-table row has an actual smaller representative;
2. whether a global swap-local graph order can validate the same-size replacement;
3. whether a barrier switching injection supplies the missing entropy baseline;
4. whether the cold-corridor data can always be promoted to a full decorated Type B envelope;
5. whether the sparse pair defect admits the asserted connected serial geometry;
6. whether the interior-stub repair preserves all global numerical thresholds.

Lean evidence helps locate these obligations and occasionally already contains the shape of a needed decision split. It does not repair a missing manuscript lemma, and a stronger kernel-checked arithmetic helper does not show that the graph branch produces its stronger hypotheses. The paper statement, routing graph, and formal contracts should therefore be repaired in that order and then checked together.
