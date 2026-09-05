// Adapted from repair_and_closure.md §§5.3–5.4, 10, 12. See web/README.md for the coverage map.
export const SELECTION_ROWS = [
  [
    "A **bounded / finite** object (bounded support, bounded length, bounded configuration)",
    "(1) Direct hit; (2) contextual distinction → target-defective quotient; (3) silent compression; (4) finite enumeration of what remains, then structural exclusion of the survivors",
    "Exhaustiveness of hit/defect/compression; the enumeration is at the right parameters (window order 13, $\\ell\\le 40$); survivors are excluded by a *structural* fact, not by re-enumeration ([167]→[168])"
  ],
  [
    "A **long chain** or corridor of finitely typed states",
    "Finite-state pumping: read $Q+1$ states, two coincide; extract the exchange; route by hit / defect / compression",
    "Existence of a first failure is *proved*, not assumed (the corridor either terminates within $M_{\\rm cold}=Q_{\\rm cold}+30$ vertices or repeats); equal-length ($\\delta=0$) exchanges that escape the trichotomy are covered by a finite table"
  ],
  [
    "**Overlapping / nonadditive** supports (a product or independence sentence failed)",
    "(1) Retain the first failing fibre with its full state; (2) minimal *connected* overlap obstruction; (3) uncross into a serial system; (4) sumset → arithmetic progression → full-modulus hit; (5) or periodic response class with a concrete exit",
    "Connectivity of the minimal obstruction; each saving charged *once* to its minimal connected support (`rem:entropy-lives-here`); the arithmetic is at full modulus, not just the odd part"
  ],
  [
    "A **same-size competitor** the well-order cannot see",
    "Refine the order lexicographically by a canonical invariant $\\Phi$; exchange; show $\\Phi$ strictly decreases",
    "Every earlier use of minimality compares strictly smaller $(\\lvert V\\rvert,\\lvert E\\rvert)$ and so remains valid in the refined order (`lem:refined-minimality-swap`)"
  ],
  [
    "An **asymptotic side condition** ($n\\ge N_0$, $\\sigma\\le C\\sqrt n$)",
    "Exactify: restate the collision as an integer inequality on the object; its failure is a structural residual, not a size condition",
    "Each allowance is a bound on a quantity the residual carries exactly; the failure rearranges to something the next move consumes (linearly many cold windows)"
  ],
  [
    "A **discarded remainder** (an \"extraction loss,\" an $o(n)$ that was dropped)",
    "Charge it into an existing ledger with a no-overcount lemma; the loss becomes fan data / Type B charge / a peel",
    "The receiving ledger's admission conditions hold (the two corridor incidences at $z$ are distinct connector tails); the charge is not also counted where it was discarded"
  ],
  [
    "Downstream **reads a cap only through one inequality**",
    "Cap substitution: supply that one inequality from a different producer on the new branch; the continuation applies verbatim",
    "\"Nothing else in [25]–[64] reads the density cap\" is verified by reading every consumer; any additional consumption (the private-carrier rate at [120]–[122]) gets its own diamond"
  ],
  [
    "A residual class that **survives but is small**",
    "Aggregate closure: total capacity (member count × per-member capacity × multiplicity) is sublinear against a linear deficit",
    "Currencies are not mixed; the linear deficit and the sublinear capacity are measured against the same $\\lvert R\\rvert$"
  ],
  [
    "A **loop** with no obvious end (peel, reselect, re-run)",
    "Define a nonnegative integer measure; prove each pass decreases it by one *and* restores every standing invariant",
    "The measure is on the bookkeeping only (\"the graph, the packed windows, the boundary profiles, the target-safety constraints, and all target-response quotients remain the same\"); the charge update is exact ($1/4$-unit)"
  ],
  [
    "The residual **coincides with an excluded exit**",
    "Identification: show the residual's data satisfy the defining conditions of an exit the branch says is absent",
    "Every witness the exit requires is *declared* on the branch (`lem:typeA-deletion-witness-declared`), not reconstructed"
  ],
  [
    "**Linearly many bounded components** of a labelled class closed under relabeling",
    "Orbit count: $\\lvert\\text{class}\\rvert\\ge\\lvert R\\rvert!/\\lvert\\mathrm{Aut}\\rvert$; components give $\\log\\lvert\\mathrm{Aut}\\rvert\\le K\\log K+O(\\lvert R\\rvert)$; compare with the budget",
    "$K$ is bounded (every component has a deficient vertex, or a $W$-edge, or $\\ge4$ vertices); the state map being compared is invariant under the relabelings; the class is the one the budget counts (Part IV of `closure_proofs.md`)"
  ],
  [
    "**No bounded local test** sees anything wrong",
    "Entropy / compression squeeze in the correct class",
    "The class is the one the budget does not already charge (minimum degree $\\ge3$, `rem:blocked-class-checks`(a)); a sanity family shows the threshold is not below what the route can give (1/81)"
  ],
  [
    "A **minimal counterexample with a bounded-degree region** and no arithmetic hit",
    "Run *every* minimality move, not only the ones already on the branch: deletion (edge with both ends of degree $\\ge4$), **contraction** (an edge whose ends share no degree-3 neighbour: contracting it gives a smaller graph with $\\delta\\ge3$, so a $2^k$-cycle of the contraction lifts to a $(2^k+1)$-cycle through the edge), replacement (a piece with a smaller representative)",
    "The contracted graph must stay simple with $\\delta\\ge3$ (common neighbours of the edge must have degree $\\ge4$); the lifted cycle must not be a cycle of the original (`closure_proofs.md` Theorem 18)"
  ],
  [
    "A **high-degree vertex** appears in a subcubic argument",
    "Dichotomy on $J\\cap V_{\\ge4}=\\varnothing$; use independence of $V_{\\ge4}$ (node [10]) to force cubic neighbours; hand off as decorated fan data",
    "The handoff's termination: the $A\\to B\\to A$ alternation consumes a finite token set once (`rem:typeA-typeB-stratification`)"
  ],
  [
    "PDE: **loss of compactness**",
    "Concentration → retain core, normalize, consume critical mass; translation escape → recentre or prove local invisibility; scale escape → order scales, promote inner to a new core; profile splitting → mass decoupling; weak-to-strong failure → new charged defect; pressure/gauge defect → separate and close elliptically; terminal-time escape → endpoint estimate",
    "Each edge preserves the normalization and the topology, gauge and resource data its successor consumes; each new core consumes a fixed amount of bounded resource (Theorems 3.3–3.4)"
  ]
] as const;

export const MOVE_RULES = [
  "**Only branch-state facts, fixed inputs, and textbook material.** A move that needs a global result not among the inputs is not a closure; it is a defect. Refine the case structure instead.",
  "**Prefer moves that make progress in a well-founded sense.** Every step outputs a closed branch or a *strictly smaller named residual* — smaller in size, in live exits, or in an explicitly monitored parameter. A lemma whose residual is not smaller, finite, charged or routed relocates the difficulty and counts as no progress.",
  "**Prefer the cheapest currency first.** Direct hit and contextual distinction cost nothing; compression needs context-universality; charging needs a full scheme; entropy needs the right class. The manuscript's trichotomies are ordered this way (hit, defect, compression) for a reason.",
  "**Separate currencies.** Deficiency, surplus, entropy, rank, boundary mass and concentration are distinct unless a proved interface converts one into another; an obstruction is paid once. Check the moves × budgets monotonicity table after any deletion, replacement, peel, charge transfer or hand-off.",
  "**Keep both squeezes alive.** Outside the explicit residuals the contradiction is reached in two arithmetically independent forms: obstruction ($W_2\\ge2.543|R|$ against $\\le0.611|R|$, slack $4.1\\times$) and net charge ($0.25|R|$ against $\\tau_{\\rm win}=0.2282|R|$, slack $\\approx9.6\\%$). Any repair to an estimate must keep demand $>$ supply in the form it feeds.",
  "**Do not launder.** If a move's exhaustiveness is not proved on the retained fibre, the residual is retained under its exact negation, not renamed as a blocker, quotient, exit, or Type B witness. Node [182] is the model.",
  "**Check forward references.** A required invariant introduced at a strictly later node is a forward-reference gap. For any result that produces the contradiction, confirm the chain inv 8 ← `cor:uncompressible` ← `lem:replacement` is intact and not circular with the result invoking it.",
  "**Check the interface, not the prose.** The consumer of the closure must accept exactly the typed witness the move produces (a decorated handoff at [65] needs a heavy centre with separated connector tails; an exit-(4) peel needs a declared deletion witness).",
  "**Never split on whether a lemma holds; split on the first hypothesis its proof consumes.** A diamond whose no-arm is \"$\\neg$(conclusion)\" has no consumer. It is admissible only as a temporary honest endpoint — an open node — and Section 4.6 is the procedure for pushing it down to admissible diamonds.",
  "**Enumerate the minimality moves before enumerating tools.** A minimal counterexample supports deletion, contraction, and replacement; check which of them the branch has already consumed before looking for a new tool. No lemma is added to the record for a move unless it is executed on the incoming residual.",
  "**Inventory before moving.** No move is chosen for a residual until its structural inventory (§4.7) is written against the register. The move is the technique that evaluates the most unaccounted structure. Re-applying an upstream move to an accounted property, importing a closure theorem, or enumerating the whole residual are not moves.",
  "**Relocation is not progress.** A step that removes a unit from one ledger and records it in another ledger with no payer (a peel, a deferral, a \"routing record\") has not closed, charged, or shrunk anything. It is admissible only if the receiving ledger has a consumer with capacity; otherwise it is the re-encoding failure of Section 9, and the residual it produces will be tautologically linear (Section 8.2).",
  "**An unproved intermediate fact is a diamond, not a stop.** When the move you selected needs a fact $F$ about the residual that you cannot prove from the ledger (e.g. \"the terminal spectrum of the piece is doubling\"), $F$ becomes the hypothesis of the next split: the $F$ arm continues with the selected move, and the $\\neg F$ arm is a new typed residual whose data is $\\neg F$ itself — and $\\neg F$ is usually the more structured side (a non-doubling spectrum is periodic; an unbounded object has a repeat; a non-Menger vertex has a small cut). Run the inventory of §4.7 on the $\\neg F$ arm and select again — but only if the split passes the two admissibility tests of §4.8; if the $\\neg F$ arm's data is not a property of the residual's own object, the selected move was wrong and the split must not be made. Stopping at \"$F$ is needed\" or looking for $F$ as an external theorem is the extrapolation failure of Section 9; the residual is closed only when every leaf is `False`, and the branch record shows which $F$ were split on (the [181] record, since removed).",
  "**The recorded plan is binding.** When this guide (or the branch record) has fixed, for an open node, the typed object and the selected move with its step table (as §7 and §8 do), the work on that node is the execution of that plan. Any deviation — a different object, a different move, a reformulation \"equivalent to\" the node — is itself a repair of the plan and must be recorded as such, with the first failing step of the plan and the reason, *before* any work is done on the new object. Work that silently changes the object is off-protocol whatever it proves. (",
  "**A certificate of non-closure is not structure.** Typed residual data often includes records of what *failed*: an exit-(4) demand token $(q,S_0,S_1,Y,E)$ records that a quotient is target-defective by exhibiting an alternative realization $S_1$ and a hypothetical context $Y$; a routing record, a deferral, an \"open unit\" record the same kind of thing. Only the actual realization ($S_0$, the load $u$, its trace, its pocket) is a property of $G$. In the inventory, a certificate contributes *no* row of positive structure; it contributes only the fact that one method is closed off. Counting certificates (tokens per incidence) therefore counts nothing about $G$ beyond the count of the actual objects they are attached to.",
  "**Never re-prove the residual; never re-apply an upstream move.** Once a node's residual is typed, the facts on its ledger are settled: the extremal choices already made (the packing, the counterexample, the ledger orderings), the upstream diamonds already taken, and the reasons upstream consumers failed are *inputs*, not work. The following are forbidden at an open node, each because it spends effort on the parent instead of the residual:\n    - re-deriving, re-auditing or re-defining an upstream object (reading how the packing was chosen, re-checking a consumer's vacuity a second time, re-computing a rate) once its ledger fact is on the record;\n    - refining an upstream extremal choice as the move for a downstream node (a secondary criterion on the packing is a repair of the node where the packing was chosen, not a closing move here);\n    - re-applying an upstream move to an accounted row (Menger where the cut is already typed, contraction where I7 is already on the ledger, a count where the count is the residual);\n    - writing \"why this route cannot close\" records as work products — one sentence in the inventory's *accounted* column is the whole record, and a limit theorem is written only when it is the terminal certificate the node will carry.\n    The only admissible work at an open node is: inventory (§4.7), selection of a move that lands on a closed row or a smaller typed object (§4.8), and execution of that move.",
  "**Check the move's preconditions against the inventory before selecting it.** Every closing move has *target rows* (what it evaluates) and *precondition rows* (what must already be present for it to apply: internally disjoint returns for exit (2), a shared window for exit (3), a smaller representative with the same profile for exit (5), bounded size for a table). A move is admissible only if its precondition rows appear in the residual's inventory as *present*. Selecting a move by its target rows alone produces a diamond whose no-arm is \"the precondition fails\", which is typically an accounted row (a theta instead of two disjoint returns; a second window instead of a shared one) and therefore neither closes nor shrinks.",
  "**A move sold on a finite table must have its table computed before it is selected.** When the closing power of a move rests on \"a linear supply against a fixed finite table\" (overlap arithmetic, label relations, offset tables), the table is computed *at selection time*, and the move is admissible only if the table is restrictive enough to contradict the supply on the residual's actual parameters. Announcing the move first and computing the table afterwards is the F1 pattern in a new form."
] as const;

export const CLOSURE_CHECKLISTS = [
  {
    "title": "Before touching a branch",
    "source": "§12.1",
    "items": [
      "I have identified the *first* failing node, not a downstream symptom.",
      "I have written $\\llbracket B_{k-1}\\rrbracket$: every invariant at an earlier-or-equal node, every exclusion, the active case, the residual data.",
      "I have read the whole conjunction of facts, not one lemma in isolation.",
      "I have followed the directed graph and the Requires column, not prose citations.",
      "I have checked whether a routed residual already covers what I think is missing."
    ]
  },
  {
    "title": "Admitting a dichotomy",
    "source": "§12.2",
    "items": [
      "$H$ is written as an exact proposition about the object on this branch, quantifiers included.",
      "$H$ is not already on the record (else cite it; if it is a conjunction, use the ordered split).",
      "The yes-arm is the old continuation with $H$ stated; no interface theorem's statement changed.",
      "$\\neg H$ is typed: I can say what object, witness, fibre, count or bound it hands the next move.",
      "Both sides are productive (both-sides test).",
      "New nodes are appended after the last existing number."
    ]
  },
  {
    "title": "Closing a residual",
    "source": "§12.3",
    "items": [
      "The object being closed is the residual as typed by its producer, not a restatement (Rule 0, §4.8).",
      "Each split made on the way passes the locality and consumption tests of §4.8.",
      "I named the currency (compression / quantity / constraint) and the row of the selection table.",
      "The move uses only branch-state facts, fixed inputs, and textbook material.",
      "The move makes well-founded progress (strictly smaller named residual, or a certificate).",
      "Every witness the consumer requires is *declared* on the branch, not reconstructed.",
      "For charging: demands distinct, assignment total, tie-break explicit, capacities certified on this branch, multiplicity bounded, no currency mixed.",
      "For loops: integer measure, strict decrease, invariant preservation inside the peel lemma.",
      "For refined orders: every earlier use of minimality still compares smaller objects.",
      "For compression/entropy: the class is the one the budget does not already charge; each saving charged once.",
      "For exhaustive routings: exhaustiveness is *proved* on the retained fibre; otherwise the exact negation is retained as a named open node.",
      "Both independent squeezes still have positive slack."
    ]
  },
  {
    "title": "Declaring a node closed",
    "source": "§12.4",
    "items": [
      "Every reachable terminal has a proved closure certificate (hit, defect, compression, capacity, rigidity, identification with a closed row, or exhaustive terminal enumeration). An exact open residual records unfinished work; it is not a closure certificate.",
      "The execution checks of §4.10 pass: no repeated exhausted move, no object or fibre substitution, no unconsumed outcome, and no remaining child obligation.",
      "Diagram, dependency table (Failure route), constraint ledger, per-lemma requirements, resilience row, and audit table are updated and agree.",
      "No forward reference: every Requires entry is introduced at an earlier-or-equal node.",
      "(Lean) Gate A: elaborates with no tracer axiom. Gate B: the `Holds` proposition is the manuscript's statement. Gate C: canonical carrier only.",
      "The weaker theorem that holds until any remaining open node closes is stated."
    ]
  },
  {
    "title": "Reopening an open node",
    "source": "§12.5",
    "items": [
      "The residual is written as its producer typed it (Rule 0, §4.8), with every ledger fact attached; no \"equivalent\" reformulation is used as the object.",
      "The plan already recorded for the node (§7, §8) is the one being executed; any deviation is recorded as a repair of the plan with its first failing step (rule 14).",
      "The open node's residual is written as $\\neg C$ for a named lemma's conclusion $C$ on a named retained input.",
      "The intended proof of $C$ is expanded into steps $X_1\\wedge\\cdots\\wedge X_m$ (constructions, preservation claims, cited lemmas).",
      "For each step: ledger question (fact present on *this* branch?), object question (property of the transferred object?), fibre question (output stays in the class?).",
      "The first failing step is the new diamond; its negation is typed and has a consumer from the selection table.",
      "No upstream object was re-derived, no upstream extremal choice refined, no upstream move re-applied, no no-go record written (rule 16); all effort went to inventory, selection, execution.",
      "Every diamond passes the locality test and the consumption test of §4.8 and names the measure it decreases, the closed branch it routes to, or the finite table it leaves.",
      "The residual inventory (§4.7) is written: every present property, its upstream consumer or \"not accounted\", the technique it enables, the certificate.",
      "Shared obligations across constructors are identified and ordered (cross-branch audit first, shared local lemma second).",
      "The old node keeps its number and becomes the decision; new nodes are appended.",
      "Every remaining local lemma is on the execution queue with its exact inputs, closing move and failure route. For a full-closure request, these lemmas and all their children are proved before completion is reported."
    ]
  },
  {
    "title": "Auditing an offered consumer",
    "source": "§12.6",
    "items": [
      "The consumer's hypothesis is written as a bound on a named quantity $Z$.",
      "$Z$'s definition is traced back to the ledger (demand, paid, unpaid); the no-overcount identity is written out.",
      "The lower bound the ledger forces on $Z$ is computed from the burden and deficit lemmas already on the branch.",
      "Compare the forced lower bound with the consumer’s required upper bound, including strictness. If they are incompatible, that consumer is unavailable on this branch; return to the structural inventory. Equality alone is not a contradiction.",
      "Only after the inventory (§4.7): the currency table (Section 5.2) is filled in as a diagnostic; every exhausted currency is marked. The closing move is chosen from the inventory's selection, never from the currency table alone."
    ]
  }
] as const;

export const ARTIFACT_ROWS = [
  [
    "**Proof-dependency diagram**",
    "Replace the old step by a diamond; draw the yes-arm into the existing continuation; append the new nodes with fresh numbers; give every new terminal the right shape (solid = closed here; dashed = proxy for a closure drawn elsewhere); add \"continue at [n]\" arrows. Only the live state is drawn"
  ],
  [
    "**Diagram map and node-by-node audit table**",
    "One row per new node: input, output, mathematical source"
  ],
  [
    "**Detailed dependency table** (Item · Node(s) · Node/theorem · Formal content · **Failure route** · Label)",
    "A new item for the repair, whose *Failure route* cell names where each arm goes — this cell is what makes the leaf-totality check mechanical"
  ],
  [
    "**Constraint ledger** (invariants 1–44)",
    "If $\\neg H$ or a new closure becomes a reusable fact, give it an invariant number with \"where introduced / where consumed / role.\" Ledger-invariant numbers and node numbers are separate namespaces"
  ],
  [
    "**Per-lemma requirements table** (Result · Stage · Node(s) · Requires · What it does · Role)",
    "Every new lemma, with its Requires cell. Then run the check: every invariant in Requires is established at an earlier-or-equal node; a later one is a forward-reference gap"
  ],
  [
    "**Resilience appendix** (Node · Closing lemma · Closing condition · Slack · Redundant cover · Residual counterexample)",
    "For each new closing cell, what survives if its lemma is false: all standing invariants plus the negation of the conclusion. \"No leaf degrades to nothing\""
  ],
  [
    "**Monotone-hypothesis / moves × budgets table**",
    "Re-check that each new deletion, replacement, peel, transfer or handoff preserves every account it touches"
  ],
  [
    "**Node audit table** (Lean)",
    "Gate A/B/C verdicts for the row; the applicable CT(s); the manuscript label(s). Live status goes only in the two tables, never in prose"
  ]
] as const;

