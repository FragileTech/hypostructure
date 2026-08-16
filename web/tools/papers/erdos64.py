"""The Erdős–Gyárfás paper: one manuscript, eleven diagram panels."""

from __future__ import annotations

from proof_graph import ChapterSpec, ProofSpec, TableSpec

PART_TITLES = {
    "fig:proof-diagram-part-i": "Part I - Counterexample selection to the P13 packing",
    "fig:proof-diagram-part-ii": "Part II - The remainder and its curvature rank",
    "fig:proof-diagram-part-iii": "Part III - Branch D: rank-reducing dependence",
    "fig:proof-diagram-part-iv": "Part IV - Full rank and the two-budget split",
    "fig:proof-diagram-part-v": "Part V - Net charge and the Type A / Type B split",
    "fig:proof-diagram-part-vi": "Part VI - Type B fan analysis",
    "fig:proof-diagram-part-vii": "Part VII - Type B, degree-four centers",
    "fig:proof-diagram-part-viii": "Part VIII - Type A receiver ladder and exits 1-7",
    "fig:proof-diagram-part-ix": "Part IX - Route-8 pressure descent",
    "fig:proof-diagram-part-x": "Part X - Sparse surplus accounting",
    "fig:proof-diagram-part-xi": "Part XI - The hot/cold window interface",
}

# Continuation arrows in this manuscript name a later node rather than repeating
# it, and the joins are stated in the figure captions rather than drawn.
# Source: the captions of Parts I-XI.
CONTINUATIONS = (
    ("20", "125", "surplus-pair accounting branch, expanded in Part X"),
    ("24", "145", "cold branch, expanded in Part XI"),
    ("25", "26", "Residual A continues in Part II"),
    ("33", "35", "Branch D continues in Part III"),
    ("34", "47", "Residual B continues in Part IV"),
    ("56", "57", "the large-budget net cap continues in Part V"),
    ("63", "86", "Type A, expanded in Part VIII"),
    ("64", "65", "Type B, expanded in Part VI"),
    ("68", "78", "no: the degree-four branch, expanded in Part VII"),
    ("77", "110", "route-8 cores continue in Part IX"),
    ("108", "66", "exit 7 hands off to Type B"),
    ("109", "110", "route-8 residual, expanded in Part IX"),
)

# This paper numbers its panels but does not tabulate what each one does, the way
# the Navier-Stokes manuscripts do in their diagram map. These summaries are
# written from the paper's own overview: its numbered account of the argument,
# the node labels, and the figure captions.
PART_SUMMARIES = {
    "fig:proof-diagram-part-i": (
        "Sets the argument up and narrows it down. A counterexample is assumed and the "
        "smallest one chosen, which turns the question into arithmetic: no edge may have "
        "a Mersenne return. Minimality then forces the graph to be edge-critical with its "
        "high-degree vertices independent, and an external theorem forces it to contain "
        "induced thirteen-vertex paths. Packing those paths splits the graph into windows "
        "and a remainder, and everything after this is an accounting contest between the two."
    ),
    "fig:proof-diagram-part-ii": (
        "Measures the remainder. It is large, contains no cubic core of its own, and its "
        "deficiency is bounded by what the windows can supply. Counting the wedges it must "
        "contain gives a lower bound on curvature, and the panel ends on the question the "
        "next two turn on: whether that curvature has full rank."
    ),
    "fig:proof-diagram-part-iii": (
        "Takes the branch where curvature rank drops. A drop means some curvature test is "
        "redundant, and the redundancy has to be visible somewhere: in a quotient that is "
        "defective, in an atom that compresses, or spread across a support. Each case "
        "contradicts minimality or the replacement lemma, so the whole branch closes here."
    ),
    "fig:proof-diagram-part-iv": (
        "Takes the complementary branch, where curvature has full rank and so costs the "
        "remainder a definite amount. The argument then splits on how much entropy the "
        "remainder has: a low-entropy remainder is repetitive enough that the cost closes "
        "it under the entropy cap, while a high-entropy one survives into the large-budget "
        "residual."
    ),
    "fig:proof-diagram-part-v": (
        "Localizes the surviving residual. Its net charge is non-negative globally, so if "
        "the books are to fail they must fail somewhere in particular: a connected support "
        "of negative net charge. Whether that support carries high-degree surplus decides "
        "which of the two local analyses claims it."
    ),
    "fig:proof-diagram-part-vi": (
        "Analyses a support with high-degree centres. The centres are independent and their "
        "fan neighbours cubic, which bounds the fans and lets each be certified. Fans that "
        "fail certification, or whose ledgers overlap, are charged against the global "
        "surplus budget, and the panel shows the deficit cannot be carried outside route 8."
    ),
    "fig:proof-diagram-part-vii": (
        "The same analysis for centres of degree exactly four, where the fan profile is "
        "rigid enough to compute. The cheap cases close on the spot; the difficult ones "
        "turn on whether the incidence payment and the disjointness ledger can both be met."
    ),
    "fig:proof-diagram-part-viii": (
        "Analyses a support with no surplus, where deficiency alone must account for the "
        "charge. Receivers are either unsaturated, in which case a discharging argument "
        "closes them, or saturated, in which case seven explicit exits are tested in turn. "
        "Five close outright, one peels a load and returns, one hands off; what is left "
        "over is route 8."
    ),
    "fig:proof-diagram-part-ix": (
        "Closes route 8, the last way out. The burden it carries forces many basins, while "
        "the private carriers each entry needs force few; the two bounds are incompatible "
        "unless some entry has only two carriers. That case is exactly the one already "
        "peeled away earlier, so it cannot occur here either."
    ),
    "fig:proof-diagram-part-x": (
        "Handles the graphs that are not near-cubic, before the entropy budget is spent. "
        "The excess surplus is extracted as ports and charged through a ledger of blockers "
        "and capacity tokens that counts each blocked pair exactly once. Overloading any "
        "token class forces a geometric structure that either exits or caps the surplus, "
        "which is what puts the graph on the near-cubic spine."
    ),
    "fig:proof-diagram-part-xi": (
        "Handles the cold windows set aside at the hot/cold split. If the packing is sparse "
        "enough the carrier inequality closes it; otherwise the hot failure forces a linear "
        "family of cold windows, each contributing stub excess. Extracting bounded germs "
        "from that excess leaves three shapes, and all three either produce the target cycle "
        "or compress."
    ),
}

ALIASES = (
    ("25", "26"),
    ("33", "35"),
    ("34", "47"),
    ("56", "57"),
    ("64", "65"),
    ("77", "109", "110"),
    ("66", "108"),
)

LEDGER_START = "\\subsection*{The constraint ledger}"
LEDGER_STOP = "\\subsection*{Per-lemma invariant requirements}"

CHAPTER = ChapterSpec(
    id="erdos-gyarfas",
    prefix="",
    source="to_formalize/original_erdos_64_proof.tex",
    title="Powers of two in graphs of minimum degree three",
    short_title="The proof",
    description="A single manuscript, drawn as eleven dependency panels.",
    diagrams=(
        "\\subsection*{Proof-dependency diagram}",
        "\\subsection*{Detailed dependency table}",
    ),
    part_titles=PART_TITLES,
    part_summaries=PART_SUMMARIES,
    # Item | Diagram node(s) | Node / theorem | Formal content | Failure route | Label
    node_tables=(TableSpec(
        start="\\subsection*{Detailed dependency table}",
        stop="\\subsection*{The constraint ledger}",
        columns=6,
        first_cell=r"\d+$",
        nodes=1,
        name=2,
        detail=3,
        outcome=4,
        sources=5,
    ),),
    # Result | Stage | Diagram node(s) | Requires | What it does | Role
    result_tables=(TableSpec(
        start="\\subsection*{Per-lemma invariant requirements}",
        stop="\\section{Target cycles as Mersenne returns}",
        columns=6,
        sources=0,
        name=1,
        nodes=2,
        extra=3,
        detail=4,
        outcome=5,
    ),),
    # # | Invariant | Node (first tracked) | Constraint on G | Budget | Used by
    ledger_tables=(
        TableSpec(
            start=LEDGER_START,
            stop=LEDGER_STOP,
            columns=6,
            first_cell=r"\d+$",
            number=0,
            name=1,
            nodes=2,
            detail=3,
            outcome=4,
            sources=5,
        ),
        # The carrier block (constraints 30-38) omits the Budget column.
        TableSpec(
            start=LEDGER_START,
            stop=LEDGER_STOP,
            columns=5,
            first_cell=r"\d+$",
            number=0,
            name=1,
            nodes=2,
            detail=3,
            sources=4,
        ),
    ),
    # Node | Closing lemma | Closing condition | Slack | Redundant cover | Residual
    closure_tables=(TableSpec(
        start="\\section{Proof resilience",
        stop="\\end{document}",
        columns=6,
        nodes=0,
        sources=1,
        name=2,
        detail=3,
        extra=4,
        outcome=5,
    ),),
    # Constant | Value | Meaning | Established in
    glossary_tables=(TableSpec(
        start="\\subsection*{Standing notation and constants}",
        stop="\\subsection*{Proof-dependency diagram}",
        columns=4,
        first_cell=r"\$",
        name=0,
        detail=1,
        outcome=2,
        sources=3,
    ),),
    continuations=CONTINUATIONS,
    aliases=ALIASES,
)

SPEC = ProofSpec(
    id="erdos-gyarfas-64",
    slug="erdos-gyarfas",
    title="Every graph with minimum degree three has a cycle of length a power of two",
    subtitle="An interactive walk through the proof-dependency diagram of the original paper",
    chapters=(CHAPTER,),
)
