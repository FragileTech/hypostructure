"""The Navier–Stokes regularity proof: three manuscripts, one argument.

Each paper numbers its own diagram from [1], so the chapters carry prefixes and
the reader sees `S12`, `I12`, `II12`. All three share a layout: a diagram map, a
node-by-node audit table, a monotone ledger of retained facts, and a
branch-closure audit.
"""

from __future__ import annotations

from proof_graph import ChapterSpec, ProofSpec, TableSpec


MAP_START = "\\subsection{Diagram map}"
MAP_STOP = "\\subsection{Proof-dependency diagram}"


def _map_table() -> TableSpec:
    """Part | Nodes | Branch resolved | Principal sources.

    The paper's own account of what each panel of its diagram resolves.
    """
    return TableSpec(
        start=MAP_START,
        stop=MAP_STOP,
        columns=4,
        name=0,
        nodes=1,
        detail=2,
        sources=3,
    )


# What each panel is called. The paper numbers its parts but does not name them,
# and `Part VII` alone tells a reader nothing.
SETUP_TITLES = {
    "fig:local-typeI-proof-flow-entry": "Part I - From a singular point to a profile",
    "fig:local-typeI-proof-flow-exhaustion": "Part II - Exhausting the Type I classes",
}

TYPE_I_TITLES = {
    "fig:typeI-proof-flow-entry": "Part I - The residual class, stated exactly",
    "fig:typeI-proof-flow-refined": "Part II - Ten refined states, taken in order",
    "fig:typeI-proof-flow-tail-geometry": "Part III - Tail geometry and the pressure atlas",
    "fig:typeI-proof-flow-terminal": "Part IV - The eight terminal alternatives",
    "fig:typeI-proof-flow-diffuse": "Part V - When the defect spreads out",
    "fig:typeI-proof-flow-critical-tail": "Part VI - When the mass sits in the tail",
    "fig:typeI-proof-flow-hidden-scale": "Part VII - Failure hidden at an intermediate scale",
    "fig:typeI-proof-flow-coherent": "Part VIII - Tails that stay coherent",
    "fig:typeI-proof-flow-recurrence": "Part IX - The single atom, and the contradiction",
}

TYPE_II_TITLES = {
    "fig:typeII-proof-flow-part-i": "Part I - Entry, repaired gauge and one core",
    "fig:typeII-proof-flow-part-ii": "Part II - Where compactness fails",
    "fig:typeII-proof-flow-part-iii": "Part III - The terminal limit, classified",
    "fig:typeII-proof-flow-part-iv": "Part IV - Naming the first failure",
    "fig:typeII-proof-flow-part-v": "Part V - Bounded windows",
    "fig:typeII-proof-flow-part-vi": "Part VI - Runaway modulation",
    "fig:typeII-proof-flow-part-vii": "Part VII - Bounded modulation, with a defect",
    "fig:typeII-proof-flow-part-viii": "Part VIII - Whether the cost stays canonical",
    "fig:typeII-proof-flow-part-ix": "Part IX - Cores that stay active",
    "fig:typeII-proof-flow-part-x": "Part X - Rebuilding the pressure",
    "fig:typeII-proof-flow-part-xi": "Part XI - Data carried by pressure alone",
    "fig:typeII-proof-flow-part-xii": "Part XII - Critical tightness and diffuse tails",
}


def _node_table(start: str, stop: str) -> TableSpec:
    """Node | State or test | Exact proof source | Successor or closure."""
    return TableSpec(
        start=start,
        stop=stop,
        columns=4,
        first_cell=r"\[\d+\]",
        outcome_is_successor=True,
        nodes=0,
        # The state column *is* the description here, so it is not also shown as
        # a separate name.
        detail=1,
        sources=2,
        outcome=3,
    )


def _ledger_table(start: str, stop: str) -> TableSpec:
    """Fact | Established by | Retained through | Terminal use."""
    return TableSpec(
        start=start,
        stop=stop,
        columns=4,
        name=0,
        sources=1,
        nodes=2,
        detail=3,
    )


def _closure_table(start: str, stop: str) -> TableSpec:
    """State or exit | Diagram route | Closure source | Terminal output.

    The dossier belongs to the terminal the row closes at, which is the last
    column; the route column records the path that reaches it.
    """
    return TableSpec(
        start=start,
        stop=stop,
        columns=4,
        name=0,
        number=1,
        sources=2,
        nodes=3,
    )


SETUP = ChapterSpec(
    id="setup",
    prefix="S",
    source="to_formalize/proof_setup.tex",
    title="Local concentration and the Type I / Type II dichotomy",
    short_title="Setup",
    description=(
        "Takes a suspected singular point, extracts a nonzero ancient profile "
        "from it, and closes every Type I class except one residual family."
    ),
    diagrams=("\\subsection{Proof-dependency diagram}", "\\subsection{Node-by-node audit table}"),
    part_titles=SETUP_TITLES,
    map_tables=(_map_table(),),
    node_tables=(
        _node_table("\\subsection{Node-by-node audit table}", "\\subsection{Monotone proof ledger}"),
    ),
    ledger_tables=(
        _ledger_table("\\subsection{Monotone proof ledger}", "\\subsection{Branch-closure audit ledger}"),
    ),
    closure_tables=(
        _closure_table("\\subsection{Branch-closure audit ledger}", "\\section*{Part I."),
    ),
)

TYPE_I = ChapterSpec(
    id="type-i",
    prefix="I",
    source="to_formalize/type_I_residual_closure.tex",
    title="Closing the Type I residual class",
    short_title="Type I residual",
    description=(
        "Decomposes the one family the setup paper leaves open — axisymmetric, "
        "rotational, stationary-hull, affine, critical-tail and generic strata — "
        "and shows each is empty."
    ),
    diagrams=("\\subsection{Proof-dependency diagram}", "\\subsection{Node-by-node audit table}"),
    part_titles=TYPE_I_TITLES,
    map_tables=(_map_table(),),
    node_tables=(
        _node_table("\\subsection{Node-by-node audit table}", "\\subsection{Monotone retained-fact ledger}"),
    ),
    ledger_tables=(
        _ledger_table("\\subsection{Monotone retained-fact ledger}", "\\subsection{Branch-closure audit table}"),
    ),
    closure_tables=(
        _closure_table(
            "\\subsection{Branch-closure audit table}",
            "\\subsection{Local Type I singularities enter",
        ),
    ),
    # Symbol | Meaning
    glossary_tables=(
        TableSpec(
            start="\\subsection{Notation, threshold, and gauge directories}",
            stop="\\section{Exclusion of the axisymmetric",
            columns=2,
            first_cell=r"[\\$]",
            name=0,
            outcome=1,
        ),
    ),
)

TYPE_II = ChapterSpec(
    id="type-ii",
    prefix="II",
    source="to_formalize/type_II_regularity.tex",
    title="Excluding the Type II branch",
    short_title="Type II regularity",
    description=(
        "Partitions the Type II alternative into repaired-gauge, multibubble, "
        "rough-core, scale-collapse, carrier-routing and terminal-profile exits, "
        "and closes every one."
    ),
    diagrams=("\\subsection{Proof-dependency diagram}", "\\subsection{Node-by-node audit table}"),
    part_titles=TYPE_II_TITLES,
    map_tables=(_map_table(),),
    node_tables=(
        _node_table(
            "\\subsection{Node-by-node audit table}",
            "\\subsection{Monotone retained-obstruction ledger}",
        ),
    ),
    ledger_tables=(
        _ledger_table(
            "\\subsection{Monotone retained-obstruction ledger}",
            "\\subsection{Branch-closure audit ledger}",
        ),
    ),
    closure_tables=(
        _closure_table("\\subsection{Branch-closure audit ledger}", "\\section{Local Single-Core Criterion}"),
    ),
)

# The papers hand off to one another in prose rather than in a diagram. These
# joins are stated in to_formalize/overall_proof_architecture.tex: its
# architecture tree (the Type I and Type II branches of a local CKN
# concentration) and its per-file summary of what each manuscript closes.
CROSSINGS = (
    (
        "S4",
        "II1",
        "the Type II branch of the same local concentration, excluded in the Type II paper",
    ),
    (
        "S38",
        "I1",
        "the retained residual row, closed in the Type I residual paper",
    ),
    (
        "I159",
        "S39",
        "the residual class is empty; the setup paper's final assembly resumes",
    ),
)

SPEC = ProofSpec(
    id="navier-stokes-regularity",
    slug="navier-stokes",
    title="No finite-energy Navier–Stokes solution develops a local singularity",
    subtitle="One argument across three manuscripts, drawn as a single dependency graph",
    chapters=(SETUP, TYPE_I, TYPE_II),
    crossings=CROSSINGS,
)
