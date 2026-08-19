"""Read a mathematics paper's proof-dependency diagram into a graph.

Papers in this repository draw their argument as numbered TikZ panels — nodes
carrying ``\\textbf{[n]}`` and arrows carrying branch conditions — alongside
tables that say which lemmas and definitions stand behind each node. This module
knows those conventions; it does not know any particular paper. Describe one with
the dataclasses below and :func:`build_document` reads it.
"""

from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from latex_source import (
    clean_table_body,
    head_end,
    crefs,
    iter_environments,
    iter_statements,
    line_of,
    node_ids,
    read_group,
    split_cells,
    split_rows,
    strip_comments,
    to_plain,
)

# ---------------------------------------------------------------------------
# Describing a paper
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TableSpec:
    """Where to find a cross-reference table, and what its columns mean.

    ``columns`` is the exact cell count of a data row. The remaining fields name
    the zero-based column carrying each piece of information; leave one as
    ``None`` when the table does not have it.
    """

    start: str
    stop: str
    columns: int
    nodes: int | None = None
    name: int | None = None
    detail: int | None = None
    outcome: int | None = None
    sources: int | None = None
    number: int | None = None
    extra: int | None = None
    #: Only keep rows whose first cell matches this, when given.
    first_cell: str | None = None
    #: True when ``outcome`` names the step that follows, rather than describing
    #: what happens if this one fails. Only then can arrows be read from it.
    outcome_is_successor: bool = False


@dataclass(frozen=True)
class ChapterSpec:
    """One manuscript. A proof may be written across several."""

    id: str
    #: Prefixes node numbers so ids stay unique across chapters, e.g. ``S`` → ``S12``.
    prefix: str
    source: str
    title: str
    short_title: str
    description: str
    #: Section headings bounding the region that holds the diagram panels.
    diagrams: tuple[str, str]
    #: Titles for the panels, keyed by their figure label.
    part_titles: dict[str, str] = field(default_factory=dict)
    #: What each panel of the argument does, for a paper that does not tabulate
    #: it. Keyed by figure label, like the titles.
    part_summaries: dict[str, str] = field(default_factory=dict)
    #: The paper's own map of its panels: Part | Nodes | Branch resolved | ...
    map_tables: tuple[TableSpec, ...] = ()
    #: Headings bounding the chapter whose tables index the argument. Every
    #: table in it is published as written, for readers who navigate by index.
    reference_region: tuple[str, str] | None = None
    node_tables: tuple[TableSpec, ...] = ()
    result_tables: tuple[TableSpec, ...] = ()
    ledger_tables: tuple[TableSpec, ...] = ()
    closure_tables: tuple[TableSpec, ...] = ()
    glossary_tables: tuple[TableSpec, ...] = ()
    #: Joins the source states in prose rather than drawing, as (from, to, note).
    continuations: tuple[tuple[str, str, str], ...] = ()
    #: Node numbers that restate the same assertion in a later panel.
    aliases: tuple[tuple[str, ...], ...] = ()


@dataclass(frozen=True)
class ProofSpec:
    """A whole proof: one or more chapters, plus how they join."""

    id: str
    slug: str
    title: str
    subtitle: str
    chapters: tuple[ChapterSpec, ...]
    #: Joins between chapters, as (from id, to id, note). Ids carry their prefix.
    crossings: tuple[tuple[str, str, str], ...] = ()


# ---------------------------------------------------------------------------
# Diagram panels
# ---------------------------------------------------------------------------

SHAPE_BY_STYLE = {
    "box": "assertion",
    "wide": "assertion",
    "nobox": "assertion",
    "dec": "decision",
    "term": "terminal",
    # A red ellipse is a terminal the paper leaves open: an outcome no ledger
    # fact of the current object contradicts. Kept as a terminal, and flagged.
    "open": "terminal",
    # A dashed ellipse is not a new node: it is a copy of the numbered terminal
    # named inside it, drawn where an arrow needs to reach a closure that lives
    # in another panel.
    "route": "terminal",
}

GHOST_STYLES = {"route"}
OPEN_STYLES = {"open"}

_NODE_DECL = re.compile(r"\\node\[([^\]]*)\]\s*\(([^)]*)\)\s*")
_NODE_NUMBER = re.compile(r"\\textbf\{\[(\d+)\]\}[~\s]*")
_EDGE_LABEL = re.compile(r"node\[[^\]]*\]\s*\{")
_COORDINATE = re.compile(r"^[\s\d.,+\-]*$")
_FIGURE_LABEL = re.compile(r"\\label\{(fig:[^}]*)\}")
_CAPTION = re.compile(r"\\caption(?:of\{figure\})?(?:\[[^\]]*\])?\s*\{")
#: Arrows that leave the panel say where they land, e.g. `continue at [14]`.
_GOES_TO = re.compile(r"continue[sd]?\s+(?:at|to|in)\s+\[(\d+)\]", re.IGNORECASE)
_COMES_FROM = re.compile(r"\bfrom\s+\[(\d+)\]", re.IGNORECASE)


@dataclass
class Panel:
    id: str
    title: str
    #: What this stretch of the argument does, in a sentence or two.
    summary: str
    caption: str
    nodes: dict[str, dict[str, Any]]
    edges: list[dict[str, Any]]
    #: Cross-panel joins read off dangling arrows, as (from, to, note).
    crossings: list[tuple[str, str, str]]


def parse_nodes(picture: str) -> tuple[dict[str, dict[str, Any]], dict[str, str], set[str]]:
    """Nodes of one panel: ``{number: record}``, ``{tikz id: number}``, ghost ids."""
    nodes: dict[str, dict[str, Any]] = {}
    by_tikz: dict[str, str] = {}
    ghosts: set[str] = set()

    for match in _NODE_DECL.finditer(picture):
        style = match.group(1).split(",")[0].strip()
        shape = SHAPE_BY_STYLE.get(style)
        if shape is None:
            continue  # a layout rail or a floating annotation, not a state
        tikz_id = match.group(2).strip()

        # Step over an optional `at (x,y)` placement to reach the label.
        cursor = match.end()
        while cursor < len(picture) and picture[cursor] != "{":
            cursor += 1
        if cursor >= len(picture):
            continue
        label, _ = read_group(picture, cursor)

        number = _NODE_NUMBER.search(label)
        if not number:
            continue
        node_id = number.group(1)
        by_tikz[tikz_id] = node_id

        if style in GHOST_STYLES:
            ghosts.add(tikz_id)
            continue

        record: dict[str, Any] = {
            "number": node_id,
            "tikzId": tikz_id,
            "shape": shape,
            "label": _NODE_NUMBER.sub("", label, count=1).strip(),
        }
        if style in OPEN_STYLES:
            record["open"] = True
        nodes.setdefault(node_id, record)

    return nodes, by_tikz, ghosts


def parse_edges(
    picture: str,
    by_tikz: dict[str, str],
    part: str,
) -> tuple[list[dict[str, Any]], list[tuple[str, str, str]]]:
    """Arrows of one panel, plus the joins its dangling arrows point at."""
    edges: list[dict[str, Any]] = []
    crossings: list[tuple[str, str, str]] = []

    for path, _offset in iter_statements(picture, "\\draw["):
        branch: str | None = None
        label_match = _EDGE_LABEL.search(path)
        if label_match:
            try:
                branch = to_plain(read_group(path, label_match.end() - 1)[0]) or None
            except ValueError:
                branch = None

        endpoints: list[str] = []
        cursor = 0
        while cursor < len(path):
            char = path[cursor]
            if char == "\\":
                cursor += 2  # an escaped delimiter, e.g. the \( \) of inline maths
                continue
            if char == "{":
                try:
                    _, cursor = read_group(path, cursor)  # a label; never an endpoint
                except ValueError:
                    cursor += 1
                continue
            if char == "(":
                try:
                    inner, cursor = read_group(path, cursor, "(", ")")
                except ValueError:
                    cursor += 1
                    continue
                token = inner.strip()
                if token and not _COORDINATE.match(token):
                    endpoints.append(token.split(".", 1)[0])
                continue
            cursor += 1

        resolved = [by_tikz[name] for name in endpoints if name in by_tikz]

        if len(resolved) >= 2 and resolved[0] != resolved[-1]:
            edges.append(
                {
                    "id": f"{part}:{resolved[0]}->{resolved[-1]}:{len(edges)}",
                    "source": resolved[0],
                    "target": resolved[-1],
                    "branch": branch,
                    "kind": "flow",
                }
            )
            continue

        # An arrow with one end loose: the label says where it goes or came from.
        if not branch or len(resolved) != 1:
            continue
        goes = _GOES_TO.search(branch)
        if goes:
            crossings.append((resolved[0], goes.group(1), branch))
            continue
        comes = _COMES_FROM.search(branch)
        if comes:
            crossings.append((comes.group(1), resolved[0], branch))

    return edges, crossings


#: Sentences that describe how the diagram is drawn rather than what it proves.
#: The shape key on the canvas already says all of this.
_DRAWING_LEGEND = re.compile(
    r"^\s*Proof(?:-dependency)?[ -]?(?:diagram|flow)[^.]*\.\s*"
    r"|^\s*Rectangles[^.]*\.\s*"
    r"|^\s*Conventions are as in[^.]*\.\s*"
    r"|^\s*[^.]*use the convention of[^.]*\.\s*"
    r"|^\s*The bracketed numbers[^.]*\.\s*",
    re.IGNORECASE,
)


def _without_legend(caption: str) -> str:
    """A caption reduced to what it says about the mathematics."""
    text = caption.strip()
    previous = None
    while text != previous:
        previous = text
        text = _DRAWING_LEGEND.sub("", text).strip()
    return text


def parse_panels(text: str, chapter: ChapterSpec) -> list[Panel]:
    """Every diagram panel of one chapter, in source order."""
    start = text.index(chapter.diagrams[0])
    stop = text.index(chapter.diagrams[1], start)
    region = text[start:stop]

    panels: list[Panel] = []
    for picture, offset in iter_environments(region, "tikzpicture"):
        nodes, by_tikz, _ghosts = parse_nodes(picture)
        if not nodes:
            continue  # an illustrative figure, not a panel of the argument

        # The figure's identity and caption follow the picture it wraps.
        tail = region[offset:]
        label = _FIGURE_LABEL.search(tail)
        part = label.group(1) if label else f"{chapter.id}-panel-{len(panels) + 1}"

        caption = ""
        caption_at = _CAPTION.search(tail, 0, label.start() if label else len(tail))
        if caption_at:
            try:
                caption = to_plain(read_group(tail, caption_at.end() - 1)[0])
            except ValueError:
                caption = ""

        edges, crossings = parse_edges(picture, by_tikz, part)
        position = len(panels) + 1
        panels.append(
            Panel(
                id=part,
                title=chapter.part_titles.get(part) or f"Part {position}",
                summary=chapter.part_summaries.get(part, ""),
                caption=_without_legend(caption),
                nodes=nodes,
                edges=edges,
                crossings=crossings,
            )
        )

    return panels


# ---------------------------------------------------------------------------
# Cross-reference tables
# ---------------------------------------------------------------------------


def table_rows(text: str, spec: TableSpec) -> list[list[str]]:
    """Data rows of the table a spec points at, as lists of raw cells."""
    try:
        start = text.index(spec.start)
        stop = text.index(spec.stop, start)
    except ValueError:
        return []

    region = text[start:stop]
    rows: list[list[str]] = []
    bodies = [body for body, _ in iter_environments(region, "longtable")]
    bodies += [body for body, _ in iter_environments(region, "tabular")]

    for body in bodies:
        for row in split_rows(clean_table_body(body)):
            cells = split_cells(row)
            if len(cells) != spec.columns:
                continue
            if not any(cells):
                continue
            # Headings are removed by `clean_table_body`, which reads the marker
            # LaTeX itself uses. Guessing from bold text would be wrong here:
            # one paper sets its node ranges in bold too.
            if spec.first_cell and not re.match(spec.first_cell, cells[0]):
                continue
            rows.append(cells)
    return rows


def cell(row: list[str], index: int | None) -> str:
    return row[index] if index is not None and index < len(row) else ""


# ---------------------------------------------------------------------------
# The paper's own tables, published as written
# ---------------------------------------------------------------------------

#: A longtable body opens with its column specification, which would otherwise
#: be read as part of the first heading cell.
_COLUMN_SPEC = re.compile(r"^\s*(?:\{(?:[^{}]|\{[^{}]*\})*\}|\[[^\]]*\])\s*")
_ROW_NOISE = re.compile(
    r"\\(?:toprule|midrule|bottomrule|hline|endhead|endfirsthead|endfoot"
    r"|endlastfoot|relax|caption\{[^}]*\}|label\{[^}]*\})"
)
_HEADING = re.compile(
    r"\\(?:subsection\*?|section\*?|paragraph)\{((?:[^{}]|\{[^{}]*\})*)\}"
)
_SUBSECTION = re.compile(r"\\subsection\*?\{((?:[^{}]|\{[^{}]*\})*)\}")


def _table_headings(body: str, width: int) -> list[str]:
    """The column headings of a table, however the paper marks them off.

    The heading sits between rule markers rather than before them, so the slice
    that precedes the end of the heading is searched for its last row of the
    right width.
    """
    text = _COLUMN_SPEC.sub("", body, count=1)
    text = text[: head_end(text)]

    headings: list[str] = []
    for row in split_rows(_ROW_NOISE.sub("", text)):
        cells = split_cells(row)
        if len(cells) == width and len([c for c in cells if c.strip()]) >= 2:
            headings = [to_plain(c) for c in cells]
    return headings


def parse_tables(text: str, chapter: ChapterSpec) -> list[dict[str, Any]]:
    """Every table of the chapter that indexes the argument, as written."""
    if chapter.reference_region is None:
        return []
    try:
        start = text.index(chapter.reference_region[0])
        stop = text.index(chapter.reference_region[1], start)
    except ValueError:
        return []

    headings = [(match.start(), to_plain(match.group(1))) for match in _HEADING.finditer(text)]
    sections = [(match.start(), to_plain(match.group(1))) for match in _SUBSECTION.finditer(text)]

    def preceding(offsets: list[tuple[int, str]], position: int) -> str:
        found = [name for at, name in offsets if at < position]
        return found[-1] if found else ""

    tables: list[dict[str, Any]] = []
    for body, offset in iter_environments(text, "longtable"):
        if not start <= offset < stop:
            continue

        rows = [
            cells
            for cells in (split_cells(row) for row in split_rows(clean_table_body(body)))
            if len(cells) > 1 and any(cells)
        ]
        if not rows:
            continue
        width = Counter(len(row) for row in rows).most_common(1)[0][0]
        rows = [row for row in rows if len(row) == width]

        # A `\paragraph` heading ends in a full stop; a title does not need one.
        title = preceding(headings, offset).rstrip(". ")
        section = preceding(sections, offset).rstrip(". ")
        tables.append(
            {
                "id": f"{chapter.id}/{len(tables) + 1}",
                "title": title or f"Table {len(tables) + 1}",
                # A run of blocks under one heading reads as one group.
                "group": section if section and section != title else "",
                "chapter": chapter.id,
                "sourceLine": line_of(text, offset),
                "headers": _table_headings(body, width) or [""] * width,
                "rows": rows,
            }
        )
    return tables


# ---------------------------------------------------------------------------
# Labelled results
# ---------------------------------------------------------------------------

ITEM_KINDS = {
    "theorem": "theorem",
    "lemma": "lemma",
    "proposition": "proposition",
    "corollary": "corollary",
    "definition": "definition",
    "remark": "remark",
    "hypothesis": "theorem",
}

_ENV_BEGIN = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|remark|hypothesis)\}"
)
_LABEL = re.compile(r"\s*\\label(?:\[[^\]]*\])?\{([^}]*)\}")


def parse_items(text: str) -> dict[str, dict[str, Any]]:
    """Every labelled theorem-like environment, with its verbatim statement."""
    items: dict[str, dict[str, Any]] = {}
    for match in _ENV_BEGIN.finditer(text):
        environment = match.group(1)
        cursor = match.end()

        title = ""
        if cursor < len(text) and text[cursor] == "[":
            try:
                title, cursor = read_group(text, cursor, "[", "]")
            except ValueError:
                continue

        label_match = _LABEL.match(text, cursor)
        if not label_match:
            continue

        closing = f"\\end{{{environment}}}"
        end = text.find(closing, label_match.end())
        if end < 0:
            continue

        record = {
            "key": label_match.group(1),
            "kind": ITEM_KINDS[environment],
            "title": to_plain(title),
            "statementLatex": _TYPESETTING.sub("", text[label_match.end() : end]).strip(),
            "sourceLine": line_of(text, match.start()),
        }
        proof = _read_proof(text, end + len(closing))
        if proof:
            record["proofLatex"] = proof
        items[label_match.group(1)] = record
    return items


# Blank lines and a `\begin{proof}[Proof of ...]` opener may sit between a
# statement and its proof.
_PROOF_BEGIN = re.compile(r"\s*\\begin\{proof\}(?:\[[^\]]*\])?")


def _read_proof(text: str, cursor: int) -> str:
    """The proof immediately following a statement, if the paper gives one."""
    match = _PROOF_BEGIN.match(text, cursor)
    if not match:
        return ""
    depth = 1
    index = match.end()
    while index < len(text) and depth:
        opening = text.find("\\begin{proof}", index)
        closing = text.find("\\end{proof}", index)
        if closing < 0:
            return ""
        if 0 <= opening < closing:
            depth += 1
            index = opening + len("\\begin{proof}")
            continue
        depth -= 1
        if depth == 0:
            return _TYPESETTING.sub("", text[match.end() : closing]).strip()
        index = closing + len("\\end{proof}")
    return ""


#: A numbered display the paper labels, so that `\eqref` can point at it.
_DISPLAY = re.compile(r"\\begin\{(equation|align|gather|multline)\}")
_DISPLAY_LABEL = re.compile(r"\\label\{([^}]*)\}")


def parse_equations(text: str) -> dict[str, dict[str, Any]]:
    """Every labelled display, with its body.

    The label may sit anywhere inside the display, not only against the opening
    brace, so the whole body is searched.
    """
    equations: dict[str, dict[str, Any]] = {}
    position = 0
    for match in _DISPLAY.finditer(text):
        end = text.find(f"\\end{{{match.group(1)}}}", match.end())
        if end < 0:
            continue
        body = text[match.end() : end]
        label = _DISPLAY_LABEL.search(body)
        if not label:
            continue
        position += 1
        # An aligned body keeps its `&` markers, so it stays in an environment
        # the maths renderer understands.
        inner = _DISPLAY_LABEL.sub("", body).strip()
        wrapper = {"align": "aligned", "gather": "gathered", "multline": "gathered"}.get(
            match.group(1)
        )
        equations[label.group(1)] = {
            "key": label.group(1),
            "number": position,
            "latex": f"\\begin{{{wrapper}}}{inner}\\end{{{wrapper}}}" if wrapper else inner,
            "sourceLine": line_of(text, match.start()),
        }
    return equations


_NEWCOMMAND = re.compile(r"\\newcommand\{(\\[A-Za-z]+)\}\s*\{")
_DECLARE_OPERATOR = re.compile(r"\\DeclareMathOperator\{(\\[A-Za-z]+)\}\s*\{")


#: Macros whose LaTeX definition uses typesetting primitives the maths renderer
#: has no equivalent for. Replaced by something that reads the same.
MACRO_OVERRIDES = {
    # A barred integral. The paper builds it with \ooalign, which the maths
    # renderer cannot parse; this draws the same mark.
    "\\fint": "{-\\kern-0.62em\\int}",
}

#: Typesetting directives that carry no mathematical content.
_TYPESETTING = re.compile(r"\\qedhere\b|\\allowdisplaybreaks\b|\\noindent\b")


def parse_macros(text: str) -> dict[str, str]:
    """Preamble macro definitions, as a KaTeX macro table."""
    macros: dict[str, str] = {}
    head = text[: text.index("\\begin{document}")] if "\\begin{document}" in text else text
    for pattern, wrap in ((_NEWCOMMAND, "{}"), (_DECLARE_OPERATOR, "\\operatorname{{{}}}")):
        for match in pattern.finditer(head):
            try:
                body, _ = read_group(head, match.end() - 1)
            except ValueError:
                continue
            if "#" in body:
                continue  # takes arguments; never used inside a node label
            macros[match.group(1)] = wrap.format(body)
    macros.update({name: body for name, body in MACRO_OVERRIDES.items() if name in macros})
    return macros


# ---------------------------------------------------------------------------
# Assembly
# ---------------------------------------------------------------------------


_MATH_DELIMITERS = re.compile(r"^\s*(?:\$|\\\(|\\\[)|(?:\$|\\\)|\\\])\s*$")


def _bare_symbol(symbol: str) -> str:
    """A symbol without the maths delimiters the paper wrapped it in."""
    previous = None
    result = symbol.strip()
    while result != previous:
        previous = result
        result = _MATH_DELIMITERS.sub("", result).strip()
    return result


def _expand(text: str, prefix: str) -> list[str]:
    """Node ids named in a table cell, carrying the chapter's prefix."""
    return [f"{prefix}{number}" for number in node_ids(text)]


def _add(target: list[str], values: Iterable[str]) -> None:
    for value in values:
        if value not in target:
            target.append(value)


_FIRST_NODE = re.compile(r"\[(\d+)\]")


def _apply_map(text: str, chapter: ChapterSpec, panels: list[Panel]) -> None:
    """Take each panel's summary, and its part label, from the paper's own map.

    Rows are matched to panels by the first node number they name rather than by
    position: one paper writes that cell as ``\textbf{[1]}--\textbf{[12]}`` and
    spreads a row over several lines, so the range is awkward to parse but the
    first number is always there.
    """
    by_first = {panel.nodes and min(panel.nodes, key=int): panel for panel in panels}

    for spec in chapter.map_tables:
        for row in table_rows(text, spec):
            first = _FIRST_NODE.search(cell(row, spec.nodes))
            panel = by_first.get(first.group(1)) if first else None
            if panel is None:
                continue
            summary = to_plain(cell(row, spec.detail))
            if summary:
                panel.summary = summary
            label = to_plain(cell(row, spec.name)).strip()
            if label and not chapter.part_titles.get(panel.id):
                panel.title = f"Part {label}"


def _read_chapter(chapter: ChapterSpec, root: Path) -> dict[str, Any]:
    """Everything one manuscript contributes, with ids already namespaced."""
    text = strip_comments((root / chapter.source).read_text(encoding="utf-8"))
    prefix = chapter.prefix

    panels = parse_panels(text, chapter)
    items = parse_items(text)
    equations = parse_equations(text)
    tables = parse_tables(text, chapter)

    groups: list[dict[str, Any]] = []
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    crossings: list[tuple[str, str, str]] = []

    _apply_map(text, chapter, panels)

    # A later panel may redraw a closure that lives in an earlier one, under the
    # same number and in the ordinary terminal style (Part XII of the
    # Erdős–Gyárfás paper redraws the power-of-two cycle [155] of Part XI). That is
    # the same step, not a second one: the first drawing keeps it and later
    # copies only supply endpoints for their panel's arrows.
    drawn: set[str] = set()

    for panel in panels:
        groups.append(
            {
                "id": panel.id,
                "title": panel.title,
                "summary": panel.summary,
                "caption": panel.caption,
                "chapter": chapter.id,
            }
        )
        for record in panel.nodes.values():
            if record["number"] in drawn:
                continue
            drawn.add(record["number"])
            nodes.append(
                {
                    **record,
                    "id": f"{prefix}{record['number']}",
                    "group": panel.id,
                    "chapter": chapter.id,
                }
            )
        for edge in panel.edges:
            edges.append(
                {
                    **edge,
                    "id": f"{prefix}{edge['id']}",
                    "source": f"{prefix}{edge['source']}",
                    "target": f"{prefix}{edge['target']}",
                }
            )
        for source, target, note in panel.crossings:
            crossings.append((f"{prefix}{source}", f"{prefix}{target}", note))

    # Joins the paper states in prose rather than drawing.
    for source, target, note in chapter.continuations:
        crossings.append((f"{prefix}{source}", f"{prefix}{target}", note))

    by_id = {node["id"]: node for node in nodes}
    seen: set[tuple[str, str]] = set()
    for source, target, note in crossings:
        if source not in by_id or target not in by_id or source == target:
            continue
        if (source, target) in seen:
            continue
        seen.add((source, target))
        edges.append(
            {
                "id": f"continuation:{source}->{target}",
                "source": source,
                "target": target,
                "branch": note,
                "kind": "continuation",
            }
        )

    return {
        "chapter": {
            "id": chapter.id,
            "title": chapter.title,
            "shortTitle": chapter.short_title,
            "description": chapter.description,
            "source": chapter.source,
            "prefix": prefix,
        },
        "text": text,
        "spec": chapter,
        "groups": groups,
        "nodes": nodes,
        "edges": edges,
        "items": items,
        "equations": equations,
        "tables": tables,
        "macros": parse_macros(text),
    }


def _apply_tables(part: dict[str, Any]) -> tuple[list[dict], list[dict]]:
    """Read a chapter's tables onto its nodes. Returns invariants and constants."""
    chapter: ChapterSpec = part["spec"]
    text: str = part["text"]
    prefix = chapter.prefix
    items: dict[str, dict] = part["items"]
    by_id = {node["id"]: node for node in part["nodes"]}

    def resolve(labels: Iterable[str]) -> list[str]:
        """Namespaced keys for the labels a table cell cites, dropping unknowns."""
        return [items[label]["key"] for label in labels if label in items]

    def attach(node_id: str, labels: Iterable[str]) -> None:
        node = by_id.get(node_id)
        if node is None:
            return
        _add(node["itemRefs"], resolve(labels))

    for node in part["nodes"]:
        node.setdefault("overview", "")
        node.setdefault("itemRefs", [])
        node.setdefault("blocks", [])
        node.setdefault("invariantRefs", [])
        node.setdefault("constantRefs", [])
        node.setdefault("topics", [])
        node.setdefault("aliases", [])

    # The table that says what each node is and which results stand behind it.
    #
    # A row naming one node describes that node, so its sources are the node's
    # own. A row spanning a range describes a whole stretch of the argument —
    # attaching all of its sources to each member would claim, of a single step,
    # every result the block uses. Those are kept separately as block context.
    for spec in chapter.node_tables:
        for row in table_rows(text, spec):
            targets = _expand(cell(row, spec.nodes), prefix)
            name = to_plain(cell(row, spec.name))
            detail = to_plain(cell(row, spec.detail))
            outcome = to_plain(cell(row, spec.outcome))
            sources = crefs(cell(row, spec.sources))
            precise = len(targets) == 1

            block = None
            if not precise and sources:
                block = {
                    "name": name,
                    "range": cell(row, spec.nodes).strip(),
                    "itemRefs": resolve(sources),
                }

            for node_id in targets:
                node = by_id.get(node_id)
                if node is None:
                    continue
                if name:
                    _add(node["topics"], [name])
                if not node["overview"]:
                    node["overview"] = detail or name
                    node["formalContent"] = detail or name
                    node["failureRoute"] = outcome
                if precise:
                    attach(node_id, sources)
                elif block:
                    node["blocks"].append(block)

    # Some panels are entered by an arrow drawn from a layout rail rather than
    # from the node it continues. The audit table names each node's successor, so
    # it supplies the missing entry — but only where one is missing: a successor
    # cell also cites nodes a row *contradicts*, which are not successors.
    entered = {edge["target"] for edge in part["edges"]}
    for spec in chapter.node_tables:
        if not spec.outcome_is_successor:
            continue
        for row in table_rows(text, spec):
            sources = _expand(cell(row, spec.nodes), prefix)
            if len(sources) != 1 or sources[0] not in by_id:
                continue
            successor = cell(row, spec.outcome)
            for target in _expand(successor, prefix):
                if target not in by_id or target in entered or target == sources[0]:
                    continue
                entered.add(target)
                part["edges"].append(
                    {
                        "id": f"successor:{sources[0]}->{target}",
                        "source": sources[0],
                        "target": target,
                        "branch": to_plain(successor),
                        "kind": "continuation",
                    }
                )

    # A panel entry may also name its own antecedent, as in "route from [57] or
    # [58]". Read those only for nodes nothing else reaches.
    for node in part["nodes"]:
        if node["id"] in entered:
            continue
        for match in _COMES_FROM.finditer(node["label"]):
            source = f"{prefix}{match.group(1)}"
            if source in by_id and source != node["id"]:
                entered.add(node["id"])
                part["edges"].append(
                    {
                        "id": f"stated:{source}->{node['id']}",
                        "source": source,
                        "target": node["id"],
                        "branch": "stated in the node",
                        "kind": "continuation",
                    }
                )

    # Prose for individual results.
    for spec in chapter.result_tables:
        for row in table_rows(text, spec):
            keys = crefs(cell(row, spec.sources))
            if not keys:
                continue
            requires = cell(row, spec.extra)
            record = items.get(keys[0])
            if record is not None:
                record.update(
                    {
                        "stage": to_plain(cell(row, spec.name)),
                        "plain": to_plain(cell(row, spec.detail)),
                        "role": to_plain(cell(row, spec.outcome)),
                        "requires": to_plain(requires),
                        "requiresItems": resolve(crefs(requires)),
                    }
                )
            for node_id in _expand(cell(row, spec.nodes), prefix):
                attach(node_id, keys[:1])

    # Standing constraints.
    invariants: list[dict[str, Any]] = []
    seen_invariants: set[int] = set()
    for spec in chapter.ledger_tables:
        for index, row in enumerate(table_rows(text, spec), start=len(invariants) + 1):
            number = cell(row, spec.number).strip()
            key = int(number) if number.isdigit() else index
            if key in seen_invariants:
                continue  # the same constraint restated in a narrower table
            seen_invariants.add(key)
            targets = _expand(cell(row, spec.nodes), prefix)
            invariants.append(
                {
                    # Each manuscript numbers its own constraints from one, so
                    # identity has to carry the manuscript too.
                    "id": f"{chapter.id}:{key}",
                    "number": key,
                    "chapter": chapter.id,
                    "name": to_plain(cell(row, spec.name)),
                    "nodes": targets,
                    "constraint": to_plain(cell(row, spec.detail)),
                    "budget": to_plain(cell(row, spec.outcome)),
                    "usedBy": resolve(crefs(cell(row, spec.sources))),
                }
            )
            for node_id in targets:
                node = by_id.get(node_id)
                if node is not None:
                    _add(node["invariantRefs"], [f"{chapter.id}:{key}"])

    # How each terminal closes.
    for spec in chapter.closure_tables:
        for row in table_rows(text, spec):
            targets = _expand(cell(row, spec.nodes), prefix)
            sources = crefs(cell(row, spec.sources))
            dossier = {
                "closingResult": to_plain(cell(row, spec.sources)),
                "closingItems": resolve(sources),
                "closingCondition": to_plain(cell(row, spec.name)),
                "route": to_plain(cell(row, spec.number)),
                "slack": to_plain(cell(row, spec.detail)),
                "redundantCover": to_plain(cell(row, spec.extra)),
                "residualCounterexample": to_plain(cell(row, spec.outcome)),
            }
            for node_id in targets:
                node = by_id.get(node_id)
                if node is None:
                    continue
                node.setdefault("dossier", dossier)
                attach(node_id, sources)

    # Notation and constants.
    constants: list[dict[str, Any]] = []
    for spec in chapter.glossary_tables:
        for row in table_rows(text, spec):
            symbol = cell(row, spec.name).strip()
            if not symbol:
                continue
            constants.append(
                {
                    "symbol": symbol,
                    "value": cell(row, spec.detail).strip() if spec.detail is not None else "",
                    "meaning": to_plain(cell(row, spec.outcome)),
                    "establishedIn": resolve(crefs(cell(row, spec.sources))),
                    "chapter": chapter.id,
                }
            )

    return invariants, constants


def build_document(spec: ProofSpec, root: Path) -> dict[str, Any]:
    """Read a whole proof — one chapter or several — into one document."""
    parts = [_read_chapter(chapter, root) for chapter in spec.chapters]
    multi = len(parts) > 1

    macros: dict[str, str] = {}
    groups: list[dict] = []
    nodes: list[dict] = []
    edges: list[dict] = []
    invariants: list[dict] = []
    constants: list[dict] = []
    tables: list[dict] = []
    items: dict[str, dict] = {}
    equations: dict[str, dict] = {}

    for part in parts:
        chapter: ChapterSpec = part["spec"]
        # Label names are reused between manuscripts, so each chapter owns a
        # namespace. Records stay keyed by the label the paper writes, while the
        # `key` they carry — and everything that points at them — is namespaced.
        namespace = f"{chapter.id}/" if multi else ""
        for label, record in part["items"].items():
            record["key"] = f"{namespace}{label}"
            record["chapter"] = chapter.id
            items[record["key"]] = record
        for label, record in part["equations"].items():
            record["key"] = f"{namespace}{label}"
            record["chapter"] = chapter.id
            equations[record["key"]] = record

        chapter_invariants, chapter_constants = _apply_tables(part)
        invariants.extend(chapter_invariants)
        constants.extend(chapter_constants)

        groups.extend(part["groups"])
        tables.extend(part["tables"])
        nodes.extend(part["nodes"])
        edges.extend(part["edges"])
        for name, body in part["macros"].items():
            macros.setdefault(name, body)

    by_id = {node["id"]: node for node in nodes}

    # Aliases: a node restated in a later panel shares the other copy's sources.
    for chapter in spec.chapters:
        for group in chapter.aliases:
            present = [f"{chapter.prefix}{number}" for number in group]
            present = [key for key in present if key in by_id]
            for key in present:
                node = by_id[key]
                node["aliases"] = [other for other in present if other != key]
    for node in nodes:
        for other_id in node["aliases"]:
            other = by_id[other_id]
            _add(node["itemRefs"], other["itemRefs"])
            _add(node["invariantRefs"], other["invariantRefs"])
            if not node["overview"]:
                node["overview"] = other["overview"]

    # Constants are matched by the symbol appearing in a node's own text, so the
    # maths delimiters around it — which differ between papers — come off first.
    for constant in constants:
        head = _bare_symbol(constant["symbol"]).split("=")[0]
        if not head:
            continue
        for node in nodes:
            if node.get("chapter") != constant.get("chapter"):
                continue
            if head in node["label"] and constant["symbol"] not in node["constantRefs"]:
                node["constantRefs"].append(constant["symbol"])

    for source, target, note in spec.crossings:
        if source in by_id and target in by_id:
            edges.append(
                {
                    "id": f"crossing:{source}->{target}",
                    "source": source,
                    "target": target,
                    "branch": note,
                    "kind": "continuation",
                }
            )

    # A result the step already claims as its own is not repeated as block
    # context: the block list is strictly what the step does *not* claim.
    for node in nodes:
        own = set(node["itemRefs"])
        blocks = []
        for block in node["blocks"]:
            rest = [key for key in block["itemRefs"] if key not in own]
            if rest:
                blocks.append({**block, "itemRefs": rest})
        node["blocks"] = blocks

    document: dict[str, Any] = {
        "id": spec.id,
        "slug": spec.slug,
        "title": spec.title,
        "subtitle": spec.subtitle,
        "source": {
            "files": [chapter.source for chapter in spec.chapters],
            "diagramNodes": len(nodes),
            "figures": len(groups),
        },
        "macros": macros,
        "groups": groups,
        "nodes": nodes,
        "edges": edges,
        "items": [items[key] for key in sorted(items)],
        "equations": list(equations.values()),
        "invariants": invariants,
        "constants": constants,
        "tables": tables,
    }
    if multi:
        document["chapters"] = [part["chapter"] for part in parts]
    return document
