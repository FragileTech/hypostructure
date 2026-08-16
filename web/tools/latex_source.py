"""Small LaTeX source utilities shared by the proof-graph extractors.

Nothing here is specific to a particular paper: these are generic helpers for
walking a LaTeX file, reading brace-balanced groups, and splitting tabular rows.
"""

from __future__ import annotations

import re
from typing import Iterator


def read_group(text: str, open_index: int, open_char: str = "{", close_char: str = "}") -> tuple[str, int]:
    """Read a brace-balanced group.

    ``open_index`` must point at ``open_char``.  Returns the group's *contents*
    (without the delimiters) and the index just past the closing delimiter.
    Escaped delimiters (``\\{``) are ignored, as is anything inside a ``\\%``
    comment is not -- the caller is expected to have stripped comments first.
    """
    if text[open_index] != open_char:
        raise ValueError(f"expected {open_char!r} at {open_index}, found {text[open_index]!r}")
    depth = 0
    index = open_index
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == open_char:
            depth += 1
        elif char == close_char:
            depth -= 1
            if depth == 0:
                return text[open_index + 1 : index], index + 1
        index += 1
    raise ValueError(f"unbalanced {open_char!r} starting at {open_index}")


def strip_comments(text: str) -> str:
    """Remove ``%`` comments while preserving line structure and ``\\%``."""
    out: list[str] = []
    for line in text.split("\n"):
        index = 0
        cut = len(line)
        while index < len(line):
            if line[index] == "\\":
                index += 2
                continue
            if line[index] == "%":
                cut = index
                break
            index += 1
        out.append(line[:cut])
    return "\n".join(out)


def line_of(text: str, index: int) -> int:
    """1-based line number of a character offset."""
    return text.count("\n", 0, index) + 1


#: A row separator, with the optional extra spacing LaTeX allows after it.
_ROW_SPLIT = re.compile(r"\\\\\*?(?:\[[^\]]*\])?(?!\w)")


def split_rows(body: str) -> list[str]:
    """Split a tabular body on unescaped row separators."""
    return [row for row in _ROW_SPLIT.split(body)]


def split_cells(row: str) -> list[str]:
    """Split a tabular row on ``&``, respecting braces and ``\\&``."""
    cells: list[str] = []
    current: list[str] = []
    depth = 0
    index = 0
    while index < len(row):
        char = row[index]
        if char == "\\":
            current.append(row[index : index + 2])
            index += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
        if char == "&" and depth == 0:
            cells.append("".join(current))
            current = []
            index += 1
            continue
        current.append(char)
        index += 1
    cells.append("".join(current))
    return [cell.strip() for cell in cells]


_TABLE_NOISE = re.compile(
    r"\\(?:toprule|midrule|bottomrule|endhead|endfoot|endfirsthead|endlastfoot"
    r"|hline|noalign|relax|caption|captionsetup)\b"
)
_TABLE_SPAN = re.compile(r"\\multicolumn\{\d+\}\{[^{}]*\}\{[^{}]*\}")
#: How a table can mark the end of its heading, most reliable first. A longtable
#: names its heading explicitly; booktabs closes it with the first rule; a plain
#: ruled table has only its first line. `\hline` is last because such tables also
#: use it between data rows, so only the first one can be the heading.
_HEAD_MARKERS = (
    (re.compile(r"\\(?:endfirsthead|endhead)\b"), "last"),
    (re.compile(r"\\midrule\b"), "first"),
    (re.compile(r"\\hline\b"), "first"),
)


def head_end(body: str) -> int:
    """Where a table's heading ends, or 0 when it has no marked heading."""
    for pattern, which in _HEAD_MARKERS:
        found = list(pattern.finditer(body))
        if found:
            return (found[-1] if which == "last" else found[0]).end()
    return 0


def clean_table_body(body: str) -> str:
    """Reduce a table body to its data rows.

    A heading is not always marked up differently from the data — some papers set
    it in plain text — so it is identified the way LaTeX does, by the
    ``\\endhead`` or ``\\midrule`` that closes it, and everything up to the last
    such marker is dropped.

    ``\\relax`` matters too: a row that begins ``[1] &`` would otherwise be read
    as an optional argument, so some papers guard every row with one.
    """
    return _TABLE_SPAN.sub("", _TABLE_NOISE.sub("", body[head_end(body) :]))


def iter_statements(text: str, opener: str) -> Iterator[tuple[str, int]]:
    """Yield each ``opener … ;`` statement, as ``(body after the opener, start)``.

    The terminating semicolon is the first one at bracket and brace depth zero,
    so a label such as ``node[above]{compact; to [58]}`` does not end the
    statement early.
    """
    for match in re.finditer(re.escape(opener), text):
        index = match.end()
        # An opener such as `\draw[` leaves us already inside a bracket.
        depth = opener.count("[") + opener.count("{")
        while index < len(text):
            char = text[index]
            if char == "\\":
                index += 2
                continue
            if char in "[{":
                depth += 1
            elif char in "]}":
                depth -= 1
            elif char == ";" and depth == 0:
                break
            index += 1
        yield text[match.end() : index], match.start()


def iter_environments(text: str, name: str) -> Iterator[tuple[str, int]]:
    """Yield ``(body, start_index)`` for each ``\\begin{name} ... \\end{name}``."""
    begin = f"\\begin{{{name}}}"
    end = f"\\end{{{name}}}"
    index = 0
    while True:
        start = text.find(begin, index)
        if start < 0:
            return
        stop = text.find(end, start)
        if stop < 0:
            return
        yield text[start + len(begin) : stop], start
        index = stop + len(end)


_CREF = re.compile(r"\\(?:c|C)ref\{([^}]*)\}")


def crefs(text: str) -> list[str]:
    """Every label referenced by ``\\cref``/``\\Cref``, comma lists expanded."""
    found: list[str] = []
    for group in _CREF.findall(text):
        for label in group.split(","):
            label = label.strip()
            if label and label not in found:
                found.append(label)
    return found


_NODE_RANGE = re.compile(r"\[(\d+)\](?:\s*--\s*\[(\d+)\])?")


def node_ids(text: str) -> list[str]:
    """Expand a diagram-node cell such as ``[63], [86]--[109]`` into ids."""
    found: list[str] = []
    for start, stop in _NODE_RANGE.findall(text):
        low = int(start)
        high = int(stop) if stop else low
        for value in range(low, high + 1):
            key = str(value)
            if key not in found:
                found.append(key)
    return found


_LATEX_TEXT_MACROS = re.compile(r"\\(?:emph|textbf|textit|texttt|textsc|mbox|text)\{")


def to_plain(text: str) -> str:
    """Best-effort plain-text rendering of a LaTeX fragment.

    Math is preserved verbatim (the frontend renders it with KaTeX); only text
    formatting wrappers and whitespace are normalised.
    """
    result = text
    while True:
        match = _LATEX_TEXT_MACROS.search(result)
        if not match:
            break
        inner, end = read_group(result, match.end() - 1)
        result = result[: match.start()] + inner + result[end:]
    result = result.replace("``", "\u201c").replace("''", "\u201d")
    result = result.replace("~", " ").replace("\\,", " ").replace("\\ ", " ")
    result = re.sub(r"\\\\", " ", result)
    result = re.sub(r"\s+", " ", result)
    return result.strip()
