/**
 * A small LaTeX reader: enough to render the statements a mathematics paper
 * writes, without pretending to be a full TeX engine.
 *
 * The source is cut into segments — running text, inline or display maths, line
 * breaks, list items, and cross-references — which the renderer turns into DOM.
 * Maths is handed to KaTeX untouched, so the paper's own notation survives.
 */

export type Segment =
  | { kind: "text"; value: string }
  | { kind: "math"; value: string; display: boolean }
  | { kind: "break" }
  | { kind: "item" }
  | { kind: "ref"; key: string };

interface Delimiter {
  open: string;
  close: string;
  display: boolean;
}

const DELIMITERS: Delimiter[] = [
  { open: "$$", close: "$$", display: true },
  { open: "\\[", close: "\\]", display: true },
  { open: "\\(", close: "\\)", display: false },
  { open: "$", close: "$", display: false },
];

/**
 * Display environments, and the wrapper the maths renderer needs for each.
 *
 * An aligned body keeps its `&` markers, so it has to stay inside an
 * environment the renderer understands; a plain equation does not.
 */
const DISPLAY_ENVIRONMENTS: [name: string, wrapper: string | null][] = [
  ["equation*", null],
  ["equation", null],
  ["align*", "aligned"],
  ["align", "aligned"],
  ["aligned", "aligned"],
  ["multline*", "gathered"],
  ["multline", "gathered"],
  ["gather*", "gathered"],
  ["gather", "gathered"],
];

const TEXT_MACROS = ["emph", "textbf", "textit", "texttt", "textsc", "mbox"];

const ONLY_REFERENCES = /^\s*(?:\\(?:[cC]ref|eqref|ref)\{[^}]*\}[\s,;.]*)+$/;
const LABEL = /\\label(?:\[[^\]]*\])?\{[^}]*\}/g;

/** A display carries its own label; that is bookkeeping, not mathematics. */
function withoutLabels(body: string): string {
  return body.replace(LABEL, "");
}

/** Split maths out of a LaTeX fragment, leaving prose to be cleaned up after. */
function splitMath(source: string): Segment[] {
  const segments: Segment[] = [];
  let buffer = "";
  let cursor = 0;

  const flush = (): void => {
    if (buffer) {
      segments.push({ kind: "text", value: buffer });
      buffer = "";
    }
  };

  while (cursor < source.length) {
    // A display environment behaves like \[ ... \].
    let matchedEnvironment = false;
    if (source.startsWith("\\begin{", cursor)) {
      for (const [name, wrapper] of DISPLAY_ENVIRONMENTS) {
        const open = `\\begin{${name}}`;
        if (!source.startsWith(open, cursor)) continue;
        const close = `\\end{${name}}`;
        const end = source.indexOf(close, cursor + open.length);
        if (end < 0) break;
        flush();
        const body = withoutLabels(source.slice(cursor + open.length, end));
        segments.push({
          kind: "math",
          value: wrapper ? `\\begin{${wrapper}}${body}\\end{${wrapper}}` : body,
          display: true,
        });
        cursor = end + close.length;
        matchedEnvironment = true;
        break;
      }
    }
    if (matchedEnvironment) continue;

    let matchedDelimiter = false;
    for (const delimiter of DELIMITERS) {
      if (!source.startsWith(delimiter.open, cursor)) continue;
      if (delimiter.open === "$" && isEscaped(source, cursor)) continue;
      const end = findClose(source, cursor + delimiter.open.length, delimiter.close);
      if (end < 0) continue;
      const body = source.slice(cursor + delimiter.open.length, end);

      // Some papers wrap a bare cross-reference in maths delimiters. There is no
      // mathematics in it, and the renderer would choke, so it stays prose.
      if (ONLY_REFERENCES.test(body)) {
        buffer += body;
        cursor = end + delimiter.close.length;
        matchedDelimiter = true;
        break;
      }

      flush();
      segments.push({ kind: "math", value: withoutLabels(body), display: delimiter.display });
      cursor = end + delimiter.close.length;
      matchedDelimiter = true;
      break;
    }
    if (matchedDelimiter) continue;

    if (source[cursor] === "\\" && cursor + 1 < source.length) {
      // Keep escapes intact so `\$` never opens a maths run.
      buffer += source.slice(cursor, cursor + 2);
      cursor += 2;
      continue;
    }

    buffer += source[cursor];
    cursor += 1;
  }

  flush();
  return segments;
}

/** True when the character at `index` is escaped by an odd run of backslashes. */
function isEscaped(source: string, index: number): boolean {
  let backslashes = 0;
  while (index - backslashes > 0 && source[index - backslashes - 1] === "\\") {
    backslashes += 1;
  }
  return backslashes % 2 === 1;
}

function findClose(source: string, from: number, close: string): number {
  let cursor = from;
  while (cursor < source.length) {
    // The closing delimiter may itself start with a backslash (`\)`, `\]`), so
    // test for it before treating a backslash as an escape.
    if (source.startsWith(close, cursor)) return cursor;
    if (source[cursor] === "\\") {
      cursor += 2;
      continue;
    }
    cursor += 1;
  }
  return -1;
}

function unwrapTextMacros(source: string): string {
  let result = source;
  for (const name of TEXT_MACROS) {
    const marker = `\\${name}{`;
    let index = result.indexOf(marker);
    while (index >= 0) {
      let depth = 0;
      let cursor = index + marker.length - 1;
      let end = -1;
      while (cursor < result.length) {
        const char = result[cursor];
        if (char === "\\") {
          cursor += 2;
          continue;
        }
        if (char === "{") depth += 1;
        else if (char === "}") {
          depth -= 1;
          if (depth === 0) {
            end = cursor;
            break;
          }
        }
        cursor += 1;
      }
      if (end < 0) break;
      result =
        result.slice(0, index) +
        result.slice(index + marker.length, end) +
        result.slice(end + 1);
      index = result.indexOf(marker);
    }
  }
  return result;
}

// Every way these papers point at something: `\cref`, `\Cref`, `\eqref`, `\ref`.
const REF = /\\(?:[cC]ref|eqref|ref)\{([^}]*)\}/;
const STRIPPED_ENVIRONMENTS =
  /\\(?:begin|end)\{(?:enumerate|itemize|description|remark|proof|center|small|scriptsize)\}(?:\[[^\]]*\])?/g;

/** Turn one prose chunk into text, break, item and reference segments. */
function readProse(source: string): Segment[] {
  let text = unwrapTextMacros(source);
  text = text.replace(STRIPPED_ENVIRONMENTS, "");
  text = text.replace(/\\label(?:\[[^\]]*\])?\{[^}]*\}/g, "");
  text = text.replace(/\\(?:qquad|quad|,|;|:|!)/g, " ");
  text = text.replace(/``/g, "“").replace(/''/g, "”");
  text = text.replace(/(?<!-)---(?!-)/g, "—").replace(/(?<!-)--(?!-)/g, "–");
  text = text.replace(/~/g, " ");

  const segments: Segment[] = [];
  let buffer = "";
  const flush = (): void => {
    const value = buffer.replace(/[ \t]*\n[ \t]*/g, " ").replace(/[ \t]{2,}/g, " ");
    if (value) segments.push({ kind: "text", value });
    buffer = "";
  };

  let cursor = 0;
  while (cursor < text.length) {
    if (text.startsWith("\\\\", cursor)) {
      flush();
      segments.push({ kind: "break" });
      cursor += 2;
      continue;
    }
    if (text.startsWith("\\item", cursor)) {
      flush();
      segments.push({ kind: "item" });
      cursor += 5;
      continue;
    }
    const reference = REF.exec(text.slice(cursor));
    if (reference && reference.index === 0) {
      flush();
      for (const key of reference[1].split(",")) {
        const trimmed = key.trim();
        if (trimmed) segments.push({ kind: "ref", key: trimmed });
      }
      cursor += reference[0].length;
      continue;
    }
    if (text.startsWith("\n\n", cursor)) {
      flush();
      segments.push({ kind: "break" });
      while (text[cursor] === "\n") cursor += 1;
      continue;
    }
    buffer += text[cursor];
    cursor += 1;
  }
  flush();
  return segments;
}

/** Parse a LaTeX fragment into renderable segments. */
export function parseLatex(source: string): Segment[] {
  const segments: Segment[] = [];
  for (const segment of splitMath(source ?? "")) {
    if (segment.kind !== "text") {
      segments.push(segment);
      continue;
    }
    segments.push(...readProse(segment.value));
  }
  // A reference is followed by its sentence's punctuation; drop the space the
  // surrounding LaTeX left between them.
  for (let position = 1; position < segments.length; position += 1) {
    const previous = segments[position - 1];
    const current = segments[position];
    if (previous.kind === "ref" && current.kind === "text") {
      current.value = current.value.replace(/^ +([.,;:)])/, "$1");
    }
  }

  // Collapse leading/trailing structural noise.
  while (segments.length && segments[0].kind === "break") segments.shift();
  while (segments.length && segments[segments.length - 1].kind === "break") segments.pop();
  return segments;
}

/** A plain-text approximation, for titles, tooltips and document metadata. */
export function latexToPlainText(source: string): string {
  return parseLatex(source)
    .map((segment) => {
      switch (segment.kind) {
        case "text":
          return segment.value;
        case "math":
          return segment.value.replace(/\\[a-zA-Z]+|[{}]/g, "").replace(/\s+/g, " ");
        case "ref":
          return segment.key;
        default:
          return " ";
      }
    })
    .join("")
    .replace(/\s+/g, " ")
    .trim();
}
