/**
 * A small tokenizer for Lean 4 snippets, enough to colour documentation
 * examples. It knows comments, strings, backtick names, attributes, the
 * keywords a reader meets in this framework, and the sorts. Everything else
 * is plain text. It is deliberately not a parser.
 */

export type LeanTokenKind =
  | "keyword"
  | "comment"
  | "string"
  | "name"
  | "attribute"
  | "sort"
  | "hole"
  | "plain";

export interface LeanToken {
  kind: LeanTokenKind;
  text: string;
}

const KEYWORDS = new Set([
  "abbrev",
  "at",
  "by",
  "calc",
  "cases",
  "change",
  "class",
  "decide",
  "def",
  "deriving",
  "do",
  "else",
  "end",
  "exact",
  "example",
  "export",
  "extends",
  "fun",
  "have",
  "if",
  "import",
  "in",
  "inductive",
  "instance",
  "intro",
  "let",
  "match",
  "namespace",
  "noncomputable",
  "obtain",
  "open",
  "private",
  "protected",
  "rfl",
  "section",
  "show",
  "simp",
  "simpa",
  "structure",
  "syntax",
  "then",
  "theorem",
  "universe",
  "variable",
  "where",
  "with",
]);

const SORTS = new Set(["Type", "Prop", "Sort"]);

const IDENTIFIER_START = /[A-Za-z_À-￿]/;
const IDENTIFIER_PART = /[A-Za-z0-9_'.?!À-￿]/;

/** Split one Lean source string into coloured tokens. Concatenating the token texts gives the source back. */
export function highlightLean(source: string): LeanToken[] {
  const tokens: LeanToken[] = [];
  let plain = "";
  const flush = () => {
    if (plain) tokens.push({ kind: "plain", text: plain });
    plain = "";
  };
  const push = (kind: LeanTokenKind, text: string) => {
    flush();
    tokens.push({ kind, text });
  };

  let index = 0;
  while (index < source.length) {
    const rest = source.slice(index);

    // Block comments, including doc comments, nested one level deep is enough for docs.
    if (rest.startsWith("/-")) {
      let depth = 0;
      let end = index;
      while (end < source.length) {
        if (source.startsWith("/-", end)) {
          depth += 1;
          end += 2;
        } else if (source.startsWith("-/", end)) {
          depth -= 1;
          end += 2;
          if (depth === 0) break;
        } else {
          end += 1;
        }
      }
      push("comment", source.slice(index, end));
      index = end;
      continue;
    }

    if (rest.startsWith("--")) {
      const newline = source.indexOf("\n", index);
      const end = newline === -1 ? source.length : newline;
      push("comment", source.slice(index, end));
      index = end;
      continue;
    }

    if (rest.startsWith('"')) {
      let end = index + 1;
      while (end < source.length && source[end] !== '"') {
        if (source[end] === "\\") end += 1;
        end += 1;
      }
      end = Math.min(end + 1, source.length);
      push("string", source.slice(index, end));
      index = end;
      continue;
    }

    // Attributes: @[simp], @[reducible]
    if (rest.startsWith("@[")) {
      const close = source.indexOf("]", index);
      const end = close === -1 ? source.length : close + 1;
      push("attribute", source.slice(index, end));
      index = end;
      continue;
    }

    // Backtick names: `Hypostructure.Core.Strategy.contradiction and ``ident
    if (rest.startsWith("`") && !rest.startsWith("`(")) {
      let end = index;
      while (source[end] === "`") end += 1;
      while (end < source.length && IDENTIFIER_PART.test(source[end])) end += 1;
      if (end > index + 1) {
        push("name", source.slice(index, end));
        index = end;
        continue;
      }
    }

    // Term-level macro token used by the framework for its authority.
    if (rest.startsWith("exactLedgerInternal%")) {
      push("hole", "exactLedgerInternal%");
      index += "exactLedgerInternal%".length;
      continue;
    }

    if (IDENTIFIER_START.test(source[index])) {
      let end = index + 1;
      while (end < source.length && IDENTIFIER_PART.test(source[end])) end += 1;
      // A trailing dot belongs to the punctuation, not the identifier.
      while (end > index + 1 && source[end - 1] === ".") end -= 1;
      const word = source.slice(index, end);
      if (word === "sorry") push("hole", word);
      else if (KEYWORDS.has(word)) push("keyword", word);
      else if (SORTS.has(word)) push("sort", word);
      else plain += word;
      index = end;
      continue;
    }

    plain += source[index];
    index += 1;
  }
  flush();
  return tokens;
}
