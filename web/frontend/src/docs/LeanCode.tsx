import { highlightLean } from "./lean-highlight";

/** Trim the leading blank line and common indentation from a template literal. */
function dedent(source: string): string {
  const lines = source.replace(/^\n/, "").replace(/\s+$/, "").split("\n");
  const indents = lines
    .filter((line) => line.trim().length > 0)
    .map((line) => line.match(/^ */)![0].length);
  const indent = indents.length ? Math.min(...indents) : 0;
  return lines.map((line) => line.slice(indent)).join("\n");
}

/** A block of Lean, coloured. `source` names where the snippet was taken from. */
export function LeanCode({ children, source }: { children: string; source?: string }) {
  const tokens = highlightLean(dedent(children));
  return (
    <figure className="lean-code">
      <pre>
        <code>
          {tokens.map((token, index) =>
            token.kind === "plain" ? (
              token.text
            ) : (
              <span key={index} className={`tok-${token.kind}`}>
                {token.text}
              </span>
            ),
          )}
        </code>
      </pre>
      {source ? <figcaption>{source}</figcaption> : null}
    </figure>
  );
}

/** Inline Lean, for a name or a short expression in running prose. */
export function L({ children }: { children: string }) {
  return <code className="lean-inline">{children}</code>;
}
