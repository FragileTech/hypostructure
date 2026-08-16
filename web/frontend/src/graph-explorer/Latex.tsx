import { createContext, useContext, useMemo, useState } from "react";
import katex from "katex";

import { parseLatex, type Segment } from "./latex";

/** How a reference should be shown, and what it leads to. */
export interface Reference {
  label: string;
  /** True when clicking it should move the reader somewhere. */
  actionable: boolean;
  /**
   * Mathematics to reveal in place rather than navigate to — used for a
   * reference to a numbered display, where jumping away mid-sentence would lose
   * the reader's place.
   */
  preview?: string;
  /** Shown under a revealed preview, naming exactly what it is. */
  note?: string;
}

interface MathContextValue {
  macros: Record<string, string>;
  /** Called when the reader clicks a cross-reference such as `lem:full-rank`. */
  onReference?: (key: string) => void;
  /** How to name a reference key, and whether clicking it does anything. */
  resolveReference?: (key: string) => Reference;
}

const MathContext = createContext<MathContextValue>({ macros: {} });

export function MathProvider({
  macros,
  onReference,
  resolveReference,
  children,
}: MathContextValue & { children: React.ReactNode }) {
  const value = useMemo(
    () => ({ macros, onReference, resolveReference }),
    [macros, onReference, resolveReference],
  );
  return <MathContext.Provider value={value}>{children}</MathContext.Provider>;
}

function renderMath(
  value: string,
  display: boolean,
  macros: Record<string, string>,
): string {
  try {
    return katex.renderToString(value, {
      displayMode: display,
      throwOnError: false,
      strict: false,
      trust: false,
      // KaTeX mutates the macro table it is given; hand it a copy.
      macros: { ...macros },
    });
  } catch {
    return "";
  }
}

/**
 * Render a LaTeX fragment: prose as text, mathematics through KaTeX, and
 * `\cref` cross-references as buttons that jump to the referenced result.
 */
export function Latex({ value, className }: { value: string; className?: string }) {
  const { macros, onReference, resolveReference } = useContext(MathContext);
  const segments = useMemo(() => parseLatex(value), [value]);

  return (
    <span className={className ? `latex ${className}` : "latex"}>
      {segments.map((segment, position) => (
        <SegmentView
          key={position}
          segment={segment}
          macros={macros}
          onReference={onReference}
          resolveReference={resolveReference}
        />
      ))}
    </span>
  );
}

/**
 * A reference the reader can open where it stands.
 *
 * Pointing at a numbered display is not really navigation — the reader wants to
 * see the inequality without losing the sentence — so the display unfolds in
 * place instead of moving the view.
 */
function InlineReference({
  label,
  title,
  note,
  latex,
  macros,
}: {
  label: string;
  title: string;
  note?: string;
  latex: string;
  macros: Record<string, string>;
}) {
  const [open, setOpen] = useState(false);

  return (
    <>
      <button
        type="button"
        className={open ? "latex-ref is-open" : "latex-ref"}
        aria-expanded={open}
        title={title}
        onClick={() => setOpen((current) => !current)}
      >
        {label}
      </button>
      {open ? (
        <span className="latex-inline-reference">
          <span
            className="latex-math is-display"
            dangerouslySetInnerHTML={{ __html: renderMath(latex, true, macros) }}
          />
          {note ? <small>{note}</small> : null}
        </span>
      ) : null}
    </>
  );
}

function SegmentView({
  segment,
  macros,
  onReference,
  resolveReference,
}: {
  segment: Segment;
  macros: Record<string, string>;
} & Pick<MathContextValue, "onReference" | "resolveReference">) {
  switch (segment.kind) {
    case "text":
      return <>{segment.value}</>;
    case "break":
      return <br />;
    case "item":
      return <span className="latex-item" aria-hidden="true" />;
    case "ref": {
      const reference = resolveReference?.(segment.key);
      const label = reference?.label ?? segment.key;

      if (reference?.preview) {
        return (
          <InlineReference
            label={label}
            title={reference.note ?? segment.key}
            note={reference.note}
            latex={reference.preview}
            macros={macros}
          />
        );
      }
      if (!onReference || (reference && !reference.actionable)) {
        return (
          <span className="latex-ref is-plain" title={segment.key}>
            {label}
          </span>
        );
      }
      return (
        <button
          type="button"
          className="latex-ref"
          onClick={() => onReference(segment.key)}
          title={segment.key}
        >
          {label}
        </button>
      );
    }
    case "math":
      return (
        <span
          className={segment.display ? "latex-math is-display" : "latex-math"}
          // KaTeX output is generated here from the paper's own source, never
          // from anything a reader can supply.
          dangerouslySetInnerHTML={{
            __html: renderMath(segment.value, segment.display, macros),
          }}
        />
      );
  }
}
