import { createContext, useContext, useMemo, useState } from "react";
import katex from "katex";

import { parseLatex, type ParseOptions, type Segment } from "./latex";

/** How a reference should be shown, and what it leads to. */
export interface Reference {
  label: string;
  /** True when clicking it should move the reader somewhere. */
  actionable: boolean;
  /**
   * Something to reveal in place rather than navigate to, where jumping away
   * mid-sentence would lose the reader's place: the body of a numbered display
   * (`math`, handed to KaTeX as it stands) or the full statement of an
   * auxiliary result (`statement`, prose with maths inside, read like any other).
   */
  preview?: { kind: "math" | "statement"; source: string };
  /** Shown under a revealed preview, naming exactly what it is. */
  note?: string;
}

interface MathContextValue {
  macros: Record<string, string>;
  /** Called when the reader clicks a cross-reference such as `lem:full-rank`. */
  onReference?: (key: string) => void;
  /** How to name a reference key, and whether clicking it does anything. */
  resolveReference?: (key: string) => Reference;
  /** Called when the reader clicks a diagram step named in the text. */
  onNode?: (number: string) => void;
}

const MathContext = createContext<MathContextValue>({ macros: {} });

export function MathProvider({
  macros,
  onReference,
  resolveReference,
  onNode,
  children,
}: MathContextValue & { children: React.ReactNode }) {
  const value = useMemo(
    () => ({ macros, onReference, resolveReference, onNode }),
    [macros, onNode, onReference, resolveReference],
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
export function Latex({
  value,
  className,
  nodes = false,
}: {
  value: string;
  className?: string;
  /** Read bracketed integers as diagram steps. See `ParseOptions`. */
  nodes?: boolean;
}) {
  const { macros, onReference, resolveReference, onNode } = useContext(MathContext);
  const options = useMemo<ParseOptions>(() => ({ nodes }), [nodes]);
  const segments = useMemo(() => parseLatex(value, options), [options, value]);

  const render = (segment: Segment, position: number) => (
    <SegmentView
      key={position}
      segment={segment}
      macros={macros}
      onReference={onReference}
      resolveReference={resolveReference}
      onNode={onNode}
    />
  );
  const hasList = segments.some((segment) => segment.kind === "list" || segment.kind === "item");
  const fullClassName = className ? `latex ${className}` : "latex";
  if (!hasList) return <span className={fullClassName}>{segments.map(render)}</span>;
  return <div className={fullClassName}>{buildTree(segments, render)}</div>;
}

interface ListFrame {
  ordered: boolean;
  labelled: boolean;
  items: { label?: string; children: React.ReactNode[] }[];
  /** Content seen before the first `\item`. */
  preamble: React.ReactNode[];
  implicit: boolean;
}

/** Group list boundaries and items into nested `<ul>`/`<ol>` elements. */
function buildTree(
  segments: Segment[],
  render: (segment: Segment, position: number) => React.ReactNode,
): React.ReactNode[] {
  const root: React.ReactNode[] = [];
  const stack: ListFrame[] = [];
  const sink = (): React.ReactNode[] => {
    const frame = stack[stack.length - 1];
    if (!frame) return root;
    const last = frame.items[frame.items.length - 1];
    return last ? last.children : frame.preamble;
  };
  const close = (position: number): void => {
    const frame = stack.pop();
    if (!frame) return;
    const Tag = frame.ordered ? "ol" : "ul";
    const element = (
      <Tag
        key={`list-${position}`}
        className={frame.labelled ? "latex-list is-labelled" : "latex-list"}
      >
        {frame.items.map((item, index) => (
          <li key={index} className="latex-item">
            {item.label ? <span className="latex-item-label">{item.label}</span> : null}
            {item.children}
          </li>
        ))}
      </Tag>
    );
    const target = sink();
    target.push(...frame.preamble, element);
  };

  segments.forEach((segment, position) => {
    if (segment.kind === "list") {
      if (segment.open) {
        stack.push({ ordered: segment.ordered, labelled: false, items: [], preamble: [], implicit: false });
      } else {
        // Close implicit lists opened by stray items first.
        while (stack.length && stack[stack.length - 1].implicit) close(position);
        close(position);
      }
      return;
    }
    if (segment.kind === "item") {
      if (!stack.length) {
        stack.push({ ordered: false, labelled: false, items: [], preamble: [], implicit: true });
      }
      const frame = stack[stack.length - 1];
      if (segment.label) frame.labelled = true;
      frame.items.push({ label: segment.label, children: [] });
      return;
    }
    sink().push(render(segment, position));
  });
  while (stack.length) close(segments.length);
  return root;
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
  preview,
  macros,
}: {
  label: string;
  title: string;
  note?: string;
  preview: NonNullable<Reference["preview"]>;
  macros: Record<string, string>;
}) {
  const [open, setOpen] = useState(false);

  return (
    <>
      <RefControl
        className={open ? "latex-ref is-open" : "latex-ref"}
        expanded={open}
        title={title}
        onActivate={() => setOpen((current) => !current)}
      >
        {label}
      </RefControl>
      {open ? (
        <span className="latex-inline-reference">
          {preview.kind === "math" ? (
            <span
              className="latex-math is-display"
              dangerouslySetInnerHTML={{ __html: renderMath(preview.source, true, macros) }}
            />
          ) : (
            <Latex value={preview.source} className="latex-inline-statement" />
          )}
          {note ? <small>{note}</small> : null}
        </span>
      ) : null}
    </>
  );
}

/**
 * A clickable reference that still copies as text. A real `<button>` is skipped
 * when a reader selects a passage and copies it, leaving "in the sense of ."
 * behind; an inline element with the button role keeps both behaviours.
 */
function RefControl({
  className,
  title,
  expanded,
  onActivate,
  children,
}: {
  className: string;
  title?: string;
  expanded?: boolean;
  onActivate: () => void;
  children: React.ReactNode;
}) {
  return (
    <span
      role="button"
      tabIndex={0}
      className={className}
      aria-expanded={expanded}
      title={title}
      onClick={onActivate}
      onKeyDown={(event) => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          onActivate();
        }
      }}
    >
      {children}
    </span>
  );
}

function SegmentView({
  segment,
  macros,
  onReference,
  resolveReference,
  onNode,
}: {
  segment: Segment;
  macros: Record<string, string>;
} & Pick<MathContextValue, "onReference" | "resolveReference" | "onNode">) {
  switch (segment.kind) {
    case "text":
      return <>{segment.value}</>;
    case "break":
      return <br />;
    case "item":
    case "list":
      // Structure is assembled by `buildTree`; nothing to draw inline.
      return null;
    case "node":
      return onNode ? (
        <button
          type="button"
          className="chip chip-node"
          onClick={() => onNode(segment.id)}
          title={`Go to step ${segment.id}`}
        >
          {segment.id}
        </button>
      ) : (
        <>[{segment.id}]</>
      );
    case "ref": {
      const reference = resolveReference?.(segment.key);
      const label = reference?.label || segment.key;

      if (reference?.preview) {
        return (
          <InlineReference
            label={label}
            title={reference.note ?? segment.key}
            note={reference.note}
            preview={reference.preview}
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
        <RefControl className="latex-ref" title={segment.key} onActivate={() => onReference(segment.key)}>
          {label}
        </RefControl>
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
