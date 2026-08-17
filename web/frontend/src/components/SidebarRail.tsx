import { useEffect, useRef, type KeyboardEvent, type ReactNode } from "react";
import { useLocation } from "react-router-dom";

import type { Sidebar } from "../hooks/useSidebar";

/** What is focusable inside a rail: its entries, and the drawer's close button. */
const FOCUSABLE = "a[href], button:not([disabled])";

function RailGlyph() {
  return (
    <svg aria-hidden="true" width="14" height="14" viewBox="0 0 16 16" fill="none">
      <path
        d="M2 4h12M2 8h12M2 12h12"
        stroke="currentColor"
        strokeWidth="1.6"
        strokeLinecap="round"
      />
    </svg>
  );
}

/**
 * The chrome around a table of contents: the toggle that folds it away, and —
 * on a narrow screen, where the rail becomes a drawer over the article — the
 * scrim and the close button.
 *
 * The rail's entries are the caller's; this only wraps them. The state lives
 * with the page, which needs it for its own grid.
 *
 * Note that a folded rail is hidden in CSS, with `visibility`, and is never
 * unmounted or marked `aria-hidden`. Visibility takes it out of the tab order
 * and out of the accessibility tree just as well, and leaving the entries in
 * the document keeps every page of the rail addressable — which is what the
 * docs tests check. Do not "fix" this by conditionally rendering the nav.
 */
export function SidebarRail({
  sidebar,
  label,
  id,
  className,
  children,
}: {
  sidebar: Sidebar;
  /** The nav's accessible name. Tests match on it — keep existing values. */
  label: string;
  /** The nav's id, for the toggle's aria-controls. */
  id: string;
  /** The page's own rail class, e.g. "docs-rail". */
  className: string;
  children: ReactNode;
}) {
  const toggle = useRef<HTMLButtonElement>(null);
  const close = useRef<HTMLButtonElement>(null);
  const panel = useRef<HTMLElement>(null);
  const { pathname, search } = useLocation();
  const drawer = sidebar.compact && sidebar.open;

  // Choosing an entry navigates; the drawer covering the article should go away
  // with it. The tables rail selects through the query string, so that counts
  // as navigation too.
  const dismiss = sidebar.close;
  useEffect(() => {
    dismiss();
  }, [dismiss, pathname, search]);

  // A drawer over a scrim is modal in effect: focus should follow it in, and
  // come back to the toggle when it leaves. The ref keeps the first render from
  // stealing focus onto a toggle nobody pressed.
  const wasOpen = useRef(false);
  useEffect(() => {
    if (drawer) close.current?.focus();
    else if (wasOpen.current) toggle.current?.focus();
    wasOpen.current = drawer;
  }, [drawer]);

  // ...and should not escape it while it is up.
  const onKeyDown = (event: KeyboardEvent<HTMLElement>) => {
    if (!drawer || event.key !== "Tab") return;
    const stops = panel.current?.querySelectorAll<HTMLElement>(FOCUSABLE);
    if (!stops?.length) return;
    const first = stops[0];
    const last = stops[stops.length - 1];
    if (event.shiftKey && document.activeElement === first) {
      event.preventDefault();
      last.focus();
    } else if (!event.shiftKey && document.activeElement === last) {
      event.preventDefault();
      first.focus();
    }
  };

  return (
    <div className="rail-shell">
      {/* Hidden above the breakpoint, so it is never in the way on a desktop. */}
      <div className="rail-scrim" aria-hidden="true" onClick={sidebar.close} />
      <button
        ref={toggle}
        type="button"
        className="rail-toggle"
        aria-expanded={sidebar.expanded}
        aria-controls={id}
        onClick={sidebar.toggle}
      >
        <RailGlyph />
        <span className="rail-toggle-label">Contents</span>
      </button>
      <nav
        ref={panel}
        id={id}
        className={`rail-panel ${className}`}
        aria-label={label}
        onKeyDown={onKeyDown}
      >
        <button
          ref={close}
          type="button"
          className="rail-close"
          aria-label="Close the contents"
          onClick={sidebar.close}
        >
          <svg aria-hidden="true" width="14" height="14" viewBox="0 0 16 16" fill="none">
            <path
              d="m4 4 8 8m0-8-8 8"
              stroke="currentColor"
              strokeWidth="1.6"
              strokeLinecap="round"
            />
          </svg>
        </button>
        {children}
      </nav>
    </div>
  );
}
