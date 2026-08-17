import { useCallback, useEffect, useState, useSyncExternalStore } from "react";

/** Must be kept in step with the rail media queries in styles/app.css. */
export const RAIL_BREAKPOINT = 900;

export interface Sidebar {
  /** The viewport is narrow enough that the rail is an off-canvas drawer. */
  compact: boolean;
  /** Wide viewport: the rail column is folded down to its gutter. */
  collapsed: boolean;
  /** Narrow viewport: the drawer is showing. */
  open: boolean;
  /** What the toggle's aria-expanded says, whichever mode we are in. */
  expanded: boolean;
  /** What the one toggle button does right now. */
  toggle: () => void;
  close: () => void;
}

/** Subscribes to a media query, and says false wherever there is no matchMedia. */
function useMediaQuery(query: string): boolean {
  const subscribe = useCallback(
    (notify: () => void) => {
      // Absent in jsdom, and in any server render.
      const list = window.matchMedia?.(query);
      if (!list) return () => {};
      if (list.addEventListener) {
        list.addEventListener("change", notify);
        return () => list.removeEventListener("change", notify);
      }
      // Safari before 14 only has the deprecated pair.
      list.addListener(notify);
      return () => list.removeListener(notify);
    },
    [query],
  );
  return useSyncExternalStore(
    subscribe,
    () => window.matchMedia?.(query).matches ?? false,
    () => false,
  );
}

/**
 * The state behind a collapsible rail: folded away on a wide screen, an
 * off-canvas drawer on a narrow one.
 *
 * The two are deliberately separate bits. Someone who folds the rail away at
 * their desk should not find a drawer already open on their phone, and opening
 * the drawer once should not fold the rail away for good. Only the desktop
 * preference is remembered.
 */
export function useSidebar(storageKey: string): Sidebar {
  const compact = useMediaQuery(`(max-width: ${RAIL_BREAKPOINT}px)`);

  const [collapsed, setCollapsed] = useState<boolean>(() => {
    // Read in the initialiser so the first paint is already right: no flash of
    // an expanded rail. Storage is not always reachable — a sandboxed frame
    // refuses it outright — and the rail has a perfectly good default without it.
    try {
      return window.localStorage.getItem(storageKey) === "1";
    } catch {
      return false;
    }
  });
  const [open, setOpen] = useState(false);

  useEffect(() => {
    try {
      window.localStorage.setItem(storageKey, collapsed ? "1" : "0");
    } catch {
      // Remembering the preference is a convenience, not a requirement.
    }
  }, [storageKey, collapsed]);

  // Widening the window — or turning the phone — must not stand a drawer up
  // over a layout that has no room for it, nor strand the scroll lock.
  useEffect(() => {
    if (!compact) setOpen(false);
  }, [compact]);

  useEffect(() => {
    if (!compact || !open) return;
    const close = (event: KeyboardEvent) => {
      if (event.key === "Escape") setOpen(false);
    };
    document.addEventListener("keydown", close);
    return () => document.removeEventListener("keydown", close);
  }, [compact, open]);

  // The drawer covers the article, so the article must not scroll behind it.
  useEffect(() => {
    if (!compact || !open) return;
    document.body.classList.add("has-rail-open");
    return () => document.body.classList.remove("has-rail-open");
  }, [compact, open]);

  const toggle = useCallback(() => {
    if (compact) setOpen((value) => !value);
    else setCollapsed((value) => !value);
  }, [compact]);

  const close = useCallback(() => setOpen(false), []);

  return { compact, collapsed, open, expanded: compact ? open : !collapsed, toggle, close };
}

/** The state classes for the element that owns the rail's grid. */
export function railPageClass(base: string, sidebar: Sidebar): string {
  return [base, sidebar.collapsed && "is-rail-collapsed", sidebar.open && "is-rail-open"]
    .filter(Boolean)
    .join(" ");
}
