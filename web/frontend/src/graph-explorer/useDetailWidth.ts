import { useCallback, useEffect, useRef, useState } from "react";

export const DEFAULT_DETAIL_WIDTH = 420;
const MIN_WIDTH = 300;
/** Always leave this much room for the diagram itself. */
const MIN_CANVAS = 320;

/** A width that stays readable without squeezing the diagram out of view. */
export function clampDetailWidth(width: number, available: number): number {
  const maximum = Math.max(MIN_WIDTH, available - MIN_CANVAS);
  return Math.round(Math.min(Math.max(width, MIN_WIDTH), maximum));
}

/**
 * A user-resizable width for the detail column, remembered between visits.
 *
 * Returns the current width, a ref to put on the element the drag is measured
 * against, and the handlers for the divider.
 */
export function useDetailWidth(storageKey: string) {
  const container = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState<number>(() => {
    // Storage is not always reachable — a sandboxed frame refuses it outright —
    // and the column has a perfectly good default without it.
    try {
      const stored = Number(window.localStorage.getItem(storageKey));
      return Number.isFinite(stored) && stored > 0 ? stored : DEFAULT_DETAIL_WIDTH;
    } catch {
      return DEFAULT_DETAIL_WIDTH;
    }
  });
  // Tracked in a ref as well as state: a pointer can move in the same frame as
  // the press, before a re-render would have told the move handler to listen.
  const active = useRef(false);
  const [dragging, setDragging] = useState(false);

  const apply = useCallback((next: number) => {
    const available = container.current?.getBoundingClientRect().width ?? Infinity;
    setWidth(clampDetailWidth(next, available));
  }, []);

  // Persist, and keep the column legal when the window is resized.
  useEffect(() => {
    try {
      window.localStorage.setItem(storageKey, String(width));
    } catch {
      // Remembering the width is a convenience, not a requirement.
    }
  }, [storageKey, width]);

  useEffect(() => {
    const onResize = () => apply(width);
    window.addEventListener("resize", onResize);
    return () => window.removeEventListener("resize", onResize);
  }, [apply, width]);

  const onPointerDown = useCallback(
    (event: React.PointerEvent<HTMLDivElement>) => {
      event.preventDefault();
      event.currentTarget.setPointerCapture(event.pointerId);
      active.current = true;
      setDragging(true);
    },
    [],
  );

  const onPointerMove = useCallback(
    (event: React.PointerEvent<HTMLDivElement>) => {
      if (!active.current) return;
      const bounds = container.current?.getBoundingClientRect();
      if (!bounds) return;
      apply(bounds.right - event.clientX);
    },
    [apply],
  );

  const onPointerUp = useCallback((event: React.PointerEvent<HTMLDivElement>) => {
    if (event.currentTarget.hasPointerCapture(event.pointerId)) {
      event.currentTarget.releasePointerCapture(event.pointerId);
    }
    active.current = false;
    setDragging(false);
  }, []);

  const onKeyDown = useCallback(
    (event: React.KeyboardEvent<HTMLDivElement>) => {
      const step = event.shiftKey ? 64 : 16;
      if (event.key === "ArrowLeft") {
        event.preventDefault();
        apply(width + step);
      } else if (event.key === "ArrowRight") {
        event.preventDefault();
        apply(width - step);
      } else if (event.key === "Home" || event.key === "Enter") {
        event.preventDefault();
        apply(DEFAULT_DETAIL_WIDTH);
      }
    },
    [apply, width],
  );

  const reset = useCallback(() => apply(DEFAULT_DETAIL_WIDTH), [apply]);

  return {
    container,
    width,
    dragging,
    handleProps: {
      onPointerDown,
      onPointerMove,
      onPointerUp,
      onPointerCancel: onPointerUp,
      onKeyDown,
      onDoubleClick: reset,
    },
  };
}
