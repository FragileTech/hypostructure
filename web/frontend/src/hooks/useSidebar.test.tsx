import { act, fireEvent, render, screen } from "@testing-library/react";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

import { railPageClass, useSidebar } from "./useSidebar";

const KEY = "test:rail";

/** A stand-in for a page that owns a rail. */
function Harness() {
  const sidebar = useSidebar(KEY);
  return (
    <div data-testid="page" className={railPageClass("page", sidebar)}>
      <button type="button" data-testid="toggle" onClick={sidebar.toggle}>
        Contents
      </button>
      <output data-testid="compact">{String(sidebar.compact)}</output>
      <output data-testid="collapsed">{String(sidebar.collapsed)}</output>
      <output data-testid="open">{String(sidebar.open)}</output>
      <output data-testid="expanded">{String(sidebar.expanded)}</output>
    </div>
  );
}

function state(name: string) {
  return screen.getByTestId(name).textContent;
}

function toggle() {
  act(() => {
    fireEvent.click(screen.getByTestId("toggle"));
  });
}

const original = Object.getOwnPropertyDescriptor(window, "matchMedia");
let listeners: (() => void)[] = [];

/** A controllable matchMedia, the analogue of useDetailWidth's stubLayout. */
function stubMedia(matches: boolean) {
  listeners = [];
  Object.defineProperty(window, "matchMedia", {
    writable: true,
    configurable: true,
    value: vi.fn((query: string) => ({
      media: query,
      matches,
      onchange: null,
      addEventListener: (_: string, listener: () => void) => listeners.push(listener),
      removeEventListener: (_: string, listener: () => void) => {
        listeners = listeners.filter((entry) => entry !== listener);
      },
      addListener: (listener: () => void) => listeners.push(listener),
      removeListener: (listener: () => void) => {
        listeners = listeners.filter((entry) => entry !== listener);
      },
      dispatchEvent: () => false,
    })),
  });
}

/** Report a new viewport to everyone listening, as a real browser would. */
function resizeTo(matches: boolean) {
  const notify = [...listeners];
  stubMedia(matches);
  // The subscription survives the swap, so re-register what was listening.
  listeners = notify;
  act(() => {
    for (const listener of notify) listener();
  });
}

describe("useSidebar", () => {
  beforeEach(() => {
    window.localStorage.clear();
    document.body.className = "";
    stubMedia(false);
  });

  afterEach(() => {
    if (original) Object.defineProperty(window, "matchMedia", original);
  });

  it("starts expanded on a wide viewport", () => {
    render(<Harness />);
    expect(state("compact")).toBe("false");
    expect(state("collapsed")).toBe("false");
    expect(state("open")).toBe("false");
    expect(state("expanded")).toBe("true");
  });

  it("folds the rail away on a wide viewport, and remembers it", () => {
    const first = render(<Harness />);
    toggle();
    expect(state("collapsed")).toBe("true");
    expect(state("expanded")).toBe("false");
    expect(screen.getByTestId("page")).toHaveClass("is-rail-collapsed");
    expect(window.localStorage.getItem(KEY)).toBe("1");
    first.unmount();

    render(<Harness />);
    expect(state("collapsed")).toBe("true");
  });

  it("ignores a stored preference that is not one it wrote", () => {
    window.localStorage.setItem(KEY, "yes please");
    render(<Harness />);
    expect(state("collapsed")).toBe("false");
  });

  it("works where storage is refused outright", () => {
    const storage = Object.getOwnPropertyDescriptor(window, "localStorage");
    Object.defineProperty(window, "localStorage", {
      configurable: true,
      value: {
        getItem() {
          throw new Error("denied");
        },
        setItem() {
          throw new Error("denied");
        },
      },
    });
    try {
      render(<Harness />);
      expect(state("collapsed")).toBe("false");
      toggle();
      expect(state("collapsed")).toBe("true");
    } finally {
      if (storage) Object.defineProperty(window, "localStorage", storage);
    }
  });

  it("opens the drawer instead of folding, on a narrow viewport", () => {
    stubMedia(true);
    render(<Harness />);
    expect(state("compact")).toBe("true");
    toggle();
    expect(state("open")).toBe("true");
    expect(state("collapsed")).toBe("false");
    expect(state("expanded")).toBe("true");
    expect(screen.getByTestId("page")).toHaveClass("is-rail-open");
  });

  it("does not open the drawer just because the rail was folded at a desk", () => {
    window.localStorage.setItem(KEY, "1");
    stubMedia(true);
    render(<Harness />);
    expect(state("collapsed")).toBe("true");
    expect(state("open")).toBe("false");
    expect(state("expanded")).toBe("false");
  });

  it("closes the drawer on Escape", () => {
    stubMedia(true);
    render(<Harness />);
    toggle();
    act(() => {
      fireEvent.keyDown(document, { key: "Escape" });
    });
    expect(state("open")).toBe("false");
  });

  it("locks the page behind the drawer, and lets go again", () => {
    stubMedia(true);
    const view = render(<Harness />);
    toggle();
    expect(document.body).toHaveClass("has-rail-open");
    toggle();
    expect(document.body).not.toHaveClass("has-rail-open");

    toggle();
    expect(document.body).toHaveClass("has-rail-open");
    view.unmount();
    expect(document.body).not.toHaveClass("has-rail-open");
  });

  it("puts an open drawer away when the window is widened", () => {
    stubMedia(true);
    render(<Harness />);
    toggle();
    expect(state("open")).toBe("true");

    resizeTo(false);
    expect(state("compact")).toBe("false");
    expect(state("open")).toBe("false");
    expect(document.body).not.toHaveClass("has-rail-open");
  });

  it("stops listening to the viewport once it is gone", () => {
    const view = render(<Harness />);
    expect(listeners.length).toBeGreaterThan(0);
    view.unmount();
    expect(listeners).toHaveLength(0);
  });

  it("renders where there is no matchMedia at all", () => {
    Object.defineProperty(window, "matchMedia", { writable: true, configurable: true, value: undefined });
    render(<Harness />);
    expect(state("compact")).toBe("false");
    toggle();
    expect(state("collapsed")).toBe("true");
  });
});
