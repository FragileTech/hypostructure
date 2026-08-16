import { act, fireEvent, render, screen } from "@testing-library/react";
import { beforeEach, describe, expect, it } from "vitest";

import { DEFAULT_DETAIL_WIDTH, useDetailWidth } from "./useDetailWidth";

const KEY = "test:detail-width";

/** A stand-in for the explorer's canvas/divider/detail row. */
function Harness({ containerWidth = 1400 }: { containerWidth?: number }) {
  const detail = useDetailWidth(KEY);
  return (
    <div
      ref={detail.container}
      data-testid="body"
      // jsdom has no layout, so the row reports its width itself.
      style={{ width: containerWidth }}
    >
      <div data-testid="handle" role="separator" tabIndex={0} {...detail.handleProps} />
      <output data-testid="width">{detail.width}</output>
      <output data-testid="dragging">{String(detail.dragging)}</output>
    </div>
  );
}

function stubLayout(width: number, right: number) {
  Element.prototype.getBoundingClientRect = function () {
    return { width, right, left: right - width, top: 0, bottom: 0, height: 0, x: 0, y: 0, toJSON: () => ({}) } as DOMRect;
  };
}

function width() {
  return Number(screen.getByTestId("width").textContent);
}

function drag(clientX: number) {
  const handle = screen.getByTestId("handle");
  // jsdom does not implement pointer capture.
  Object.assign(handle, {
    setPointerCapture: () => {},
    releasePointerCapture: () => {},
    hasPointerCapture: () => false,
  });
  act(() => {
    fireEvent.pointerDown(handle, { pointerId: 1 });
    fireEvent.pointerMove(handle, { pointerId: 1, clientX });
  });
}

describe("useDetailWidth", () => {
  beforeEach(() => {
    window.localStorage.clear();
    stubLayout(1400, 1400);
  });

  it("starts at the default width", () => {
    render(<Harness />);
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH);
  });

  it("widens the column as the divider is dragged left", () => {
    render(<Harness />);
    drag(800);
    expect(width()).toBe(600);
    expect(screen.getByTestId("dragging").textContent).toBe("true");
  });

  it("narrows it as the divider is dragged right", () => {
    render(<Harness />);
    drag(1100);
    expect(width()).toBe(300);
  });

  it("refuses to squeeze out either side", () => {
    render(<Harness />);
    drag(10); // dragged far past the left edge
    expect(width()).toBe(1080);

    drag(1399); // dragged onto the right edge
    expect(width()).toBe(300);
  });

  it("stops dragging when the pointer is released", () => {
    render(<Harness />);
    drag(800);
    act(() => {
      fireEvent.pointerUp(screen.getByTestId("handle"), { pointerId: 1 });
      fireEvent.pointerMove(screen.getByTestId("handle"), { pointerId: 1, clientX: 1200 });
    });
    expect(screen.getByTestId("dragging").textContent).toBe("false");
    expect(width()).toBe(600);
  });

  it("can be resized from the keyboard", () => {
    render(<Harness />);
    const handle = screen.getByTestId("handle");
    act(() => {
      fireEvent.keyDown(handle, { key: "ArrowLeft" });
    });
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH + 16);
    act(() => {
      fireEvent.keyDown(handle, { key: "ArrowRight", shiftKey: true });
    });
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH - 48);
  });

  it("resets on Home and on a double-click", () => {
    render(<Harness />);
    const handle = screen.getByTestId("handle");
    drag(800);
    act(() => {
      fireEvent.keyDown(handle, { key: "Home" });
    });
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH);

    drag(800);
    act(() => {
      fireEvent.doubleClick(handle);
    });
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH);
  });

  it("remembers the width for the next visit", () => {
    const first = render(<Harness />);
    drag(900);
    expect(width()).toBe(500);
    first.unmount();

    render(<Harness />);
    expect(width()).toBe(500);
  });

  it("ignores a stored width that is not a usable number", () => {
    window.localStorage.setItem(KEY, "not a width");
    render(<Harness />);
    expect(width()).toBe(DEFAULT_DETAIL_WIDTH);
  });
});
