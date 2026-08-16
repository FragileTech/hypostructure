import "@testing-library/jest-dom/vitest";

// jsdom does not implement PointerEvent. Testing Library builds pointer events
// from window[EventConstructor], so pointing it at MouseEvent is what makes
// clientX survive into the handlers under test.
if (!("PointerEvent" in window)) {
  Object.defineProperty(window, "PointerEvent", { value: MouseEvent, writable: true });
}

// The canvas measures itself with a ResizeObserver, which jsdom has no notion
// of. Nothing under test depends on a measurement arriving, only on the canvas
// mounting without throwing.
if (!("ResizeObserver" in window)) {
  Object.defineProperty(window, "ResizeObserver", {
    writable: true,
    value: class {
      observe() {}
      unobserve() {}
      disconnect() {}
    },
  });
}

if (!("DOMMatrixReadOnly" in window)) {
  Object.defineProperty(window, "DOMMatrixReadOnly", {
    writable: true,
    value: class {
      m22 = 1;
      constructor(_transform?: string) {}
    },
  });
}
