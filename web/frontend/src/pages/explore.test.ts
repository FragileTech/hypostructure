/**
 * The explorer's view state as the address bar carries it.
 */

import { describe, expect, it } from "vitest";

import { readState } from "./ExplorePage";

describe("readState", () => {
  it("reads as a reader unless the link asks for a referee", () => {
    expect(readState(new URLSearchParams("step=15")).mode).toBe("reader");
    expect(readState(new URLSearchParams("step=15&mode=referee")).mode).toBe("referee");
    expect(readState(new URLSearchParams("mode=editor")).mode).toBe("reader");
  });

  it("keeps the rest of the view", () => {
    const state = readState(
      new URLSearchParams("step=15&panel=p&paper=c&trace=both&q=x&result=r&constraint=one:1"),
    );
    expect(state).toEqual({
      selected: "15",
      group: "p",
      chapter: "c",
      trace: "both",
      query: "x",
      item: "r",
      mode: "reader",
      constraint: "one:1",
    });
  });
});
