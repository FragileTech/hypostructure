import { render, screen, within } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { describe, expect, it, vi } from "vitest";

import { MathProvider } from "./Latex";
import { TableView } from "./TableView";
import { TEST_DOCUMENT } from "./test-document";

const TABLE = TEST_DOCUMENT.tables[0];

function show(overrides: Partial<Parameters<typeof TableView>[0]> = {}, onNode = vi.fn()) {
  const utilities = render(
    <MathProvider macros={TEST_DOCUMENT.macros} onNode={onNode}>
      <TableView table={TABLE} {...overrides} />
    </MathProvider>,
  );
  return { ...utilities, onNode };
}

describe("TableView", () => {
  it("prints the table as the paper set it", () => {
    show();
    for (const heading of TABLE.headers) {
      expect(screen.getByRole("columnheader", { name: heading })).toBeInTheDocument();
    }
    expect(screen.getAllByRole("row")).toHaveLength(TABLE.rows.length + 1);
    expect(screen.getByText("2 rows")).toBeInTheDocument();
  });

  it("narrows to the rows that mention the query", () => {
    show({ query: "odd" });
    expect(screen.getAllByRole("row")).toHaveLength(2); // the heading and one match
    expect(screen.getByText("1 of 2 rows")).toBeInTheDocument();
  });

  it("says so when nothing matches", () => {
    show({ query: "nothing here" });
    expect(screen.getByText("No row mentions that.")).toBeInTheDocument();
  });

  it("turns a step number into a way into the diagram", async () => {
    const user = userEvent.setup();
    const { onNode } = show();

    const first = screen.getAllByRole("row")[1];
    await user.click(within(first).getByRole("button", { name: "2" }));
    expect(onNode).toHaveBeenCalledWith("2");
  });

  it("names the result a cell cites rather than printing its key", () => {
    show();
    // Without a resolver the key stands in; the page supplies one.
    expect(screen.getByText("lem:halving")).toBeInTheDocument();
  });
});
