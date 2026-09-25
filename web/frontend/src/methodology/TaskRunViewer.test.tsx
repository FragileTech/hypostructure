import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it } from "vitest";
import { TaskRunViewer } from "./TaskRunViewer";

describe("proof run viewer", () => {
  it("shows the exact next task and separate progress measures", () => {
    render(<TaskRunViewer initialSnapshot={{
      branch: "B", branch_status: "open", atomic_tasks: { accepted: 4 },
      productive_moves: 1, open_outcomes: ["survivor-1"],
      next: {
        diagnostic: null,
        branch: { endpoint: "B implies False", incoming: "producer P, left arm",
          objects: ["the selected graph G"], source_revision: "abc123" },
        task: { id: "T7", phase: "7", mode: "DISCOVER", kind: "relate_new_and_retained",
          goal: "Prove the overlap restriction on G", objects: ["G"],
          reads: ["branch B", "accepted degree bound"], interaction: "degree and overlap",
          acceptance: "two cited reviews", allowed_write: "proof.md" },
      },
    }} />);
    fireEvent.click(screen.getByText("Inspect a proof run"));
    expect(screen.getByText("4")).toBeInTheDocument();
    expect(screen.getByText("1")).toBeInTheDocument();
    expect(screen.getByRole("heading", { name: "Next task: T7" })).toBeInTheDocument();
    expect(screen.getByText(/B implies False; incoming from producer P, left arm/)).toBeInTheDocument();
    expect(screen.getByText("degree and overlap")).toBeInTheDocument();
    expect(screen.getByText("Prove the overlap restriction on G")).toBeInTheDocument();
    expect(screen.getByText("two cited reviews")).toBeInTheDocument();
    expect(screen.getByText(/survivor-1/)).toBeInTheDocument();
  });
});
