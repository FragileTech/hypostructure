import { useState } from "react";

type Task = {
  id: string;
  phase: string;
  mode: string;
  kind: string;
  goal: string;
  objects: string[];
  reads: string[];
  interaction: string;
  acceptance: string;
  allowed_write: string;
};

type Snapshot = {
  branch: string;
  branch_status: string;
  atomic_tasks: Record<string, number>;
  productive_moves: number;
  open_outcomes: string[];
  next: {
    task: Task | null;
    branch?: { endpoint: string; incoming: string; objects: string[]; source_revision: string };
    diagnostic: string | null;
  };
};

function isSnapshot(value: unknown): value is Snapshot {
  if (!value || typeof value !== "object") return false;
  const record = value as Partial<Snapshot>;
  const next = record.next;
  if (!next || typeof next !== "object" ||
      (next.diagnostic !== null && typeof next.diagnostic !== "string")) return false;
  if (next.task !== null) {
    if (!next.task || typeof next.task !== "object" || !next.branch) return false;
    const task = next.task as Partial<Task>;
    if (![task.id, task.goal, task.interaction, task.acceptance, task.allowed_write]
      .every(field => typeof field === "string") ||
      !Array.isArray(task.reads) || !Array.isArray(next.branch.objects) ||
      typeof next.branch.endpoint !== "string" ||
      typeof next.branch.incoming !== "string" ||
      typeof next.branch.source_revision !== "string") return false;
  }
  return typeof record.branch === "string" && typeof record.branch_status === "string" &&
    typeof record.productive_moves === "number" && Array.isArray(record.open_outcomes) &&
    record.open_outcomes.every(outcome => typeof outcome === "string") &&
    !!record.atomic_tasks && typeof record.atomic_tasks === "object" &&
    typeof record.atomic_tasks.accepted === "number";
}

export function TaskRunViewer({ initialSnapshot }: { initialSnapshot?: Snapshot }) {
  const [snapshot, setSnapshot] = useState<Snapshot | undefined>(initialSnapshot);
  const [error, setError] = useState("");

  async function load(file: File | undefined) {
    if (!file) return;
    try {
      const value: unknown = JSON.parse(await file.text());
      if (!isSnapshot(value)) throw new Error("This is not a task queue status file.");
      setSnapshot(value);
      setError("");
    } catch (caught) {
      setError(caught instanceof Error ? caught.message : "Could not read this file.");
    }
  }

  const selected = snapshot?.next.task;
  const branch = snapshot?.next.branch;
  return <details className="task-run-viewer">
    <summary>Inspect a proof run</summary>
    <p>Save the task controller’s <code>status</code> output as JSON, then open it here. The file stays in your browser.</p>
    <label>Proof run status file <input type="file" accept=".json,application/json" onChange={event => void load(event.target.files?.[0])} /></label>
    {error && <p role="alert">{error}</p>}
    {snapshot && <div className="task-run-status">
      <div className="task-run-measures" aria-label="Separate proof progress measures">
        <p><strong>{snapshot.atomic_tasks.accepted ?? 0}</strong><span>accepted tasks</span></p>
        <p><strong>{snapshot.productive_moves}</strong><span>productive moves</span></p>
        <p><strong>{snapshot.branch_status === "closed" ? "Closed" : "Open"}</strong><span>branch {snapshot.branch}</span></p>
      </div>
      {selected && branch ? <section aria-label="Next proof task">
        <h5>Next task: {selected.id}</h5>
        <p>Run this single problem in a fresh isolated context. Preserve the complete retained hypotheses; return one result for independent review.</p>
        <dl className="recipe-contract">
          <div><dt>Exact residual</dt><dd>{branch.endpoint}; incoming from {branch.incoming}. Source: {branch.source_revision}.</dd></div>
          <div><dt>Retained objects</dt><dd>{branch.objects.join("; ")}</dd></div>
          <div><dt>Selected interaction</dt><dd>{selected.interaction || "Phase 0 branch restoration"}</dd></div>
          <div><dt>Requested output</dt><dd>{selected.goal}</dd></div>
          <div><dt>Permitted inputs</dt><dd>{selected.reads.join("; ")}</dd></div>
          <div><dt>Write scope</dt><dd>{selected.allowed_write}</dd></div>
          <div><dt>Acceptance</dt><dd>{selected.acceptance}</dd></div>
        </dl>
      </section> : <p>{snapshot.next.diagnostic ?? "No next task is ready."}</p>}
      {snapshot.open_outcomes.length > 0 && <p><strong>Open outcomes:</strong> {snapshot.open_outcomes.join(", ")}</p>}
    </div>}
  </details>;
}
