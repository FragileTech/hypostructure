import workflow from "../../../../tools/methodology_gate/policy/workflow.json";
import { SELECTION_ROWS, ARTIFACT_ROWS } from "./recipe-reference";
import { TaskRunViewer } from "./TaskRunViewer";
import { Latex } from "../graph-explorer";

const taskflow = workflow.taskflow;

function Table({ caption, heads, rows }: { caption: string; heads: readonly string[]; rows: readonly (readonly string[])[] }) {
  return <div className="methodology-table-wrap recipe-table-wrap" tabIndex={0} role="region" aria-label={caption}>
    <table className="methodology-map recipe-table"><caption>{caption}</caption>
      <thead><tr>{heads.map(head => <th key={head} scope="col">{head}</th>)}</tr></thead>
      <tbody>{rows.map((row, index) => <tr key={index}>{row.map((cell, col) => col === 0
        ? <th scope="row" key={col}><Latex value={cell} /></th>
        : <td key={col}><Latex value={cell} /></td>)}</tr>)}</tbody>
    </table>
  </div>;
}

function TaskKinds({ kinds }: { kinds: readonly string[] }) {
  return <><p><strong>One task per fresh context.</strong> Each assignment below is a separate mathematical problem with its own worker, retained hypotheses, requested result and stopping condition. A worker returns its result before another context starts the next task.</p>
    <p><strong>Available tasks:</strong> {kinds.map(kind => kind.replaceAll("_", " ")).join(" · ")}</p></>;
}

function PhaseZero() {
  return <>
    <p>Pin the source revision and reconstruct the complete incoming residual: its exact endpoint, tagged incoming alternative, retained objects and domains, valid inherited premises, and applicable minimality or fixed imports. A merged node keeps each producer’s premises on its own arm.</p>
    <TaskKinds kinds={taskflow.phase_zero.tasks} />
    <p><strong>Gate:</strong> {taskflow.phase_zero.gate} {taskflow.phase_zero.fast_path}</p>
  </>;
}

function Phase({ number }: { number: keyof typeof taskflow.phase_descriptions }) {
  const phase = taskflow.phase_descriptions[number];
  const kinds = taskflow.phase_tasks[number];
  return <>
    <dl className="recipe-contract">
      <div><dt>Start with</dt><dd>{phase.input}</dd></div>
      <div><dt>Required result</dt><dd>{phase.output}</dd></div>
      <div><dt>Review gate</dt><dd>{phase.gate}</dd></div>
    </dl>
    <TaskKinds kinds={kinds} />
    {number === "1" && <p>A logical premise may be used again in a new interaction. A finite credit needs a proved remaining balance, disjointness, or resource split before another charge.</p>}
    {number === "2" && <p>Record the mathematical link between facts on the actual object. The presence of an observable does not establish a matching, bound, or witness with a desired property. Techniques belong in Phase 4.</p>}
    {number === "3" && <p>Compare the best supported structural tensions before choosing a textbook move. The prospect is a question and proposed consequence, not yet an accepted implication.</p>}
    {number === "4" && <Table caption="Residual shapes and possible textbook moves" heads={["Retained shape", "Candidates to check", "Application obligations"]} rows={SELECTION_ROWS} />}
    {number === "5" && <p>For every output condition O, prove the conditional payoff from the complete branch and O. An intermediate lemma can be retained without counting it as a productive move. A surviving arm needs an exact next local analysis, with the terminal obligation recorded explicitly.</p>}
    {number === "6" && <p>Each task defines or proves one narrow result on the authorized objects. A new inference becomes its own obligation. EG formalization keeps the canonical ExactLedger and owner-local proof policy; discovery records do not carry proof facts.</p>}
    {number === "7" && <p>First combine new information with retained restrictions and revisit newly enabled local moves. Test constraint, compression, and quantity separately. Keep every surviving outcome on the full inherited branch; closing one sibling leaves the parent open.</p>}
    {number === "8" && <><Table caption="Proof artifacts to synchronize" heads={["Artifact", "Required verification"]} rows={ARTIFACT_ROWS} />
      <p>A checked open-boundary reduction describes where a counterexample could remain. It does not close those cases. For transformed objects, include the actual projection or transport in the reduction theorem.</p></>}
  </>;
}

const phases = Object.entries(taskflow.phase_descriptions) as [keyof typeof taskflow.phase_descriptions, (typeof taskflow.phase_descriptions)[keyof typeof taskflow.phase_descriptions]][];

export const EXECUTION_RECIPE_PARTS = [
  { id: "recipe-phase-zero", title: `0. ${taskflow.phase_zero.title}`, parent: "recipe", Content: PhaseZero },
  ...phases.map(([number, phase]) => ({
    id: `recipe-${workflow.stages.find(stage => String(stage.number) === number)?.id ?? number}`,
    title: `${number}. ${phase.title}`,
    parent: "recipe",
    Content: function Stage() { return <Phase number={number} />; },
  })),
];

export function TaskContract() {
  return <>
    <p>{workflow.rule}</p>
    <p>Identify the objects, match textbook hypotheses, carry out the deduction, and verify its output. Routine steps need concise justification. Review objections identify a concrete local defect; accepted prerequisites remain available at their stated domains.</p>
    <p><strong>Task, move, and branch have separate completion states.</strong> {taskflow.units.task} {taskflow.units.move} {taskflow.units.branch}</p>
    <p>The next assignment displays the exact residual, selected interaction, requested output, permitted inputs, and acceptance condition. It is selected from ready tasks in dependency order, with repair and integration ahead of unrelated exploration. An empty queue calls for a missing-dependency diagnosis.</p>
    <p>{taskflow.context_policy.inputs} {taskflow.context_policy.stop}</p>
    <p>{taskflow.context_policy.review} {taskflow.context_policy.admission}</p>
    <pre tabIndex={0} aria-label="Single task fields"><code>{taskflow.task_fields.join("\n")}</code></pre>
    <p>{taskflow.worker_instruction}</p>
    <TaskRunViewer />
  </>;
}
