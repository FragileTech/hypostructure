import type { ReactNode } from "react";
import { Latex } from "../graph-explorer";
import { ARTIFACT_ROWS, CLOSURE_CHECKLISTS, MOVE_RULES, SELECTION_ROWS } from "./recipe-reference";

// Editorial adaptation of repair_and_closure.md. The source coverage map is in web/README.md.
// Keep content independent of MethodologySection so its navigation can import these entries.
function Text({ children }: { children: string }) {
  // Only emphasis and code are editorial markup. Mathematics uses the site's existing reader.
  return <>{children.split(/(`[^`]+`|\*\*[^*]+\*\*|\*[^*]+\*)/g).map((part, index) => {
    if (part.startsWith("`")) return <code key={index}>{part.slice(1, -1)}</code>;
    if (part.startsWith("**")) return <strong key={index}><Latex value={part.slice(2, -2)} /></strong>;
    if (part.startsWith("*")) return <em key={index}><Latex value={part.slice(1, -1)} /></em>;
    return <Latex key={index} value={part} />;
  })}</>;
}

function Table({ caption, heads, rows }: { caption: string; heads: readonly string[]; rows: readonly (readonly string[])[] }) {
  return <div className="methodology-table-wrap recipe-table-wrap" tabIndex={0} role="region" aria-label={caption}>
    <table className="methodology-map recipe-table">
      <caption>{caption}</caption>
      <thead><tr>{heads.map(head => <th key={head} scope="col">{head}</th>)}</tr></thead>
      <tbody>{rows.map((row, index) => <tr key={index}>{row.map((cell, column) => column === 0
        ? <th scope="row" key={column}><Text>{cell}</Text></th>
        : <td key={column}><Text>{cell}</Text></td>)}</tr>)}</tbody>
    </table>
  </div>;
}

function Contract({ input, output, failure }: { input: string; output: string; failure: string }) {
  return <dl className="recipe-contract">
    <div><dt>Start with</dt><dd>{input}</dd></div>
    <div><dt>Required result</dt><dd>{output}</dd></div>
    <div><dt>If an obligation fails</dt><dd>{failure}</dd></div>
  </dl>;
}

function Template({ title, children }: { title: string; children: string }) {
  return <section className="recipe-template" aria-label={title}>
    <h5>{title}</h5><pre tabIndex={0} aria-label={`${title}: selectable text`}><code>{children}</code></pre>
  </section>;
}

function Establish() {
  return <>
    <Contract input="The first unresolved node, its incoming path, and the requested endpoint."
      output="One exact branch record with its full conjunction of facts and the obligation to prove."
      failure="Trace the missing input to its producer. Do not replace the branch by an easier projection or add an assumption." />
    <p>Read the directed proof graph and the node’s Requires entries. Separate the statement in the manuscript, the proposition actually implemented, and the current audit status. A citation to a later closure identifies a destination; it does not automatically supply an earlier hypothesis. Keep diagram-node numbers, invariant numbers, and dependency-table item numbers separate.</p>
    <p>Write the branch as its producer typed it. Retain standing hypotheses, the minimality order, every selected diamond outcome, quantitative bounds, and all constructed objects. A component, an inequality, or a family of locally admissible graphs is only part of that state. Facts that are harmless separately may contradict each other in conjunction.</p>
    <Latex className="methodology-display" value={String.raw`\[B=(H_0,\preceq,E,I,R,V,Q,A).\]`} />
    <Table caption="The record carried through every move" heads={["Field", "What to retain"]} rows={[
      ["Standing hypotheses and order", "The theorem hypotheses, counterexample assumption, fixed imported results, and the precise well-founded comparison."],
      ["Exclusions and invariants", "Every previously excluded exit and every positive fact, including counts, ranks, budgets, caps and exact ledger identities."],
      ["Residual and vocabulary", "The actual support, marks, receiver, peeling set, traces, witnesses, boundary profiles, response coordinates and realization domain."],
      ["Queue and evidence", "The exact obligation, every outstanding child, the intended consumers, and evidence for the transitions already made."],
    ]} />
    <p>For an analytic branch, retain normalization, gauge, topology, centres, scales and observer witnesses as well as bounds. A transformation may preserve an estimate while changing the representative to which the next statement applies. Prove the transport explicitly.</p>
    <Template title="Branch record">{`Node and manuscript label:
Requested endpoint:
Exact incoming proposition and active branch condition:
Standing hypotheses and fixed imports:
Minimality / progress order:
Inherited exclusions, invariants, quantitative accounts:
Selected objects and all their indices:
Exact outstanding proposition:
Previous moves and current child queue:
Sources for mathematics / implementation / status:`}</Template>
  </>;
}

function Inventory() {
  return <>
    <Contract input="The complete branch record and its previous move history."
      output="An inventory identifying concrete, present structural properties that earlier moves have not evaluated."
      failure="Mark an unavailable prerequisite as absent. Retain accounted facts as usable premises and inspect another unaccounted observable." />
    <p>Read the structural register row by row. Distinguish a property from its observable, a proof-state hypothesis, the technique that evaluates it, and the certificate returned. Use the problem’s registered property and technique vocabulary; the same inventory discipline applies across combinatorial, analytic and other structural arguments.</p>
    <p>An earlier estimate may have used a property globally while leaving a marked local incidence pattern unaccounted. Establish that difference precisely. “Same technique on a new name” is not novelty. Compare each candidate with rejected and completed attempts.</p>
    <Table caption="Structural inventory template" heads={["Property / observable", "Present as", "Accounted upstream?", "Technique and certificate"]} rows={[
      ["Registered property and exact observable", "Concrete set, number, order, relation or family on this branch; name its indices", "Node or previous attempt and what it evaluated, or the precise aspect not accounted", "Textbook move, its prerequisites, and the witnesses or typed outcomes it returns"],
    ]} />
    <p>Include the upstream quantitative accounts in this table. Do not let an appealing local picture erase hot-state counts, packing maximality, rank, demand assignments or absorption capacities. A hypothetical distinguishing context is a certificate about an attempted quotient; its paths do not become actual paths in the original graph.</p>
    <p>For example, vertex separation between marked origins and receivers evaluates a different observable from matching entries to essential incidences. Keep those networks separate in the inventory. The distinction permits checking a candidate; it does not establish that either linkage or separator closes the branch.</p>
    <Template title="Move-history comparison">{`Technique:
Exact observable and retained object:
Hypotheses used:
Upstream or rejected attempt with the same tuple:
What that attempt already evaluated:
Concrete unaccounted property targeted now:
Newly proved premise or corrected construction, if repairing an attempt:
Returned certificate and consumer for every outcome:`}</Template>
    <p>After an admitted split, update the inventory using the new typed data. An accounted fact remains available in every child that inherits it. Do not re-prove it, discard it, or treat the word “accounted” as a reason to stop.</p>
  </>;
}

function Selection() {
  return <>
    <Contract input="Present unaccounted structure, candidate textbook moves, and the complete attempt record."
      output="An admitted move with proved prerequisites and productive outcomes, selected for the structure it consumes."
      failure="Execute the required local construction first or choose another candidate. Do not announce a move on the strength of its intended conclusion." />
    <ol className="recipe-actions">
      <li>Write the textbook statement with its exact quantifiers. Match every hypothesis to evidence on the current branch. Disjoint returns, a shared window, a smaller representative, and a bounded table are prerequisites to prove, not descriptive names.</li>
      <li>Write each possible output and its consumer. Check locality, structural consumption, exact interfaces, and strict progress before admission. An unavailable cold-branch theorem cannot consume a hot-branch overlap merely because both are called overlaps.</li>
      <li>Among admitted candidates, prefer the move that evaluates the most unaccounted structure. Break ties toward constraint, then compression, then quantity. Do not select solely by how many register rows a theorem mentions.</li>
      <li>If closing power rests on a finite table, compute it at the actual parameters before selecting the move. A table with surviving patterns must have a proved structural consumer for every survivor.</li>
    </ol>
    <Table caption="Which currency does the configuration supply?" heads={["Currency", "Local proof obligations"]} rows={[
      ["Constraint", "Produce an actual target witness, a context distinguishing the exact responses, a rigidity contradiction, or an identification with an excluded exit."],
      ["Compression", "Construct the smaller representative; prove the boundary profile, baseline hypotheses and target response survive in every required context; then apply minimality."],
      ["Quantity", "Define distinct demands, eligible payers, a total canonical assignment, capacities and multiplicities. Prove no double counting before summing."],
    ]} />
    <Latex className="methodology-display" value={String.raw`\[|D|=\sum_{p\in P}|\pi^{-1}(p)|\le\sum_{p\in P}c(p).\]`} />
    <p>For exact demand and supply bounds, retain constants and strictness:</p>
    <Latex className="methodology-display" value={String.raw`\[an-b\le cn+d,\quad a>c\quad\Longrightarrow\quad(a-c)n\le b+d.\]`} />
    <p>The larger arm closes only when the bounds contradict each other. The bounded arm remains an obligation until its finite configurations are covered. Surplus, deficiency, rank, entropy and boundary mass cannot pay each other without a proved conversion.</p>
    <Table caption="Residual shape → textbook move → application checks" heads={["Retained shape", "Candidate moves", "What must be proved"]} rows={SELECTION_ROWS} />
    <p className="recipe-note">The table lists candidates, not automatic licences. Refined extremal choices belong at the step owning that choice and require an authorized repair; they are not a way to restart a later branch. A move already exhausted on the same observable remains exhausted.</p>
    <h5>The eighteen rules for choosing and executing a move</h5>
    <ol className="recipe-rules">{MOVE_RULES.map((rule, index) => {
      const [lead, ...items] = rule.split(/\n\s+- /);
      return <li key={index}><Text>{lead}</Text>{items.length > 0 && <ul>{items.map((item, i) => <li key={i}><Text>{item}</Text></li>)}</ul>}</li>;
    })}</ol>
  </>;
}

function Repair() {
  return <>
    <Contract input="The intended local proof, expanded into constructions and preservation obligations."
      output="An exhaustive repair at the first failed obligation, preserving successful continuations and the full state."
      failure="Re-inventory the retained obstruction. Admit a further split only if its negative arm has local data and a verified progress route." />
    <p>Locate the first unsupported step rather than a downstream symptom. Expand the intended proof into obligations <Latex value={String.raw`\(X_1,\ldots,X_m\)`} />. For each, ask: is its premise on this ledger, is it about the transferred object, and does the output remain in the consumer’s exact class?</p>
    <p>When a missing hypothesis is an admissible branch test, preserve the old proof on its positive side. On failure retain the first failed coordinate together with every successful earlier coordinate:</p>
    <Latex className="methodology-display" value={String.raw`\[\neg X_1\;\vee\;(X_1\wedge\neg X_2)\;\vee\;\cdots\;\vee\;(X_1\wedge\cdots\wedge X_{m-1}\wedge\neg X_m).\]`} />
    <Table caption="Admission checks for a repair" heads={["Check", "Evidence required"]} rows={[
      ["Refinement", "Every child satisfies the parent’s complete retained conditions; any change of representative has a proved transport."],
      ["Exhaustiveness", "Every parent object enters at least one child. Degeneracies and failed constructions are included."],
      ["Locality", "The new condition is on the retained object. A fact about a larger outside object may be recorded, but does not itself shrink this residual."],
      ["Consumption", "Name the unaccounted structural row and show precisely how the move evaluates or uses it."],
      ["Progress", "Every outcome closes, identifies with a closed row, or has a smaller typed residual with proved well-founded decrease."],
    ]} />
    <Latex className="methodology-display" value={String.raw`\[\llbracket B_i\rrbracket\subseteq\llbracket B\rrbracket,\qquad\llbracket B\rrbracket\subseteq\bigcup_i\llbracket B_i\rrbracket.\]`} />
    <p>A correct dichotomy alone is insufficient. Failure of either locality or consumption blocks admission, and passing both still requires progress. Splitting on “the desired lemma is false” can record an honest unfinished endpoint, but does not supply its closing construction.</p>
    <p>Keep the original step identity for the repaired decision and append new states. Preserve the statement consumed by existing descendants. Resolve shared preservation and cross-branch obligations once before duplicating work across constructors. Architectural repair ends when all routes are specified; a full-closure request additionally requires proving their local lemmas.</p>
    <Table caption="Recognize the repair being made" heads={["Defect", "Repair action"]} rows={[
      ["Estimate used without a hypothesis", "Insert the missing hypothesis test before first use; preserve the old argument on its valid arm."],
      ["Partial classification", "Prove the first-failure or repeat alternative exists, then cover every exceptional case."],
      ["State too small for transport", "At the owning step, retain the witnesses, topology or gauge the intended proof actually needs; prove the revised transport."],
      ["Opaque unproved implication", "Expand its construction and descend to the first local obligation with admissible positive and negative outcomes."],
    ]} />
  </>;
}

function Execute() {
  return <>
    <Contract input="The selected textbook move, proved prerequisites, exact objects, and consumers."
      output="A proved application constructing the actual certificates and all preservation facts."
      failure="Identify the first failed obligation, use all retained structure to repair the construction, and continue. Needing a local proof is an execution task." />
    <p>Build the witness the consumer actually accepts. The word “quotient” does not establish a boundary profile; “compression” does not establish strict decrease; “first separator” does not construct a registered switch reading. Match support, receiver, marks, peeling set, response pieces and realization domain exactly, or prove transport before use.</p>
    <Table caption="Execution record for one move" heads={["Field", "Required evidence"]} rows={[
      ["Unaccounted structure", "Property IDs, exact observable, and comparison with all earlier attempts."],
      ["Textbook move", "Its exact statement and the branch facts proving each hypothesis."],
      ["Construction", "Actual graph paths, representatives, assignments or analytic witnesses, with their defining properties proved."],
      ["Preservation", "Same interface and degree fibre; baseline and target conditions; every account, representative and invariant needed downstream."],
      ["Exhaustive outcomes", "All arms, including shared segments, degenerate objects, equality cases and failed identifications."],
      ["Consumers", "All hypotheses of a closed row, or invariant preservation and strict decrease for a smaller typed residual."],
      ["Finite certification", "A complete generator, a coverage proof, the actual parameter bounds, and a terminal certificate for every generated case."],
    ]} />
    <h5>Five execution checks for any local construction</h5>
    <ol className="recipe-actions">
      <li><strong>Check history before retrying.</strong> Compare technique, observable, retained object and hypotheses. A corrected attempt needs a specific repaired construction or newly proved premise.</li>
      <li><strong>Keep the exact objects.</strong> A target-completeness claim about two registered response pieces does not compare a full support with an arbitrary replacement. Packages indexed by different conditions do not share exclusions automatically. Newly exposed boundary edges are not automatically part of the original supply, and marked origins retain their demands. Properties of one realized object do not constrain every member of a realization family without proof.</li>
      <li><strong>Prove the local application.</strong> Construct all fields and verify them before committing a transition. “This needs a lemma” names work to perform; it is not a completed result or a reason to switch to a feasibility discussion.</li>
      <li><strong>Consume every complementary outcome.</strong> A Menger linkage–separator split without consumers, or a theta table with survivors, has not reduced the branch. A smaller table or fewer unaccounted rows is not automatically a decreasing residual measure.</li>
      <li><strong>Keep status exact.</strong> Distinguish candidate, proved local implication, admitted reduction and closed branch. A smaller residual goes onto the queue. Full closure requires discharging that queue.</li>
    </ol>
    <p>For replacements, compare the actual glued object with the original in the declared order. For entropy, verify the state map’s domain, joint realizability, relabeling invariance when used, and that the saved information is not already charged elsewhere. For a handoff, construct the actual separated tails and all admission fields; a structural resemblance is insufficient.</p>
    <p>Do not manufacture positive geometry from failure certificates. A cycle in a hypothetical distinguishing context constrains the comparison that produced it. It is not an additional cycle in the selected graph, and counting such certificates does not count distinct actual channels.</p>
    <p>A private verdict that a branch is impossible has no evidential standing and must not determine move selection. Do not invoke a user-specified fallback early: verify and record its required exhaustion conditions first. At an obstacle, the next operation is the retained-state inventory and the next admissible local construction.</p>
  </>;
}

function Outcomes() {
  return <>
    <Contract input="The proved local implication with every possible outcome exposed."
      output="A terminal certificate for each arm, or a proved recursive step whose children remain on the execution queue."
      failure="Keep the exact surviving state and execute its next admissible move. Do not rename an uncovered case as a known exit." />
    <Table caption="How an outcome is discharged" heads={["Outcome", "Certificate", "Remaining work"]} rows={[
      ["Direct contradiction", "An actual target witness or incompatible retained facts", "Publish and consume the contradiction on this arm."],
      ["Identification", "The complete input of an already closed row, including its declared witnesses", "Apply that row on the exact branch; a destination name alone is not enough."],
      ["Strict descent", "A smaller typed object, preserved invariants and accounts, and a well-founded measure", "Execute every recursive child and prove the base cases."],
      ["Terminal table", "Coverage of the bounded configuration and a closure certificate for every case", "Consume survivors structurally; a computation with unexplained survivors is unfinished."],
      ["Uncovered implication", "The exact retained input and negation of the missing proposition", "Record an open obligation, expose its first construction failure, and continue the recipe."],
    ]} />
    <p>A peeling loop needs both descent and restoration of its invariants. In the exit-(4) example,</p>
    <Latex className="methodology-display" value={String.raw`\[\Lambda_4=\sum_w|\mathcal L(w)\setminus P_4(w)|\]`} />
    <p>decreases by one per peel. Prove the exact charge update as well. The graph, windows, boundary profiles and target constraints stay attached. Termination of this bookkeeping loop does not prove the receiving ledger can pay its obligations.</p>
    <p>For quantitative transitions record constants and multiplicities, not just arrows. If a demand is split across children, state the aggregate estimate and bound overlap; compute the final constant from the terminal estimates. Preserve the positive slack of every independent squeeze used by the proof.</p>
    <Template title="Outcome and queue record">{`Parent node and full retained state:
Exhaustive arm conditions:
For each arm:
  Actual output witnesses and preserved indices:
  Structural rows consumed:
  Terminal certificate / exact closed consumer:
  OR child residual, measure before and after, strict-decrease proof:
  Preserved invariants, charge updates and multiplicity:
  Next local obligation and its prerequisites:
Base cases:
Outstanding queue after this step:
Parent closes only when every child is discharged.`}</Template>
    <p>An open residual is not a counterexample. If counterexample construction is the requested alternative, supply an actual object and verify the theorem hypotheses and failure of the target. Neither an unresolved proof obligation nor an admissible local pattern establishes that endpoint.</p>
  </>;
}

function Verify() {
  return <>
    <Contract input="The complete executed branch tree and its certificates."
      output="All reachable arms discharged, all required proof artifacts synchronized, and the requested implementation checks passed."
      failure="Keep the first exact failed obligation on the queue and repair it. Passing a build cannot replace proving the intended statement." />
    <p>Check the branch as a whole. A route with a named consumer establishes architectural coverage only. Mathematical closure requires the edge proofs and terminal certificates; kernel verification also requires that the formal propositions match the manuscript and use the permitted ledger. Passing one check does not imply the others.</p>
    <Table caption="Artifacts to synchronize after a proved repair" heads={["Artifact", "Update and verification"]} rows={ARTIFACT_ROWS} />
    <h5>Six checklists for execution and review</h5>
    <div className="recipe-checklists">{CLOSURE_CHECKLISTS.map(group => <section key={group.source} aria-label={group.title}>
      <h5>{group.title}</h5>
      <ul>{group.items.map((item, index) => <li key={index}><Text>{item}</Text></li>)}</ul>
    </section>)}</div>
    <details className="recipe-details"><summary>Implementing the recipe in a typed proof system</summary>
      <p>Read the active residual and established facts through the proof system’s canonical state. Construct the selected mathematical object locally in its owning step, publish the exact proposition under its declared key, and retain inherited facts. A side callback or detached certificate is not a substitute for the incoming state.</p>
      <p>An exhaustive decision extends the ledger separately on each arm. A returned non-False residual records unfinished work even if the term elaborates. Closure must consume an actual contradiction or an already established incompatibility. Check the mathematical statement, publication schema, wiring, ancestry and kernel result independently.</p>
      <p>Respect the authorized scope of the formal development. Do not weaken valid mathematics to make transport compile. The same separation between proposition, state carrier, execution and audit applies in any proof assistant.</p>
    </details>
  </>;
}

function Example({ title, children }: { title: string; children: ReactNode }) {
  return <details className="recipe-details"><summary>{title}</summary>
    {children}
  </details>;
}

const EXECUTOR_PROMPT = `Execute structural exhaustion on the selected open branch.

1. Scope. Work only within the authorized files and proof scope. Fix the requested endpoint. Keep project instructions separate from mathematical hypotheses.

2. Object. Copy the producer’s exact typed residual and every inherited fact. Keep selected supports, receivers, peeling sets, witnesses, response pieces and realization domains fixed unless transport is proved. Do not replace the branch by a projection or an “equivalent” inequality.

3. Hypotheses. Use only retained facts, fixed imports and textbook material. Do not assume a missing premise. Prove its local construction or consider an admissible first-failure split with consumers for both arms.

4. Inventory. List present properties, exact observables, upstream consumers, unaccounted structure, enabled techniques and prerequisite evidence. Include quantitative accounts. Hypothetical failure certificates do not become positive geometry in the original object.

5. Selection. Compare every candidate with upstream, rejected and unimplemented attempts using (technique, observable, object, hypotheses). Among admitted candidates select the move consuming the most unaccounted structure. Compute a proposed terminal table at the actual parameters before relying on it.

6. Execution. Implement the textbook move, construct its actual witnesses and prove all preservation claims. Execute all outcomes. At a failed obligation, inventory the retained obstruction and continue. A smaller residual is an intermediate obligation; discharge its children and base cases before reporting full closure.

7. Discipline. Do not repeat exhausted moves, re-prove settled upstream facts, change the object, reselect an upstream extremal choice, or substitute a feasibility discussion, no-go report or whole-residual search for local execution. An accounted fact is available data, not a stop sign. Do not invoke a user-specified fallback before its required exhaustion conditions have been verified and recorded.

8. Claims. Distinguish candidate, proved local implication, admitted reduction and closed branch. Every admitted arm needs a verified closure route or a typed residual with proved strict decrease. Remove rejected moves from the active proof and retain one inventory sentence explaining the rejection. A table with survivors or a split without consumers is not a reduction.

9. Reporting. Record the exact object, consumed rows, every arm’s certificate or measure, and the next obligation with its prerequisites. Update the diagram, dependencies, ledgers and audit tables from evidence. An open residual or successful build is not full closure; a counterexample requires an actual verified object.

10. Persistence. Execute the authorized queue until every requested branch is closed. Do not stop at “a local lemma is needed”, a plan, or a promise. If interrupted, preserve the exact unfinished queue. Correct a deviation in the work record before continuing.`;

function GenericPractice() {
  return <>
    <p>These abstract exercises show how to apply the recipe without relying on a particular theorem, proof graph or implementation status. For each one, identify the retained object, the failed hypothesis, the structural certificate, and the exact consumer of every outcome.</p>
    <Template title="Seven-field repair report">{`What failed:
The exact hypothesis exposed:
The exhaustive dichotomy inserted:
What each residual carries:
Closing moves and certificates for every arm:
Inherited statements and accounts preserved:
Where the proof, dependencies and status are recorded:`}</Template>
    <Example title="Exactify an asymptotic estimate">
      <p><strong>Input.</strong> A bound is written with an unspecified “sufficiently large” condition, although the branch carries exact integer quantities.</p>
      <p><strong>Move.</strong> Rewrite the condition as an exact integer inequality. The positive arm preserves the original estimate; the negative arm gives a concrete amount of mass, deficit or obstruction that the next ledger can consume.</p>
      <p><strong>Checks.</strong> Prove the rearrangement, retain the exact quantities, and route every size regime. The lower-bound residual is useful only when a later move has a certified capacity comparison.</p>
    </Example>
    <Example title="Repair an independence or realization claim">
      <p><strong>Input.</strong> Several local states are individually realizable, but their joint product has not been proved.</p>
      <p><strong>Move sequence.</strong> Test the joint fiber in exposure order. On success, prove the savings add in the declared class. On failure, retain the first failing fiber and its complete outside record, extract a minimal connected overlap obstruction, and construct the actual serial or replacement object before applying arithmetic.</p>
      <p><strong>Checks.</strong> Do not infer joint realization from separate realizations. Charge overlap once, preserve the boundary interface, and give every arithmetic or periodic alternative an actual object-level consumer.</p>
    </Example>
    <Example title="Peel while preserving the account">
      <p><strong>Input.</strong> Some loads, coordinates or witnesses have been routed to a special branch but are still included in an ordinary charge.</p>
      <p><strong>Move.</strong> Define the exact peel set, remove one eligible item, prove the ledger update, and decrease a nonnegative integer measure. Restore every graph, state, boundary and target invariant after the peel.</p>
      <p><strong>Complementary arm.</strong> If the rate or capacity test fails, publish the exact demand and absorption ledgers. Termination of the peel is not payment; the residual remains on the queue until a consumer is proved.</p>
    </Example>
    <Example title="Identify an excluded alternative">
      <p><strong>Input.</strong> The branch excludes a named alternative, and the retained data appear to contain its defining witness.</p>
      <p><strong>Construction.</strong> Read the witness from the branch, verify every interface field and preservation condition, and prove the produced object satisfies the alternative’s definition.</p>
      <p><strong>Terminal.</strong> Only the exact identification closes. A similar-looking object or a witness reconstructed from another family does not satisfy the consumer.</p>
    </Example>
    <Example title="Prove that a first failure exists">
      <p><strong>Input.</strong> A corridor or finite-state procedure is classified by its first boundary event, but existence of that event was only assumed.</p>
      <p><strong>Move.</strong> Prove either that the boundary is reached within the stated bound or that two retained states repeat. Route the target hit, defect, compression, handoff and bounded exceptional configuration separately.</p>
      <p><strong>Checks.</strong> Prove silent compression in every compatible context, handle equality cases with their own table, and consume table survivors structurally.</p>
    </Example>
    <Example title="Preserve observers and representatives across transitions">
      <p><strong>Input.</strong> A proof step keeps a numerical estimate but discards the observer, gauge, topology or representative needed by the next step.</p>
      <p><strong>Move.</strong> Extend the branch state with the missing witness or normalize and recenter before applying the continuation. Split concentration, translation, scale, profile and gauge failures as separate typed outcomes.</p>
      <p><strong>Checks.</strong> Prove the transport of every retained resource and close the lost-kernel or escape alternative independently. A successful estimate alone does not identify the object to which the next theorem applies.</p>
    </Example>
    <h5>Executor prompt</h5>
    <p>Use this prompt with the eight stages and their evidence checks. It is a reusable operating procedure, not a proof-specific status report.</p>
    <Template title="Reusable executor prompt">{EXECUTOR_PROMPT}</Template>
    <details className="recipe-details"><summary>Glossary and source guide</summary>
      <Table caption="Terms used by the recipe" heads={["Term", "Meaning"]} rows={[
        ["Branch state", "The complete accumulated context and selected objects, not a projection of their properties."],
        ["Semantic region", "All objects satisfying every condition retained on the branch."],
        ["Consumer", "A registered step accepting the exact produced proposition and witnesses."],
        ["Both-sides test", "Admission requires productive positive and negative outcomes with proved application prerequisites."],
        ["Output interface", "The explicit facts downstream steps may read; repair preserves this interface."],
        ["First failure", "The earliest failed construction obligation, retained with all earlier successful obligations."],
        ["Currency", "Constraint, compression or quantity, with proved conversions and no double charging."],
        ["Leaf totality", "Every output has a closure certificate or belongs to the domain of another registered step. An open queue still requires execution."],
        ["Full closure", "Every reachable arm is proved closed and all required implementation and wiring checks pass."]
      ]} />
      <p>The recipe is adapted from the repair-and-closure manual. Its examples are intentionally abstract; the mathematical statement, implementation carrier and status record for a particular application belong to that application’s own sources.</p>
    </details>
  </>;
}

export const EXECUTION_RECIPE_PARTS = [
  { id: "recipe-branch", title: "1. Establish the branch", parent: "recipe", Content: Establish },
  { id: "recipe-inventory", title: "2. Inventory unused structure", parent: "recipe", Content: Inventory },
  { id: "recipe-selection", title: "3. Select an admissible move", parent: "recipe", Content: Selection },
  { id: "recipe-repair", title: "4. Repair the first failed obligation", parent: "recipe", Content: Repair },
  { id: "recipe-execute", title: "5. Execute the construction", parent: "recipe", Content: Execute },
  { id: "recipe-outcomes", title: "6. Discharge every outcome", parent: "recipe", Content: Outcomes },
  { id: "recipe-verify", title: "7. Verify and record closure", parent: "recipe", Content: Verify },
  { id: "recipe-practice", title: "8. Worked repairs and templates", parent: "recipe", Content: GenericPractice },
] as const;
