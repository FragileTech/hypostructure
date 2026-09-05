import type { ReactNode } from "react";
import { Link } from "react-router-dom";
import { Latex } from "../graph-explorer";
import { propertyAnchor, techniqueAnchor, type PropertyId, type TechniqueId } from "../structural-survey/data";
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

function Coordinate({ id, kind }: { id: PropertyId | TechniqueId; kind: "property" | "technique" }) {
  const target = kind === "property" ? propertyAnchor(id as PropertyId) : techniqueAnchor(id as TechniqueId);
  return <button type="button" className={`survey-coordinate is-${kind}`} aria-label={`Recipe: go to ${kind} ${id}`}
    onClick={() => document.getElementById(target)?.scrollIntoView({ behavior: "smooth", block: "center" })}>{id}</button>;
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
    <p>For a PDE branch, retain normalization, gauge, topology, centres, scales and the observer witnesses as well as bounds. A rescaling may preserve an estimate while changing the representative to which the next statement applies. Prove the transport explicitly.</p>
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
    <p>Read the structural register row by row. Distinguish a property from its observable, a proof-state hypothesis, the technique that evaluates it, and the certificate returned. The graph register supplies A01–I06 and T01–T19; apply the corresponding domain vocabulary for other subjects.</p>
    <p>An upstream estimate may have used a property globally while leaving a marked local incidence pattern unaccounted. Establish that difference precisely. “Same technique on a new name” is not novelty. Compare each candidate with withdrawn and unimplemented attempts as well as completed nodes.</p>
    <Table caption="Structural inventory template" heads={["Property / observable", "Present as", "Accounted upstream?", "Technique and certificate"]} rows={[
      ["Registered property and exact observable", "Concrete set, number, order, relation or family on this branch; name its indices", "Node or previous attempt and what it evaluated, or the precise aspect not accounted", "Textbook move, its prerequisites, and the witnesses or typed outcomes it returns"],
    ]} />
    <p>Include the upstream quantitative accounts in this table. Do not let an appealing local picture erase hot-state counts, packing maximality, rank, demand assignments or absorption capacities. A hypothetical distinguishing context is a certificate about an attempted quotient; its paths do not become actual paths in the original graph.</p>
    <p>For example, vertex separation between four marked origins and the original receivers evaluates a different observable from matching entries to essential incidences. The graph linkage uses <Coordinate id="B04" kind="property" /> and <Coordinate id="T14" kind="technique" />. That distinction permits checking the candidate; it does not establish that either linkage or separator closes the branch.</p>
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
    <p className="recipe-note">The table lists candidates, not automatic licences. Refined extremal choices belong at the node owning that choice and require an authorized repair; they are not a way to restart a downstream branch. A move already exhausted on the same observable remains exhausted.</p>
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
    <p>Keep the original node number for the repaired decision and append new nodes. Preserve the statement consumed by existing descendants. Resolve shared preservation and cross-branch obligations once before duplicating work across constructors. Architectural repair ends when all routes are specified; a full-closure request additionally requires proving their local lemmas.</p>
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
    <h5>Five checks learned from the node [185] attempt</h5>
    <ol className="recipe-actions">
      <li><strong>Check history before retrying.</strong> Compare technique, observable, retained object and hypotheses. A corrected attempt needs a specific repaired construction or newly proved premise.</li>
      <li><strong>Keep the exact objects.</strong> Q1 target-completeness compares its two registered response pieces. It does not compare the full support with an arbitrary fold. Empty-peeling and current-peeling packages do not share no-exit facts automatically. Separator edges are not original boundary supply, and marks on the separator keep their demands. Actual-graph properties do not constrain every realization-family member without proof.</li>
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
    <details className="recipe-details"><summary>Implementing the recipe through the Lean ledger</summary>
      <p>Read the active residual and established facts through the sealed ledger inputs. Construct the selected mathematical object locally in its owning executor, publish the exact proposition under its declared key, and retain the inherited facts. A side callback or detached certificate is not a substitute for the incoming ledger.</p>
      <p>An exhaustive decision extends the ledger separately on each arm. A returned non-False residual records unfinished work even if the term elaborates. Closure must consume an actual contradiction or an already established incompatibility. Check the mathematical statement, publication schema, wiring, ancestry and kernel result independently.</p>
      <p>Respect the authorized edit scope. The project’s one-label implementation discipline determines the local unit of repair; a full-branch request still requires all authorized descendant obligations. Do not weaken valid mathematics to make transport compile. Consult the live API and audit tables before copying historical declaration names.</p>
      <p><Link to="/lean/ledger">Read the ExactLedger documentation</Link>{" · "}<Link to="/lean/writing-facts">Writing facts</Link>{" · "}<Link to="/lean/closing">Closing a branch</Link>{" · "}<Link to="/lean/assembly">Assembling the proof</Link></p>
    </details>
  </>;
}

function Example({ title, status, steps = [], children }: { title: string; status: string; steps?: string[]; children: ReactNode }) {
  return <details className="recipe-details"><summary>{title}</summary>
    <p className="recipe-example-status"><strong>Reading status:</strong> {status}</p>
    {children}
    {steps.length > 0 && <p className="methodology-steps">{steps.map(step => <Link className="chip chip-node" key={step} to={`/erdos-gyarfas/explore?step=${step}`} title={`Open step [${step}]`}>{step}</Link>)}</p>}
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

function Practice() {
  return <>
    <p>The cases below are worked readings of the source document. Their purpose is to show the exact input, move and evidence required. Historical proof plans and incomplete formalizations are labelled as such; a construction proposed in a repair history is not thereby a closed branch.</p>
    <Template title="Seven-field repair report">{`What failed:
The exact hypothesis exposed:
The exhaustive dichotomy inserted:
What each residual carries:
Closing moves and certificates for every arm:
Inherited statements and accounts preserved:
Where the proof, dependencies and status are recorded:`}</Template>
    <Example title="Exactify an asymptotic collision — [173]–[177]" status="Manuscript repair example; the arrows below describe its stated routing, not a new kernel-check claim." steps={["173", "175", "176", "177"]}>
      <p><strong>Input and failure.</strong> A net-charge collision used asymptotic allowances and appeared to require a sufficiently large graph. The branch already carried exact window counts and surplus values.</p>
      <Latex className="methodology-display" value={String.raw`\[15p_{13}+\sigma_W-\sigma_R<\tfrac14(n-13p_{13}),\qquad p_{13}=|\mathcal P_{\rm hot}|+C.\]`} />
      <p><strong>Split and negative data.</strong> Test this exact inequality. Its positive arm uses the existing collision. Its negative arm gives</p>
      <Latex className="methodology-display" value={String.raw`\[C\ge\frac{n-73|\mathcal P_{\rm hot}|-4(\sigma_W-\sigma_R)}{73}.\]`} />
      <p><strong>Consumers.</strong> On the branch where this forces cold mass, inspect the actual first-failure support. A subcubic support must supply the declared cold configuration. A high-degree centre must supply two distinct separated connector tails before the Type B ledger can accept it. Retain the old positive continuation and prove that each discarded incidence is charged only once.</p>
    </Example>
    <Example title="Repair a realization claim — [158]–[168]" status="Manuscript repair example; every cap substitution and finite-table survivor still needs the stated application evidence." steps={["158", "160", "163", "167", "168"]}>
      <p><strong>Input and split.</strong> Joint realization of window states in labelled near-cubic skeletons was an unsupported sentence. Test that realization on its declared family. Keep the original continuation on the positive arm and the precise failed-realization count on the negative arm.</p>
      <p><strong>Move sequence.</strong> Test the deficiency cap and the separate private-carrier rate. Reuse a continuation only after checking that these are exactly the quantities it reads. Neutral equal-length configurations then require a canonical replacement or a symmetric strand pair. A refined order is justified at its owning choice by preserving every earlier strict size comparison.</p>
      <p><strong>Finite and structural checks.</strong> The source’s two-strand table at parameters 13 and 40 has 96 hits among 533 configurations. That count is not closure. The stated survivor exclusion uses actual attachment incidences: the symmetric pair requires two external stubs, while the selected interior window vertices have only one. Prove the configurations are the selected ones before using this contradiction.</p>
    </Example>
    <Example title="Retain the first failing fibre — [169]–[172]" status="Intended manuscript continuation with an explicit graph-realization obligation. Arithmetic alone does not certify the entire route." steps={["169", "170", "171", "172a", "172b", "172c"]}>
      <p><strong>Input.</strong> Window completions may overlap, so separate state counts do not imply a joint product bound. Test conditional fibre bounds in their exposure order.</p>
      <p><strong>Positive arm.</strong> Prove the savings add in the declared near-cubic class, then compare its code length with the skeleton budget. Verify that the same information was not already counted elsewhere.</p>
      <p><strong>Negative arm.</strong> Retain the first failing scale, barrier, outside record, exposed prefix and fibre. Extract a cardinality-minimal connected overlap obstruction; prove connectivity by component concatenation. Construct the actual serial system before applying sumset arithmetic. Its paths, disjointness, increment bounds and realized cycles must all belong to the retained graph.</p>
      <p><strong>Closing check.</strong> Use the full modulus and residue-specific range. Charge each overlap once to its minimal connected support. A theorem about abstract serial arithmetic does not fill a missing graph construction.</p>
    </Example>
    <Example title="Peel without losing the account — [101], [123], [181]" status="Descent and routing example. The failed-rate residual and its descendants remain separate closure obligations." steps={["101", "123", "181"]}>
      <p><strong>Failure.</strong> A routed load used by a target-defective quotient was also counted as ordinary Type A charge. Introduce the exact peeling set before summing unpeeled loads.</p>
      <p><strong>Execution.</strong> Remove one eligible load from the unpeeled account, retain its declared exit witness, prove the quarter-unit charge update, and decrease the nonnegative integer measure by one. Restore all graph, packing, response and target invariants after every peel.</p>
      <p><strong>Complementary arm.</strong> If the reduced-rate test fails, publish the exact demand, absorption, blocker and stage ledgers. Do not assume the open burden is sublinear. A termination proof does not pay the receiving ledger; the failed-rate branch stays on the queue.</p>
    </Example>
    <Example title="Identify an already excluded exit — [124]" status="Local identification pattern. It applies only to the exact witness and exit-free branch described here." steps={["124"]}>
      <p><strong>Input.</strong> A true route-8 entry has the required essential carriers and a declared carrier-deletion witness, while its branch excludes exit (4).</p>
      <p><strong>Construction.</strong> Select an essential carrier, read its declared deletion witness, and prove that the resulting quotient belongs to the canonical exit-(4) family for the same receiver.</p>
      <p><strong>Terminal.</strong> The constructed witness realizes precisely the excluded exit. The contradiction uses both conjuncts of the retained entry. A similar-looking arbitrary deletion or a reconstructed witness from another family does not satisfy this consumer.</p>
    </Example>
    <Example title="Prove first failure exists — [145]–[157]" status="Manuscript classification example; its bounded and equal-length cases require the stated tables." steps={["145", "150", "157"]}>
      <p><strong>Input.</strong> Failure of the hot cap leaves cold mass and actual corridors. Prove that a corridor reaches the successor stub within the state bound or repeats a state; do not assume a first failure exists.</p>
      <p><strong>Routing.</strong> The source distinguishes an actual target hit, a target defect, a proper target-complete compression, a declared handoff, and a bounded configuration. For silent compression prove all-context response preservation and strict size decrease. Equal-length exchanges need their separate same-interface table.</p>
      <p><strong>Exception check.</strong> The interval of 13 offsets avoids 4, 8, 16 and 32 only at lengths 17, 18 and 19 within the stated bound. These survivors are explicit cases to consume, not an excuse to run a larger unrelated enumeration.</p>
    </Example>
    <Example title="Reopen exact negated implications — [178]–[182]" status="Open residual and historical repair plan. The proposed constructors are not presented as implemented closures." steps={["178", "179", "180", "182"]}>
      <p><strong>Retained alternatives.</strong> The three failures concern conditional factorization of the graph skeleton model, exhaustive routing of the actual pair-return package, or arithmetic/periodic coverage of the graph-realized serial system. Keep the corresponding input with each negated implication.</p>
      <p><strong>Proposed repair order.</strong> Expand factorization into the precise baseline family, joint realization and reconstruction obligations. For uncrossing, check the actual returns, overlap support, and graph realization of every claimed alternative. For arithmetic, check the exact increment spectrum and full-modulus hypotheses. At each first failure, admit a local split only after proving its negative consumer or strict descent.</p>
      <p><strong>Boundary.</strong> The source’s constructor plans organize remaining work. Definitions of coordinates, a drawn repair graph or a successful typecheck do not prove those obligations. Preserve the exact open state until each construction and complementary case is discharged.</p>
    </Example>
    <Example title="Use the full pressure ledger — historical [181] plan" status="Historical proposal and plan repair, not a current closure certificate." steps={["181", "183", "184", "185"]}>
      <p><strong>Input.</strong> Keep the entry family, receivers, essential cores, declared deletion witnesses, trace basins, peel chain, maximal demand and absorption assignments, blockers and failed reduced-rate test. The residual is not merely a subcubic component with high density.</p>
      <p><strong>Consumer audit.</strong> Compare the exact burden forced by those ledgers with the offered consumer’s hypotheses. If incompatible, do not keep trying the same rate estimate. Inventory the structural information not yet used, including the incidence pattern of the actual marked family.</p>
      <p><strong>Historical O7 proposal.</strong> The document proposed a two-support exclusion and later recorded repairs to that plan. Hypothetical deletion contexts do not supply actual distinct channels, and a Hall obstruction does not automatically satisfy a cold serial-system theorem. Verify each missing application on the retained branch before promoting any proposal to a transition.</p>
    </Example>
    <Example title="Reject activity that does not reduce the branch — [185]" status="Rejected closure attempts. These examples explain execution checks; they do not close [185]." steps={["185"]}>
      <p><strong>Theta extraction.</strong> A correct local enumeration left surviving patterns and supplied no terminal consumer. It did not reduce the outstanding obligation. Check the table’s closing power before announcing a move.</p>
      <p><strong>Vertex fold.</strong> A smaller folded support was compared with the original graph, while retained Q1 target-completeness concerned two different registered response pieces. The required identification was absent. Match the consumer’s exact objects before applying minimality.</p>
      <p><strong>Menger.</strong> A linkage–separator lemma evaluated an unaccounted observable but left both kinds of output without closure continuations. Prove the consumers and preserve all marked loads, including those on the separator. A correct auxiliary lemma is not yet an admitted reduction.</p>
    </Example>
    <Example title="Preserve observers, budget regimes and analytic kernels" status="Examples from the methodology’s graph and PDE repair history; each illustrates a specific retained-state obligation." steps={["19", "125", "144"]}>
      <p><strong>Observer compactness.</strong> A profile-only state cannot guarantee that observer witnesses stay in a compact cylinder. The Type I repair retains the observation data and separates density and event-balance outcomes, including the sparse branch, before reusing the successor argument.</p>
      <p><strong>Budget regime.</strong> A graph-counting budget valid on the near-cubic spine needs that hypothesis before its first use. The surplus branch must actually produce the same spine estimate consumed by the main line; naming a surplus exception does not suffice.</p>
      <p><strong>Stokes kernel.</strong> Smooth vorticity does not identify velocity: a divergence-free, curl-free field may remain. The local example <Latex value={String.raw`\(u=a(t)e_1,\ p=-a'(t)x_1\)`} /> shows why curl alone loses information. The finite-energy argument must eliminate the kernel separately, using the expanding-ball estimate, before recovering the pressure tail.</p>
    </Example>
    <h5>Executor prompt</h5>
    <p>This prompt adapts the repository instructions to the authorized scope of the current proof. Use it with the eight stages and their evidence checks, rather than as a substitute for them.</p>
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
        ["Full closure", "Every reachable arm is proved closed and all required implementation and wiring checks pass."],
      ]} />
      <p>Source: <code>repair_and_closure.md</code>, especially §§4.7–4.10, 5, 10–13. The structural register below supplies the property and textbook-technique vocabulary. The worked examples draw on §§6–8; their historical proposals are not live implementation status. Mathematical statements belong to the manuscripts, implementation evidence to the actual declarations, and EG status to the live audit tables.</p>
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
  { id: "recipe-practice", title: "8. Worked repairs and templates", parent: "recipe", Content: Practice },
] as const;
