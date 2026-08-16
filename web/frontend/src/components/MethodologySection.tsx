import { useEffect, useState, type ReactNode } from "react";
import { Link } from "react-router-dom";

import { Latex } from "../graph-explorer";
import { findProof } from "../proofs/registry";

/** The parts of the account, in reading order; the rail is built from this. */
export const METHODOLOGY_PARTS = [
  { id: "philosophy", title: "Structure has a cost" },
  { id: "constraint", title: "Cost as constraint: the invariant ladder", parent: "philosophy" },
  { id: "quantity", title: "Cost as quantity: structural accounting", parent: "philosophy" },
  { id: "compression", title: "Cost as compression: repetition and exact types", parent: "philosophy" },
  { id: "llm", title: "Designed to leverage language models" },
  { id: "mechanisms", title: "Leveraging what language models do best", parent: "llm" },
  { id: "controls", title: "Mitigating the usual failure modes", parent: "llm" },
  { id: "artifacts", title: "The artifacts: diagrams and tables" },
  { id: "repair", title: "Red-teaming and repair" },
  { id: "moves", title: "The proof moves" },
  { id: "iteration", title: "One iteration of the method" },
  { id: "proofs", title: "In the two proofs" },
  { id: "progression", title: "In one line" },
] as const;

type PartId = (typeof METHODOLOGY_PARTS)[number]["id"];

/** The element id a part is anchored at. */
export function partAnchor(id: PartId): string {
  return `methodology-${id}`;
}

/** A part's parent, when it is a subsection of another part. */
function parentOf(id: PartId): PartId | undefined {
  const part = METHODOLOGY_PARTS.find((entry) => entry.id === id)!;
  return "parent" in part ? part.parent : undefined;
}

function Part({ id, children }: { id: PartId; children: ReactNode }) {
  const part = METHODOLOGY_PARTS.find((entry) => entry.id === id)!;
  const nested = parentOf(id) !== undefined;
  return (
    <article className={nested ? "methodology-part is-nested" : "methodology-part"} id={partAnchor(id)}>
      {nested ? <h4>{part.title}</h4> : <h3>{part.title}</h3>}
      {children}
    </article>
  );
}

/**
 * Which part is in view, for the rail. Read from the scroll position rather
 * than an IntersectionObserver so it is deterministic and works in jsdom: the
 * current part is the last one whose top has passed the reading line.
 */
function useCurrentPart(): PartId {
  const [current, setCurrent] = useState<PartId>(METHODOLOGY_PARTS[0].id);

  useEffect(() => {
    const line = 120; // px from the top of the viewport, below the sticky header
    const update = () => {
      let found: PartId = METHODOLOGY_PARTS[0].id;
      for (const part of METHODOLOGY_PARTS) {
        const element = document.getElementById(partAnchor(part.id));
        if (element && element.getBoundingClientRect().top <= line) found = part.id;
      }
      setCurrent(found);
    };
    update();
    window.addEventListener("scroll", update, { passive: true });
    window.addEventListener("resize", update);
    return () => {
      window.removeEventListener("scroll", update);
      window.removeEventListener("resize", update);
    };
  }, []);

  return current;
}

/**
 * The rail beside the account, hung in the page's left margin so the text keeps
 * its width; on a viewport too narrow for that margin it becomes a row of chips
 * above the text. Buttons rather than `href="#…"` links, because the site's
 * hash router would read the fragment as a route.
 */
function RailButton({ id, title, current }: { id: PartId; title: string; current: PartId }) {
  return (
    <button
      type="button"
      className={id === current ? "is-current" : undefined}
      aria-current={id === current ? "true" : undefined}
      onClick={() =>
        document.getElementById(partAnchor(id))?.scrollIntoView({ behavior: "smooth", block: "start" })
      }
    >
      {title}
    </button>
  );
}

function MethodologyRail() {
  const current = useCurrentPart();
  return (
    <nav className="methodology-rail" aria-label="The methodology">
      <div className="methodology-rail-inner">
        <p className="methodology-rail-lead">Structural Exhaustion, part by part.</p>
        <ul>
          {METHODOLOGY_PARTS.filter((part) => parentOf(part.id) === undefined).map((part) => (
            <li key={part.id}>
              <RailButton id={part.id} title={part.title} current={current} />
              {METHODOLOGY_PARTS.some((child) => parentOf(child.id) === part.id) ? (
                <ul>
                  {METHODOLOGY_PARTS.filter((child) => parentOf(child.id) === part.id).map((child) => (
                    <li key={child.id}>
                      <RailButton id={child.id} title={child.title} current={current} />
                    </li>
                  ))}
                </ul>
              ) : null}
            </li>
          ))}
        </ul>
      </div>
    </nav>
  );
}


/** Where a move is applied: the explorer step ids, as the papers number them. */
interface MoveSide {
  text: string;
  /** Empty when the move is not used on that side; the cell says why. */
  steps: string[];
}

interface ProofMove {
  name: string;
  /** The classical technique the move is a disciplined form of, if the manual names one. */
  origin?: string;
  what: string;
  eg: MoveSide;
  ns: MoveSide;
}

/** The library, in the reference manual's order, then the moves the analytic proofs added. */
export const PROOF_MOVES: ProofMove[] = [
  {
    name: "Local target tests",
    what: "Replace the target predicate by a finite family of bounded-radius local tests, proved equivalent to it. A realized test closes the branch at once; the absence of every test defines the target-avoiding state that all later work reasons about.",
    eg: {
      text: "A cycle of length a power of two exists exactly when some oriented edge has a return path of Mersenne length. The counterexample condition becomes “no edge has a Mersenne return”, and every later step is a consequence of that local prohibition.",
      steps: ["5", "6", "7"],
    },
    ns: {
      text: "The Caffarelli–Kohn–Nirenberg ε-regularity criterion: small local scale-invariant energy and dissipation give regularity, so a singular point yields a sequence of shrinking cylinders on which mass concentrates. The Type II analysis re-enters through the same local test.",
      steps: ["S2", "S5", "II4"],
    },
  },
  {
    name: "Minimality and replacement",
    origin: "minimal counterexample; representative / protrusion replacement",
    what: "Take the counterexample minimal under a well-founded order and use it in two disciplined ways: a deletion branch, when removing a piece keeps the hypotheses and shrinks the object, and a replacement branch, where context universality of the substitute is proved before sizes are compared.",
    eg: {
      text: "A lexicographically minimal counterexample with no proper 3-core; boundaried atoms, the replacement lemma, and hereditary target-uncompressibility — the standing lever that no proper atom admits a target-complete compression.",
      steps: ["4", "8", "13", "14"],
    },
    ns: {
      text: "Rescale about the singular point and extract a normalized, centred, non-zero ancient Seregin profile; a minimal ancient solution exists (least sup-norm over the normalized class). The Type I / Type II rate dichotomy fixes which normalization applies.",
      steps: ["S11", "I3", "II2"],
    },
  },
  {
    name: "External-type compression",
    origin: "Myhill–Nerode context equivalence",
    what: "A piece is typed by its target-relevant responses to every compatible outside context. Equal type licenses replacement; the first component on which two types differ is a defect and is routed as information.",
    eg: {
      text: "Boundary degree profiles, context universality and the exact response profiles of atoms; the cold same-interface table, whose rows are indexed by profile, stubs, offsets and target response.",
      steps: ["11", "12", "36", "38"],
    },
    ns: {
      text: "Terminal profiles are typed by their local responses on a chart — noncomparable, separated, or comparable up to a perturbative residual — and two profiles are identified only through a recorded transport, never by resemblance.",
      steps: ["II48", "II52", "I57"],
    },
  },
  {
    name: "Charging schemes",
    origin: "discharging (four-colour architecture)",
    what: "Name the demands, the eligible payers, a canonical assignment with an explicit tie-break, and each payer's certified capacity — in that order. The global inequality is the sum of those local obligations.",
    eg: {
      text: "The surplus-token ledger (blockers, capacity tokens, primitive carriers) and the Type A receiver discharging, in which each receiver's charge is its missing-port count less one quarter.",
      steps: ["134", "136", "91"],
    },
    ns: {
      text: "The scale-collapse cost: a cost functional integrated along the collapse, with finite-cost and cost-divergence exclusions, and cost criteria proved under fixed and moving cutoffs.",
      steps: ["II30", "II31", "II36"],
    },
  },
  {
    name: "Local-to-global bookkeeping",
    what: "Assemble a global estimate only through four separate lemmas: local tests give local demands, demands are charged canonically, and the charges are compared with capacity. No global inequality is asserted directly.",
    eg: {
      text: "Window, stub, wedge and net-charge accounts, each proved locally before any entropy or surplus estimate is invoked.",
      steps: ["29", "30", "52"],
    },
    ns: {
      text: "Every input is local on compact cylinders — no node assumes a whole-space norm; the terminal assembly is built from local statements together with the retained ledger.",
      steps: ["S9", "II19", "II54"],
    },
  },
  {
    name: "Active/dormant dichotomy",
    origin: "first-failure principle",
    what: "Monitor a quantity along an index and take the first place it fails the required bound. Before it, the account pays; at it, a bounded witness appears; a shortfall on the active side becomes dormant mass that is counted separately.",
    eg: {
      text: "The hot/cold window interface: failure of the hot entropy account forces a linear amount of cold mass, which is closed by its own structural and quantitative arguments.",
      steps: ["22", "150", "153"],
    },
    ns: {
      text: "The Type II dispatcher: the ordered exhaustion theorem assigns every branch exactly one first failed row, classified at one routing diamond; on the Type I side, the minimal first-bad mesoscopic oscillation scale.",
      steps: ["II56", "II6", "I102"],
    },
  },
  {
    name: "Exchange trichotomy",
    origin: "exchange / switching arguments",
    what: "Compare two structures with the same interface over a finite context generator. Either some context realizes the target, some context distinguishes them, or none does — and then the larger is replaced by the smaller.",
    eg: {
      text: "The cold bounded-germ trichotomy — hit-realized, hit-distinguished, silent — and the switch and theta germs with bounded increment.",
      steps: ["154", "155", "156", "157"],
    },
    ns: {
      text: "Same-point and separated-point reductions of terminal profiles: a comparison realizes a closed alternative, separates the two profiles, or lets one stand for the other.",
      steps: ["II48", "II49", "II52"],
    },
  },
  {
    name: "Finite-state pumping",
    origin: "pigeonhole; the pumping lemma",
    what: "Along a long chain of finitely typed states some exact type repeats. Equal exact type lets the segment between be removed, which minimality forbids; different types yield a first distinguishing context.",
    eg: {
      text: "Trace-basin profiles, cold corridors, periodic carriers and the same-interface table; on the entropy side, one dominant rooted type pumped into a linear family of independent translates.",
      steps: ["50", "51", "157"],
    },
    ns: {
      text: "Recurrence of active paths and the finite-graph cycle lemma for chains of concentration profiles; reselection of bounded windows and nesting of pressure-only rows are proved well-founded and so terminate.",
      steps: ["I141", "I143", "II67", "II117"],
    },
  },
  {
    name: "Overload exhaustion",
    origin: "pigeonhole over finite fibres",
    what: "When a payer is charged beyond its capacity, extract a homogeneous subfamily from its fibre and route that structure, rather than assuming bounded multiplicity inside the charging lemma.",
    eg: {
      text: "Same-token matching and star extraction; role-homogeneous overloads discharged by the geometric closure.",
      steps: ["137", "140", "142", "143"],
    },
    ns: {
      text: "Mass that will not fit into a single core forces a multibubble or cascade, which is excluded; terminal frames are reselected finitely often until a local critical mass is forced and closed.",
      steps: ["II11", "II12", "II97", "II106"],
    },
  },
  {
    name: "Default refinement",
    what: "When a residual survives every current invariant but exposes a finite datum that has no name yet, promote that datum to a label, partition the residual by it, and rerun the local classification fibre by fibre.",
    eg: {
      text: "Label-class refinement whenever a surviving class exposes a missing datum — the finite label algebra is the alphabet being refined.",
      steps: ["18", "114"],
    },
    ns: {
      text: "The refined residual decomposition of the Type I remainder into ten named strata — axisymmetric, rotational, stationary-hull, affine, log-diffuse, Young, and the homogeneous, log-periodic and aperiodic critical tails, plus the generic class — each closed on its own.",
      steps: ["I12", "I13", "I17"],
    },
  },
  {
    name: "Localization",
    origin: "first-moment argument",
    what: "If an additive budget over the whole object is negative, some connected admissible piece is negative; admissibility is chosen so that the piece stays inside the reach of the local tools.",
    eg: {
      text: "Localization of negative net charge to a connected admissible support, the entry into the Type A / Type B local analysis.",
      steps: ["58", "59", "61"],
    },
    ns: {
      text: "Domain localization and selected windows; the local Caccioppoli estimate and localized pressure compactness on compact cylinders.",
      steps: ["II16", "II19", "II22"],
    },
  },
  {
    name: "Peeling loop",
    origin: "well-founded recursion",
    what: "Remove one certified unit of routed load per pass, restoring every standing invariant inside the peel lemma itself, and let a decreasing measure terminate the loop.",
    eg: {
      text: "Exit-(4) target-defect peeling, a finite strictly decreasing loop in the routed load, and its large-budget descent.",
      steps: ["101", "102", "123"],
    },
    ns: {
      text: "Bounded-window reselection and nested pressure-only rows, each shown well-founded so the process bottoms out; shell and annular accounting across scales.",
      steps: ["II66", "II67", "II117"],
    },
  },
  {
    name: "Tiered charging",
    what: "When a charging scheme is only conditionally available, its failure defines a canonical minimal obstruction, which becomes a demand in a second-tier scheme; the tiers are reconciled by disjointness or an explicit split.",
    eg: {
      text: "The Type B incidence and disjointness ledgers, and the minimal overlap obstruction that a failed second ledger leaves behind.",
      steps: ["72", "73", "75", "81"],
    },
    ns: {
      text: "Cost phases ordered by a lexicographic dependency rank; when the cost channel stops being canonical, the first non-canonical point is what closes the branch.",
      steps: ["II31", "II32", "II88", "II89"],
    },
  },
  {
    name: "Aggregate closure",
    what: "A residual class forced to carry a linear deficit is closed by showing its total capacity — member count times per-member capacity, multiplicity included — is sublinear.",
    eg: {
      text: "Type B bridge residuals are sublinear: they are charged to disjoint surplus units of total size O(√n) and cannot carry the linear deficit; route-8-only aggregate estimates.",
      steps: ["75", "76", "85", "120"],
    },
    ns: {
      text: "No direct counterpart in this form. The nearest is the mass floor for an active profile against the finite local mass: a positive finite mass contradicts the loss-row classification, and a retained mass contradicts a zero limit.",
      steps: ["II27", "II98"],
    },
  },
  {
    name: "Rank forcing",
    what: "Define a target-relative rank on the family of tests before any budget is spent. A rank drop is structure and is routed; on the full-rank branch the budget is charged once, on certified independent coordinates.",
    eg: {
      text: "Curvature rank: full curvature rank is forced before entropy is charged, and rank drops are routed to target defect, proper compression or delocalization.",
      steps: ["31", "32", "34", "47"],
    },
    ns: {
      text: "Not used. “Rank” in the Navier–Stokes manuscripts is only the ordinal descent measure of the exit ledger, not a dimensional independence count.",
      steps: [],
    },
  },
  {
    name: "Whole-object exact types",
    what: "The degenerate case with no outside context: the closed type is computed as explicit finite data, and two whole objects are identified only on literal equality of that data.",
    eg: {
      text: "Whole-graph exact response profiles in the no-silent-global-smearing branch.",
      steps: ["43", "45"],
    },
    ns: {
      text: "Not needed. Retained frames are compared through ancestry maps rather than a closed type.",
      steps: [],
    },
  },
  {
    name: "Target thickening",
    origin: "sparse cycle-length forcing",
    what: "For a sparse target set, form bounded offset blocks around each candidate; at small scales only finitely many block positions dodge the target and become labels, at large scales repeated increments sweep whole residue classes.",
    eg: {
      text: "Window offsets 0 to 12, doubling-orbit arithmetic and completion classes around the powers of two, on the cold windows.",
      steps: ["151", "152"],
    },
    ns: {
      text: "Not applicable: the target is a regularity threshold, not a sparse arithmetic set.",
      steps: [],
    },
  },
  // The remaining moves are ones a finite object never calls for; the analytic
  // development added them.
  {
    name: "Limit extraction and transport back",
    origin: "compactness",
    what: "Pass to a subsequence and extract a descendant object, then return to the original branch along explicit ancestry maps and transports. Two obligations: the limit cannot create a hidden terminal state, and every ledger fact must persist through the extraction.",
    eg: {
      text: "Not needed: the object is finite, and repetition is exhausted by pumping instead of by a limit.",
      steps: [],
    },
    ns: {
      text: "Seregin extraction into the raw generated descendant hull; scale reselection giving another limit; descendant recentering and the profile decomposition with its ancestry — each returning to the original state along a recorded map.",
      steps: ["S10", "S13", "I33", "I53", "II47"],
    },
  },
  {
    name: "Symmetry fixing and gauge repair",
    what: "Before anything is classified, quotient out the continuous symmetries by fixing a canonical representative — centre, translate, choose the gauge — and prove that every later quantity transports under that chart.",
    eg: {
      text: "Essentially trivial: the lexicographic choice of the minimal counterexample and the canonical tie-breaks inside the ledgers are the only normalisations a finite graph needs.",
      steps: ["4"],
    },
    ns: {
      text: "Time-translation and centring of the profile, the pressure gauge modulo functions of time, and the repaired-gauge representation that removes the gauge freedom before the single-core test.",
      steps: ["S12", "I42", "I43", "II8", "II10"],
    },
  },
  {
    name: "Rigidity closure by a fixed input",
    what: "Close a named label class outright by one of the theorems fixed at the outset — a classification or Liouville theorem for that class — so the class is empty rather than further refined.",
    eg: {
      text: "The Hegde–Sandeep–Shashank theorem: a P₁₃-free graph of minimum degree three already has a power-of-two cycle, so the counterexample must contain an induced P₁₃.",
      steps: ["15", "16"],
    },
    ns: {
      text: "Each Liouville class of the ancient profile is emptied by its own imported theorem — small amplitude, stationary L³, uniformly tight, and the five structure-and-decay subclasses — leaving only the residual family.",
      steps: ["S21", "S23", "S27", "S30", "I118"],
    },
  },
  {
    name: "Monotone quantity along scale",
    origin: "monotonicity formulas; virial identities",
    what: "Produce a quantity that is monotone in the scale parameter — under fixed or moving cutoffs — so that a collapsing scale must pay a cost. This is where the analytic proof manufactures the budget the charging moves then spend.",
    eg: {
      text: "None: the graph proof's budgets are counting and entropy bounds, not quantities monotone in a parameter.",
      steps: [],
    },
    ns: {
      text: "Corrected monotonicity and the exhaustive carrier routing, the log-annular oscillation virial identity, and the negative scale-drift and positive scale-shell rows it closes.",
      steps: ["II33", "I83", "II73", "II74"],
    },
  },
];

/** The explorer route for a step, in whichever proof its id belongs to. */
function stepPath(id: string): string {
  const slug = /^(S|I|II)\d+$/.test(id) ? "navier-stokes" : "erdos-gyarfas";
  return `/${slug}/explore?step=${id}`;
}

function StepLinks({ steps }: { steps: string[] }) {
  if (steps.length === 0) return null;
  return (
    <span className="methodology-steps">
      {steps.map((id) => (
        <Link key={id} to={stepPath(id)} className="chip chip-node" title={`Open step [${id}]`}>
          {id}
        </Link>
      ))}
    </span>
  );
}

function MoveRow({ move }: { move: ProofMove }) {
  return (
    <tr>
      <td>
        <strong>{move.name}</strong>
        {move.origin ? (
          <small className="methodology-move-origin">from: {move.origin}</small>
        ) : null}
      </td>
      <td>{move.what}</td>
      <td>
        {move.eg.text} <StepLinks steps={move.eg.steps} />
      </td>
      <td>
        {move.ns.text} <StepLinks steps={move.ns.steps} />
      </td>
    </tr>
  );
}

/**
 * How a failed step is repaired: the step's unstated hypothesis becomes a test,
 * the finished argument is kept on the side where it holds, and the other side
 * is a new branch appended after the last existing step. Drawn in the site's
 * node language — rectangles assert, hexagons test, pills close — with the
 * theme tokens, so it follows light and dark mode.
 */
function RepairDiagram() {
  const ink = "var(--ink)";
  const muted = "var(--ink-muted)";
  const font = "var(--sans)";
  const box = (x: number, y: number, w: number, h: number, kind: "step" | "new") => (
    <rect
      x={x}
      y={y}
      width={w}
      height={h}
      rx={7}
      fill="var(--surface)"
      stroke={kind === "new" ? "var(--continuation)" : "var(--assertion)"}
      strokeWidth={1.5}
      strokeDasharray={kind === "new" ? "5 3" : undefined}
    />
  );
  const hex = (x: number, y: number, w: number, h: number) => {
    const t = w * 0.09;
    const d = `M${x + t},${y} L${x + w - t},${y} L${x + w},${y + h / 2} L${x + w - t},${y + h} L${x + t},${y + h} L${x},${y + h / 2} Z`;
    return (
      <path
        d={d}
        fill="color-mix(in srgb, var(--decision) 8%, var(--surface))"
        stroke="var(--decision)"
        strokeWidth={1.5}
      />
    );
  };
  const pill = (x: number, y: number, w: number, h: number) => (
    <rect
      x={x}
      y={y}
      width={w}
      height={h}
      rx={h / 2}
      fill="color-mix(in srgb, var(--terminal) 9%, var(--surface))"
      stroke="var(--terminal)"
      strokeWidth={1.5}
    />
  );
  const arrow = (x1: number, y1: number, x2: number, y2: number, dashed = false) => (
    <line
      x1={x1}
      y1={y1}
      x2={x2}
      y2={y2}
      stroke={dashed ? "var(--continuation)" : "var(--line-strong)"}
      strokeWidth={1.4}
      strokeDasharray={dashed ? "5 4" : undefined}
      markerEnd={dashed ? "url(#repair-arrow-new)" : "url(#repair-arrow)"}
    />
  );
  const label = (
    x: number,
    y: number,
    lines: string[],
    options: { size?: number; fill?: string; anchor?: "start" | "middle"; mono?: boolean } = {},
  ) => (
    <text
      x={x}
      y={y}
      fontFamily={options.mono ? "var(--mono)" : font}
      fontSize={options.size ?? 11}
      fill={options.fill ?? ink}
      textAnchor={options.anchor ?? "middle"}
    >
      {lines.map((line, index) => (
        <tspan key={index} x={x} dy={index === 0 ? 0 : 13}>
          {line}
        </tspan>
      ))}
    </text>
  );

  return (
    <svg
      viewBox="0 0 760 330"
      role="img"
      aria-labelledby="repair-diagram-title"
      className="methodology-repair-diagram"
    >
      <title id="repair-diagram-title">
        How a failed step is repaired: the unstated hypothesis becomes a test, the
        finished argument is kept where it holds, and its failure opens a new branch
        appended after the last existing step.
      </title>
      <defs>
        <marker id="repair-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 Z" fill="var(--line-strong)" />
        </marker>
        <marker id="repair-arrow-new" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
          <path d="M0,0 L10,5 L0,10 Z" fill="var(--continuation)" />
        </marker>
      </defs>

      {/* Before */}
      {label(12, 22, ["BEFORE"], { size: 10, fill: muted, anchor: "start" })}
      {label(12, 36, ["red-teaming finds that step S uses H without stating it"], {
        size: 10.5,
        fill: muted,
        anchor: "start",
      })}
      {box(12, 52, 150, 44, "step")}
      {label(87, 70, ["[k−1] branch state"], { size: 11 })}
      {label(87, 84, ["ledger so far"], { size: 10, fill: muted })}
      {arrow(162, 74, 202, 74)}
      {box(202, 52, 170, 44, "step")}
      {label(287, 70, ["[k] step S"], { size: 11 })}
      {label(287, 84, ["silently assumes H"], { size: 10, fill: "var(--decision)" })}
      {arrow(372, 74, 412, 74)}
      {box(412, 52, 130, 44, "step")}
      {label(477, 70, ["[k+1] …"], { size: 11 })}
      {label(477, 84, ["consumes S"], { size: 10, fill: muted })}
      {arrow(542, 74, 582, 74)}
      {pill(582, 52, 160, 44)}
      {label(662, 70, ["[m] closure"], { size: 11 })}
      {label(662, 84, ["cites the interface theorem"], { size: 10, fill: muted })}

      <line x1={12} y1={116} x2={748} y2={116} stroke="var(--line)" strokeWidth={1} />

      {/* After */}
      {label(12, 138, ["AFTER"], { size: 10, fill: muted, anchor: "start" })}
      {label(12, 152, ["H becomes a test at [k]; S survives where H holds; ¬H is a new branch that inherits the ledger and records ¬H as a fact"], {
        size: 10.5,
        fill: muted,
        anchor: "start",
      })}
      {box(12, 172, 150, 44, "step")}
      {label(87, 190, ["[k−1] branch state"], { size: 11 })}
      {label(87, 204, ["unchanged"], { size: 10, fill: muted })}
      {arrow(162, 194, 202, 194)}
      {hex(202, 168, 170, 52)}
      {label(287, 190, ["[k] does H hold?"], { size: 11 })}
      {label(287, 204, ["the hypothesis S needed"], { size: 10, fill: "var(--decision)" })}
      {arrow(372, 194, 412, 194)}
      {label(392, 186, ["yes"], { size: 10, fill: muted })}
      {box(412, 172, 130, 44, "step")}
      {label(477, 190, ["[k+1] step S"], { size: 11 })}
      {label(477, 204, ["kept, now with H stated"], { size: 10, fill: muted })}
      {arrow(542, 194, 582, 194)}
      {pill(582, 172, 160, 44)}
      {label(662, 190, ["[m] closure"], { size: 11 })}
      {label(662, 204, ["same statement, same citation"], { size: 10, fill: muted })}

      {/* the new branch, appended after the last existing step */}
      {arrow(287, 220, 287, 262, true)}
      {label(300, 244, ["no: ¬H recorded"], { size: 10, fill: "var(--continuation)", anchor: "start" })}
      {box(202, 262, 170, 44, "new")}
      {label(287, 280, ["[N+1] ledger + ¬H"], { size: 11 })}
      {label(287, 294, ["new branch, numbered after [N]"], { size: 10, fill: muted })}
      {arrow(372, 284, 412, 284, true)}
      {box(412, 262, 130, 44, "new")}
      {label(477, 280, ["[N+2] local analysis"], { size: 11 })}
      {label(477, 294, ["with tools suited to ¬H"], { size: 10, fill: muted })}
      {arrow(542, 284, 582, 284, true)}
      {pill(582, 262, 160, 44)}
      {label(662, 280, ["[N+3] closed on its own"], { size: 11 })}
      {label(662, 294, ["or routed to a closed row"], { size: 10, fill: muted })}
      {label(12, 322, ["Solid: unchanged.  Dashed: appended by the repair.  Node numbers are never reassigned, so the numbering keeps the history."], {
        size: 10,
        fill: muted,
        anchor: "start",
      })}
    </svg>
  );
}

/**
 * The landing page's account of how the two proofs were built.
 *
 * A reading of *Structural Exhaustion: An Auditable Method for Long-Form
 * LLM-Assisted Proof Development* (Duran-Ballester, 2026), condensed for a
 * reader who is about to walk one of the diagrams and wants to know why they
 * look the way they do — why every step is a branch test, a residual, or a
 * closure, and why the papers carry ledgers and audit tables at all.
 */
export function MethodologySection() {
  const erdos = findProof("erdos-gyarfas");
  const navier = findProof("navier-stokes");

  return (
    <section id="methodology" className="methodology" aria-labelledby="methodology-title">
      <header className="methodology-header">
        <p className="hero-eyebrow">The methodology</p>
        <h2 id="methodology-title">Structural Exhaustion</h2>
        <p className="methodology-lead">
          Both proofs on this site were developed the same way. Each is an
          evolving system of cases, hypotheses, quantitative resources and
          closure obligations, kept explicit from the first step to the last,
          and organised around a single principle: a counterexample cannot
          avoid the target for free, and the proof's task is to make it pay
          until it cannot.
        </p>
      </header>

      <div className="methodology-layout">
        <MethodologyRail />
        <div className="methodology-body">
          <Part id="philosophy">
            <p>
              The theorems addressed here have the form{" "}
              <em>every mathematical object <Latex value="\(X\)" /> with property{" "}
              <Latex value="\(H\)" /> also has property <Latex value="\(T\)" /></em>
              — formally{" "}
              <Latex value="\(\forall X\in\mathcal X,\ H(X)\Rightarrow T(X)\)" />.
              The proof strategy is always the same. Assume a counterexample: an
              object with <Latex value="\(H(X)\wedge\neg T(X)\)" />, chosen
              minimal under a well-founded order. Then study its structure{" "}
              <em>locally</em> — what its pieces must look like, how they may
              be arranged, what each local configuration forces — and continue
              until a contradiction is reached. Whatever the proof imports from
              the literature is fixed before this study begins; from then on
              every step is local, and a branch closes only through what has
              been established on it together with straightforward textbook
              facts.
            </p>
            <p>
              The contradiction is never an accident of the argument. It is
              imposed by the <strong>structural cost</strong> of building such
              a counterexample. Every property the object must have in order to
              avoid the target constrains what else it can be, and there are
              only three ways for the account to be settled:
            </p>
            <dl className="methodology-costs">
              <div>
                <dt>Compression</dt>
                <dd>
                  The structure admits a smaller object with the same relevant
                  behaviour. Minimality forbids it, so that structure cannot
                  occur.
                </dd>
              </div>
              <div>
                <dt>Quantity</dt>
                <dd>
                  The structure carries a numerical cost — demands, capacities,
                  deficits, entropy, rank — that is tracked against every other
                  property of the object until the combination is no longer
                  affordable.
                </dd>
              </div>
              <div>
                <dt>Constraint</dt>
                <dd>
                  One structural property imposes a restriction that is
                  incompatible with the restrictions already imposed by
                  others; the accumulated record of what the object must be
                  leaves it nothing to be.
                </dd>
              </div>
            </dl>
            <p>
              A minimal counterexample is therefore treated as an adversary
              that must continually pay for avoiding the target, in one of
              these three currencies. Each failed attempt to force the target
              is mined for what it says about the counterexample, and that
              information is recorded as a restriction it must now satisfy. The
              proof advances by converting ignorance about the counterexample
              into an ever longer list of what it is still allowed to be, until
              the list is empty. Each of the three currencies is taken up in
              turn below.
            </p>

            <Part id="constraint">
              <p>
                The first currency is constraint. A proposed invariant{" "}
                <Latex value="\(P\)" /> passes the <em>both-sides test</em> when
                both <Latex value="\(P\)" /> and <Latex value="\(\neg P\)" /> have
                productive consequences: the positive side must feed an account,
                an estimate or a closure mechanism, and the negative side must
                force a bounded residual, a first-failure witness, a structural
                obstruction or another named route. A predicate whose failure has
                no declared consequence stays out of the proof.
              </p>
              <p>
                The same test is the fault-recovery mechanism. When an argument
                turns out to depend on an assumption that was never established,
                the assumption becomes a new case split: the finished argument
                survives on the branch where it holds, and its failure defines a
                complementary branch that receives its own analysis. In the
                motivating example, an entropy argument was found to require
                independently realizable configurations; the completed “hot”
                branch was kept, and the exposed “cold” branch was closed by
                separate structural and quantitative arguments.
              </p>
              <p>
                Each admitted dichotomy places one more certified restriction on
                the surviving counterexample, so the record along a branch only
                grows. A branch carries three such records — its standing
                hypotheses <Latex value="\(H\)" />, the local events certified
                absent (its exclusions <Latex value="\(E\)" />), and the
                positive invariants <Latex value="\(I\)" /> admitted by the
                both-sides test. Writing <Latex value="\(B_i\)" /> for the
                branch state after <Latex value="\(i\)" /> moves,
              </p>
              <Latex
                className="methodology-display"
                value="\[H(B_i)\subseteq H(B_{i+1}),\qquad E(B_i)\subseteq E(B_{i+1}),\qquad I(B_i)\subseteq I(B_{i+1}),\]"
              />
              <p>
                except where an explicitly proved transport lemma replaces one
                representation by an equivalent one. (The full branch state,
                of which these are three coordinates, is spelled out in{" "}
                <em>One iteration of the method</em>.) A later estimate is used only once every
                hypothesis it requires has been established on the branch where
                it is used. The contradiction by constraint is reached when the
                accumulated restrictions are jointly unsatisfiable.
              </p>
            </Part>

            <Part id="quantity">
              <p>
                The second currency is quantity. Once the proof knows that some
                structure must occur in bulk, that bulk is written as{" "}
                <em>demands</em> to be assigned to limited <em>payers</em>. A
                charging scheme names the demand set <Latex value="\(D\)" />, the
                payer set <Latex value="\(P\)" />, a canonical assignment{" "}
                <Latex value="\(\pi:D\to P\)" /> and a certified capacity{" "}
                <Latex value="\(c(p)\)" /> for each payer; the global inequality
                is then
              </p>
              <Latex
                className="methodology-display"
                value="\[|D|=\sum_{p\in P}|\pi^{-1}(p)|\ \le\ \sum_{p\in P}c(p).\]"
              />
              <p>
                Every symbol carries a local obligation: demands distinct,
                assignment total, ties resolved consistently, each capacity valid
                in the current branch state. When demand exceeds capacity some
                payer is overloaded, and an overloaded class typically yields a
                homogeneous family, a matching, a star or a chain — quantitative
                pressure converted back into structure.
              </p>
              <p>
                Deficiency, surplus, entropy, rank, boundary mass and
                concentration are kept as separate currencies unless a proved
                interface converts one into another, so that no obstruction is
                paid for twice with the same resource. Coefficients are outputs,
                not guesses: if a family of size <Latex value="\(n\)" /> forces at
                least <Latex value="\(an-b\)" /> demands and the payers supply at
                most <Latex value="\(cn+d\)" /> with <Latex value="\(a>c\)" />,
                any counterexample satisfies{" "}
                <Latex value="\((a-c)\,n\le b+d\)" />; everything above the
                threshold <Latex value="\((b+d)/(a-c)\)" /> closes by overload and
                what lies below is a bounded family to check. The mathematical
                content is the strict gap between the two rates; the algebra only
                locates where that gap closes the branch. Finally, every
                structural move — deletion, replacement, peeling, charge
                transfer, handoff — is checked against every account it may
                affect, and a move that breaks an account's monotonicity names
                the missing boundary term or surplus correction. This{" "}
                <em>moves × budgets</em> table is one of the audit artifacts the
                papers carry.
              </p>
            </Part>

            <Part id="compression">
              <p>
                The third currency is compression. Long structures repeat, and
                repetition is exhaustible. Pieces receive <em>finite labels</em>{" "}
                recording exactly the classification downstream arguments need,
                so that many pieces with one label form the homogeneous families
                on which standard combinatorics operates. For replacement
                arguments coarse similarity is insufficient, since two pieces may
                behave differently once embedded; pieces are therefore refined by
                their target-relative external type. Two pieces{" "}
                <Latex value="\(K_1,K_2\)" /> with the same boundary have the same
                type when{" "}
                <Latex value="\(T(C\oplus K_1)\Leftrightarrow T(C\oplus K_2)\)" />{" "}
                for every allowed outside context <Latex value="\(C\)" />, and a
                shorter piece of the same type then contradicts minimality.
              </p>
              <p>
                Comparing or exchanging two such structures has three outcomes,
                and the trichotomy is used throughout: a <strong>hit</strong>{" "}
                realizes the target directly; a <strong>defect</strong> is a
                context that distinguishes them, and so is new structural
                information; a <strong>compression</strong> is the absence of any
                distinguishing context, which allows the larger to be replaced by
                the smaller.
              </p>
              <p>
                When a property fails somewhere along a chain, a scale hierarchy
                or an iteration, the proof takes the <strong>first failure</strong>:
                everything before it satisfies the property, and the failure
                itself is a bounded local witness that can be charged, labelled or
                routed. Sequences of finitely typed states eventually repeat, and
                exact repetition is an opportunity to pump, compress or
                distinguish. Some residuals are removed one certified unit at a
                time, provided each iteration restores the branch state and
                decreases a well-founded measure.
              </p>
            </Part>
          </Part>

          <Part id="llm">
            <p>
              Structural Exhaustion is a proof method designed to be carried
              out with language models, and it shows in every working practice.
              Each practice was chosen so that the step it asks for is one a
              model performs well — reasoning about the consequences of an
              assumption, keeping many named quantities straight once they are
              written down, recalling textbook moves, attacking a claim — and
              each recurring way models fail on long arguments is met by a
              structural check rather than by vigilance. The two subsections
              below take these in turn: what the method leverages, and what it
              mitigates.
            </p>

            <Part id="mechanisms">
              <p>
                A research proof built this way needs hundreds of mutually
                dependent local moves, each compatible with every earlier
                exclusion, hypothesis and account. That scale is where free-form
                proof development breaks down, and it is also where language
                models are unusually capable, provided the state is explicit. The
                method is a set of working practices, each chosen to keep the cost
                of the counterexample visible and each resting on a specific
                capability of the model.
              </p>
              <div className="methodology-table-wrap">
                <table className="methodology-map">
                  <thead>
                    <tr>
                      <th scope="col">How the proof is built</th>
                      <th scope="col">The capability it leverages</th>
                    </tr>
                  </thead>
                  <tbody>
                    <tr>
                      <td>
                        <strong>Local structural study.</strong> The undifferentiated{" "}
                        <Latex value="\(\neg T\)" /> is replaced by a family of
                        local events any one of which would produce the target;
                        the counterexample is characterised by their absence, and
                        every absent event becomes usable information.
                      </td>
                      <td>
                        Reasoning about the structural consequences of an
                        assumption: what a graph, profile or decomposition must
                        look like if a property holds or fails.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Fixed inputs, then local steps only.</strong> Every
                        global theorem the proof imports from the literature is
                        fixed at the outset — stated exactly, cited, and listed
                        in the dependency table with the status “imported”. From
                        that point on the proof admits only local steps, and a
                        branch may close only through the branch state, the fixed
                        inputs, and straightforward textbook facts cited at their
                        use. No new global result is introduced mid-proof, and
                        nothing is deferred as an open obligation.
                      </td>
                      <td>
                        Working reliably inside a declared, finite interface,
                        rather than against an open literature whose results
                        would have to be recalled and trusted mid-argument.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Backward-designed invariants.</strong> Resources
                        already at hand — minimality, the target's algebra, the
                        fixed inputs, charging schemes, finite label sets, exact
                        types, certificates — are inventoried first, and each new
                        hypothesis is chosen because it lets one of them make
                        progress.
                      </td>
                      <td>
                        Reading a tool's hypotheses and producing the branch
                        predicate that would make it applicable.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Two-sided branching.</strong> A case split is
                        admitted only when both outcomes are productive: the
                        positive side feeds an account or a closure, the negative
                        side forces a bounded residual, a first-failure witness or
                        a named route.
                      </td>
                      <td>
                        Proposing case distinctions and stating what each side
                        implies, so that neither is left as an unexamined
                        remainder.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Explicit accounting.</strong> Global obstruction is
                        expressed through named demands, payers, capacities,
                        deficits and surpluses, kept as separate currencies with
                        canonical assignments; an overloaded payer or an unbalanced
                        budget forces new structure.
                      </td>
                      <td>
                        Maintaining large collections of named quantities,
                        constraints and cross-references reliably, once they are
                        written down rather than held in prose.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Finite labels and exact types.</strong> Pieces are
                        classified by exactly the data downstream arguments need,
                        refined until equal type is strong enough to license
                        replacement, so repetition becomes an exhaustible
                        resource.
                      </td>
                      <td>
                        Producing and reading finite classifications, case
                        matrices and finite-state descriptions.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Composition of standard moves.</strong> Minimal
                        counterexample, pigeonhole, charging, switching, first
                        failure, compactness, replacement and enumeration are the
                        primitives; the recurring combinations are named as{" "}
                        <em>proof moves</em> — tabulated in their own section
                        below — each a contract whose instance-specific inputs
                        must be proved each time.
                      </td>
                      <td>
                        Broad familiarity with textbook techniques, so novelty
                        can be concentrated in the interfaces and closure lemmas
                        rather than in the primitives.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Counterexample-driven repair.</strong> Every proposed
                        claim is asked two questions — can it be proved, and what
                        follows structurally from its failure? A counterexample to
                        an intermediate claim exposes an exceptional
                        configuration, a deficient account or a distinguishing
                        context, and refines the case structure instead of
                        discarding work.
                      </td>
                      <td>
                        Attacking a proposed statement and finding the
                        configuration in which it fails.
                      </td>
                    </tr>
                    <tr>
                      <td>
                        <strong>Diagrams, tables and ledgers as the proof state.</strong>{" "}
                        Branch tables expose missing cases, dependency tables
                        expose unsupported conclusions, ledgers expose double
                        counting; the bookkeeping is rich enough that later
                        deductions can be read off it.
                      </td>
                      <td>
                        Reading and generating structured textual objects, which
                        hold many relationships more reliably than compressed
                        prose.
                      </td>
                    </tr>
                  </tbody>
                </table>
              </div>
              <p>
                The division of labour follows. Within declared interfaces the
                model maintains state, proposes splits, fills ledgers, drafts
                obligations and criticises candidates; human review and
                mathematical verification decide whether the proposed lemmas,
                routing contracts, computations and closures are valid. Global
                conclusions rest only on the verified composition of local
                outputs.
              </p>
            </Part>

            <Part id="controls">
              <p>
                The reference manual records seven operational risks observed
                while the Erdős–Gyárfás proof was being developed with language
                models, and treats each as a design assumption: the method turns
                the risk into a structural check, so that the failure is either
                impossible to commit or impossible to conceal. An eighth, the
                loss of forward tracking, is the one the others most often reduce
                to. Each entry below states the failure and then the discipline
                that prevents it.
              </p>
              <dl className="methodology-controls methodology-controls-wide">
                <div>
                  <dt>Lost forward tracking</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> An estimate, error term or residual is
                      carried forward through many subsequent steps, and somewhere
                      along the way it is silently loosened, dropped, or applied
                      under hypotheses that no longer hold. This is the
                      characteristic long-range failure of language models: each
                      local step is plausible, but the quantity being tracked has
                      quietly changed meaning by the time it is used.
                    </p>
                    <p>
                      <em>The discipline.</em> The method does not ask the model to
                      track a remainder forward at all. Whenever a tool cannot
                      absorb the whole of what it is applied to, the part it
                      cannot absorb becomes a branch of its own, and the question
                      posed is not “how does this remainder propagate?” but “why
                      could the tool in use not account for it?”. The answer
                      names the property the remainder has and the tool lacked,
                      and the remainder is then attacked locally with a tool
                      suited to that property. Nothing is carried; everything
                      that survives a step is re-stated as a typed residual with
                      the data its next consumer needs.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Extrapolation beyond standard material</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> Generated steps deserve closer scrutiny
                      the moment an argument leaves well-represented material. A
                      branch may then rely on a global result that was not among
                      the proof's inputs — a theorem recalled from memory, a
                      strengthening of a cited one, or a result the literature
                      does not contain — presented as an established mechanism,
                      or left standing as “to be proved”.
                    </p>
                    <p>
                      <em>The discipline.</em> The set of imported global theorems
                      is fixed before the first step and never grows: each is
                      stated exactly, cited, and recorded in the dependency table
                      as “imported”. Everything after that is a local step,
                      “proved here”, drawn from a small vocabulary of standard
                      mechanisms — minimal-counterexample replacement, charging
                      with bounded multiplicity, pigeonhole and finite-state
                      repetition, matching and star extraction, exchange,
                      exhaustive finite enumeration — and a branch may close only
                      through the branch state, the fixed inputs, and
                      straightforward textbook facts cited at the point of use.
                      Instance-specific lemmas and any extension of the proof
                      language remain separate, audited obligations. A branch
                      that would need a new global theorem to close is not
                      closed; it is a defect, repaired by refining the case
                      structure until it closes locally.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Omitted difficult steps</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> A generated draft reads like a proof
                      while omitting the one step that carries the difficulty —
                      typically hidden behind a phrase such as “this structure
                      should be impossible” or “this cannot happen generically”.
                    </p>
                    <p>
                      <em>The discipline.</em> A branch closes only when every leaf
                      terminates in one of a fixed, finite list of certificate
                      types, and every residual has a name. Phrases of the kind
                      above are classified as prompts for further stratification,
                      not as closures. Because the terminal states are
                      enumerated, an omitted step is exposed syntactically —
                      as a leaf with no certificate — before any mathematical
                      judgment is required.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Unsupported global estimates</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> An unconstrained draft gravitates toward
                      a single global inequality — a counting argument, an entropy
                      bound, a spectral estimate — that appears to resolve
                      everything at once. Such estimates concentrate the common
                      errors: an unjustified independence assumption, a double
                      count, a boundary term absorbed without justification.
                    </p>
                    <p>
                      <em>The discipline.</em> An inequality is admitted only in
                      the form the bookkeeping produces: in the simplest case{" "}
                      <Latex value="\(|\mathcal D|\le C\,|\mathcal P|\)" /> from
                      a canonical charging scheme and a bounded-multiplicity
                      lemma, and in general the weighted, payer-specific ledger
                      inequality. Each ingredient — the demands, the assignment,
                      the multiplicity bound, each capacity — is a named local
                      claim, and the global conclusion is the output of that
                      bookkeeping rather than its premise.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Re-encoding the difficulty</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> A model that stalls on a step asks for
                      “one more lemma” whose statement restates the original
                      problem at another level, so the difficulty is relocated
                      rather than reduced.
                    </p>
                    <p>
                      <em>The discipline.</em> A progress invariant: every step
                      outputs either a closed branch or a <strong>strictly smaller</strong>{" "}
                      named residual — smaller in size, in the number of live
                      exits, or in an explicitly monitored complexity parameter.
                      A proposed lemma counts as progress only when its residual
                      is smaller, finite, charged or routed. A bookkeeping step
                      factors through overload, monochromatic extraction and the
                      exchange trichotomy; an unconditional statement about all
                      large objects with some property is a new global theorem,
                      which is not admitted as a step and calls for further
                      branch refinement instead.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Untyped residuals</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> The model declares that the adversarial
                      object has none of the structures the available tools
                      require, and treats the remaining case as a reason to stop.
                    </p>
                    <p>
                      <em>The discipline.</em> The branch-state ledger records the
                      absence of a feature as a positive fact and routes it: it
                      feeds a budget, strengthens an exclusion, creates a
                      repetition payload, or triggers a language extension under
                      the repair protocol. An untyped residual is an invalid
                      worksheet row, not an open mathematical case.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Deferential agreement with erroneous steps</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> A model in an assistant role accepts a
                      user-supplied step whose hypotheses, quantifiers, branch
                      state or output type do not match the current obligation.
                      The failure is not one of mathematical creativity but of
                      interface discipline.
                    </p>
                    <p>
                      <em>The discipline.</em> Agreement has no formal status. A
                      proposed step enters the system only as a worksheet row
                      with declared inputs, quantitative data, schema obligations
                      and a typed output, and is accepted only once the relevant
                      schema obligation has been discharged. When the row fails,
                      the required response is a typed reject, a named residual
                      or an alternative routed payload — never conversational
                      assent.
                    </p>
                  </dd>
                </div>
                <div>
                  <dt>Status-cue audit drift</dt>
                  <dd>
                    <p>
                      <em>The failure.</em> A local audit is replaced by an appeal
                      to the problem's published status — “this is a famous open
                      problem, so the step must be wrong” or “so it must be
                      right”.
                    </p>
                    <p>
                      <em>The discipline.</em> Status is context, neither a
                      certificate nor a defect. Positive steps and red-team
                      objections use the same interface: an objection must name a
                      failed schema, a missing import, a stale branch state, an
                      unconsumed payload, an unregistered global theorem or a
                      candidate scope issue. Inventing a new terminal such as
                      “open problem” is drift in the return alphabet.
                      Certification remains a property of the documented
                      mathematical, computational and review artifacts.
                    </p>
                  </dd>
                </div>
              </dl>
              <p>
                When a proposed lemma does fail, its counterexample is kept as
                data — it may reveal a missing term, a boundary case, an incorrect
                interface, an insufficient label or a new residual pattern — and
                the repair is the least drastic that fits: <strong>numerical</strong>{" "}
                (recompute constants, enumerations or slack),{" "}
                <strong>structural</strong> (correct a hypothesis, invariant,
                route, type or account within the existing vocabulary),{" "}
                <strong>pattern-level</strong> (promote a residual that keeps
                surviving into a reusable mechanism with a declared interface),
                or a <strong>language extension</strong> (new descriptors and
                transitions for an obstruction the vocabulary cannot yet
                express). Explicit residuals also degrade gracefully: withdrawing
                one closure leaves a precise weaker theorem naming the
                counterexample class that remains.
              </p>
              <p>
                Two properties are kept deliberately separate. Architectural
                completeness — an exhaustive branch graph in which every leaf has
                a consumer — is checked by the structure itself. Mathematical
                validity — every edge lemma being correct — is a matter for
                review and, where available, formalization. The method makes the
                second question explicit and local; it does not answer it. That
                is also why the architecture sits well with proof assistants: a
                typed residual is a theorem statement, a tactic contract is an
                interface, and a finite certificate can be checked by a small
                program.
              </p>
            </Part>
          </Part>

          <Part id="artifacts">
            <p>
              A proof of several hundred steps cannot be held in working memory,
              by a model or by a reader. Chapter 1 of each manuscript therefore
              carries a fixed set of artifacts that record the architecture of
              the argument before any local machinery is introduced. The body
              of the paper remains the single source of mathematical truth; the
              artifacts record its dependency order, its standing constraints,
              and how every branch closes. They are what allows a model to work
              on one step at a time without losing the argument, and what
              allows a reviewer to check one step at a time without re-reading
              the whole. This site is a rendering of them: the explorer draws
              the diagram, and the <em>Tables</em> section publishes the
              chapter-1 tables as written.
            </p>
            <p>
              The artifacts are necessary because of the shape the method
              produces. A conventional proof is a line of paragraphs; a proof
              by structural exhaustion is a graph. Every admitted dichotomy
              opens two branches, each branch accumulates its own record of
              hypotheses, exclusions and spent budgets, residuals are routed
              across panels to consumers defined elsewhere, and terminal
              closures sit at the ends of many distinct paths — 157 numbered
              steps in the Erdős–Gyárfás argument, 333 across the three
              Navier–Stokes manuscripts. On such an object the questions that
              matter are positional: which branch am I on, what has been
              established on it and nothing else, where does this remainder go
              next, and does every path end in a closure? Prose cannot answer
              them reliably at that scale, for a model working one step at a
              time or for a reviewer reading it; the diagram and the tables
              are what make the graph legible, navigable and checkable.
            </p>
            <dl className="methodology-controls methodology-controls-wide methodology-artifacts">
              <div>
                <dt>The proof-dependency diagram</dt>
                <dd>
                  <p>
                    <em>What it records.</em> The whole argument as a directed
                    acyclic graph of numbered nodes, drawn across several
                    panels. Rectangles are states or interfaces with one live
                    edge in and one out; diamonds are exhaustive tests whose
                    outgoing edges carry branch labels; solid ellipses are
                    terminal closures with no outgoing edge; a “continue at
                    [n]” arrow joins one panel to the next. Only the live state
                    is drawn: facts already entered into the ledger stay
                    available and are not redrawn as backward arrows.
                  </p>
                  <p>
                    <em>Why it helps.</em> For the model, a node number is a
                    complete address: its incoming edges are exactly the
                    hypotheses available at that step and its outgoing edges
                    are exactly the conclusions it may return, so a step can
                    be drafted, criticised or repaired in isolation. For the
                    reviewer, coverage is visible at a glance — a test with a
                    missing side or a leaf without a closure is a gap in the
                    picture, found before any mathematics is read.
                  </p>
                </dd>
              </div>
              <div>
                <dt>The diagram map and the node-by-node audit table</dt>
                <dd>
                  <p>
                    <em>What they record.</em> The map says, panel by panel,
                    which part of the argument that panel carries, which nodes
                    it holds and which branch it resolves. The audit table
                    then goes node by node: the statement in the body that
                    supports it, its formal content, its failure route, and its
                    successor — with a terminal entry meaning a proof closure,
                    not merely a named alternative.
                  </p>
                  <p>
                    <em>Why they help.</em> They bind every box in the picture
                    to a labelled result in the text, in both directions. A
                    model filling in a node knows precisely which lemma it is
                    writing and what that lemma must return; a reviewer can
                    verify any single row against the body and knows that
                    nothing in the diagram is unsupported prose.
                  </p>
                </dd>
              </div>
              <div>
                <dt>The constraint ledger</dt>
                <dd>
                  <p>
                    <em>What it records.</em> The numbered structural constraints
                    a minimal counterexample must satisfy — the invariants —
                    with the budget each one spends, the results that introduce
                    it and the results that consume it; the standing constants
                    and normalisations; and, in a separate block, the external
                    inputs, each with the exact statement used, the constraint
                    it imposes and where it is used. In the analytic setting the
                    same role is played by the monotone proof ledger, which
                    lists the facts that persist through subsequence
                    extraction, translation and limits.
                  </p>
                  <p>
                    <em>Why it helps.</em> This is the branch state made
                    concrete. The model reads the hypotheses it may use from
                    the ledger rather than reconstructing them from prose, and
                    a later estimate can only cite invariants that appear
                    above it. The reviewer sees the same list, and can confirm
                    that no budget is spent twice and no fact is used before it
                    is established. Ledger-invariant numbers and diagram-node
                    numbers are kept as separate namespaces so the two
                    artifacts cannot be confused.
                  </p>
                </dd>
              </div>
              <div>
                <dt>The per-result requirement table</dt>
                <dd>
                  <p>
                    <em>What it records.</em> The reverse index: for every
                    labelled result, the invariants it requires as input, a
                    plain-language description, its role, and its position in
                    the flow — both a coarse stage label and the exact diagram
                    node.
                  </p>
                  <p>
                    <em>Why it helps.</em> A lemma can be verified in isolation
                    by confirming that everything in its “Requires” cell
                    is established at an earlier or equal stage. When an
                    invariant changes, the same table lists every downstream
                    result that depends on it, so a repair is a finite,
                    enumerated task rather than a re-reading of the paper —
                    for the model performing the repair and for the reviewer
                    checking its extent.
                  </p>
                </dd>
              </div>
              <div>
                <dt>The branch-closure audit ledger</dt>
                <dd>
                  <p>
                    <em>What it records.</em> That every non-regular path from
                    the root reaches exactly one of the listed closures, and,
                    for each closure, the statement that produces the class
                    and the theorem that actually eliminates it — kept apart,
                    since naming a class is not the same as excluding it.
                  </p>
                  <p>
                    <em>Why it helps.</em> It is the leaf-totality check written
                    down. A model cannot leave a branch open without an empty
                    row; a reviewer can audit the whole proof's coverage from
                    one table, and read from it exactly which theorem carries
                    the weight at each terminal.
                  </p>
                </dd>
              </div>
              <div>
                <dt>Notation, constants and the diagram legend</dt>
                <dd>
                  <p>
                    <em>What they record.</em> The standing notation and every
                    named constant with its value and the result that fixes
                    it; the glossary of symbols; and the legend that says what
                    each shape and arrow in the diagram means.
                  </p>
                  <p>
                    <em>Why they help.</em> They keep the vocabulary fixed
                    across hundreds of pages, so a symbol means the same thing
                    at node [120] as at node [3], for the model generating text
                    and the reader checking it. Constants are outputs of local
                    estimates, and the table shows which estimate produced
                    each one.
                  </p>
                </dd>
              </div>
            </dl>
            <p>
              The common property of these artifacts is that they are
              structured text: tables, numbered lists and labelled graphs
              rather than compressed prose. That is the representation in
              which a language model manipulates many relationships reliably,
              and it is also the representation in which a human reviewer can
              check one relationship without holding the rest in mind. The
              diagram exposes an omitted branch, the requirement table exposes
              an unsupported conclusion, and the ledgers expose a double count
              — each syntactically, before any mathematical judgment is
              needed. The bookkeeping is rich enough that later deductions can
              be read off the state of the ledger itself, which is what makes
              the additional length of the papers a working tool rather than a
              cost.
            </p>
          </Part>

          <Part id="repair">
            <p>
              Every proposed claim is attacked before it is admitted. Each
              candidate lemma is asked two questions — can it be proved, and
              what follows structurally from its failure? — and the second is
              asked in earnest: the model, or a reviewer, is set to find the
              configuration in which the claim fails. A successful attack is a{" "}
              <em>defect</em>, and a defect is data. Its counterexample names
              the hypothesis <Latex value="\(H\)" /> the argument was silently
              relying on: an independence assumption, a boundary case, a
              compactness property the state did not carry.
            </p>
            <p>
              The repair rule is always the same. <Latex value="\(H\)" />{" "}
              becomes a test at the step that used it. On the side where{" "}
              <Latex value="\(H\)" /> holds, the finished argument survives
              verbatim, now with its hypothesis stated. On the other side a
              new branch opens: it inherits the whole ledger accumulated up to
              that step, records <Latex value="\(\neg H\)" /> as one more
              positive fact about the counterexample, and is analysed on its
              own with tools suited to <Latex value="\(\neg H\)" />, until it
              closes or routes into a row that is already closed. Existing
              step numbers are never reassigned; the new steps are appended
              after the last existing one. Downstream, a consumer keeps citing
              the same interface theorem — its statement is preserved and only
              its proof now routes through the new branch — so nothing already
              proved is invalidated. Until the new branch closes, the proof is
              a precise weaker theorem: everything holds except on the named
              class where <Latex value="\(\neg H\)" />.
            </p>
            <figure className="methodology-figure">
              <RepairDiagram />
              <figcaption>
                A repair as it appears in the diagrams. The step that used an
                unstated hypothesis becomes a test; its yes-side is the old
                argument, unchanged; its no-side is a new branch, appended
                after the last existing step, that carries the negated
                hypothesis as a fact and is closed on its own.
              </figcaption>
            </figure>
            <p>
              Three repairs from the two developments, one for each kind of
              mistake that red-teaming most often finds. The chips open the
              explorer at the steps concerned.
            </p>
            <dl className="methodology-controls methodology-controls-wide methodology-repairs">
              <div>
                <dt>A compactness claim on too small a state</dt>
                <dd>
                  <p>
                    <em>What red-teaming found.</em> Navier–Stokes, Type I. A
                    lemma asserted that the successor relation between retained
                    concentration profiles was closed, and a chain of
                    downstream results — recurrence on the path space, a
                    compact retained core, the exclusion of infinite descendant
                    chains — rested on it. The diagonal argument in its proof
                    did not go through: a witness for one pair could be centred
                    at a point escaping to infinity, outside every cylinder on
                    which the convergence was known.
                  </p>
                  <p>
                    <em>The hypothesis it exposed.</em> Closedness needs the
                    observer witnesses — the observer, its pressure chart, its
                    realization from the original sequence — to stay in a fixed
                    compact cylinder. A state made of profiles alone was too
                    small to carry that; the paper now records the defect as
                    “no profile-only closedness”, a standing prohibition in its
                    provenance table.
                  </p>
                  <p>
                    <em>The repair.</em> The step that used the claim became a
                    three-way test on covariant density and event balance.
                    Positive density and a balanced event law close where the
                    old argument closed. The third outcome — a zero-density
                    chain sustained by a persistent root current — is the new{" "}
                    <em>sparse branch</em>, carrying exactly the failure of the
                    old lemma as its defining fact; it is reduced through
                    critical-shell accounting to an interscale-flux class that
                    is then shown empty.
                  </p>
                  <p>
                    <em>What was left untouched.</em> Steps [141]–[146] were
                    re-typed inside their existing numbers, not renumbered. The
                    interface theorem “no infinite retained concentration
                    chain” kept its statement, so the finite-family branch and
                    every later closure cite it unchanged; the state grew — a
                    language extension — and the rest of the ledger was reused
                    rather than rebuilt.
                  </p>
                  <StepLinks steps={["I141", "I142", "I143", "I144", "I145", "I146", "I152"]} />
                </dd>
              </div>
              <div>
                <dt>An estimate missing a hypothesis</dt>
                <dd>
                  <p>
                    <em>What red-teaming found.</em> Erdős–Gyárfás. The entropy
                    cap on the packed <Latex value="\(P_{13}\)" /> windows was
                    stated flatly: too many windows spend more entropy than the
                    skeleton budget supplies. Attacking it showed that a window
                    pays its full entropy price only when the canonical package
                    of independent coordinates behind it is actually live in
                    the comparison being run.
                  </p>
                  <p>
                    <em>The hypothesis it exposed.</em> The independent-target
                    entropy lemma requires <em>independently realizable</em>{" "}
                    coordinates. Windows carrying a live package — the hot ones
                    — pay; windows that do not — the cold ones — pay nothing,
                    and the cap says nothing about them.
                  </p>
                  <p>
                    <em>The repair.</em> The step became the hot/cold split:
                    “does the live-hot entropy cap close?”. Yes is the old
                    overflow terminal, unchanged. No opens the cold branch,
                    which inherits the spine estimate and every earlier
                    invariant and adds “the hot cap failed” as a fact — which
                    forces a linear amount of cold mass, then a stub excess,
                    then a first-failure extraction along cold corridors, and
                    finally the bounded-germ trichotomy: hit, defect or
                    compression, with a finite same-interface table for the
                    ties. The cold branch has no terminal residual.
                  </p>
                  <p>
                    <em>What was left untouched.</em> The hot-side terminal and
                    every step from [25] onward. The cold branch was appended
                    as [145]–[157] and hangs from a decision numbered [22]:
                    the numbering itself records that it came later.
                  </p>
                  <StepLinks steps={["22", "23", "24", "145", "150", "153", "154", "155", "156", "157"]} />
                </dd>
              </div>
              <div>
                <dt>A budget used outside its regime</dt>
                <dd>
                  <p>
                    <em>What red-teaming found.</em> Erdős–Gyárfás. The skeleton
                    budget <Latex value="\(B_{\mathrm{skel}}=\tfrac32 n\log_2 n+o(n\log n)\)" />{" "}
                    that the entropy arguments spend is only valid on a
                    near-cubic spine — a graph whose surplus above cubic is
                    small. The main line had been spending it without saying
                    so.
                  </p>
                  <p>
                    <em>The hypothesis it exposed.</em> The surplus{" "}
                    <Latex value="\(\sigma(G)=2m-3n\)" /> must be{" "}
                    <Latex value="\(O(\sqrt n)\)" />. A counterexample with
                    large surplus is outside the budget's regime and needs its
                    own accounting.
                  </p>
                  <p>
                    <em>The repair.</em> A test on the surplus was placed before
                    the budget is first used. Its no-side is the old main line.
                    Its yes-side is the surplus-pair accounting branch: excess
                    ports become an active family, pairs are split into
                    blocker-free and blocked, blocked pairs are charged through
                    a canonical blocker ledger and capacity tokens, and any
                    overload is exhausted by homogeneous matching-or-star
                    extraction. Its output is precisely the near-cubic spine
                    estimate the main line consumes.
                  </p>
                  <p>
                    <em>What was left untouched.</em> Every step of the main
                    line, which now receives the spine estimate as an
                    established hypothesis instead of assuming it. The branch
                    was appended as [125]–[144] and hangs from a decision
                    numbered [19].
                  </p>
                  <StepLinks steps={["19", "20", "125", "130", "134", "137", "144"]} />
                </dd>
              </div>
            </dl>
            <p>
              The three sit at different levels of the repair hierarchy. The
              two Erdős–Gyárfás repairs are structural: a hypothesis was made
              explicit and a case split added within the existing vocabulary.
              The Navier–Stokes repair is a language extension: the branch
              state had to grow to carry witnesses, and a new class of
              residual — the sparse branch — entered the vocabulary with its
              own closure. In none of the three was any previously closed
              branch reopened, and in each the numbering shows what happened:
              a branch numbered far after the decision it hangs from —
              [22]→[145], [19]→[125], the re-typed [143]→[146] — was added
              after the main line was numbered, whereas contiguous
              continuations such as [64]→[65] and [109]→[110] belong to the
              original design. This is also what graceful degradation means in
              practice. The Erdős–Gyárfás manuscript closes with a resilience
              appendix listing, for each closing lemma, the residual class its
              failure would leave — a counterexample satisfying every standing
              invariant up to that step together with the negation of the
              lemma's conclusion — so that, in its words, no leaf degrades to
              nothing.
            </p>
          </Part>


          <Part id="moves">
            <p>
              The three currencies are spent through a fixed vocabulary of
              proof moves. Each move consumes a recorded branch state and
              returns either a closure certificate or a named residual routed
              to another move; each is a familiar technique from the
              literature — minimal counterexample, replacement, discharging,
              exchange, pigeonhole, first failure, well-founded recursion —
              written as a contract with declared inputs, obligations and
              outputs. The moves are mechanisms only: when to invoke one, and
              with what parameters, is a separate strategic decision made on
              the branch. The reference manual demonstrates them on graphs;
              the Navier–Stokes development instantiates the same contracts
              with analytic state. The two right-hand columns give that
              correspondence as this site reads it from the manuscripts, and
              the numbered chips open the explorer at the steps where each
              move is applied — the same step numbers the papers use. Where a
              move is not needed on one side the table says so rather than
              forcing an analogy.
            </p>
            <div className="methodology-table-wrap">
              <table className="methodology-map methodology-moves">
                <thead>
                  <tr>
                    <th scope="col">Move</th>
                    <th scope="col">What it does</th>
                    <th scope="col">In Erdős–Gyárfás</th>
                    <th scope="col">In Navier–Stokes</th>
                  </tr>
                </thead>
                <tbody>
                  {PROOF_MOVES.map((move) => (
                    <MoveRow key={move.name} move={move} />
                  ))}
                </tbody>
              </table>
            </div>
            <p>
              The two right-hand columns differ in every noun and agree in
              every verb. The graph proof spends its budgets in entropy and
              surplus, the PDE proof in scale-collapse cost and retained mass;
              one side classifies pieces by 399 window labels, the other by
              ten residual strata and a four-row exit ledger; one compresses
              by replacing an atom, the other by passing to a limit and
              returning along an ancestry map. But the operations — test the
              target locally, use minimality, compare by type, charge, take
              the first failure, pump, extract from an overload, localize,
              descend on a well-founded measure, refine the labels, route the
              remainder — are the same contracts, and they close a
              combinatorial and an analytic problem in the same way. The last
              four moves entered the vocabulary with the analytic proofs; they
              are the ones a finite object never calls for: extracting a limit and transporting facts back
              along its ancestry, fixing a continuous symmetry before
              classifying, closing a class by an imported rigidity theorem, and
              manufacturing a budget from a quantity that is monotone in the
              scale. Where a move is absent from a column, it is because that
              problem never generated the obstruction the move handles, not
              because the move could not be stated there.
            </p>
          </Part>

          <Part id="iteration">
            <p>
              A branch is its complete accumulated context — not the phrase
              “the remaining difficult case” but everything that has been
              established on the way to it. The method writes that context as
              a tuple of eight coordinates, each of which earlier sections have
              already used:
            </p>
            <Latex className="methodology-display" value="\[B=(H_0,\preceq,E,I,R,V,Q,A)\]" />
            <dl className="methodology-state">
              <div>
                <dt><Latex value="\(H_0\)" /></dt>
                <dd>
                  The standing hypotheses: the baseline property of the object,
                  the assumption that it is a counterexample, and the global
                  theorems fixed at the outset.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(\preceq\)" /></dt>
                <dd>
                  The well-founded order the counterexample is minimal under —
                  the measure that minimality, compression and every peeling
                  or reselection loop decrease.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(E\)" /></dt>
                <dd>
                  The exclusions: the local events certified absent — the
                  Mersenne returns no edge has, the Liouville classes the
                  profile does not belong to.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(I\)" /></dt>
                <dd>
                  The positive invariants admitted by the both-sides test and
                  accumulated along the invariant ladder — full curvature rank,
                  the near-cubic spine estimate, a retained active core.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(R\)" /></dt>
                <dd>
                  The residual data: what is currently known about the
                  remaining object beyond the invariants — the profile, the
                  support, the ledger balances it carries.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(V\)" /></dt>
                <dd>
                  The vocabulary the residual is expressed in: the finite
                  labels, exact types and residual classes in use — the
                  alphabet a default refinement or a language extension
                  enlarges.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(Q\)" /></dt>
                <dd>
                  The queue of typed payloads awaiting a consumer: every
                  surviving obstruction emitted by a move, with the data its
                  declared consumer needs.
                </dd>
              </div>
              <div>
                <dt><Latex value="\(A\)" /></dt>
                <dd>
                  The audit record: the diagram nodes, ledgers and tables of
                  the previous sections, which is what lets a step be checked
                  in isolation.
                </dd>
              </div>
            </dl>
            <p>
              A transition must state which coordinates it reads, which it
              changes, and why the rest remain valid; the monotone record of
              the constraint section is the statement that{" "}
              <Latex value="\(H\)" />, <Latex value="\(E\)" /> and{" "}
              <Latex value="\(I\)" /> only grow. From a state and its queue,
              one cycle runs:
            </p>
            <ol className="methodology-cycle">
              <li>
                <strong>Propose</strong> an invariant, case split, budget, label,
                local test, exchange or candidate lemma that may advance the
                branch.
              </li>
              <li>
                <strong>Admit</strong> it only if both outcomes are productive,
                the required resources exist, and every surviving case has a
                declared route. No new global result may enter here: a move
                draws only on the branch state, the inputs fixed at the outset,
                and straightforward textbook facts.
              </li>
              <li>
                <strong>Select</strong> an admitted move whose prerequisites are
                in the current state or can be synthesized from it.
              </li>
              <li>
                <strong>Execute</strong> — prove, review or compute the local
                obligations before the proof state is allowed to change.
              </li>
              <li>
                <strong>Route</strong>: close what closes, and emit every
                surviving obstruction as a typed residual with a named consumer.
              </li>
              <li>
                <strong>Record</strong> the branch tree, invariant and exclusion
                ledgers, dependencies and residual queue.
              </li>
            </ol>
            <p>
              The safety condition is <em>leaf totality</em>: every outcome a
              step returns lies either in a declared closure class or in the
              domain of another registered step. A branch without a consumer is
              caught by the architecture before anyone assesses the harder
              local mathematics. This is what the terminals, branch labels and
              “continue at” arrows in the diagrams are.
            </p>
          </Part>

          <Part id="proofs">
            <ul className="methodology-cases">
              {erdos ? (
                <li>
                  <Link to={`/${erdos.slug}`}>
                    <span className="proof-grid-glyph" aria-hidden="true">
                      {erdos.glyph}
                    </span>
                    <h4>{erdos.name}</h4>
                    <p>
                      The origin of the method. One long minimal-counterexample
                      spine along which minimum-degree information,
                      induced-path restrictions, admissible cycle-length
                      windows, local response types and several separate charge
                      accounts are transported. A branch that rules out one
                      cycle-producing configuration returns the graph together
                      with the certified absence of that configuration, so every
                      non-closing step hands the next a strictly stronger state.
                    </p>
                  </Link>
                </li>
              ) : null}
              {navier ? (
                <li>
                  <Link to={`/${navier.slug}`}>
                    <span className="proof-grid-glyph" aria-hidden="true">
                      {navier.glyph}
                    </span>
                    <h4>{navier.name}</h4>
                    <p>
                      The same architecture with analytic state. A finite graph
                      label becomes a profile carrying scale, centre, gauge,
                      concentration and ancestry data; normalization transports
                      a hypothetical singularity into an ancient solution; a
                      failed Liouville route emits a residual holding both the
                      failed criterion and the data the closure paper needs.
                      Conclusions about descendant profiles return to the
                      original state through explicit ancestry maps and gauge
                      transports, and the Type II paper's separate first-failure
                      layer turns a negative statement about a whole cascade
                      into the scale and witness at which it breaks.
                    </p>
                  </Link>
                </li>
              ) : null}
            </ul>
          </Part>

          <Part id="progression">
            <p>The whole method compresses to a progression:</p>
            <Latex
              className="methodology-display"
              value="\[\begin{aligned}\text{productive two-sided branches}&\Longrightarrow\text{typed structural obstructions},\\ \text{typed structural obstructions}&\Longrightarrow\text{recorded cumulative pressure},\\ \text{recorded cumulative pressure}&\Longrightarrow\text{one of the declared closure classes}.\end{aligned}\]"
            />
            <p>
              Iteration continues until every branch has a declared terminal
              certificate or an explicitly stated residual obligation. The
              diagrams on this site are those trees; the tables are the ledgers.
            </p>
          </Part>
        </div>
      </div>
    </section>
  );
}
