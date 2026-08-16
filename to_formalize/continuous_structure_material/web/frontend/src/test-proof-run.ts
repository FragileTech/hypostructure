import type {
  HypostructureProofRun,
  SemanticAutorouteRecord,
} from "./proof-run-types";

/**
 * Synthetic unit-test data for the proof-run UI.
 *
 * This value is deliberately self-contained. It is not a generated artifact,
 * evidence for a mathematical theorem, or a substitute for a kernel-certified
 * `reduceDag%` reduction in production.
 */
export const syntheticAutoroute: SemanticAutorouteRecord = {
  source_id: "v0",
  destination_id: "v1",
  source_depth: 1,
  destination_depth: 8,
  relation: "literal_residual",
  compatible_candidates: [
    {
      node_id: "v1",
      depth: 8,
      relation: "literal_residual",
    },
  ],
  selection: {
    rule: "deepest_most_restrictive",
    selected_candidate_id: "v1",
    tie_break: "smallest_stable_structural_id",
  },
  bridge_provenance: {
    relation_witness: "BridgeCertificate.residual_eq",
    target_congruence: "literal_residual_identity",
    destination_requirements: ["nearest_enclosing_continuation_entry"],
    ledger_ancestors: ["literal_predecessor_stage"],
    framework_lemmas: [
      "Hypostructure.Core.Residual.Ledger.extend_previous",
    ],
    ledger_extension: "Hypostructure.Core.Residual.Ledger.Extension",
  },
  presentation: {
    label: "Synthetic literal transport",
    note: "Cosmetic route commentary retained in the JSON fixture.",
    tags: ["synthetic", "autoroute"],
  },
  work: 1,
  acyclic: true,
};

export const syntheticCertifiedProofRun = {
  $schema: "https://json-schema.org/draft/2020-12/schema",
  schema_id:
    "https://structural-exhaustion.local/schemas/hypostructure-proof-run.schema.json",
  artifact_type: "hypostructure_proof_run",
  schema_version: "2.3.0",
  framework: {
    name: "Hypostructure",
    version: "test",
    proof_authority: "Lean kernel",
  },
  run: {
    name: "Synthetic certified reduction fixture",
    kind: "certified_reduction",
    certified: true,
  },
  problem: {
    id: "synthetic-frontend-unit-fixture",
    identity: {
      definition_ref: "SyntheticFrontendFixture.problemDefinition",
      module: "SyntheticFrontendFixture",
      source_expression: "synthetic unit-test data",
    },
    presentation: {
      label: "Synthetic frontend fixture",
      note: "Self-contained certified-shape data used only by React unit tests.",
      tags: ["synthetic", "unit-test"],
      authored_signature: null,
      authored_statement: null,
    },
    formal: {
      ambient_type: {
        declaration_ref: "SyntheticFrontendFixture.State",
        rendering: "SyntheticState",
      },
      baseline_predicate: {
        declaration_ref: "SyntheticFrontendFixture.Baseline",
        rendering: "fun _ => True",
      },
      branch_state: {
        declaration_ref: "SyntheticFrontendFixture.BranchState",
        rendering: "SyntheticBranchState",
      },
      target_predicate: {
        declaration_ref: "SyntheticFrontendFixture.Target",
        rendering: "fun n => n + 0 = n",
      },
      statement: {
        declaration_ref: "SyntheticFrontendFixture.statement",
        rendering: "∀ n : Nat, n + 0 = n",
      },
    },
  },
  strategy_registrations: [
    {
      id: "ordered_witness_scan:0",
      kind: "ordered_witness_scan",
      index: 0,
      presentation: {
        label: "Synthetic ordered witness scan",
        note: "Produces the literal residual consumed by the framework route.",
        tags: ["synthetic", "schedule"],
      },
      components: [
        {
          label: "rooted-return validation",
          note: "Synthetic searchable component metadata.",
          tags: ["synthetic"],
        },
      ],
      interface: [
        { name: "schedule", role: "contract_field" },
      ],
      outputs: [
        {
          port: "residual",
          presentation: {
            label: "Literal residual",
            note: "Routed by Core-owned autorouting semantics.",
            tags: ["synthetic"],
          },
          closed: false,
        },
      ],
    },
    {
      id: "finite_density_budget:0",
      kind: "finite_density_budget",
      index: 0,
      presentation: {
        label: "Synthetic finite density budget",
        note: "Represents the current registered density-budget strategy.",
        tags: ["synthetic", "density"],
      },
      components: [],
      interface: [{ name: "density_budget", role: "contract_field" }],
      outputs: [
        {
          port: "residual",
          presentation: {
            label: "Retained density residual",
            note: "Preserved by the certified reduction.",
            tags: ["synthetic"],
          },
          closed: false,
        },
      ],
    },
  ],
  dag: {
    representation: "normalized_directed_graph",
    entry: "v0",
    nodes: [
      {
        id: "v0",
        internal_id: 0,
        kind: "operation",
        strategy: {
          kind: "ordered_witness_scan",
          index: 0,
          registration_id: "ordered_witness_scan:0",
        },
        presentation: {
          authored: {
            label: "certificate decision",
            note: "Synthetic route source.",
          },
          registered: {
            label: "Synthetic ordered witness scan",
            note: "Produces the literal residual consumed by the framework route.",
            tags: ["synthetic", "schedule"],
          },
          resolved: {
            label: "certificate decision",
            note: "Synthetic route source.",
          },
        },
        components: [
          {
            label: "rooted-return validation",
            note: "Synthetic searchable component metadata.",
            tags: ["synthetic"],
          },
        ],
        status: "certified",
      },
      {
        id: "v2",
        internal_id: 2,
        kind: "operation",
        strategy: {
          kind: "finite_density_budget",
          index: 0,
          registration_id: "finite_density_budget:0",
        },
        presentation: {
          authored: { label: "density budget", note: "Current API strategy." },
          registered: {
            label: "Synthetic finite density budget",
            note: "Represents the current registered density-budget strategy.",
            tags: ["synthetic", "density"],
          },
          resolved: { label: "density budget", note: "Current API strategy." },
        },
        components: [],
        status: "certified",
      },
      {
        id: "v1",
        internal_id: 1,
        kind: "operation",
        strategy: {
          kind: "target_or_avoid",
          index: null,
          registration_id: null,
        },
        presentation: {
          authored: {
            label: "synthetic target closure",
            note: "Consumes the routed residual.",
          },
          registered: {
            label: "Synthetic target closure",
            note: "Closes the routed synthetic residual.",
            tags: ["synthetic", "closure"],
          },
          resolved: {
            label: "synthetic target closure",
            note: "Consumes the routed residual.",
          },
        },
        components: [],
        status: "certified",
      },
    ],
    edges: [
      {
        id: "e0",
        internal_id: 0,
        kind: "autoroute",
        source: "v0",
        target: "v1",
        output: "residual",
        presentation: {
          label: "literal residual",
          note: "Synthetic Core-resolved route.",
        },
        status: "active",
      },
      {
        id: "e1",
        internal_id: 1,
        kind: "terminal",
        source: "v1",
        target: "t0",
        output: "target",
        presentation: {
          label: "target closed",
          note: "Synthetic closed terminal edge.",
        },
        status: "closed",
      },
      {
        id: "e2",
        internal_id: 2,
        kind: "sequence",
        source: "v0",
        target: "v2",
        output: "residual",
        presentation: {
          label: "density continuation",
          note: "Synthetic current-API continuation.",
        },
        status: "active",
      },
      {
        id: "e3",
        internal_id: 3,
        kind: "terminal",
        source: "v2",
        target: "t1",
        output: "residual",
        presentation: {
          label: "retained residual",
          note: "Open branch of the certified reduction.",
        },
        status: "open",
      },
    ],
    terminals: [
      {
        id: "t0",
        internal_id: 0,
        kind: "proof_terminal",
        status: "closed",
        reason: "Synthetic target witness closes the only terminal.",
        residual: {
          kind: "none",
          disposition: "closed",
          baseline_ref: "problem.formal.baseline_predicate",
          constraints: {
            representation: "all_entry_paths",
            terminal_ref: "t0",
          },
        },
      },
      {
        id: "t1",
        internal_id: 1,
        kind: "branch_endpoint",
        status: "open",
        reason: "Synthetic density residual remains available for continuation.",
        residual: {
          kind: "accumulated_strategy_residual",
          disposition: "open",
          baseline_ref: "problem.formal.baseline_predicate",
          constraints: {
            representation: "all_entry_paths",
            terminal_ref: "t1",
          },
        },
      },
    ],
    autoroutes: [syntheticAutoroute],
  },
  execution: {
    result: "reduced",
    statement_ref: "execution.target_or_residual",
    checks_bound: 3,
    work_bound: 3,
    residual_disposition: "retained",
  },
  trust: {
    kernel_checked: true,
    proof_term_exported: false,
    verification_note:
      "Synthetic certified-shape unit fixture; production certification remains Core-owned.",
  },
} satisfies HypostructureProofRun;
