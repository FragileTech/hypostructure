export interface Documentation {
  label: string | null;
  note: string | null;
  tags: string[];
}

export interface LabelNote {
  label: string | null;
  note: string | null;
}

export type StrategyKind =
  | "ordered_witness_scan"
  | "response_classifier"
  | "capacity_ledger"
  | "support_localization"
  | "rank_budget"
  | "closed_code"
  | "dichotomy"
  | "counterexample_localization"
  | "minimal_counterexample_selection"
  | "target_algebra_reduction"
  | "minimal_subobject_exclusion"
  | "critical_modification_structure"
  | "interface_replacement_closure"
  | "obstruction_packing_closure"
  | "exact_finite_local_algebra"
  | "finite_barrier_enumeration"
  | "scale_threshold_dichotomy"
  | "atom_context_obstruction_dichotomy"
  | "finite_density_budget"
  | "ordered_surplus_activation"
  | "baseline_demand_accounting"
  | "canonical_pair_response_accounting"
  | "canonical_capacity_token_accounting"
  | "coupled_homogeneous_fibre_pressure"
  | "finite_bottleneck_classification"
  | "homogeneous_bottleneck"
  | "support_complement_normalization"
  | "boundary_demand_accounting"
  | "local_supply_lower_bound"
  | "target_relative_rank_dichotomy"
  | "finite_state_capacity"
  | "finite_schedule_capacity"
  | "cold_branch_aggregation"
  | "finite_state_net_charge_continuation"
  | "target_or_avoid";

export interface StrategyReference {
  kind: StrategyKind;
  index: number | null;
  registration_id: string | null;
}

export interface StrategyRegistration {
  id: string;
  kind: StrategyKind;
  index: number;
  presentation: Documentation;
  components: Documentation[];
  interface: Array<{ name: string; role: "contract_field" }>;
  outputs: Array<{
    port:
      | "left"
      | "right"
      | "atom"
      | "context"
      | "target"
      | "residual"
      | "above"
      | "at_or_below"
      | "type_A"
      | "type_B";
    presentation: Documentation;
    closed: boolean;
  }>;
  closures?: { target: boolean; residual: boolean };
}

export interface StrategyNode {
  id: string;
  internal_id: number;
  kind: "operation" | "decision";
  strategy: StrategyReference;
  presentation: {
    authored: LabelNote;
    registered: Documentation;
    resolved: LabelNote;
  };
  components: Documentation[];
  status: "active" | "certified";
}

export interface JoinNode {
  id: string;
  internal_id: number;
  kind: "join";
  presentation: LabelNote;
  status: "active";
}

export type DagNode = StrategyNode | JoinNode;

export interface DagEdge {
  id: string;
  internal_id: number;
  kind: "sequence" | "output" | "terminal" | "join" | "autoroute";
  source: string;
  target: string;
  output: string | null;
  presentation: LabelNote;
  status: "active" | "conditional" | "open" | "closed";
}

export interface DagTerminal {
  id: string;
  internal_id: number;
  kind: "branch_endpoint" | "target" | "proof_terminal";
  status: "open" | "closed";
  reason: string;
  residual: {
    kind: "none" | "accumulated_strategy_residual";
    disposition: "open" | "closed";
    baseline_ref: "problem.formal.baseline_predicate";
    constraints: {
      representation: "all_entry_paths";
      terminal_ref: string;
    };
  };
}

export interface AutorouteCandidate {
  node_id: string;
  depth: number;
  relation: "literal_residual";
}

export interface AutorouteSelection {
  rule: "deepest_most_restrictive";
  selected_candidate_id: string;
  tie_break: "smallest_stable_structural_id";
}

export interface AutorouteBridgeProvenance {
  relation_witness: string;
  target_congruence: string;
  destination_requirements: string[];
  ledger_ancestors: string[];
  framework_lemmas: string[];
  ledger_extension: string;
}

export interface SemanticAutorouteRecord {
  source_id: string;
  destination_id: string;
  source_depth: number;
  destination_depth: number;
  relation: "literal_residual";
  compatible_candidates: AutorouteCandidate[];
  selection: AutorouteSelection;
  bridge_provenance: AutorouteBridgeProvenance;
  presentation: Documentation;
  work: 1;
  acyclic: true;
}

export interface FormalReference {
  declaration_ref: string;
  rendering: string;
}

export interface HypostructureProofRun {
  $schema: string;
  schema_id: string;
  artifact_type: "hypostructure_proof_run";
  schema_version: "2.3.0";
  framework: {
    name: "Hypostructure";
    version: string;
    proof_authority: "Lean kernel";
  };
  run: {
    name: string;
    kind: "certified_reduction";
    certified: true;
  };
  problem: {
    id: string;
    identity: {
      definition_ref: string;
      module: string;
      source_expression: string;
    };
    presentation: Documentation & {
      authored_signature: string | null;
      authored_statement: string | null;
    };
    formal: {
      ambient_type: FormalReference;
      baseline_predicate: FormalReference;
      branch_state: FormalReference;
      target_predicate: FormalReference;
      statement: FormalReference;
    };
  };
  strategy_registrations: StrategyRegistration[];
  dag: {
    representation: "normalized_directed_graph";
    entry: string;
    nodes: DagNode[];
    edges: DagEdge[];
    terminals: DagTerminal[];
    autoroutes: SemanticAutorouteRecord[];
  };
  execution: {
    result: "reduced";
    statement_ref: "execution.target_or_residual";
    checks_bound: number;
    work_bound: number;
    residual_disposition: "retained";
  };
  trust: {
    kernel_checked: true;
    proof_term_exported: false;
    verification_note: string;
  };
}
