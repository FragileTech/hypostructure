"""Residual-first task scheduler. Metadata here never substitutes for proof evidence.

The benchmark scheduler provides atomic assignments, evidence review,
integration priority, and
separate task/move/branch completion states. Mathematical truth is established
by the cited proof artifacts and reviewers, not by this module.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
from pathlib import Path

from .policy.workflow import SPEC

POLICY = SPEC["taskflow"]
PHASES = {"0", *(str(n) for n in range(1, 9))}
MODES = {"DISCOVER", "FORMALIZE", "AUDIT"}
TASK_FIELDS = set(POLICY["task_fields"])
RESULTS = set(POLICY["worker_results"])
TERMINAL = {"closed", "open_survivor"}


class TaskError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise TaskError(message)


def nonempty(value: object) -> bool:
    return isinstance(value, str) and bool(value.strip())


def evidence_valid(ref: dict, root: Path) -> bool:
    if not isinstance(ref, dict) or set(ref) != {"path", "sha256", "locator"}:
        return False
    if not all(nonempty(ref[k]) for k in ref):
        return False
    if len(ref["sha256"]) != 64 or any(c not in "0123456789abcdef" for c in ref["sha256"]):
        return False
    path = (root / ref["path"]).resolve()
    return (path.is_relative_to(root.resolve()) and path.is_file() and
            hashlib.sha256(path.read_bytes()).hexdigest() == ref["sha256"])


def archived_evidence_valid(ref: dict, root: Path) -> bool:
    """Check immutable bytes cited before an authorized source-file edit.

    New submissions and reviews still use ``evidence_valid`` against the live
    path.  The archive only lets earlier accepted reviews remain inspectable;
    ``stale_tasks`` also requires the current source bytes to have their own
    accepted, kernel-checked construction review.
    """
    if not isinstance(ref, dict) or set(ref) != {"path", "sha256", "locator"}:
        return False
    if not all(nonempty(ref[k]) for k in ref):
        return False
    if len(ref["sha256"]) != 64 or any(c not in "0123456789abcdef" for c in ref["sha256"]):
        return False
    path = (root / ref["path"]).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        return False
    archive = root / "tools" / "methodology_gate" / "evidence_snapshots" / ref["sha256"]
    return archive.is_file() and hashlib.sha256(archive.read_bytes()).hexdigest() == ref["sha256"]


def benchmark_fingerprint() -> str:
    """Bind each run to the exact shared policy and dispatch instructions."""
    base = Path(__file__).parent
    paths = [p for p in (base / "policy").rglob("*")
             if p.is_file() and "__pycache__" not in p.parts and p.suffix != ".pyc"]
    paths += [base / "taskflow.py", base / "atomic_runner.py"]
    manifest = {str(p.relative_to(base)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(paths)}
    return hashlib.sha256(json.dumps(manifest, sort_keys=True).encode()).hexdigest()


def require_current_benchmark(state: dict) -> None:
    require(state.get("schema") == 2 and
            state.get("benchmark_policy_sha256") == benchmark_fingerprint(),
            "Run does not match the current benchmark policy")


def fresh(branch: dict) -> dict:
    required = {"id", "revision", "source_revision", "endpoint", "incoming",
                "objects", "minimality", "imports", "accounts", "open_outcomes"}
    require(set(branch) == required, "Branch snapshot needs every Phase 0 field")
    for key in ("id", "revision", "source_revision", "endpoint", "incoming"):
        require(nonempty(branch[key]), f"Missing branch {key}")
    for key in ("objects", "imports", "accounts", "open_outcomes"):
        require(isinstance(branch[key], list), f"Branch {key} must be a list")
    require(branch["open_outcomes"] and len(branch["open_outcomes"]) ==
            len(set(branch["open_outcomes"])) and
            all(nonempty(x) for x in branch["open_outcomes"]),
            "Open branch needs distinct tagged outcomes")
    require(isinstance(branch["minimality"], str), "State exact minimality or an empty string")
    return {"schema": 2, "benchmark_policy_sha256": benchmark_fingerprint(), "branch": branch, "initial_outcomes": list(branch["open_outcomes"]),
            "tasks": {}, "moves": {},
            "structural_uses": [], "interactions": [], "side_observations": [],
            "branch_status": "open", "branch_certificate": None}


def add_task(state: dict, contract: dict) -> None:
    require_current_benchmark(state)
    require(state["branch_status"] == "open", "Closed branch cannot receive new tasks")
    require(set(contract) == TASK_FIELDS, "Task must have the exact policy fields")
    task_id = contract["id"]
    require(nonempty(task_id) and task_id not in state["tasks"], "Duplicate or empty task ID")
    require(contract["mode"] in MODES and str(contract["phase"]) in PHASES,
            "Invalid mode or phase")
    phase = str(contract["phase"])
    require(contract["branch_revision"] == state["branch"]["revision"],
            "Task is not pinned to the current branch revision")
    require(contract["kind"] in (POLICY["phase_zero"]["tasks"] if phase == "0"
            else POLICY["phase_tasks"][phase]), "Task kind is outside its phase")
    for key in ("move_id", "goal", "interaction", "parent_payoff", "allowed_write",
                "acceptance", "on_failure"):
        require(isinstance(contract[key], str) and (key == "move_id" or
                key == "interaction" or key == "parent_payoff" or bool(contract[key].strip())),
                f"Invalid task {key}")
    require(isinstance(contract["objects"], list) and contract["objects"] and
            all(nonempty(x) for x in contract["objects"]),
            "Task needs actual object identities")
    require(isinstance(contract["reads"], list) and
            f"branch:{state['branch']['revision']}" in contract["reads"] and
            all(nonempty(x) for x in contract["reads"]),
            "Task needs the full branch reference and accepted inputs")
    require(contract["allowed_write"] not in {"*", "/", "."},
            "Task write scope must name a designated artifact")
    deps = contract["depends_on"]
    require(isinstance(deps, list) and len(deps) == len(set(deps)) and
            all(dep in state["tasks"] for dep in deps), "Dependencies must exist")
    state["tasks"][task_id] = {"contract": contract, "status": "pending",
                                "submission": None, "reviews": [], "history": []}


def retry(state: dict, task_id: str, root: Path) -> None:
    require_current_benchmark(state)
    require(task_id in state["tasks"], "Unknown task")
    item = state["tasks"][task_id]
    require(item["status"] == "rejected" or task_id in stale_tasks(state, root),
            "Retry needs rejected or stale evidence")
    affected = {task_id}
    changed = True
    while changed:
        old_size = len(affected)
        affected.update(key for key, value in state["tasks"].items()
                        if any(dep in affected for dep in value["contract"]["depends_on"]))
        changed = len(affected) != old_size
    for key in affected:
        target = state["tasks"][key]
        if target["submission"] is not None:
            target["history"].append({"submission": target["submission"],
                                      "reviews": target["reviews"]})
        target.update(status="pending", submission=None, reviews=[])
    for field in ("structural_uses", "interactions", "side_observations"):
        state[field] = [entry for entry in state[field] if entry["task"] not in affected]
    survivors = {}
    open_outcomes = list(state["initial_outcomes"])
    for move_id, move in state["moves"].items():
        used = {move["coverage_task"], *move["prerequisites"],
                *move["construction_tasks"], *move["conditional_payoff_tasks"],
                *(arm["task"] for arm in move["outcomes"])}
        if used & affected or move["source_outcome"] not in open_outcomes:
            continue
        open_outcomes.remove(move["source_outcome"])
        open_outcomes.extend(arm["id"] for arm in move["outcomes"]
                             if arm["status"] == "open_survivor")
        survivors[move_id] = move
    state["moves"] = survivors
    state["branch"]["open_outcomes"] = open_outcomes
    state["branch_status"] = "open"
    state["branch_certificate"] = None


def supersede(state: dict, task_id: str, repair: dict) -> None:
    require_current_benchmark(state)
    """Retain a rejected attempt while allowing its accepted earlier-stage repair."""
    require(task_id in state["tasks"], "Unknown task")
    item = state["tasks"][task_id]
    require(item["status"] == "rejected", "Only a rejected task can be superseded")
    require(set(repair) == {"repair_task", "reason"} and
            nonempty(repair["reason"]), "Supersession needs a repair task and reason")
    repair_id = repair["repair_task"]
    require(repair_id in state["tasks"] and
            state["tasks"][repair_id]["status"] == "accepted",
            "Repair task needs accepted evidence")
    require(int(state["tasks"][repair_id]["contract"]["phase"]) <=
            int(item["contract"]["phase"]),
            "Repair must return to the defective stage or earlier")
    require(not any(other["status"] == "accepted" and
                    depends_on(state, other_id, task_id)
                    for other_id, other in state["tasks"].items()),
            "Accepted dependents must be invalidated before supersession")
    item["status"] = "superseded"
    item["supersession"] = repair


def stale_tasks(state: dict, root: Path) -> list[str]:
    def current_version_reviewed(ref: dict) -> bool:
        path = (root / ref["path"]).resolve()
        if not path.is_relative_to(root.resolve()) or not path.is_file():
            return False
        current_hash = hashlib.sha256(path.read_bytes()).hexdigest()
        return any(
            task["status"] == "accepted" and
            str(task["contract"]["phase"]) in {"6", "7"} and
            task["contract"]["allowed_write"] == ref["path"] and
            task["submission"]["implementation_status"] == "kernel_checked" and
            any(e["path"] == ref["path"] and e["sha256"] == current_hash
                for e in task["submission"]["evidence"]) and
            all(any(e["path"] == ref["path"] and e["sha256"] == current_hash
                    for e in review["evidence"])
                for review in task["reviews"])
            for task in state["tasks"].values())

    def accepted_reference_valid(ref: dict) -> bool:
        return (evidence_valid(ref, root) or
                (archived_evidence_valid(ref, root) and
                 current_version_reviewed(ref)))

    return [key for key, item in state["tasks"].items()
            if item["status"] == "accepted" and
            (not all(accepted_reference_valid(ref)
                     for ref in item["submission"]["evidence"]) or
             not all(accepted_reference_valid(ref)
                     for review in item["reviews"] for ref in review["evidence"]))]


def ready(state: dict) -> list[str]:
    if state["branch_status"] == "closed":
        return []
    phase_zero_complete = all(any(item["status"] == "accepted" and
                                  item["contract"]["kind"] == kind and
                                  str(item["contract"]["phase"]) == "0"
                                  for item in state["tasks"].values())
                              for kind in POLICY["phase_zero"]["tasks"])
    return [key for key, item in state["tasks"].items()
            if item["status"] == "pending" and
            (phase_zero_complete or str(item["contract"]["phase"]) == "0") and all(
                state["tasks"][dep]["status"] == "accepted"
                for dep in item["contract"]["depends_on"])]


def depends_on(state: dict, task_id: str, ancestor: str) -> bool:
    pending = list(state["tasks"][task_id]["contract"]["depends_on"])
    seen = set()
    while pending:
        current = pending.pop()
        if current == ancestor:
            return True
        if current not in seen:
            seen.add(current)
            pending.extend(state["tasks"][current]["contract"]["depends_on"])
    return False


def next_task(state: dict, root: Path | None = None) -> dict:
    require_current_benchmark(state)
    if root is not None:
        stale = stale_tasks(state, root)
        if stale:
            return {"task": None, "diagnostic": "Repair stale evidence for " + ", ".join(stale)}
    rejected = [key for key, item in state["tasks"].items() if item["status"] == "rejected"]
    if rejected:
        return {"task": None, "diagnostic": "Repair rejected task " + rejected[0]}
    for key, item in state["tasks"].items():
        if item["status"] != "accepted":
            continue
        metadata = item["submission"]["metadata"]
        for changed, kind, label in (("changed_objects", "check_transport", "Transport check"),
                                     ("changed_accounts", "reconcile_account", "Account reconciliation")):
            if metadata[changed] and not any(other["status"] == "accepted" and
                    other["contract"]["kind"] == kind and
                    key in other["contract"]["depends_on"]
                    for other in state["tasks"].values()):
                followup = [other["contract"] for other in state["tasks"].values()
                            if other["status"] == "pending" and
                            other["contract"]["kind"] == kind and
                            key in other["contract"]["depends_on"] and
                            other["contract"]["id"] in ready(state)]
                if followup:
                    return {"task": sorted(followup, key=lambda x: x["id"])[0],
                            "branch": state["branch"],
                            "worker_instruction": POLICY["worker_instruction"], "diagnostic": None}
                return {"task": None, "diagnostic": f"{label} required for {key}"}
    candidates = ready(state)
    # Accepted construction facts require an integration task before another
    # structural selection. The scheduler cannot invent the mathematical link.
    outstanding = [key for key, item in state["tasks"].items()
                   if item["status"] == "accepted" and
                   str(item["contract"]["phase"]) == "6" and
                   not any(other["status"] == "accepted" and
                           other["contract"]["kind"] == "review_integration" and
                           depends_on(state, other_id, key)
                           for other_id, other in state["tasks"].items())]
    if outstanding:
        integration = [key for key in candidates if
                       str(state["tasks"][key]["contract"]["phase"]) == "7" and
                       any(depends_on(state, key, ancestor) for ancestor in outstanding)]
        if integration:
            candidates = integration
        else:
            return {"task": None, "diagnostic": "Integration task required for " + ", ".join(outstanding)}
    if not candidates:
        missing_zero = [kind for kind in POLICY["phase_zero"]["tasks"]
                        if not any(item["status"] == "accepted" and
                                   item["contract"]["kind"] == kind and
                                   str(item["contract"]["phase"]) == "0"
                                   for item in state["tasks"].values())]
        if missing_zero:
            return {"task": None, "diagnostic": "Phase 0 tasks required: " +
                    ", ".join(missing_zero)}
        return {"task": None, "diagnostic": "No ready task; inspect missing dependencies or open outcomes"}
    priority = {"review_terminal_implication": 0, "check_composition": 0,
                "relate_new_and_retained": 1, "prove_integrated_consequence": 1,
                "review_integration": 1, "form_survivor": 3,
                "select_tension": 4}
    candidates.sort(key=lambda key: (priority.get(state["tasks"][key]["contract"]["kind"], 2),
                                     key))
    return {"task": state["tasks"][candidates[0]]["contract"],
            "branch": state["branch"], "worker_instruction": POLICY["worker_instruction"],
            "diagnostic": None}


def submit(state: dict, task_id: str, result: dict, root: Path, *, assignment_checked: bool = False) -> None:
    require_current_benchmark(state)
    require(task_id in ready(state), "Task is not ready")
    if not assignment_checked and str(state["tasks"][task_id]["contract"]["phase"]) in {"2", "3", "4"}:
        selected = next_task(state, root)
        require(selected["task"] is not None and selected["task"]["id"] == task_id,
                "Repair or integrate active evidence before new exploration")
    require(set(result) == set(POLICY["result_fields"]),
            "Result fields are incomplete")
    require(result["status"] in RESULTS and nonempty(result["output"]), "Invalid worker result")
    require(result["implementation_status"] in {"none", "kernel_checked"},
            "Implementation status must be separate from mathematical review")
    refs = result["evidence"]
    require(isinstance(refs, list) and refs and all(evidence_valid(r, root) for r in refs),
            "Missing, outside, or stale evidence")
    require(isinstance(result["immediate_subobligations"], list), "Subobligations must be a list")
    if result["status"] == "NEEDS_DECOMPOSITION":
        require(nonempty(result["first_missing_inference"]) and
                bool(result["immediate_subobligations"]), "Name the first missing inference and its children")
    else:
        require(isinstance(result["first_missing_inference"], str), "Invalid missing inference field")
    metadata = result["metadata"]
    require(isinstance(metadata, dict) and set(metadata) == set(POLICY["metadata_fields"]),
            "Result metadata is incomplete")
    for key in ("changed_objects", "changed_accounts", "side_observations"):
        require(isinstance(metadata[key], list) and all(nonempty(x) for x in metadata[key]),
                f"Invalid {key}")
    use = metadata["structural_use"]
    require(use is None or (isinstance(use, dict) and set(use) ==
            set(POLICY["structural_use_fields"]) and
            all(nonempty(x) for x in use.values())), "Invalid structural-use record")
    interaction = metadata["interaction"]
    require(interaction is None or (isinstance(interaction, dict) and set(interaction) ==
            set(POLICY["interaction_fields"]) and
            isinstance(interaction["ingredients"], list) and
            len(interaction["ingredients"]) >= 2 and
            all(nonempty(x) for x in interaction["ingredients"]) and
            all(nonempty(interaction[x]) for x in
                ("object", "relation", "known", "unresolved", "domains", "previous_use"))),
            "Interaction must name linked facts and their actual relation")
    item = state["tasks"][task_id]
    item.update(status="submitted", submission=result, reviews=[])


def review(state: dict, task_id: str, verdict: dict, root: Path) -> None:
    require_current_benchmark(state)
    require(task_id in state["tasks"], "Unknown task")
    item = state["tasks"][task_id]
    require(item["status"] == "submitted", "Only a submitted task can be reviewed")
    require(set(verdict) == {"reviewer", "decision", "reason", "evidence"},
            "Review needs identity, decision, reasoning, and evidence")
    require(nonempty(verdict["reviewer"]) and nonempty(verdict["reason"]) and
            verdict["decision"] in {"accept", "reject"}, "Invalid review")
    require(verdict["reviewer"] not in [r["reviewer"] for r in item["reviews"]],
            "Reviews must be independent")
    require(isinstance(verdict["evidence"], list) and verdict["evidence"] and
            all(evidence_valid(r, root) for r in verdict["evidence"]),
            "Review must cite fresh inspected evidence")
    require(all(evidence_valid(r, root) for r in item["submission"]["evidence"]),
            "Submission evidence changed before review")
    if verdict["decision"] == "accept":
        require(item["submission"]["status"] == "SUBMITTED_RESULT",
                "A blocked or decomposed result cannot be accepted as completion")
    item["reviews"].append(verdict)
    if verdict["decision"] == "reject":
        item["status"] = "rejected"
    elif len(item["reviews"]) == 2:
        item["status"] = "accepted"
        metadata = item["submission"]["metadata"]
        for field, target in (("structural_use", "structural_uses"),
                              ("interaction", "interactions")):
            if metadata[field] is not None:
                state[target].append({"task": task_id, **metadata[field]})
        state["side_observations"].extend(
            {"task": task_id, "observation": value}
            for value in metadata["side_observations"])


def certify_move(state: dict, move: dict, root: Path | None = None) -> None:
    require_current_benchmark(state)
    require(set(move) == set(POLICY["move_fields"]), "Incomplete move record")
    require(nonempty(move["id"]) and move["id"] not in state["moves"], "Duplicate move")
    require(move["branch_revision"] == state["branch"]["revision"], "Stale move")
    require(move["source_outcome"] in state["branch"]["open_outcomes"],
            "Move must consume a live source outcome")
    require(root is None or not stale_tasks(state, root), "Stale accepted evidence")
    def accepted(task_id: str) -> bool:
        return task_id in state["tasks"] and state["tasks"][task_id]["status"] == "accepted"
    require(nonempty(move["selected_conflict"]) and
            nonempty(move["textbook_statement"]), "Move needs its selected tension and exact theorem")
    require(isinstance(move["prerequisites"], list) and
            all(accepted(k) for k in move["prerequisites"]),
            "Move prerequisites need accepted evidence")
    require(isinstance(move["construction_tasks"], list) and
            move["construction_tasks"] and
            all(accepted(k) and str(state["tasks"][k]["contract"]["phase"]) == "6"
                for k in move["construction_tasks"]),
            "Move construction needs accepted Phase 6 tasks")
    require(isinstance(move["conditional_payoff_tasks"], list) and
            move["conditional_payoff_tasks"] and
            all(accepted(k) for k in move["conditional_payoff_tasks"]),
            "Every conditional payoff needs accepted evidence")
    require(all(str(state["tasks"][k]["contract"]["phase"]) == "5" and
                state["tasks"][k]["contract"]["move_id"] == move["id"]
                for k in move["conditional_payoff_tasks"]),
            "Payoff evidence must belong to this move's Phase 5 analysis")
    require(accepted(move["coverage_task"]), "Outcome coverage is not accepted")
    coverage = state["tasks"][move["coverage_task"]]["contract"]
    require(coverage["kind"] in {"check_coverage", "prove_coverage"} and
            coverage["move_id"] == move["id"], "Coverage task is unrelated to this move")
    outcomes = move["outcomes"]
    require(isinstance(outcomes, list) and outcomes and
            len({x.get("id") for x in outcomes}) == len(outcomes), "Outcomes must be explicit and unique")
    require(len({x.get("task") for x in outcomes}) == len(outcomes) and
            len({x.get("payoff_task") for x in outcomes}) == len(outcomes),
            "Each outcome needs its own atomic analysis and conditional payoff")
    require({x.get("payoff_task") for x in outcomes} == set(move["conditional_payoff_tasks"]),
            "Conditional payoff manifest must cover exactly the listed outcomes")
    for arm in outcomes:
        require(set(arm) == {"id", "payoff_task", "task", "status", "advancement",
                             "survivor", "continuation"},
                "Each outcome needs its exact status and continuation")
        require(accepted(arm["task"]), "Outcome needs accepted evidence")
        task = state["tasks"][arm["task"]]["contract"]
        require(str(task["phase"]) == "7" and task["move_id"] == move["id"],
                "Outcome task is not this move's Phase 7 analysis")
        require(arm["status"] in TERMINAL and arm["advancement"] in POLICY["advancement"],
                "Outcome is neither a closure nor a reviewed structural payoff")
        if arm["status"] == "open_survivor":
            require(arm["advancement"] != "closure", "An open survivor is not closed")
            require(nonempty(arm["survivor"]) and arm["continuation"] in state["tasks"],
                    "Survivor needs its exact residual and scheduled local continuation")
        else:
            require(arm["advancement"] == "closure" and not arm["survivor"],
                    "A closed outcome needs closure evidence, not a survivor")
    state["moves"][move["id"]] = move
    state["branch"]["open_outcomes"] = [x for x in state["branch"]["open_outcomes"]
                                             if x != move["source_outcome"]] + [
        x["id"] for x in outcomes if x["status"] == "open_survivor"]


def close_branch(state: dict, certificate: dict, root: Path | None = None) -> None:
    require_current_benchmark(state)
    require(set(certificate) == {"task", "endpoint", "composition_tasks", "direct_closure_tasks"},
            "Branch closure needs exact endpoint and composition")
    require(certificate["endpoint"] == state["branch"]["endpoint"], "Wrong endpoint")
    require(root is None or not stale_tasks(state, root), "Stale accepted evidence")
    direct = certificate["direct_closure_tasks"]
    require(isinstance(direct, dict) and set(direct) == set(state["branch"]["open_outcomes"]),
            "Every remaining outcome needs its own direct closure certificate")
    require(len(set(direct.values())) == len(direct),
            "Each remaining outcome needs its own atomic closure check")
    for task_id in direct.values():
        require(task_id in state["tasks"] and state["tasks"][task_id]["status"] == "accepted" and
                str(state["tasks"][task_id]["contract"]["phase"]) == "7" and
                state["tasks"][task_id]["contract"]["kind"] in
                {"test_constraint", "test_compression", "test_quantity"},
                "Direct closure needs an accepted Phase 7 mechanism test")
    ids = [certificate["task"], *certificate["composition_tasks"]]
    require(all(k in state["tasks"] and state["tasks"][k]["status"] == "accepted"
                for k in ids), "Closure requires accepted verification and composition tasks")
    require(str(state["tasks"][certificate["task"]]["contract"]["phase"]) == "8",
            "Closure requires Phase 8 verification")
    state["branch"]["open_outcomes"] = []
    state["branch_status"] = "closed"
    state["branch_certificate"] = certificate


def summary(state: dict, root: Path | None = None) -> dict:
    require_current_benchmark(state)
    return {"branch": state["branch"]["id"], "branch_status": state["branch_status"],
            "atomic_tasks": {status: sum(t["status"] == status for t in state["tasks"].values())
                             for status in ("pending", "submitted", "accepted", "rejected",
                                            "superseded")},
            "productive_moves": len(state["moves"]),
            "open_outcomes": state["branch"]["open_outcomes"], "next": next_task(state, root)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("init", "add", "next", "run-task", "submit", "review", "retry", "supersede", "move", "close", "status"))
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--input", type=Path)
    parser.add_argument("--task-id")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--attempts", type=Path)
    parser.add_argument("--auth", type=Path, default=Path.home() / ".codex/auth.json")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--runtime-contract", type=Path)
    parser.add_argument("--review-attempt", type=Path)
    args = parser.parse_args()
    args.record.parent.mkdir(parents=True, exist_ok=True)
    lock_path = args.record.with_name(args.record.name + ".lock")
    with lock_path.open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise TaskError("Another controller is already operating on this task queue") from None
        execute_command(args)


def execute_command(args) -> None:
    require(args.command not in {"submit", "review"},
            "Manual worker/reviewer submission is disabled. Use run-task for fresh isolated contexts.")
    execution = None
    if args.command == "init":
        require(args.input is not None and not args.record.exists(), "New record needs an input and free path")
        state = fresh(json.loads(args.input.read_text()))
    else:
        state = json.loads(args.record.read_text())
        require_current_benchmark(state)
        if args.command == "run-task":
            from .atomic_runner import run_one
            attempts = args.attempts or args.record.parent / (args.record.stem + "-attempts")
            runtimes = (json.loads(args.runtime_contract.read_text()).get("runtime_paths", [])
                        if args.runtime_contract else [])
            execution = run_one(state, args.root.resolve(), attempts.resolve(), args.auth, args.timeout,
                                runtimes, args.review_attempt)
        if args.command == "retry":
            retry(state, args.task_id, args.root)
        if args.command in {"add", "submit", "review", "supersede", "move", "close"}:
            require(args.input is not None, "Command needs --input")
            payload = json.loads(args.input.read_text())
            if args.command == "add": add_task(state, payload)
            elif args.command == "submit": submit(state, args.task_id, payload, args.root)
            elif args.command == "review": review(state, args.task_id, payload, args.root)
            elif args.command == "supersede": supersede(state, args.task_id, payload)
            elif args.command == "move": certify_move(state, payload, args.root)
            else: close_branch(state, payload, args.root)
    if args.command in {"init", "add", "run-task", "submit", "review", "retry", "supersede", "move", "close"}:
        args.record.parent.mkdir(parents=True, exist_ok=True)
        temporary = args.record.with_suffix(args.record.suffix + ".tmp")
        temporary.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n")
        temporary.replace(args.record)
    response = next_task(state, args.root) if args.command == "next" else summary(state, args.root)
    response["context_policy"] = POLICY["context_policy"]
    if execution is not None:
        response["execution"] = execution
    print(json.dumps(response, indent=2))


if __name__ == "__main__":
    main()
