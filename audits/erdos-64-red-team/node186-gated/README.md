# Node 186 gated proof run

Launched on 2026-09-22 to close the remaining visible-entry history, preserving
the existing joint-balance proof, silent-terminal exclusion, complete incoming
ExactLedger, and all selected objects and prior facts.

- Service: `hypostructure-node186.service`
- Private run: `/home/guillem/.local/state/hypostructure-methodology/node186`
- Dedicated controller: `/home/guillem/.local/share/hypostructure-methodology-node186/controller.py`
- Launch contract: [contract.json](contract.json)
- Original open residual: [execution.md](execution.md) and [state.json](state.json)

The controller was copied from the installed current dependency-chain/Lean-first
release used by node 144. No existing installation or proof run was modified.
OS isolation passed before initialization. Executors and two independent
reviewers run through the controller; this launch certifies no proof stage.

Read actual progress with:

```sh
python3 -I /home/guillem/.local/share/hypostructure-methodology-node186/controller.py status --run /home/guillem/.local/state/hypostructure-methodology/node186
systemctl --user status hypostructure-node186
```

The initial files here remain the launch snapshot. Authoritative accepted
records, attempts, reviews, and proposed source replacements live in the private
run directory. The service log is `service.log` there. Reviewed changes accumulate
in accepted snapshots; launching the workflow does not overwrite live proof files.
The endpoint remains full node-186 closure, not another balance or a relabelled
open survivor.
