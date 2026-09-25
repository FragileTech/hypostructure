"""Validate the *inventory* of the original proof's dependency chain.

This is deliberately not a proof checker. A successful validation checks a
complete, connected inventory and evidence references, not the meaning of Lean
statements or the correctness of a claimed ExactLedger publication. Independent
review must establish those correspondences; the controller must also run every
listed kernel target. Merely setting status="kernel_checked" proves nothing.

Schema: {"target": fact_id, "facts": {fact_id: {
  "statement": exact_original_statement, "owner": upstream_node_id_or_structured_owner,
  "path": snapshot_relative_lean_path, "declaration": qualified_lean_name,
  "dependencies": [fact_id, ...],
  "status": "pending" | "kernel_checked" | "unnecessary",
  "kernel_targets": [qualified_module_name, ...],
  "statement_evidence": [evidence_id, ...],
  "publication_evidence": [evidence_id, ...],
  "unnecessary_evidence": [evidence_id, ...]
}}}.

Only the first six fact fields are always required. Kernel-checked facts need
targets and statement/publication evidence. Unnecessary facts need evidence
that the unchanged strategy does not require them. Dependencies record the
original inventory, including obligations subsequently shown unnecessary, so
those dispositions remain auditable. The target itself cannot be unnecessary.
Evidence IDs are resolved and semantically reviewed by the surrounding gate.
Pending facts may name a source file/declaration not yet implemented.
"""

from pathlib import Path, PurePosixPath


def _text(value):
    return isinstance(value, str) and bool(value.strip()) and not any(
        ord(c) < 32 for c in value)


def _statement(value):
    return isinstance(value, str) and bool(value.strip()) and not any(
        ord(c) < 32 and c not in '\n\r\t' for c in value)


def _owner(value):
    if _text(value):
        return True
    return (isinstance(value, dict) and {'node', 'label'} <= set(value)
            and all(_text(value[k]) or _strings(value[k])
                    for k in ('node', 'label'))
            and ('atomic_rows' not in value or _strings(value['atomic_rows'])))


def _name(value):
    """Conservative Lean names (Unicode identifiers and trailing apostrophes).

    Deliberately excludes quoted identifiers and all command-line syntax.
    """
    return isinstance(value, str) and bool(value) and all(
        part.rstrip("'").isidentifier() for part in value.split('.'))


def _strings(value):
    return (isinstance(value, list) and bool(value)
            and all(_text(item) for item in value)
            and len(value) == len(set(value)))


def validate_chain(manifest, source_root, complete=False, replacements=None):
    """Return structural errors; [] never substitutes for review or compilation."""
    errors = []
    if not isinstance(manifest, dict):
        return ['dependency chain must be an object']
    target, facts = manifest.get('target'), manifest.get('facts')
    if not _text(target):
        errors.append('dependency chain requires an explicit target fact ID')
    if not isinstance(facts, dict) or not facts:
        return errors + ['dependency chain requires a nonempty facts object']
    if not isinstance(target, str) or target not in facts:
        errors.append('target must identify an inventoried fact')
    root = Path(source_root).resolve()
    edges = {}
    for fact_id, fact in facts.items():
        label = f'fact {fact_id!r}'
        if not _text(fact_id):
            errors.append(f'{label}: invalid fact ID')
        if not isinstance(fact, dict):
            errors.append(f'{label}: entry must be an object')
            continue
        if not _statement(fact.get('statement')):
            errors.append(f'{label}: requires nonempty statement text (multiline allowed)')
        if not _owner(fact.get('owner')):
            errors.append(f'{label}: owner must be text or node/label/atomic_rows details')
        if not _name(fact.get('declaration')):
            errors.append(f'{label}: invalid Lean declaration identifier')
        path = fact.get('path')
        safe_path = (isinstance(path, str) and bool(path)
                     and '\\' not in path and _text(path)
                     and not PurePosixPath(path).is_absolute()
                     and all(part not in ('', '.', '..') for part in path.split('/'))
                     and PurePosixPath(path).suffix == '.lean')
        if not safe_path:
            errors.append(f'{label}: path must be snapshot-relative .lean file')
        else:
            effective_root = Path(replacements).resolve() if replacements and (Path(replacements) / path).exists() else root
            candidate = effective_root / path
            if not candidate.resolve().is_relative_to(effective_root):
                errors.append(f'{label}: path escapes source snapshot')
            elif any(p.is_symlink() for p in (candidate, *candidate.parents)
                     if p != effective_root and p.is_relative_to(effective_root)):
                errors.append(f'{label}: source path contains a symlink')
            elif fact.get('status') == 'kernel_checked' and not candidate.is_file():
                errors.append(f'{label}: kernel-checked source file is missing')
        deps = fact.get('dependencies')
        if (not isinstance(deps, list) or not all(_text(d) for d in deps)
                or len(deps) != len(set(deps))):
            errors.append(f'{label}: dependencies must be distinct fact IDs')
        else:
            edges[fact_id] = deps
            for dep in deps:
                if dep not in facts:
                    errors.append(f'{label}: missing dependency {dep!r}')
        kind = fact.get('work_kind')
        if kind is not None:
            if kind not in ('evidence_reconciliation', 'proof_repair', 'adapter'):
                errors.append(f'{label}: invalid work_kind')
            if not _statement(fact.get('work_reason')) or not _strings(fact.get('work_evidence')):
                errors.append(f'{label}: work classification requires reason and evidence IDs')
            if kind == 'adapter':
                producers = fact.get('adapter_of')
                if not _strings(producers) or not set(producers) <= set(deps or []):
                    errors.append(f'{label}: adapter_of must name recorded producer dependencies')
        status = fact.get('status')
        if status not in ('pending', 'kernel_checked', 'unnecessary'):
            errors.append(f'{label}: invalid implementation status')
        if complete and status == 'pending':
            errors.append(f'{label}: pending implementation prevents completion')
        if fact_id == target and status == 'unnecessary':
            errors.append('target cannot be disposed of as unnecessary')
        if status == 'kernel_checked':
            targets = fact.get('kernel_targets')
            if not _strings(targets) or not all(_name(t) for t in targets):
                errors.append(f'{label}: requires safe kernel module targets')
            for field in ('statement_evidence', 'publication_evidence'):
                if not _strings(fact.get(field)):
                    errors.append(f'{label}: requires {field} IDs')
        if status == 'unnecessary' and not _strings(fact.get('unnecessary_evidence')):
            errors.append(f'{label}: unnecessary disposition requires evidence IDs')

    # Iterative graph traversal avoids a recursion limit on long proof chains.
    visited, active = set(), set()
    for start in facts:
        if start in visited:
            continue
        stack = [(start, False)]
        while stack:
            node, leaving = stack.pop()
            if leaving:
                active.discard(node)
                visited.add(node)
            elif node in active:
                errors.append(f'dependency cycle at {node!r}')
            elif node not in visited and node in facts:
                active.add(node)
                stack.append((node, True))
                stack.extend((dep, False) for dep in reversed(edges.get(node, [])))
    reachable = set()
    pending = [target] if isinstance(target, str) and target in facts else []
    while pending:
        node = pending.pop()
        if node not in reachable and node in facts:
            reachable.add(node)
            pending.extend(edges.get(node, []))
    for fact_id in facts.keys() - reachable:
        errors.append(f'fact {fact_id!r}: outside the target dependency chain')
    return errors


if __name__ == '__main__':
    import argparse
    import json
    parser = argparse.ArgumentParser(description='Preflight the same dependency schema used by the controller')
    parser.add_argument('--record', type=Path, required=True)
    parser.add_argument('--sources', type=Path, required=True)
    args = parser.parse_args()
    state = json.loads((args.record / 'state.json').read_text())
    problems = validate_chain(state.get('implementation_chain'), args.sources)
    for problem in problems:
        print(problem)
    if not problems:
        print('Dependency record format valid; no mathematical or kernel certification implied.')
    raise SystemExit(bool(problems))
