#!/usr/bin/env python3
"""Build/check frozen worker references from the shared workflow and public guide."""
import argparse
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
POLICY = Path(__file__).resolve().parent / 'policy'
SOURCES = ('web/frontend/src/methodology/ExecutionRecipe.tsx',
           'web/frontend/src/methodology/recipe-reference.ts',
           'web/frontend/src/methodology/TaskRunViewer.tsx',
           'tools/methodology_gate/policy/workflow.json',
           'tools/methodology_gate/policy/structural-register.json')


def generated():
    spec = json.loads((POLICY / 'workflow.json').read_text())
    taskflow = spec['taskflow']
    text = '# Structural mathematical reasoning benchmark protocol\n\n' + spec['rule'] + '\n\n'
    text += ('The task and stage controllers use the shared benchmark contracts below. '
             'Mathematical proof facts are supplied by their accepted evidence.\n\n')
    isolation = '\n\n'.join(taskflow['context_policy'].values())
    text += '## Fresh context for every atomic task\n\n' + isolation + '\n\n'
    text += '## Phase 0. ' + taskflow['phase_zero']['title'] + '\n\n'
    text += taskflow['phase_zero']['gate'] + '\n\nTasks: ' + ', '.join(taskflow['phase_zero']['tasks']) + '.\n\n'
    for number, phase in taskflow['phase_descriptions'].items():
        text += (f"## Phase {number}. {phase['title']}\n\nInput: {phase['input']}\n\n"
                 f"Output: {phase['output']}\n\nGate: {phase['gate']}\n\n"
                 f"Atomic tasks: {', '.join(taskflow['phase_tasks'][number])}.\n\n")
    text += ('## Three completion units\n\n' + '\n\n'.join(
        f"**{name}:** {description}" for name, description in taskflow['units'].items()) + '\n\n')
    text += ('## Stage assignment contracts\n\n' + spec['accepted_stage_rule'] + '\n\n')
    text += ('Preflight proves the conditional payoff; execution constructs the output and proves actual advancement. '
             'No useful auxiliary lemma or paid interface field alone completes a productive step.\n\n')
    for stage in spec['stages']:
        text += (f"## {stage['number']}. {stage['title']}\n\nInput: {stage['input']}\n\n"
                 f"Required result: {stage['output']}\n\nReview: {stage['review']}\n\n"
                 f"Gates: {', '.join(stage['gates'])}.\n\n")
    text += ('## Shared requirements\n\nStage 1 is one compact prior-use table: registered structure, the move that '
             'used it and its effect on this residual. Trust proof obligations before the requested node; do not '
             're-prove ancestors, reconstruct the residual in Stage 1, or scan unrelated sources. Stage 2 maps and '
             'classifies the exact incoming residual and its bound witnesses. Every stage contract names a nonempty '
             'source scope; there is no full-tree fallback. The residual remains the sole mathematical object. A '
             'register never substitutes for residual-case analysis, and no arbitrary mathematical object may be '
             'introduced without an authorized construction. “No productive aspect/technique” is an execution defect, '
             'not an accepted outcome or proof conclusion; repair the earliest incomplete residual analysis. The final '
             'check concerns the new result at this node and its direct consumer, not already-proved ancestors. Read '
             'executor-prompt.md, reviewer-prompt.md and record-format.md for the exact artifact fields. A failed '
             'technique does not exhaust a property.\n')
    prompt = ('# Execute one textbook-reasoning benchmark task\n\nRequired fields: ' +
              ', '.join(taskflow['task_fields']) + '.\n\n' +
              taskflow['worker_instruction'] + '\n\n' + isolation + '\n\nReturn one of: ' +
              ', '.join(taskflow['worker_results']) + '.\n\nResult fields: ' +
              ', '.join(taskflow['result_fields']) + '.\nMetadata fields: ' +
              ', '.join(taskflow['metadata_fields']) + '.\nMove fields: ' +
              ', '.join(taskflow['move_fields']) + '.\n')
    outputs = {POLICY / 'references/protocol.md': text,
               POLICY / 'references/task-prompt.md': prompt}
    for source in SOURCES[:3]:
        outputs[POLICY / 'references' / Path(source).name] = (REPO / source).read_text()
    outputs[POLICY / 'references/sources.json'] = json.dumps({
        source: hashlib.sha256((REPO / source).read_bytes()).hexdigest() for source in SOURCES}, indent=2) + '\n'
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    stale = []
    for path, expected in generated().items():
        if not path.exists() or path.read_text() != expected:
            stale.append(str(path.relative_to(REPO)))
            if not args.check:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(expected)
    if args.check and stale:
        parser.exit(1, 'Stale frozen policy references:\n' + '\n'.join(stale) + '\n')
    print('Shared policy and frozen references agree.' if not stale else 'Rebuilt frozen policy references.')


if __name__ == '__main__':
    main()
