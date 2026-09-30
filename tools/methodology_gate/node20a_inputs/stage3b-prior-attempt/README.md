# Unreviewed Stage 3b submission, preserved (operator note; no new mathematics)

This is the complete submission of Stage 3b attempt `89bb279bfe7f461f947488ebfa49d162`
of run `node20a-2026-09-29-c6`. The controller rejected it **before review**, and the
rejection had nothing to do with its mathematics. Its `/output` directory still held a
`build/` tree of Lake products with symlinks. The controller refuses symlinks anywhere
under `/output`: `Symlink rejected: …/build/Hypostructure/CT1/Automation.ilean`. No
reviewer ever saw the submission.

What the attempt reported: one derived fact, with S1–S3 and the weakest-case
projections checked. Its own sandbox ran the direct Lean checks and
`lake build HypostructureErdos64EG.Assembly.Final` under the lane lock, and all passed.

The files here are copied byte for byte and omit the build products:

* `changes/`: the replacement source files the attempt submitted (Stage 3b allowed paths);
* `record/stage3b-event.json`: its single Stage 3b event, its new fact and its evidence index;
* `record/evidence/`: its evidence files;
* `stage3b-reasoning.md`, the kernel-certificate files and the logs.

Under the executor prompt's rule for a controller-only format or validator failure,
the next Stage 3b executor may reuse this exact mathematical artifact, its evidence
and its source changes. It still has to make one fresh current-stage event on the
current record, and it has to leave `/output` holding only `record/` and `changes/`.
The two independent reviewers still judge the mathematics.
