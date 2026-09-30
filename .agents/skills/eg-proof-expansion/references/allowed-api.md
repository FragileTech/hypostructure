# Allowed Hypostructure API

This workflow benchmarks structural mathematical reasoning: identifying relevant structure, applying established textbook mathematics, and implementing the resulting deductions in an unfamiliar controlled setting. Execute the assigned local task from its supplied hypotheses and accepted results. Assess the actual inference required; the surrounding research topic does not determine the difficulty of that inference.

Identify the retained objects, match the hypotheses of the relevant textbook result, execute the deduction, and check the requested output. Give routine steps concise, sufficient justification. Reuse accepted prerequisites at their stated types and domains. A review objection identifies a concrete missing hypothesis, invalid inference, domain mismatch, or unmet task contract and its local repair. Preserve the assigned objectives, stage boundaries, mathematical statements, and required checks.

This file is the normative plumbing allowlist for EG proof expansion.  It is
generated from the compiled Lean environment by `scripts/api_catalog.py`; do
not hand-edit the generated declaration catalog.

## Operational boundary

- The generated declarations below are the complete plumbing allowlist.  A
  public declaration elsewhere in the repository is not implicitly allowed.
- `Core.Residual.ExactLedger` is the only residual/history carrier.  Its type
  indices are the active residual and complete branch-local exact-key list.
  Each residual domain has one closed `FactSystem`, so a decidable key fixes
  one value schema and one refinement transport.  Retrieval is by
  `ExactLedger.get` or sealed `FactInputs.get`.
- A CT and a Strategy use the same `AtomicCT` executor and indexed
  `ExactLedger` output.  The output fact index is definitionally
  `manifest.Produces ++ known`.  Every cross-step theorem, certificate,
  branch decision, and datum
  must occur in `manifest.Produces`; no payload or terminal side channel
  exists.
- `AtomicCT` has no predecessor parameter.  One executor runs after any
  canonical branch cursor whose ledger contains its exact declared
  requirements; it cannot encode a producer, row, or authored execution order.
  `AtomicStrategy` is only a definitional alias and uses `AtomicCT.run`; no
  duplicate Strategy constructor, runner, conversion, or output type exists.
- Executors receive only `FactInputs`: the current residual and exactly the
  facts declared in `manifest.Requires`.  They never receive a predecessor,
  query path, producer identity, or execution-order cursor.
- Every manifest has a nonempty, duplicate-free production list.  Residual
  changes require `RefinementSystem.Refines`.  The sole `FactSystem` supplies
  transport for every key, so lookup on a descendant is
  branch-local and preserves the complete ancestry.
- `RoutedTask.selectFor` and `RoutedTask.dispatchFor` are the only scheduling
  entry points.  They compare exact keys in the canonical branch index; names
  are diagnostics only.
- The sealed `Core.Strategy.Dag.Blueprint` declarations may author topology,
  but may not transport facts or replace canonical execution.
- Generic Core, CT, Graph, or Mathlib declarations not listed here may prove
  mathematics.  They may not carry a residual, history, fact, branch result,
  execution result, or route.

No history, query, stage, store, flow, producer-specific record, product,
sigma wrapper, callback, or route payload may carry a fact beside
`ExactLedger`.

`ExactLedger.root`, `ExactLedger.append`, `ExactLedger.publishFact`,
`ExactLedger.refine`, `ExactLedger.initializeScope`, `FactInputs.ofLedger`, and
`AtomicCT.create` are framework implementation boundaries and are
intentionally omitted below.  Proof-specific EG code may not call them.  Add
or repair a proof-agnostic registered Strategy/CT adapter instead.
The boundary checker also rejects opening their namespaces to spell these
operations unqualified, and rejects any non-presentation declaration added to
the application-owned `Problem.lean`.

`ExactLedger.initializeScope` can run only on an exactly empty fact index and
publishes the first nonempty bundle.  It cannot archive an existing fact.
Every later residual transition is a proved refinement, so every fact in the
history remains queryable at the active residual.

`ExactLedger.audit` is the public proof-free audit operation.  It reports every
exact fact name and every chronological commit without exposing proof bundles
or predecessor cursors; `ExactLedger.audit_complete` certifies that the two
views account for the same append-only history,
`ExactLedger.audit_facts_unique` rules out duplicate semantic facts, and
`ExactLedger.audit_commits_nonempty` rules out empty history entries.

Raw ancestry materialization, key-index inspection, manifest readiness over
caller-supplied lists, and route-order helpers are also omitted.
Read facts only with `ExactLedger.get` outside an executor or `FactInputs.get`
inside one; schedule only with `RoutedTask.selectFor` or
`RoutedTask.dispatchFor`.

If an operation is absent below, do not emulate it in the EG application.  Add
a proof-agnostic framework API and generic fixture, then regenerate this file.

## Generated declaration catalog

Run `python3 .agents/skills/eg-proof-expansion/scripts/api_catalog.py refresh
--repo-root .` to populate this section.

<!-- BEGIN GENERATED API -->
Compiled declarations: **1066**.

Category counts: **Canonical execution** 33, **Canonical exhaustive decisions** 11, **Canonical fact-only steps and branch decisions** 5, **Canonical ledger** 98, **Canonical manifest** 35, **Canonical residual domain** 16, **Canonical scope initialization** 6, **Minimum-degree cycle spine rows** 182, **Minimum-degree cycle spine vocabulary** 646, **Sealed topology** 6, **Sealed total closure** 12, **Typed partial topology and sealed completion** 16.

The `type` fields below come from the compiled Lean environment.  Docstrings
and comments are deliberately excluded.

### `Hypostructure.Core.Residual.ExactLedger`

#### `Hypostructure.Core.Residual.AuditSnapshot`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Residual.AuditSnapshot.commits`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AuditSnapshot → List Core.Residual.CommitRecord
```

#### `Hypostructure.Core.Residual.AuditSnapshot.facts`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AuditSnapshot → List Name
```

#### `Hypostructure.Core.Residual.AuditSnapshot.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
List Name → List Core.Residual.CommitRecord → Core.Residual.AuditSnapshot
```

#### `Hypostructure.Core.Residual.AutomaticClosureReason`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Residual.AutomaticClosureReason.emptyResidual`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.AutomaticClosureReason.impossibleFact`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Name → Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.AutomaticClosureReason.incompatibleFacts`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Name → Name → Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.ClosureEvidence`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Residual.ClosureEvidence.contradiction`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ (self : Core.Residual.ClosureEvidence), False
```

#### `Hypostructure.Core.Residual.ClosureEvidence.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AutomaticClosureReason → False → Core.Residual.ClosureEvidence
```

#### `Hypostructure.Core.Residual.ClosureEvidence.reason`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.ClosureEvidence → Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.CommitInfo`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Residual.CommitInfo.checks`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitInfo → ℕ
```

#### `Hypostructure.Core.Residual.CommitInfo.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Name → ℕ → ℕ → Core.Residual.CommitInfo
```

#### `Hypostructure.Core.Residual.CommitInfo.producer`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitInfo → Name
```

#### `Hypostructure.Core.Residual.CommitInfo.work`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitInfo → ℕ
```

#### `Hypostructure.Core.Residual.CommitRecord`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Residual.CommitRecord.info`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitRecord → Core.Residual.CommitInfo
```

#### `Hypostructure.Core.Residual.CommitRecord.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
List Name → Core.Residual.CommitInfo → Core.Residual.CommitRecord
```

#### `Hypostructure.Core.Residual.CommitRecord.produced`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitRecord → List Name
```

#### `Hypostructure.Core.Residual.ExactLedger`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Residual → Core.Residual.FactKeys Residual → Type (max uResidual (uKey + 1) (uValue + 2))
```

#### `Hypostructure.Core.Residual.ExactLedger.audit`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known → Core.Residual.AuditSnapshot
```

#### `Hypostructure.Core.Residual.ExactLedger.audit_commits_nonempty`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] {current : Residual} {known : Core.Residual.FactKeys Residual}
  (history : Core.Residual.ExactLedger Residual current known),
  List.Forall (fun record => record.produced ≠ []) history.audit.commits
```

#### `Hypostructure.Core.Residual.ExactLedger.audit_complete`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] {current : Residual} {known : Core.Residual.FactKeys Residual}
  (history : Core.Residual.ExactLedger Residual current known),
  history.audit.facts = List.flatMap (fun record => record.produced) history.audit.commits.reverse
```

#### `Hypostructure.Core.Residual.ExactLedger.audit_facts_unique`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [system : Core.Residual.FactSystem Residual] {current : Residual} {known : Core.Residual.FactKeys Residual}
  (history : Core.Residual.ExactLedger Residual current known), history.audit.facts.Nodup
```

#### `Hypostructure.Core.Residual.ExactLedger.currentOf`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} → Core.Residual.ExactLedger Residual current known → Residual
```

#### `Hypostructure.Core.Residual.ExactLedger.get`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            (key : Core.Residual.FactKey Residual) → [Core.Residual.FactKeys.Has key known] → key.At current
```

#### `Hypostructure.Core.Residual.ExactLedger.getPresent`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            (key : Core.Residual.FactKey Residual) → key ∈ known → key.At current
```

#### `Hypostructure.Core.Residual.ExactLedger.latestInfo?`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known → Option Core.Residual.CommitInfo
```

#### `Hypostructure.Core.Residual.FactKey`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [system : Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Residual.FactKey.At`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] → Core.Residual.FactKey Residual → Residual → Type uValue
```

#### `Hypostructure.Core.Residual.FactKey.name`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] → Core.Residual.FactKey Residual → Name
```

#### `Hypostructure.Core.Residual.FactKey.no_data_channel`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] {Observation : Sort w} {key : Core.Residual.FactKey Residual}
  {residual : Residual} (read : key.At residual → Observation) (left right : key.At residual), read left = read right
```

#### `Hypostructure.Core.Residual.FactKey.transport`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {new old : Residual} → Core.Residual.RefinementSystem.Refines new old → key.At old → key.At new
```

#### `Hypostructure.Core.Residual.FactKeys`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Residual.FactKeys.Has`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKey Residual → Core.Residual.FactKeys Residual → Type uKey
```

#### `Hypostructure.Core.Residual.FactKeys.Has.member`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    {inst_1 : Core.Residual.FactSystem Residual} →
      {key : Core.Residual.FactKey Residual} →
        {keys : Core.Residual.FactKeys Residual} →
          [self : Core.Residual.FactKeys.Has key keys] → Core.Residual.FactKeys.Member key keys
```

#### `Hypostructure.Core.Residual.FactKeys.Has.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {keys : Core.Residual.FactKeys Residual} →
          Core.Residual.FactKeys.Member key keys → Core.Residual.FactKeys.Has key keys
```

#### `Hypostructure.Core.Residual.FactKeys.Member`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKey Residual → Core.Residual.FactKeys Residual → Type uKey
```

#### `Hypostructure.Core.Residual.FactKeys.Member.appendLeft`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {left : Core.Residual.FactKeys Residual} →
          (right : Core.Residual.FactKeys Residual) →
            Core.Residual.FactKeys.Member key left → Core.Residual.FactKeys.Member key (left ++ right)
```

#### `Hypostructure.Core.Residual.FactKeys.Member.appendRight`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {right : Core.Residual.FactKeys Residual} →
          (left : Core.Residual.FactKeys Residual) →
            Core.Residual.FactKeys.Member key right → Core.Residual.FactKeys.Member key (left ++ right)
```

#### `Hypostructure.Core.Residual.FactKeys.Member.head`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {tail : List (Core.Residual.FactKey Residual)} → Core.Residual.FactKeys.Member key (key :: tail)
```

#### `Hypostructure.Core.Residual.FactKeys.Member.tail`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {tail : Core.Residual.FactKeys Residual} →
          {other : Core.Residual.FactKey Residual} →
            Core.Residual.FactKeys.Member key tail → Core.Residual.FactKeys.Member key (other :: tail)
```

#### `Hypostructure.Core.Residual.FactKeys.Values`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Residual → Core.Residual.FactKeys Residual → Type (max uResidual uKey (uValue + 2))
```

#### `Hypostructure.Core.Residual.FactKeys.Values.cons`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {residual : Residual} →
        {key : Core.Residual.FactKey Residual} →
          {tail : Core.Residual.FactKeys Residual} →
            key.At residual →
              Core.Residual.FactKeys.Values residual tail → Core.Residual.FactKeys.Values residual (key :: tail)
```

#### `Hypostructure.Core.Residual.FactKeys.Values.nil`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → {residual : Residual} → Core.Residual.FactKeys.Values residual []
```

#### `Hypostructure.Core.Residual.FactKeys.instHasConsFactKey`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {tail : Core.Residual.FactKeys Residual} → Core.Residual.FactKeys.Has key (key :: tail)
```

#### `Hypostructure.Core.Residual.FactKeys.instHasConsFactKey_1`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key other : Core.Residual.FactKey Residual} →
        {tail : Core.Residual.FactKeys Residual} →
          [found : Core.Residual.FactKeys.Has key tail] → Core.Residual.FactKeys.Has key (other :: tail)
```

#### `Hypostructure.Core.Residual.FactKeys.instHasHAppend`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {left right : Core.Residual.FactKeys Residual} →
          [found : Core.Residual.FactKeys.Has key right] → Core.Residual.FactKeys.Has key (left ++ right)
```

#### `Hypostructure.Core.Residual.FactKeys.instHasHAppend_1`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {left right : Core.Residual.FactKeys Residual} →
          [found : Core.Residual.FactKeys.Has key left] → Core.Residual.FactKeys.Has key (left ++ right)
```

#### `Hypostructure.Core.Residual.FactKeys.names`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Residual.FactKeys Residual → List Name
```

#### `Hypostructure.Core.Residual.FactKeys.names_append`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (left right : Core.Residual.FactKeys Residual),
  (left ++ right).names = left.names ++ right.names
```

#### `Hypostructure.Core.Residual.FactKeys.names_cons`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (key : Core.Residual.FactKey Residual)
  (tail : Core.Residual.FactKeys Residual), Core.Residual.FactKeys.names (key :: tail) = key.name :: tail.names
```

#### `Hypostructure.Core.Residual.FactKeys.names_nil`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual], Core.Residual.FactKeys.names [] = []
```

#### `Hypostructure.Core.Residual.FactSystem`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [Core.Residual.RefinementSystem Residual] → Type (max (max (uKey + 1) uResidual) (uValue + 1))
```

#### `Hypostructure.Core.Residual.FactSystem.Key`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  {inst : Core.Residual.RefinementSystem Residual} → [self : Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Residual.FactSystem.Value`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] → Core.Residual.FactSystem.Key Residual → Residual → Type uValue
```

#### `Hypostructure.Core.Residual.FactSystem.closureEvidence`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] →
      (residual : Residual) →
        Core.Residual.FactSystem.Value Core.Residual.FactSystem.closureKey residual → Core.Residual.ClosureEvidence
```

#### `Hypostructure.Core.Residual.FactSystem.closureKey`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] → Core.Residual.FactSystem.Key Residual
```

#### `Hypostructure.Core.Residual.FactSystem.closureValue`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] →
      (residual : Residual) →
        Core.Residual.ClosureEvidence → Core.Residual.FactSystem.Value Core.Residual.FactSystem.closureKey residual
```

#### `Hypostructure.Core.Residual.FactSystem.closure_name`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Residual.FactSystem Residual],
  Core.Residual.FactSystem.name Core.Residual.FactSystem.closureKey = Core.Residual.closureFactName
```

#### `Hypostructure.Core.Residual.FactSystem.keyDecidableEq`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] → DecidableEq (Core.Residual.FactSystem.Key Residual)
```

#### `Hypostructure.Core.Residual.FactSystem.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    (Key : Type uKey) →
      DecidableEq Key →
        (name : Key → Name) →
          Function.Injective name →
            (Value : Key → Residual → Type uValue) →
              (∀ (key : Key) (residual : Residual), Subsingleton (Value key residual)) →
                ({key : Key} →
                    {new old : Residual} →
                      Core.Residual.RefinementSystem.Refines new old → Value key old → Value key new) →
                  (closureKey : Key) →
                    name closureKey = Core.Residual.closureFactName →
                      ((residual : Residual) → Core.Residual.ClosureEvidence → Value closureKey residual) →
                        ((residual : Residual) → Value closureKey residual → Core.Residual.ClosureEvidence) →
                          Core.Residual.FactSystem Residual
```

#### `Hypostructure.Core.Residual.FactSystem.name`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] → Core.Residual.FactSystem.Key Residual → Name
```

#### `Hypostructure.Core.Residual.FactSystem.name_injective`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Residual.FactSystem Residual], Function.Injective Core.Residual.FactSystem.name
```

#### `Hypostructure.Core.Residual.FactSystem.transport`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactSystem.Key Residual} →
        {new old : Residual} →
          Core.Residual.RefinementSystem.Refines new old →
            Core.Residual.FactSystem.Value key old → Core.Residual.FactSystem.Value key new
```

#### `Hypostructure.Core.Residual.FactSystem.transport_refl`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (key : Core.Residual.FactKey Residual) (residual : Residual)
  (value : key.At residual), Core.Residual.FactKey.transport ⋯ value = value
```

#### `Hypostructure.Core.Residual.FactSystem.transport_trans`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (key : Core.Residual.FactKey Residual) {new middle old : Residual}
  (new_middle : Core.Residual.RefinementSystem.Refines new middle)
  (middle_old : Core.Residual.RefinementSystem.Refines middle old) (value : key.At old),
  Core.Residual.FactKey.transport ⋯ value =
    Core.Residual.FactKey.transport new_middle (Core.Residual.FactKey.transport middle_old value)
```

#### `Hypostructure.Core.Residual.FactSystem.value_subsingleton`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Residual.FactSystem Residual] (key : Core.Residual.FactSystem.Key Residual) (residual : Residual),
  Subsingleton (Core.Residual.FactSystem.Value key residual)
```

#### `Hypostructure.Core.Residual.RefinementSystem`

- Category: Canonical ledger
- Kind: `inductive`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Type uResidual → Type (max uResidual (uSubject + 1))
```

#### `Hypostructure.Core.Residual.RefinementSystem.Refines`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} → [self : Core.Residual.RefinementSystem Residual] → Residual → Residual → Prop
```

#### `Hypostructure.Core.Residual.RefinementSystem.Subject`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(Residual : Type uResidual) → [self : Core.Residual.RefinementSystem Residual] → Type uSubject
```

#### `Hypostructure.Core.Residual.RefinementSystem.mk`

- Category: Canonical ledger
- Kind: `constructor`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  (Subject : Type uSubject) →
    (subject : Residual → Subject) →
      (Refines : Residual → Residual → Prop) →
        (∀ (residual : Residual), Refines residual residual) →
          (∀ {new middle old : Residual}, Refines new middle → Refines middle old → Refines new old) →
            (∀ {new old : Residual}, Refines new old → subject new = subject old) →
              Core.Residual.RefinementSystem Residual
```

#### `Hypostructure.Core.Residual.RefinementSystem.refl`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [self : Core.Residual.RefinementSystem Residual] (residual : Residual),
  Core.Residual.RefinementSystem.Refines residual residual
```

#### `Hypostructure.Core.Residual.RefinementSystem.subject`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [self : Core.Residual.RefinementSystem Residual] → Residual → Core.Residual.RefinementSystem.Subject Residual
```

#### `Hypostructure.Core.Residual.RefinementSystem.subjectOf`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [system : Core.Residual.RefinementSystem Residual] → Residual → Core.Residual.RefinementSystem.Subject Residual
```

#### `Hypostructure.Core.Residual.RefinementSystem.subject_eq`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [self : Core.Residual.RefinementSystem Residual] {new old : Residual},
  Core.Residual.RefinementSystem.Refines new old →
    Core.Residual.RefinementSystem.subject new = Core.Residual.RefinementSystem.subject old
```

#### `Hypostructure.Core.Residual.RefinementSystem.trans`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [self : Core.Residual.RefinementSystem Residual] {new middle old : Residual},
  Core.Residual.RefinementSystem.Refines new middle →
    Core.Residual.RefinementSystem.Refines middle old → Core.Residual.RefinementSystem.Refines new old
```

#### `Hypostructure.Core.Residual.closureFactName`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Name
```

#### `Hypostructure.Core.Residual.factValueSubsingleton`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [system : Core.Residual.FactSystem Residual] (key : Core.Residual.FactSystem.Key Residual) (residual : Residual),
  Subsingleton (Core.Residual.FactSystem.Value key residual)
```

#### `Hypostructure.Core.Residual.instDecidableEqAuditSnapshot`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
DecidableEq Core.Residual.AuditSnapshot
```

#### `Hypostructure.Core.Residual.instDecidableEqAuditSnapshot.decEq`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(x x_1 : Core.Residual.AuditSnapshot) → Decidable (x = x_1)
```

#### `Hypostructure.Core.Residual.instDecidableEqAutomaticClosureReason`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
DecidableEq Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.instDecidableEqAutomaticClosureReason.decEq`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(x x_1 : Core.Residual.AutomaticClosureReason) → Decidable (x = x_1)
```

#### `Hypostructure.Core.Residual.instDecidableEqCommitInfo`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
DecidableEq Core.Residual.CommitInfo
```

#### `Hypostructure.Core.Residual.instDecidableEqCommitInfo.decEq`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(x x_1 : Core.Residual.CommitInfo) → Decidable (x = x_1)
```

#### `Hypostructure.Core.Residual.instDecidableEqCommitRecord`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
DecidableEq Core.Residual.CommitRecord
```

#### `Hypostructure.Core.Residual.instDecidableEqCommitRecord.decEq`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
(x x_1 : Core.Residual.CommitRecord) → Decidable (x = x_1)
```

#### `Hypostructure.Core.Residual.instDecidableEqKey`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] → DecidableEq (Core.Residual.FactSystem.Key Residual)
```

#### `Hypostructure.Core.Residual.instReprAuditSnapshot`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Repr Core.Residual.AuditSnapshot
```

#### `Hypostructure.Core.Residual.instReprAuditSnapshot.repr`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AuditSnapshot → ℕ → Format
```

#### `Hypostructure.Core.Residual.instReprAutomaticClosureReason`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Repr Core.Residual.AutomaticClosureReason
```

#### `Hypostructure.Core.Residual.instReprAutomaticClosureReason.repr`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.AutomaticClosureReason → ℕ → Format
```

#### `Hypostructure.Core.Residual.instReprCommitInfo`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Repr Core.Residual.CommitInfo
```

#### `Hypostructure.Core.Residual.instReprCommitInfo.repr`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitInfo → ℕ → Format
```

#### `Hypostructure.Core.Residual.instReprCommitRecord`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Repr Core.Residual.CommitRecord
```

#### `Hypostructure.Core.Residual.instReprCommitRecord.repr`

- Category: Canonical ledger
- Kind: `definition`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
Core.Residual.CommitRecord → ℕ → Format
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.AtomicCT`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [Core.Residual.FactSystem Residual] → Type (max (max uKey uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.AtomicCT.id`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.AtomicCT Residual → Name
```

#### `Hypostructure.Core.Strategy.AtomicCT.manifest`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.AtomicCT Residual → Core.Strategy.FactManifest Residual
```

#### `Hypostructure.Core.Strategy.AtomicCT.outputResidual`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          (ct : Core.Strategy.AtomicCT Residual) →
            [Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
              Core.Residual.ExactLedger Residual current known → Residual
```

#### `Hypostructure.Core.Strategy.AtomicCT.run`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          (ct : Core.Strategy.AtomicCT Residual) →
            [inst_2 : Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
              (previous : Core.Residual.ExactLedger Residual current known) →
                autoParam (List.Disjoint ct.manifest.Produces known) Core.Strategy.AtomicCT.run._auto_1 →
                  Core.Residual.ExactLedger Residual (ct.outputResidual previous) (ct.manifest.Produces ++ known)
```

#### `Hypostructure.Core.Strategy.AtomicCT.runAndCloseIfEmpty`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      [inst_1 : Core.Strategy.EmptinessOracle Residual] →
        {current : Residual} →
          {known : Core.Residual.FactKeys Residual} →
            (ct : Core.Strategy.AtomicCT Residual) →
              [inst_2 : Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
                (previous : Core.Residual.ExactLedger Residual current known) →
                  (commitFresh :
                      autoParam (List.Disjoint ct.manifest.Produces known)
                        Core.Strategy.AtomicCT.runAndCloseIfEmpty._auto_1) →
                    autoParam (Core.Residual.FactSystem.closureKey ∉ ct.manifest.Produces ++ known)
                        Core.Strategy.AtomicCT.runAndCloseIfEmpty._auto_3 →
                      Core.Strategy.EmptinessResult (ct.run previous commitFresh)
```

#### `Hypostructure.Core.Strategy.AtomicCT.runAndCloseIncompatible`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          (ct : Core.Strategy.AtomicCT Residual) →
            [inst_1 : Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
              (previous : Core.Residual.ExactLedger Residual current known) →
                (left right : Core.Residual.FactKey Residual) →
                  [Core.Residual.FactKeys.Has left known] →
                    [Core.Residual.FactKeys.Has right ct.manifest.Produces] →
                      [Core.Strategy.Incompatible Residual left right] →
                        autoParam (List.Disjoint ct.manifest.Produces known)
                            Core.Strategy.AtomicCT.runAndCloseIncompatible._auto_1 →
                          autoParam (Core.Residual.FactSystem.closureKey ∉ ct.manifest.Produces ++ known)
                              Core.Strategy.AtomicCT.runAndCloseIncompatible._auto_3 →
                            Core.Residual.ExactLedger Residual (ct.outputResidual previous)
                              (Core.Residual.FactSystem.closureKey :: (ct.manifest.Produces ++ known))
```

### `Hypostructure.Core.Strategy.AtomicDecision`

#### `Hypostructure.Core.Strategy.AtomicDecision`

- Category: Canonical exhaustive decisions
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [Core.Residual.FactSystem Residual] → Type (max (max uKey uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.AtomicDecision.id`

- Category: Canonical exhaustive decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.AtomicDecision Residual → Name
```

#### `Hypostructure.Core.Strategy.AtomicDecision.manifest`

- Category: Canonical exhaustive decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.AtomicDecision Residual → Core.Strategy.DecisionManifest Residual
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.AtomicResult`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactManifest Residual → Residual → Type (max (max uKey uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.AtomicResult.checks`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {manifest : Core.Strategy.FactManifest Residual} →
        {next : Residual} → Core.Strategy.AtomicResult manifest next → ℕ
```

#### `Hypostructure.Core.Strategy.AtomicResult.facts`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {manifest : Core.Strategy.FactManifest Residual} →
        {next : Residual} →
          Core.Strategy.AtomicResult manifest next → Core.Residual.FactKeys.Values next manifest.Produces
```

#### `Hypostructure.Core.Strategy.AtomicResult.mk`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {manifest : Core.Strategy.FactManifest Residual} →
        {next : Residual} →
          Core.Residual.FactKeys.Values next manifest.Produces → ℕ → ℕ → Core.Strategy.AtomicResult manifest next
```

#### `Hypostructure.Core.Strategy.AtomicResult.work`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {manifest : Core.Strategy.FactManifest Residual} →
        {next : Residual} → Core.Strategy.AtomicResult manifest next → ℕ
```

#### `Hypostructure.Core.Strategy.AtomicStrategy`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [Core.Residual.FactSystem Residual] → Type (max (max uKey uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.AutomaticClosureReason`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
Type
```

### `Hypostructure.Core.Strategy.ClosingProgram`

#### `Hypostructure.Core.Strategy.ClosingDag`

- Category: Sealed total closure
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  Core.Target P →
    [Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Type (max (max (max (uAmbient + 1) (uBranch + 1)) (u_1 + 1)) (u_2 + 3))
```

#### `Hypostructure.Core.Strategy.ClosingDag.ofCounterexampleScope`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  (T : Core.Target P) →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      (scope : Core.Strategy.CounterexampleScope T) →
        Core.Strategy.ClosingProgram (Core.Strategy.ProblemInput P) [scope.selection] → Core.Strategy.ClosingDag T
```

#### `Hypostructure.Core.Strategy.ClosingDag.statement`

- Category: Sealed total closure
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} {T : Core.Target P} [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)]
  (dag : Core.Strategy.ClosingDag T), T.Statement
```

#### `Hypostructure.Core.Strategy.ClosingProgram`

- Category: Sealed total closure
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKeys Residual → Type (max (max (uKey + 1) (uResidual + 1)) (uValue + 3))
```

#### `Hypostructure.Core.Strategy.ClosingProgram.atomic`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (ct : Core.Strategy.AtomicCT Residual) →
          [Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
            Core.Strategy.ClosingProgram Residual (ct.manifest.Produces ++ known) →
              autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.ClosingProgram.atomic._auto_1 →
                autoParam (Core.Residual.FactSystem.closureKey ∉ ct.manifest.Produces)
                    Core.Strategy.ClosingProgram.atomic._auto_3 →
                  autoParam (List.Disjoint ct.manifest.Produces known) Core.Strategy.ClosingProgram.atomic._auto_5 →
                    Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.ClosingProgram.branch`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (decision : Core.Strategy.AtomicDecision Residual) →
          [Core.Strategy.FactKeys.Available decision.manifest.Requires known] →
            Core.Strategy.ClosingProgram Residual (decision.manifest.left :: known) →
              Core.Strategy.ClosingProgram Residual (decision.manifest.right :: known) →
                autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.ClosingProgram.branch._auto_1 →
                  autoParam (decision.manifest.left ∉ known) Core.Strategy.ClosingProgram.branch._auto_3 →
                    autoParam (decision.manifest.right ∉ known) Core.Strategy.ClosingProgram.branch._auto_5 →
                      Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.ClosingProgram.closeIfEmpty`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        [Core.Strategy.EmptinessOracle Residual] →
          Core.Strategy.ClosingProgram Residual known →
            autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.ClosingProgram.closeIfEmpty._auto_1 →
              Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.ClosingProgram.closeImpossible`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (key : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has key known] →
            [Core.Strategy.Impossible Residual key] →
              autoParam (Core.Residual.FactSystem.closureKey ∉ known)
                  Core.Strategy.ClosingProgram.closeImpossible._auto_1 →
                Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.ClosingProgram.closeIncompatible`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (left right : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has left known] →
            [Core.Residual.FactKeys.Has right known] →
              [Core.Strategy.Incompatible Residual left right] →
                autoParam (Core.Residual.FactSystem.closureKey ∉ known)
                    Core.Strategy.ClosingProgram.closeIncompatible._auto_1 →
                  Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.ClosingProgram.closed`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        [present : Core.Residual.FactKeys.Has Core.Residual.FactSystem.closureKey known] →
          Core.Strategy.ClosingProgram Residual known
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.ContradictionEvidence`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
Type
```

### `Hypostructure.Core.Strategy.ClosingProgram`

#### `Hypostructure.Core.Strategy.CounterexampleScope`

- Category: Sealed total closure
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  Core.Target P →
    [Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Type (max (max (max uAmbient uBranch) (u_1 + 1)) (u_2 + 2))
```

#### `Hypostructure.Core.Strategy.CounterexampleScope.selection`

- Category: Sealed total closure
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ClosingProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.CounterexampleScope T → Core.Residual.FactKey (Core.Strategy.ProblemInput P)
```

### `Hypostructure.Core.Strategy.Dag`

#### `Hypostructure.Core.Strategy.Dag.Blueprint`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  Core.Target P →
    [Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Type (max (max (max uAmbient uBranch) (uKey + 1)) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.autoroute`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.Dag.Blueprint T → optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint T
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.branch`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.Dag.Blueprint T →
        Core.Strategy.AtomicDecision (Core.Strategy.ProblemInput P) →
          optParam (Core.Strategy.Dag.Blueprint T → Core.Strategy.Dag.Blueprint T) id →
            optParam (Core.Strategy.Dag.Blueprint T → Core.Strategy.Dag.Blueprint T) id →
              optParam String "" →
                optParam String "" →
                  optParam String "" →
                    optParam String "" → optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint T
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.root`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] → Core.Strategy.Dag.Blueprint T
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.scope`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.Dag.Blueprint T → Core.Strategy.CounterexampleScope T → Core.Strategy.Dag.Blueprint T
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.step`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.Dag.Blueprint T →
        Core.Strategy.AtomicCT (Core.Strategy.ProblemInput P) →
          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint T
```

### `Hypostructure.Core.Strategy.FactOnlyStrategy`

#### `Hypostructure.Core.Strategy.Decision`

- Category: Canonical fact-only steps and branch decisions
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactOnlyStrategy.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.FactKey Residual →
            Core.Residual.FactKey Residual →
              Core.Residual.ExactLedger Residual current known → Type (max (max (uKey + 1) uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.Decision.left`

- Category: Canonical fact-only steps and branch decisions
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactOnlyStrategy.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          {left right : Core.Residual.FactKey Residual} →
            {_previous : Core.Residual.ExactLedger Residual current known} →
              Core.Residual.ExactLedger Residual current (left :: known) → Core.Strategy.Decision left right _previous
```

#### `Hypostructure.Core.Strategy.Decision.right`

- Category: Canonical fact-only steps and branch decisions
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactOnlyStrategy.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          {left right : Core.Residual.FactKey Residual} →
            {_previous : Core.Residual.ExactLedger Residual current known} →
              Core.Residual.ExactLedger Residual current (right :: known) → Core.Strategy.Decision left right _previous
```

#### `Hypostructure.Core.Strategy.Decision.run`

- Category: Canonical fact-only steps and branch decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactOnlyStrategy.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          (previous : Core.Residual.ExactLedger Residual current known) →
            (left right : Core.Residual.FactKey Residual) →
              Name →
                left.At current ⊕ right.At current →
                  autoParam (left ∉ known) Core.Strategy.Decision.run._auto_1 →
                    autoParam (right ∉ known) Core.Strategy.Decision.run._auto_3 →
                      Core.Strategy.Decision left right previous
```

### `Hypostructure.Core.Strategy.AtomicDecision`

#### `Hypostructure.Core.Strategy.DecisionManifest`

- Category: Canonical exhaustive decisions
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [system : Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Strategy.DecisionManifest.distinct`

- Category: Canonical exhaustive decisions
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [system : Core.Residual.FactSystem Residual] (self : Core.Strategy.DecisionManifest Residual), self.left ≠ self.right
```

#### `Hypostructure.Core.Strategy.DecisionManifest.left`

- Category: Canonical exhaustive decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      Core.Strategy.DecisionManifest Residual → Core.Residual.FactKey Residual
```

#### `Hypostructure.Core.Strategy.DecisionManifest.left_ne_closure`

- Category: Canonical exhaustive decisions
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [system : Core.Residual.FactSystem Residual] (self : Core.Strategy.DecisionManifest Residual),
  self.left ≠ Core.Residual.FactSystem.closureKey
```

#### `Hypostructure.Core.Strategy.DecisionManifest.mk`

- Category: Canonical exhaustive decisions
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactRequirements Residual →
        (left right : Core.Residual.FactKey Residual) →
          left ≠ right →
            left ≠ Core.Residual.FactSystem.closureKey →
              right ≠ Core.Residual.FactSystem.closureKey → Core.Strategy.DecisionManifest Residual
```

#### `Hypostructure.Core.Strategy.DecisionManifest.right`

- Category: Canonical exhaustive decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      Core.Strategy.DecisionManifest Residual → Core.Residual.FactKey Residual
```

#### `Hypostructure.Core.Strategy.DecisionManifest.right_ne_closure`

- Category: Canonical exhaustive decisions
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [system : Core.Residual.FactSystem Residual] (self : Core.Strategy.DecisionManifest Residual),
  self.right ≠ Core.Residual.FactSystem.closureKey
```

#### `Hypostructure.Core.Strategy.DecisionManifest.toFactRequirements`

- Category: Canonical exhaustive decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/AtomicDecision.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      Core.Strategy.DecisionManifest Residual → Core.Strategy.FactRequirements Residual
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.EmptinessOracle`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
(Residual : Type uResidual) → [Core.Residual.RefinementSystem Residual] → Type uResidual
```

#### `Hypostructure.Core.Strategy.EmptinessOracle.Empty`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} → [self : Core.Strategy.EmptinessOracle Residual] → Residual → Prop
```

#### `Hypostructure.Core.Strategy.EmptinessOracle.decideEmpty`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  {inst : Core.Residual.RefinementSystem Residual} →
    [self : Core.Strategy.EmptinessOracle Residual] →
      (residual : Residual) → Decidable (Core.Strategy.EmptinessOracle.Empty residual)
```

#### `Hypostructure.Core.Strategy.EmptinessOracle.impossible`

- Category: Canonical execution
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Strategy.EmptinessOracle Residual] (residual : Residual),
  Core.Strategy.EmptinessOracle.Empty residual → False
```

#### `Hypostructure.Core.Strategy.EmptinessOracle.mk`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    (Empty : Residual → Prop) →
      ((residual : Residual) → Decidable (Empty residual)) →
        (∀ (residual : Residual), Empty residual → False) → Core.Strategy.EmptinessOracle Residual
```

#### `Hypostructure.Core.Strategy.EmptinessResult`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      [oracle : Core.Strategy.EmptinessOracle Residual] →
        {current : Residual} →
          {known : Core.Residual.FactKeys Residual} →
            Core.Residual.ExactLedger Residual current known → Type (max (max (uKey + 1) uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.EmptinessResult.closed`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      [oracle : Core.Strategy.EmptinessOracle Residual] →
        {current : Residual} →
          {known : Core.Residual.FactKeys Residual} →
            {previous : Core.Residual.ExactLedger Residual current known} →
              Core.Residual.ExactLedger Residual current (Core.Residual.FactSystem.closureKey :: known) →
                Core.Strategy.EmptinessResult previous
```

#### `Hypostructure.Core.Strategy.EmptinessResult.open`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      [oracle : Core.Strategy.EmptinessOracle Residual] →
        {current : Residual} →
          {known : Core.Residual.FactKeys Residual} →
            {previous : Core.Residual.ExactLedger Residual current known} → Core.Strategy.EmptinessResult previous
```

### `Hypostructure.Core.Strategy.FactManifest`

#### `Hypostructure.Core.Strategy.FactInputs`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactRequirements Residual → Type (max (max uKey uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.FactInputs.current`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {requirements : Core.Strategy.FactRequirements Residual} → Core.Strategy.FactInputs requirements → Residual
```

#### `Hypostructure.Core.Strategy.FactInputs.get`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {requirements : Core.Strategy.FactRequirements Residual} →
        (inputs : Core.Strategy.FactInputs requirements) →
          (key : Core.Residual.FactKey Residual) →
            [Core.Residual.FactKeys.Has key requirements.Requires] → key.At inputs.current
```

#### `Hypostructure.Core.Strategy.FactKeys.Available`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKeys Residual →
        Core.Residual.FactKeys Residual → Type (max (max (uKey + 1) uResidual) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.FactKeys.instAvailableConsFactKeyOfHas`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {key : Core.Residual.FactKey Residual} →
        {tail known : Core.Residual.FactKeys Residual} →
          [found : Core.Residual.FactKeys.Has key known] →
            [rest : Core.Strategy.FactKeys.Available tail known] → Core.Strategy.FactKeys.Available (key :: tail) known
```

#### `Hypostructure.Core.Strategy.FactKeys.instAvailableNilFactKey`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} → Core.Strategy.FactKeys.Available [] known
```

#### `Hypostructure.Core.Strategy.FactManifest`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Strategy.FactManifest.Produces`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.FactManifest Residual → Core.Residual.FactKeys Residual
```

#### `Hypostructure.Core.Strategy.FactManifest.mk`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactRequirements Residual →
        (Produces : Core.Residual.FactKeys Residual) →
          List.Nodup Produces → Produces ≠ [] → Core.Strategy.FactManifest Residual
```

#### `Hypostructure.Core.Strategy.FactManifest.producedNames`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.FactManifest Residual → List Name
```

#### `Hypostructure.Core.Strategy.FactManifest.producesNonempty`

- Category: Canonical manifest
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (self : Core.Strategy.FactManifest Residual), self.Produces ≠ []
```

#### `Hypostructure.Core.Strategy.FactManifest.producesUnique`

- Category: Canonical manifest
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (self : Core.Strategy.FactManifest Residual), List.Nodup self.Produces
```

#### `Hypostructure.Core.Strategy.FactManifest.requiredNames`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.FactManifest Residual → List Name
```

#### `Hypostructure.Core.Strategy.FactManifest.toFactRequirements`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactManifest Residual → Core.Strategy.FactRequirements Residual
```

#### `Hypostructure.Core.Strategy.FactRequirements`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Strategy.FactRequirements.Requires`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.FactRequirements Residual → Core.Residual.FactKeys Residual
```

#### `Hypostructure.Core.Strategy.FactRequirements.mk`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      (Requires : Core.Residual.FactKeys Residual) → List.Nodup Requires → Core.Strategy.FactRequirements Residual
```

#### `Hypostructure.Core.Strategy.FactRequirements.requiresUnique`

- Category: Canonical manifest
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (self : Core.Strategy.FactRequirements Residual),
  List.Nodup self.Requires
```

### `Hypostructure.Core.Strategy.ProblemResidual`

#### `Hypostructure.Core.Strategy.FactVocabulary`

- Category: Canonical residual domain
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
Core.Problem → Type (max (max (max uAmbient uBranch) (uKey + 1)) (uValue + 1))
```

#### `Hypostructure.Core.Strategy.FactVocabulary.Key`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → Core.Strategy.FactVocabulary P → Type uKey
```

#### `Hypostructure.Core.Strategy.FactVocabulary.Value`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → (self : Core.Strategy.FactVocabulary P) → self.Key → Core.Strategy.ProblemInput P → Type uValue
```

#### `Hypostructure.Core.Strategy.FactVocabulary.WithClosure`

- Category: Canonical residual domain
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → Core.Strategy.FactVocabulary P → Type uKey
```

#### `Hypostructure.Core.Strategy.FactVocabulary.WithClosure.closed`

- Category: Canonical residual domain
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → {vocabulary : Core.Strategy.FactVocabulary P} → vocabulary.WithClosure
```

#### `Hypostructure.Core.Strategy.FactVocabulary.WithClosure.fact`

- Category: Canonical residual domain
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → {vocabulary : Core.Strategy.FactVocabulary P} → vocabulary.Key → vocabulary.WithClosure
```

#### `Hypostructure.Core.Strategy.FactVocabulary.instDecidableEqWithClosure`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → (vocabulary : Core.Strategy.FactVocabulary P) → DecidableEq vocabulary.WithClosure
```

#### `Hypostructure.Core.Strategy.FactVocabulary.keyDecidableEq`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → (self : Core.Strategy.FactVocabulary P) → DecidableEq self.Key
```

#### `Hypostructure.Core.Strategy.FactVocabulary.mk`

- Category: Canonical residual domain
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  (Key : Type uKey) →
    DecidableEq Key →
      (name : Key → Name) →
        Function.Injective name →
          (∀ (key : Key), name key ≠ Core.Residual.closureFactName) →
            (Value : Key → Core.Strategy.ProblemInput P → Type uValue) →
              (∀ (key : Key) (input : Core.Strategy.ProblemInput P), Subsingleton (Value key input)) →
                ({key : Key} →
                    {new old : Core.Strategy.ProblemInput P} →
                      new.object = old.object → Value key old → Value key new) →
                  Core.Strategy.FactVocabulary P
```

#### `Hypostructure.Core.Strategy.FactVocabulary.name`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → (self : Core.Strategy.FactVocabulary P) → self.Key → Name
```

#### `Hypostructure.Core.Strategy.FactVocabulary.name_injective`

- Category: Canonical residual domain
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} (self : Core.Strategy.FactVocabulary P), Function.Injective self.name
```

#### `Hypostructure.Core.Strategy.FactVocabulary.name_ne_closure`

- Category: Canonical residual domain
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} (self : Core.Strategy.FactVocabulary P) (key : self.Key),
  self.name key ≠ Core.Residual.closureFactName
```

#### `Hypostructure.Core.Strategy.FactVocabulary.transport`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  (self : Core.Strategy.FactVocabulary P) →
    {key : self.Key} →
      {new old : Core.Strategy.ProblemInput P} → new.object = old.object → self.Value key old → self.Value key new
```

#### `Hypostructure.Core.Strategy.FactVocabulary.value_subsingleton`

- Category: Canonical residual domain
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} (self : Core.Strategy.FactVocabulary P) (key : self.Key) (input : Core.Strategy.ProblemInput P),
  Subsingleton (self.Value key input)
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.Impossible`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Residual.FactKey Residual → Prop
```

#### `Hypostructure.Core.Strategy.Impossible.contradiction`

- Category: Canonical execution
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  {inst_1 : Core.Residual.FactSystem Residual} {key : Core.Residual.FactKey Residual}
  [self : Core.Strategy.Impossible Residual key] (residual : Residual) (a : key.At residual), False
```

#### `Hypostructure.Core.Strategy.Impossible.mk`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] {key : Core.Residual.FactKey Residual},
  (∀ (residual : Residual) (a : key.At residual), False) → Core.Strategy.Impossible Residual key
```

#### `Hypostructure.Core.Strategy.Incompatible`

- Category: Canonical execution
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKey Residual → Core.Residual.FactKey Residual → Prop
```

#### `Hypostructure.Core.Strategy.Incompatible.contradiction`

- Category: Canonical execution
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  {inst_1 : Core.Residual.FactSystem Residual} {left right : Core.Residual.FactKey Residual}
  [self : Core.Strategy.Incompatible Residual left right] (residual : Residual) (a : left.At residual)
  (a : right.At residual), False
```

#### `Hypostructure.Core.Strategy.Incompatible.mk`

- Category: Canonical execution
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] {left right : Core.Residual.FactKey Residual},
  (∀ (residual : Residual) (a : left.At residual) (a : right.At residual), False) →
    Core.Strategy.Incompatible Residual left right
```

### `Hypostructure.Core.Strategy.MinimalCounterexampleScope`

#### `Hypostructure.Core.Strategy.OpenedScope`

- Category: Canonical scope initialization
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
    Core.Residual.FactKey (Core.Strategy.ProblemInput P) →
      Type (max (max (max uAmbient uBranch) (uKey + 1)) (uValue + 2))
```

#### `Hypostructure.Core.Strategy.OpenedScope.history`

- Category: Canonical scope initialization
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
    {key : Core.Residual.FactKey (Core.Strategy.ProblemInput P)} →
      (self : Core.Strategy.OpenedScope key) →
        Core.Residual.ExactLedger (Core.Strategy.ProblemInput P) self.selected [key]
```

#### `Hypostructure.Core.Strategy.OpenedScope.mk`

- Category: Canonical scope initialization
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
    {key : Core.Residual.FactKey (Core.Strategy.ProblemInput P)} →
      (selected : Core.Strategy.ProblemInput P) →
        Core.Residual.ExactLedger (Core.Strategy.ProblemInput P) selected [key] → Core.Strategy.OpenedScope key
```

#### `Hypostructure.Core.Strategy.OpenedScope.selected`

- Category: Canonical scope initialization
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
    {key : Core.Residual.FactKey (Core.Strategy.ProblemInput P)} →
      Core.Strategy.OpenedScope key → Core.Strategy.ProblemInput P
```

### `Hypostructure.Core.Strategy.FactManifest`

#### `Hypostructure.Core.Strategy.RoutedTask`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Strategy.RoutedTask.Deadlock`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Core.Strategy.RoutedTask.Deadlock.available`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
Core.Strategy.RoutedTask.Deadlock → List Name
```

#### `Hypostructure.Core.Strategy.RoutedTask.Deadlock.missing`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
Core.Strategy.RoutedTask.Deadlock → List (Name × List Name)
```

#### `Hypostructure.Core.Strategy.RoutedTask.Deadlock.mk`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
List Name → List (Name × List Name) → Core.Strategy.RoutedTask.Deadlock
```

#### `Hypostructure.Core.Strategy.RoutedTask.RouteDecision`

- Category: Canonical manifest
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] → [Core.Residual.FactSystem Residual] → Type uKey
```

#### `Hypostructure.Core.Strategy.RoutedTask.RouteDecision.closed`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.RoutedTask.RouteDecision Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.RouteDecision.deadlock`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.RoutedTask.Deadlock → Core.Strategy.RoutedTask.RouteDecision Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.RouteDecision.run`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.RoutedTask Residual → Core.Strategy.RoutedTask.RouteDecision Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.dispatchFor`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            List (Core.Strategy.RoutedTask Residual) → Core.Strategy.RoutedTask.RouteDecision Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.id`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.RoutedTask Residual → Name
```

#### `Hypostructure.Core.Strategy.RoutedTask.instReprDeadlock`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
Repr Core.Strategy.RoutedTask.Deadlock
```

#### `Hypostructure.Core.Strategy.RoutedTask.instReprDeadlock.repr`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
Core.Strategy.RoutedTask.Deadlock → ℕ → Format
```

#### `Hypostructure.Core.Strategy.RoutedTask.manifest`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Strategy.RoutedTask Residual → Core.Strategy.FactManifest Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.mk`

- Category: Canonical manifest
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Name → ℕ → Core.Strategy.FactManifest Residual → Core.Strategy.RoutedTask Residual
```

#### `Hypostructure.Core.Strategy.RoutedTask.order`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] → Core.Strategy.RoutedTask Residual → ℕ
```

#### `Hypostructure.Core.Strategy.RoutedTask.selectFor`

- Category: Canonical manifest
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            List (Core.Strategy.RoutedTask Residual) → Option (Core.Strategy.RoutedTask Residual)
```

### `Hypostructure.Core.Strategy.StrategyProgram`

#### `Hypostructure.Core.Strategy.StrategyDag`

- Category: Typed partial topology and sealed completion
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  Core.Target P →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      List (Core.Residual.FactKeys (Core.Strategy.ProblemInput P)) →
        Type (max (max (max (uAmbient + 1) (uBranch + 1)) (u_1 + 1)) (u_2 + 3))
```

#### `Hypostructure.Core.Strategy.StrategyDag.complete`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      Core.Strategy.StrategyDag T [] → Core.Strategy.ClosingDag T
```

#### `Hypostructure.Core.Strategy.StrategyDag.ofCounterexampleScope`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  (T : Core.Target P) →
    [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
      {frontier : List (Core.Residual.FactKeys (Core.Strategy.ProblemInput P))} →
        (scope : Core.Strategy.CounterexampleScope T) →
          Core.Strategy.StrategyProgram (Core.Strategy.ProblemInput P) [scope.selection] frontier →
            Core.Strategy.StrategyDag T frontier
```

#### `Hypostructure.Core.Strategy.StrategyProgram`

- Category: Typed partial topology and sealed completion
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
(Residual : Type uResidual) →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Core.Residual.FactKeys Residual →
        List (Core.Residual.FactKeys Residual) → Type (max (max (uKey + 1) (uResidual + 1)) (uValue + 3))
```

#### `Hypostructure.Core.Strategy.StrategyProgram.atomic`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        {frontier : List (Core.Residual.FactKeys Residual)} →
          (ct : Core.Strategy.AtomicCT Residual) →
            [Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
              Core.Strategy.StrategyProgram Residual (ct.manifest.Produces ++ known) frontier →
                autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.StrategyProgram.atomic._auto_1 →
                  autoParam (Core.Residual.FactSystem.closureKey ∉ ct.manifest.Produces)
                      Core.Strategy.StrategyProgram.atomic._auto_3 →
                    autoParam (List.Disjoint ct.manifest.Produces known) Core.Strategy.StrategyProgram.atomic._auto_5 →
                      Core.Strategy.StrategyProgram Residual known frontier
```

#### `Hypostructure.Core.Strategy.StrategyProgram.atomicExplicit`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        {frontier : List (Core.Residual.FactKeys Residual)} →
          (ct : Core.Strategy.AtomicCT Residual) →
            [Core.Strategy.FactKeys.Available ct.manifest.Requires known] →
              Core.Strategy.StrategyProgram Residual (ct.manifest.Produces ++ known) frontier →
                Core.Residual.FactSystem.closureKey ∉ known →
                  Core.Residual.FactSystem.closureKey ∉ ct.manifest.Produces →
                    List.Disjoint ct.manifest.Produces known → Core.Strategy.StrategyProgram Residual known frontier
```

#### `Hypostructure.Core.Strategy.StrategyProgram.branch`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        {leftFrontier rightFrontier : List (Core.Residual.FactKeys Residual)} →
          (decision : Core.Strategy.AtomicDecision Residual) →
            [Core.Strategy.FactKeys.Available decision.manifest.Requires known] →
              Core.Strategy.StrategyProgram Residual (decision.manifest.left :: known) leftFrontier →
                Core.Strategy.StrategyProgram Residual (decision.manifest.right :: known) rightFrontier →
                  autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.StrategyProgram.branch._auto_1 →
                    autoParam (decision.manifest.left ∉ known) Core.Strategy.StrategyProgram.branch._auto_3 →
                      autoParam (decision.manifest.right ∉ known) Core.Strategy.StrategyProgram.branch._auto_5 →
                        Core.Strategy.StrategyProgram Residual known (leftFrontier ++ rightFrontier)
```

#### `Hypostructure.Core.Strategy.StrategyProgram.branchExplicit`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        {leftFrontier rightFrontier : List (Core.Residual.FactKeys Residual)} →
          (decision : Core.Strategy.AtomicDecision Residual) →
            [Core.Strategy.FactKeys.Available decision.manifest.Requires known] →
              Core.Strategy.StrategyProgram Residual (decision.manifest.left :: known) leftFrontier →
                Core.Strategy.StrategyProgram Residual (decision.manifest.right :: known) rightFrontier →
                  Core.Residual.FactSystem.closureKey ∉ known →
                    decision.manifest.left ∉ known →
                      decision.manifest.right ∉ known →
                        Core.Strategy.StrategyProgram Residual known (leftFrontier ++ rightFrontier)
```

#### `Hypostructure.Core.Strategy.StrategyProgram.closeImpossible`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (key : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has key known] →
            [Core.Strategy.Impossible Residual key] →
              autoParam (Core.Residual.FactSystem.closureKey ∉ known)
                  Core.Strategy.StrategyProgram.closeImpossible._auto_1 →
                Core.Strategy.StrategyProgram Residual known []
```

#### `Hypostructure.Core.Strategy.StrategyProgram.closeImpossibleExplicit`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (key : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has key known] →
            [Core.Strategy.Impossible Residual key] →
              Core.Residual.FactSystem.closureKey ∉ known → Core.Strategy.StrategyProgram Residual known []
```

#### `Hypostructure.Core.Strategy.StrategyProgram.closeIncompatible`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (left right : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has left known] →
            [Core.Residual.FactKeys.Has right known] →
              [Core.Strategy.Incompatible Residual left right] →
                autoParam (Core.Residual.FactSystem.closureKey ∉ known)
                    Core.Strategy.StrategyProgram.closeIncompatible._auto_1 →
                  Core.Strategy.StrategyProgram Residual known []
```

#### `Hypostructure.Core.Strategy.StrategyProgram.closeIncompatibleExplicit`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        (left right : Core.Residual.FactKey Residual) →
          [Core.Residual.FactKeys.Has left known] →
            [Core.Residual.FactKeys.Has right known] →
              [Core.Strategy.Incompatible Residual left right] →
                Core.Residual.FactSystem.closureKey ∉ known → Core.Strategy.StrategyProgram Residual known []
```

#### `Hypostructure.Core.Strategy.StrategyProgram.closed`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        [Core.Residual.FactKeys.Has Core.Residual.FactSystem.closureKey known] →
          Core.Strategy.StrategyProgram Residual known []
```

#### `Hypostructure.Core.Strategy.StrategyProgram.complete`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        Core.Strategy.StrategyProgram Residual known [] → Core.Strategy.ClosingProgram Residual known
```

#### `Hypostructure.Core.Strategy.StrategyProgram.defer`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} → Core.Strategy.StrategyProgram Residual known [known]
```

#### `Hypostructure.Core.Strategy.StrategyProgram.ofClosing`

- Category: Typed partial topology and sealed completion
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/StrategyProgram.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      {known : Core.Residual.FactKeys Residual} →
        Core.Strategy.ClosingProgram Residual known → Core.Strategy.StrategyProgram Residual known []
```

### `Hypostructure.Core.Strategy.ExactExecution`

#### `Hypostructure.Core.Strategy.closeIfEmpty`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      [oracle : Core.Strategy.EmptinessOracle Residual] →
        {current : Residual} →
          {known : Core.Residual.FactKeys Residual} →
            (previous : Core.Residual.ExactLedger Residual current known) →
              autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.closeIfEmpty._auto_1 →
                Core.Strategy.EmptinessResult previous
```

#### `Hypostructure.Core.Strategy.closeImpossible`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            (key : Core.Residual.FactKey Residual) →
              [Core.Residual.FactKeys.Has key known] →
                [Core.Strategy.Impossible Residual key] →
                  autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.closeImpossible._auto_1 →
                    Core.Residual.ExactLedger Residual current (Core.Residual.FactSystem.closureKey :: known)
```

#### `Hypostructure.Core.Strategy.closeIncompatible`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [system : Core.Residual.FactSystem Residual] →
      {current : Residual} →
        {known : Core.Residual.FactKeys Residual} →
          Core.Residual.ExactLedger Residual current known →
            (left right : Core.Residual.FactKey Residual) →
              [Core.Residual.FactKeys.Has left known] →
                [Core.Residual.FactKeys.Has right known] →
                  [Core.Strategy.Incompatible Residual left right] →
                    autoParam (Core.Residual.FactSystem.closureKey ∉ known) Core.Strategy.closeIncompatible._auto_1 →
                      Core.Residual.ExactLedger Residual current (Core.Residual.FactSystem.closureKey :: known)
```

#### `Hypostructure.Core.Strategy.closeTarget`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [system : Core.Residual.RefinementSystem Residual]
  [inst : Core.Residual.FactSystem Residual] {current : Residual} {known : Core.Residual.FactKeys Residual}
  (previous : Core.Residual.ExactLedger Residual current known) (key : Core.Residual.FactKey Residual)
  [Core.Residual.FactKeys.Has key known] (Target : Core.Residual.RefinementSystem.Subject Residual → Prop),
  (∀ (residual : Residual) (a : key.At residual), Target (Core.Residual.RefinementSystem.subject residual)) →
    Target (Core.Residual.RefinementSystem.subject current)
```

### `Hypostructure.Core.Strategy.FactOnlyStrategy`

#### `Hypostructure.Core.Strategy.factOnly`

- Category: Canonical fact-only steps and branch decisions
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/FactOnlyStrategy.lean`
- Compiled type:

```lean
{Residual : Type uResidual} →
  [inst : Core.Residual.RefinementSystem Residual] →
    [inst_1 : Core.Residual.FactSystem Residual] →
      Name →
        (manifest : Core.Strategy.FactManifest Residual) →
          ((inputs : Core.Strategy.FactInputs manifest.toFactRequirements) →
              Core.Residual.FactKeys.Values inputs.current manifest.Produces) →
            optParam ℕ 0 → optParam ℕ 0 → Core.Strategy.AtomicStrategy Residual
```

### `Hypostructure.Core.Strategy.MinimalCounterexampleScope`

#### `Hypostructure.Core.Strategy.openMinimalCounterexampleScope`

- Category: Canonical scope initialization
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  [inst : Core.Residual.FactSystem (Core.Strategy.ProblemInput P)] →
    (T : Core.Target P) →
      (progress : Core.Progress P) →
        ((G : P.Ambient) → P.BranchState G) →
          (key : Core.Residual.FactKey (Core.Strategy.ProblemInput P)) →
            ((context : Core.MinimalCounterexampleContext P T.Predicate progress) →
                key.At (Core.Strategy.selectedInput context)) →
              (input : Core.Strategy.ProblemInput P) → ¬T.Predicate input.object → Core.Strategy.OpenedScope key
```

### `Hypostructure.Core.Strategy.ProblemResidual`

#### `Hypostructure.Core.Strategy.problemInputFactSystem`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
{P : Core.Problem} → Core.Strategy.FactVocabulary P → Core.Residual.FactSystem (Core.Strategy.ProblemInput P)
```

#### `Hypostructure.Core.Strategy.problemInputRefinement`

- Category: Canonical residual domain
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
(P : Core.Problem) → Core.Residual.RefinementSystem (Core.Strategy.ProblemInput P)
```

### `Hypostructure.Core.Strategy.MinimalCounterexampleScope`

#### `Hypostructure.Core.Strategy.selectedInput`

- Category: Canonical scope initialization
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/MinimalCounterexampleScope.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {Target : P.Ambient → Prop} →
    {progress : Core.Progress P} → Core.MinimalCounterexampleContext P Target progress → Core.Strategy.ProblemInput P
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.Data`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Type 1
```

#### `Hypostructure.Graph.Strategy.Spine.Data.baselineDeficitSafety`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), Graph.baselineDeficitCoefficient self.threshold ≤ self.surplusScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.boundaryProfileInhabited`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) → Inhabited data.BoundaryProfile
```

#### `Hypostructure.Graph.Strategy.Spine.Data.bridgeDeletionSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  1 + self.dischargeScale * self.threshold + 2 * self.dischargeScale ≤ self.bridgeMassFactor * self.dischargeScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.bridgeMassSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  self.threshold + 2 + self.dischargeScale ≤ self.bridgeMassFactor * self.dischargeScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.curvatureCost_eq_barrierRow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  self.curvatureCost =
    Core.Finite.CertifiedTableAggregation.binaryRowRateFloor self.windowBarrier.table self.curvatureBarrierRow
```

#### `Hypostructure.Graph.Strategy.Spine.Data.degenerateClosureRejected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), ¬self.LengthOK 2
```

#### `Hypostructure.Graph.Strategy.Spine.Data.dischargeScale_eq_four`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.dischargeScale = 4
```

#### `Hypostructure.Graph.Strategy.Spine.Data.dischargeScale_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 0 < self.dischargeScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.entropyDenominator_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 0 < self.entropyDenominator
```

#### `Hypostructure.Graph.Strategy.Spine.Data.fanCapSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  Graph.WindowCurvature.fanPackingCap self.windowOrder + 1 ≤ self.dischargeScale * self.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.Data.five_le_windowOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data), 5 ≤ data.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.freeForcesTarget`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject),
  Graph.MinimumDegreeAtLeast self.threshold object →
    Graph.InducedPathFree object self.windowOrder → Graph.HasCycleWithLength self.LengthOK object
```

#### `Hypostructure.Graph.Strategy.Spine.Data.highCentreDeficitSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  self.dischargeScale * self.threshold < 2 * self.dischargeScale + (self.threshold + 2)
```

#### `Hypostructure.Graph.Strategy.Spine.Data.joinSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.threshold * self.windowOrder + 2 ≤ 4 * self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.labelCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), (Graph.WindowCurvature.Labels self.windowOrder).card = 399
```

#### `Hypostructure.Graph.Strategy.Spine.Data.labelSizeDistribution`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  List.take 7 (Graph.WindowCurvature.sizeDistribution self.windowOrder) = [13, 60, 122, 122, 63, 17, 2]
```

#### `Hypostructure.Graph.Strategy.Spine.Data.lengthOK_iff_powerOfTwo`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (length : ℕ), self.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length
```

#### `Hypostructure.Graph.Strategy.Spine.Data.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(toParameters : Graph.Strategy.Spine.Parameters) →
  toParameters.threshold = 3 →
    3 ≤ toParameters.threshold →
      (∀ (length : ℕ), toParameters.LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) →
        (Graph.WindowCurvature.Labels toParameters.windowOrder).card = 399 →
          List.take 7 (Graph.WindowCurvature.sizeDistribution toParameters.windowOrder) =
              [13, 60, 122, 122, 63, 17, 2] →
            (∀ (object : Graph.FiniteObject),
                Graph.MinimumDegreeAtLeast toParameters.threshold object →
                  Graph.InducedPathFree object toParameters.windowOrder →
                    Graph.HasCycleWithLength toParameters.LengthOK object) →
              toParameters.LengthOK 4 →
                ¬toParameters.LengthOK 2 →
                  toParameters.dischargeScale = 4 →
                    0 < toParameters.dischargeScale →
                      Graph.WindowCurvature.fanPackingCap toParameters.windowOrder + 1 ≤
                          toParameters.dischargeScale * toParameters.threshold →
                        toParameters.dischargeScale * toParameters.threshold <
                            2 * toParameters.dischargeScale + (toParameters.threshold + 2) →
                          toParameters.threshold * toParameters.windowOrder + 2 ≤ 4 * toParameters.windowOrder →
                            toParameters.routingLabelBound =
                                Fintype.card
                                  (Graph.SameTokenRoutingGerms.RoutingLabel
                                    (Fin toParameters.threshold → Fin toParameters.threshold)
                                    (Graph.WindowCurvature.Label toParameters.windowOrder)) →
                              Graph.TokenLoad.quadraticSafetyScale ≤
                                  2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound) →
                                Graph.baselineDeficitCoefficient toParameters.threshold ≤ toParameters.surplusScale →
                                  (windowBarrierLabel :
                                      Fin toParameters.windowBarrier.size →
                                        Graph.WindowCurvature.Label toParameters.windowOrder) →
                                    (∀ (index : Fin toParameters.windowBarrier.size),
                                        windowBarrierLabel index ∈
                                          Graph.WindowCurvature.Labels toParameters.windowOrder) →
                                      Function.Injective windowBarrierLabel →
                                        (∀ label ∈ Graph.WindowCurvature.Labels toParameters.windowOrder,
                                            ∃ index, windowBarrierLabel index = label) →
                                          (∀ (row : toParameters.windowBarrier.Index)
                                              (source target : Fin toParameters.windowBarrier.size),
                                              (toParameters.windowBarrier.profile.row
                                                      (toParameters.windowBarrier.table.counts.leftLength row)
                                                      source).getLsb
                                                  target =
                                                decide
                                                  (Graph.WindowCurvature.Safe
                                                    (toParameters.windowBarrier.table.counts.leftLength row)
                                                    (windowBarrierLabel source) (windowBarrierLabel target))) →
                                            (∀ (row : toParameters.windowBarrier.Index)
                                                (source target : Fin toParameters.windowBarrier.size),
                                                (toParameters.windowBarrier.profile.row
                                                        (toParameters.windowBarrier.table.counts.rightLength row)
                                                        source).getLsb
                                                    target =
                                                  decide
                                                    (Graph.WindowCurvature.Safe
                                                      (toParameters.windowBarrier.table.counts.rightLength row)
                                                      (windowBarrierLabel source) (windowBarrierLabel target))) →
                                              (∀ (row : toParameters.windowBarrier.Index)
                                                  (source target : Fin toParameters.windowBarrier.size),
                                                  (toParameters.windowBarrier.profile.row
                                                          (toParameters.windowBarrier.table.counts.leftLength row +
                                                            toParameters.windowBarrier.table.counts.rightLength row)
                                                          source).getLsb
                                                      target =
                                                    decide
                                                      (Graph.WindowCurvature.Safe
                                                        (toParameters.windowBarrier.table.counts.leftLength row +
                                                          toParameters.windowBarrier.table.counts.rightLength row)
                                                        (windowBarrierLabel source) (windowBarrierLabel target))) →
                                                toParameters.windowRate = toParameters.windowBarrier.binaryRateFloor →
                                                  (∀ (size : ℕ), toParameters.separatedScaleCount size ≤ size.log2) →
                                                    (∀ (size : ℕ), toParameters.separatedScaleCount size = size.log2) →
                                                      Graph.FiniteObject.netCapWindowCost toParameters.threshold
                                                              toParameters.dischargeScale toParameters.windowOrder *
                                                            toParameters.threshold <
                                                          2 * toParameters.windowRate →
                                                        toParameters.curvatureCost =
                                                            Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
                                                              toParameters.windowBarrier.table
                                                              toParameters.curvatureBarrierRow →
                                                          0 < toParameters.entropyDenominator →
                                                            toParameters.threshold + 2 + toParameters.dischargeScale ≤
                                                                toParameters.bridgeMassFactor *
                                                                  toParameters.dischargeScale →
                                                              1 + toParameters.dischargeScale * toParameters.threshold +
                                                                    2 * toParameters.dischargeScale ≤
                                                                  toParameters.bridgeMassFactor *
                                                                    toParameters.dischargeScale →
                                                                Graph.Strategy.Spine.Data
```

#### `Hypostructure.Graph.Strategy.Spine.Data.netCapRateSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  Graph.FiniteObject.netCapWindowCost self.threshold self.dischargeScale self.windowOrder * self.threshold <
    2 * self.windowRate
```

#### `Hypostructure.Graph.Strategy.Spine.Data.quadraticSafetyScale_le_spineScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data), Graph.TokenLoad.quadraticSafetyScale ≤ data.spineScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.quadraticSafetyScale_le_twiceAdditive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data), Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * data.homogeneousCap)
```

#### `Hypostructure.Graph.Strategy.Spine.Data.quadrilateralAccepted`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.LengthOK 4
```

#### `Hypostructure.Graph.Strategy.Spine.Data.roleSafety`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  Graph.TokenLoad.quadraticSafetyScale ≤ 2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound)
```

#### `Hypostructure.Graph.Strategy.Spine.Data.routingLabelBound_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  self.routingLabelBound =
    Fintype.card
      (Graph.SameTokenRoutingGerms.RoutingLabel (Fin self.threshold → Fin self.threshold)
        (Graph.WindowCurvature.Label self.windowOrder))
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleCount_eq_log2`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (size : ℕ), self.separatedScaleCount size = size.log2
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleCount_le`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (size : ℕ), self.separatedScaleCount size ≤ size.log2
```

#### `Hypostructure.Graph.Strategy.Spine.Data.three_le_threshold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 3 ≤ self.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.Data.three_le_windowOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data), 3 ≤ data.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.threshold_eq_three`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.threshold = 3
```

#### `Hypostructure.Graph.Strategy.Spine.Data.toParameters`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.Strategy.Spine.Parameters
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrierLabel`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(self : Graph.Strategy.Spine.Data) → Fin self.windowBarrier.size → Graph.WindowCurvature.Label self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrierLabel_injective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), Function.Injective self.windowBarrierLabel
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrierLabel_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (index : Fin self.windowBarrier.size),
  self.windowBarrierLabel index ∈ Graph.WindowCurvature.Labels self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrierLabel_surjective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  ∀ label ∈ Graph.WindowCurvature.Labels self.windowOrder, ∃ index, self.windowBarrierLabel index = label
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrier_left_semantic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (row : self.windowBarrier.Index) (source target : Fin self.windowBarrier.size),
  (self.windowBarrier.profile.row (self.windowBarrier.table.counts.leftLength row) source).getLsb target =
    decide
      (Graph.WindowCurvature.Safe (self.windowBarrier.table.counts.leftLength row) (self.windowBarrierLabel source)
        (self.windowBarrierLabel target))
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrier_right_semantic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (row : self.windowBarrier.Index) (source target : Fin self.windowBarrier.size),
  (self.windowBarrier.profile.row (self.windowBarrier.table.counts.rightLength row) source).getLsb target =
    decide
      (Graph.WindowCurvature.Safe (self.windowBarrier.table.counts.rightLength row) (self.windowBarrierLabel source)
        (self.windowBarrierLabel target))
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrier_sum_semantic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (row : self.windowBarrier.Index) (source target : Fin self.windowBarrier.size),
  (self.windowBarrier.profile.row
          (self.windowBarrier.table.counts.leftLength row + self.windowBarrier.table.counts.rightLength row)
          source).getLsb
      target =
    decide
      (Graph.WindowCurvature.Safe
        (self.windowBarrier.table.counts.leftLength row + self.windowBarrier.table.counts.rightLength row)
        (self.windowBarrierLabel source) (self.windowBarrierLabel target))
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowRate_eq_barrier`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.windowRate = self.windowBarrier.binaryRateFloor
```

#### `Hypostructure.Graph.Strategy.Spine.Holds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    Presentation → Graph.Strategy.Spine.Data → Graph.Strategy.Spine.Key → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Input`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → Graph.Strategy.Spine.Data → Type (max (u + 1) v)
```

#### `Hypostructure.Graph.Strategy.Spine.K`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Graph.Strategy.Spine.Key →
          Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.K_eq_iff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data} (left right : Graph.Strategy.Spine.Key),
  Graph.Strategy.Spine.K left = Graph.Strategy.Spine.K right ↔ left = right
```

#### `Hypostructure.Graph.Strategy.Spine.K_ne_closed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data} (key : Graph.Strategy.Spine.Key),
  Graph.Strategy.Spine.K key ≠ Graph.Strategy.Spine.closed
```

#### `Hypostructure.Graph.Strategy.Spine.Key`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedConfigurationResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedF4Charge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedGermFanData`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedGermSplit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedHandoffCore`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedHandoffCoreAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.activeSurplusDemands`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.activeSurplusFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.admissibleQuotientsLabelInjective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.allColdEntropyResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.atomCompression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.barrierCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.barrierEnumeration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.barrierOverflow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.baselineSpineDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.bigHubBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.bigHubVShapes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedBarrierOverlap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedClassMember`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedCompressionBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedCompressionCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedFailingSetCarries`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedFailureSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedOverlapSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedOwnRecord`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairCodeUnrealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairCountFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairEntropySandwich`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairEntropySetup`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairNoExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPrefixCompression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedScaleAdditive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.bottleneckRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.boundaryDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.boundedDensityOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.boundedOrderLarge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.boundedOrderSmall`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.branchDependence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.bridgePieceMassDichotomy`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.bridgeless`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalBlockedFreePartition`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalBlockerRoute`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalCapacityExplicit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalCertificationCriterion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalFreeExcessOfCapped`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalOverloadOfFits`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalPieceDominance`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalTokenCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalTwoExitNewLength`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalTwoExitSizeMonotone`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.ceilSqrtAboveScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.closedClasses`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldAbsorbedNeutralConfiguration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldAmbientCubic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldAmbientCubicStubExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldBranchClosed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCanonicalNeutralConfiguration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCanonicalReplacementSwap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCanonicalReplacementTrivial`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCanonicalSwapSameSize`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCanonicalSwapSmaller`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCorridorState`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCutStatesDistinct`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldExchangeBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureCompression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureDefectRoute`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFamilyEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFamilyPositive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFirstFailureOccurrence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGenuineSecondStrand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermCandidates`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermDistinguished`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermFamilyPositive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermNoneDistinguishing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermNoneRealizing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermRouted`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermSilent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermSomeDistinguishing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermSomeRealizing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldHandoffTransfer`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldHeavyEntryTerminal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldHotEntropyCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldHotEntropyOverflow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermChordSpan`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermPairMersenne`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermPairSuppression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermStretchExcision`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermStretchIncidence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMarkedGermUncompressed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMass`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMassBounded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMassLinear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldNeutralEqualLengthTerminal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldNoPositiveGerm`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldPositiveGerm`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldRepeatedStateResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldReturnCorridors`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldRoute8AtOrAbove`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldRoute8Below`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldSameInterfaceTable`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldSelectedBranchExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldSelectedFamilyEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldStubExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldSymmetricPairExcluded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldTwoStrandSurvivor`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldWindowStubStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.compatiblePairFanClosure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.compatiblePairTypeBRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.contextDefect`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.contextUniversal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coverFlowValue`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coverPayment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.crossSwitchFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cubicBaseline`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cubicNeighbourSupply`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.curvatureFullRank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.curvatureRankDrop`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.curvatureTargetRank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cutVertexBlockPaths`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cycleDoubleCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cycleRankConstraint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.cyclesThroughVertex`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.degreeProfileFibres`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.delocalizedSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.denseColdCorridorsTerminal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.denseDeficiencyAtOrAbove`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.denseDeficiencyBelow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.densityCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.densityExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.dependentPairFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.dominantRootedType`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.dominantRootedTypeWedgeFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.dominantRootedWedgeType`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.edgeSurplusIdentity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyCapActive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyCapBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyJointRealization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyPackageDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.everyWitnessSpectrumSplit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.exactCollisionFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.exactCubicBaselineBudget`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.exactResponseProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.extFreeEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.extLoadSum`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.extOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.extOverloadedToken`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fanCertificateCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fanCertificateMarked`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fanCertificateResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fanCertificateResidualMass`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fanClosedPortTypeBRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.fibrePressure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.forcedCurvatureCost`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freePairCodeUnrealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freePairCountFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freePairEntropySandwich`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freeSideCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freeSideHubs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.freeSideStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.globalBarrier`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.globalDelocalization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.groupedAbsorbedCoreSubset`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.groupedCentresHigh`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.handoffDegreeClauseEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highCentreNormalForm`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highCentreSplitForced`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highDegreeCountBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highDegreePairSum`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highDegreePositive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highDegreeSurplusCapacity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highEndpointSwitch`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highSurplusBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highSurplusConfiguration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.highSurplusOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.homogeneousBottleneck`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.homogeneousBottleneckPattern`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.homogeneousCapsFail`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.homogeneousCapsHold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hotColdPartition`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hssTargetCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubClassCounts`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubCountBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubLengthThreePairs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubLinkStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubTwoHopLinks`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.hubWindowBudget`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.incrementalSkeletonRoom`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.independentObstructionTranslates`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.independentPairFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.inducedPathAttachment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.largeBudgetResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.loadFailureSaturated`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.loadFlowValue`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.localAlgebra`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.localTypeCoordinateNonrepetitive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.localTypeCoordinateRepetitive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.lowEdgeParity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.maximalPacking`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.meetingCycleConstraint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.mersenneReturn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.minDegreeBaseline`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.mixedSparseSpineDependence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.negativeSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.neighbourhoodPairCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeLocalization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeNegative`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeNonNegative`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netDeficiencyCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.newLoadBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.noProperBaseline`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.noSuppressionChordViolation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.ofNat`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
ℕ → Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.ofNat_ctorIdx`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (x : Graph.Strategy.Spine.Key), Graph.Strategy.Spine.Key.ofNat x.ctorIdx = x
```

#### `Hypostructure.Graph.Strategy.Spine.Key.openPortSuppression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.openPortSuppressionSafe`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.orderAboveScaleSquare`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.packingOrderBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairArmAPattern`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairArmARoleAlphabet`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairArmB`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairCodeConfiguration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairConditionalFactorization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairConditionalFactorizationResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairCorrelation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairCountDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairCoverage`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairDegreeProfileFibres`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairDemandReturns`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairFactorizationFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairFailureOverlap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairFullModulus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffBoundaryType`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffCharge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffCriticalCoordinate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffDemandEnds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffFibreAtG`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffHubBalance`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffHubCharge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffHubForces`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffNetCharge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairHandoffSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairIncrementCovered`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairIncrementEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairIncrementFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairIncrementNoEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairNoProfileObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairNoResponseObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairObstructionDescent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairOverlapFirstFailure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairOverlapSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairPowerOfTwoCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairProfileObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairRealizabilityFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairResponseObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSerialArithmetic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSerialDemandSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSystemEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSystemNoEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSystemRealizability`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pairUncrossing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.paperBudgetBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.paperBudgetCertifies`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pieceDominanceIrreducible`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pieceRoutingTotal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.pieceSizeProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.portEndDegree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.primitiveCarrierCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.primitiveClassOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.properDelocalization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.realizedDensityOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.realizedOrderLarge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.realizedOrderSmall`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.receiverPortsAreWindowStubs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderClassAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderClassOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderCycleSpectrum`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderDeficiencyBelowCut`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderEntropyHigh`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderEntropyLow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderNormalized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderPathBounds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.repairIdentity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.replacementExclusion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.responseObstructionTargetDefect`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.returnAvoidance`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.roleFibrePartition`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8AchievableLengths`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ArmClosure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ArmClosureResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ArmExchange`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8BasinBurden`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CarrierCore`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CarrierCutParity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CarrierDeletionWitnesses`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CarrierInjection`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Census`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CleanLandingCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CleanLandingRules`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CoreEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8DeficitVsStubs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8DemandAbsorption`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8DemandUnitCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8EntryLowerBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ExtractedEntryCensus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8FoldPeels`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8FullArmLandingCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8HubFreeDensity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8HubFreePi`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8HubPieceExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8HubPieceMass`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8HubStubs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8JointBalance`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8LargeBudgetDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NetCapExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NetCapLarge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NetCapSmall`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NoSmallCoreEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NoTwoCarrierEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8OpenBoundarySaturated`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PackingExchange`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PeelingDescent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PieceBoundary`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PieceChainCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PieceWindowAttachment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PiecesClassified`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PiecewiseRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PrivateCarrierBudget`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8QuotientEntriesAtG`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8QuotientFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8QuotientResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Rate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateExactSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFailsCrossBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFailsFlow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFailsJoin`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFailsPiece`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ResidualProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8SmallCoreCollapse`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8SmallCoreEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8StageRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8StageRateFailed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8StrongRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8StubDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ThinIsolation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ThinSmall`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TrueResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TrueTwoCarrierEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TwoCarrierEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TwoCarrierExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedEntryCensus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedNegative`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedTrueTwoCarrierEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedTwoCarrierExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedVisibleOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnifiedVisibleResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnpaidExitFourResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnpaidTwoCarrier`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8UnpaidWitnessFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8WindowBlockers`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8WindowPieceRank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8WindowRPathGap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8WindowSelfRPathGap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8WindowStub`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8X15LongLandings`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameCenterOpenPortCompatibility`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenCrossingCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenHubCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenLadderCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenPairPartition`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenPathInteractions`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenPatternSupports`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenPatternSwap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenPatternUnresolved`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenReadingsExact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenReadingsNotReplacement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenSeedCover`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenSeparatorExcluded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenSwap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenSwapExact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenTransplantDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenTransplantSize`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenTriArmEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenU2FreeWhole`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenUnresolvedDecided`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenW0Escape`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenWalkAttachment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenWalkExchange`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameTokenWalkWindows`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sameVertexSwitchForcedPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.saturatedReceiverBasin`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.scalePressure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.selection`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.separatedPairs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.singleBoundaryShape`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.singleOpenPortSuppressionWitness`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sixVertexExtremalEnvelope`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.skeletonDominates`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.slackIndependent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.slotLinear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.slotRelation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparsePairExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparsePortActivation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparsePressureNearCubic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparsePressureOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseSlackSurplus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseSurplusSurvivor`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseTargetDefectEmpty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseTargetDefectResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseUpperEnvelope`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.specWitnessStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.spineSurplusEstimate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.starCycleConstraint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.stubDeficitIdentity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.stubSupply`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.suppressedFamilyCriticalCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.surplusAbove`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.surplusAtOrBelow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.surplusDartIdentity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.targetCompleteContextUniversality`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.targetRankCircuit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.threeRouteChain`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.threeRouteFan`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.tightEndpoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.toCtorIdx`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Key.traceIntoAbsorbedStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.traceIntoCentreStructure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularCrossShoulder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularFanCore`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularFirstLanding`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularPortReturn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularPortTypeBRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularShoulderCompletion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.twoExitNewLength`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.twoExitSizeMonotone`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.twoSwitchForcedPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeABoundedSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExclusion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFive`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFiveFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourFiniteDescent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourPeeled`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourReceiverDischarged`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourSwitchCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitOneFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitOneReturn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSevenEnvelope`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSevenFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSevenHandoff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSevenSwitch`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSix`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixGlobal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixGlobalScope`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixProper`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixProperScope`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitThreeCollision`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitThreeCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitThreeFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitTwoFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitTwoTheta`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeALowSurplus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeANoVisibleEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitOneFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitOneReturn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitThreeCollision`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitThreeFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitTwoFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledExitTwoTheta`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledNoVisibleEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledSaturatedReceiver`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledSilentExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledUnsaturatedDischarge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledVisibleEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPortReturn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAReceiverRouting`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedExitEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFour`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedReceiver`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAUnsaturatedDischarge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAUnsaturatedReceivers`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAVisibleEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAVisibleFirstExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBAbsorbedCharge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBAbsorbedHalfEdge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBAbsorbedHalfEdgeAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBAssignedSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBB2Choice`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBBridgeMass`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBBridgeReduction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBBridgeSublinear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDecoratedAssignedSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDegreeFourClosed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDegreeFourOverlap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDirectCycleFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBExcluded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBExclusionResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBFanDegreeFourCentres`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBFanDegreeFourProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBFanEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBFanHeavyCentre`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBFanLocalDichotomy`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBGlobalLocalBridge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHandoff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHandoffFails`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHighSurplus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHybridEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBOverlapObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBOverlapObstructionMass`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBRoute8Entry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBSublinearCanonicalForm`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBSublinearFailureArms`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBSublinearResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.uncompressible`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.unpaidAbsorbedWindowPort`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.vertexDeletionComponents`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.wedgeSupply`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowAttachmentGap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowChargeKinds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowClassAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowClassOverload`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowCutCapacity`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowFreeGeometry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowHubBounds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPackageRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPackageSeparated`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPackageUnrealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPositionStubs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPresent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowShadowHitCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowShadowHitExcluded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.contains`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.decEq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.level`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Level
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.list`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.membership`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → Level → Expr → Expr → Graph.Strategy.Spine.KeyFresh.Keys
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.ne`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.notMem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.ofType`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → MetaM Graph.Strategy.Spine.KeyFresh.Keys
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.Keys.type`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.bool`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Bool → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.boolRefl`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Bool → Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.closeByKernel`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
MVarId → Expr → Expr → Bool → (Expr → Expr) → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → MVarId → Expr → Expr → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.distinct`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → MVarId → Expr → Expr → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.elementsOf`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → optParam (Array Expr) #[] → MetaM (Array Expr)
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.findHypothesis`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → MetaM (Option Expr)
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.fresh`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
MVarId → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.isListSpine`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → Bool
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.listCell`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → MetaM Expr
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.mentionsListFVar`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → MetaM Bool
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.notMem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → MVarId → Expr → Expr → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.refuteVisible`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → Expr → Expr → MetaM Unit
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.restrictFresh`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.KeyFresh.Keys → Expr → Expr → Expr → Expr → MetaM (Option Expr)
```

#### `Hypostructure.Graph.Strategy.Spine.KeyFresh.visibleElements`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `opaque`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Expr → optParam (Array Expr) #[] → MetaM (Array Expr)
```

#### `Hypostructure.Graph.Strategy.Spine.PresentationLawsStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Parameters) →
  (Fin data.windowBarrier.size → Graph.WindowCurvature.Label data.windowOrder) → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Value`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        Graph.Strategy.Spine.Key →
          Core.Strategy.ProblemInput
              (Graph.Strategy.Spine.problem BranchState Presentation presentation data.toParameters) →
            Type
```

### `Hypostructure.Graph.Strategy.SpineRows.AbsorbedConfigurationResidual`

#### `Hypostructure.Graph.Strategy.Spine.absorbedConfigurationResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/AbsorbedConfigurationResidual.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.AtomCompressionDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.atomCompressionDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/AtomCompressionDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.maximalPacking) known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.atomCompression ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.atomCompression)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.B2AssignmentDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/B2AssignmentDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBHybridEntry) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateMarked)
                      known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBB2Choice ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBOverlapObstruction ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBB2Choice)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBOverlapObstruction) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.BarrierEnumeration`

#### `Hypostructure.Graph.Strategy.Spine.barrierEnumerationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/BarrierEnumeration.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.BoundaryDemand`

#### `Hypostructure.Graph.Strategy.Spine.boundaryDemandRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/BoundaryDemand.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.BranchDependence`

#### `Hypostructure.Graph.Strategy.Spine.branchDependenceRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/BranchDependence.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.BridgeFanMass`

#### `Hypostructure.Graph.Strategy.Spine.bridgeFanMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/BridgeFanMass.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Bridgeless`

#### `Hypostructure.Graph.Strategy.Spine.bridgelessRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Bridgeless.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.closed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.closureKey_eq_closed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data}, Core.Residual.FactSystem.closureKey = Graph.Strategy.Spine.closed
```

### `Hypostructure.Graph.Strategy.SpineRows.CompatiblePairFanClosure`

#### `Hypostructure.Graph.Strategy.Spine.compatiblePairFanClosureRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CompatiblePairFanClosure.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.CompatiblePairTypeBRouting`

#### `Hypostructure.Graph.Strategy.Spine.compatiblePairTypeBRoutingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CompatiblePairTypeBRouting.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Basic`

#### `Hypostructure.Graph.Strategy.Spine.contextOfSelection`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Basic.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
          ¬Graph.HasCycleWithLength data.LengthOK input.object →
            (∀ (smaller : Graph.FiniteObject),
                (Graph.Strategy.Spine.progress BranchState Presentation presentation data.toParameters).Smaller smaller
                    input.object →
                  Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
              Core.MinimalCounterexampleContext
                (Graph.Strategy.Spine.problem BranchState Presentation presentation data.toParameters)
                (Graph.HasCycleWithLength data.LengthOK)
                (Graph.Strategy.Spine.progress BranchState Presentation presentation data.toParameters)
```

### `Hypostructure.Graph.Strategy.SpineRows.ContextValidityDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ContextValidityDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.branchDependence) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.CubicBaseline`

#### `Hypostructure.Graph.Strategy.Spine.cubicBaselineRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CubicBaseline.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.CurvatureRankDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CurvatureRankDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureTargetRank) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.targetRankCircuit) known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureRankDrop ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureRankDrop)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.CurvatureTargetRank`

#### `Hypostructure.Graph.Strategy.Spine.curvatureTargetRankRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CurvatureTargetRank.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.CycleRankConstraint`

#### `Hypostructure.Graph.Strategy.Spine.cycleRankConstraintRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CycleRankConstraint.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap`

#### `Hypostructure.Graph.Strategy.Spine.degreeFourFanCertificateCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/FanCertificateCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DegreeProfileFibres`

#### `Hypostructure.Graph.Strategy.Spine.degreeProfileFibresRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DegreeProfileFibres.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DeletionCriticality`

#### `Hypostructure.Graph.Strategy.Spine.deletionCriticalityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DeletionCriticality.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DelocalizationScopeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.delocalizationScopeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DelocalizationScopeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.properDelocalization ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.globalDelocalization ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.properDelocalization)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.globalDelocalization) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.DenseNetDeficiencyCap`

#### `Hypostructure.Graph.Strategy.Spine.denseDeficiencyDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DenseNetDeficiencyCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPackageUnrealized)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.denseDeficiencyBelow ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.denseDeficiencyAtOrAbove ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.denseDeficiencyBelow)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.denseDeficiencyAtOrAbove) previous
```

#### `Hypostructure.Graph.Strategy.Spine.denseNetDeficiencyCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DenseNetDeficiencyCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DominantRootedType`

#### `Hypostructure.Graph.Strategy.Spine.dominantRootedTypeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DominantRootedType.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DominantRootedTypeWedgeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.dominantRootedTypeWedgeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DominantRootedTypeWedgeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.dominantRootedType) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.dominantRootedWedgeType ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.dominantRootedTypeWedgeFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.dominantRootedWedgeType)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.dominantRootedTypeWedgeFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.EntropyCapDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.entropyCapDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/EntropyCapDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.forcedCurvatureCost) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyPackageDemand)
                      known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapActive ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapBound ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapActive)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapBound) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.EntropyPackage`

#### `Hypostructure.Graph.Strategy.Spine.entropyPackageRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/EntropyPackage.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ExactCollisionDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.exactCollisionDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ExactCollisionDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netDeficiencyCap) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeCap ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.exactCollisionFails ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeCap)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.exactCollisionFails) previous
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.factSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        Core.Residual.FactSystem
          (Core.Strategy.ProblemInput
            (Graph.Strategy.Spine.problem BranchState Presentation presentation data.toParameters))
```

### `Hypostructure.Graph.Strategy.SpineRows.FanCertificateCap`

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/FanCertificateCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.FanCertificateDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/FanCertificateDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateCap) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateMarked ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateResidual ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateMarked)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateResidual) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.FanCertificateResidualMass`

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateResidualMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/FanCertificateResidualMass.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.FanClosedPortTypeBRouting`

#### `Hypostructure.Graph.Strategy.Spine.fanClosedPortTypeBRoutingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/FanClosedPortTypeBRouting.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ForcedCurvatureCost`

#### `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCostRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ForcedCurvatureCost.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.GlobalBarrier`

#### `Hypostructure.Graph.Strategy.Spine.globalBarrierRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/GlobalBarrier.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.HighCentreNormalForm`

#### `Hypostructure.Graph.Strategy.Spine.highCentreNormalFormRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/HighCentreNormalForm.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.LowEntropyLargeBudget`

#### `Hypostructure.Graph.Strategy.Spine.highEntropyLargeBudgetRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/LowEntropyLargeBudget.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.HotColdPartition`

#### `Hypostructure.Graph.Strategy.Spine.hotColdPartitionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/HotColdPartition.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ObstructionPacking`

#### `Hypostructure.Graph.Strategy.Spine.hssTargetCycleRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ObstructionPacking.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.HybridEntry`

#### `Hypostructure.Graph.Strategy.Spine.hybridEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/HybridEntry.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.idx`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.idx_injective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Function.Injective Graph.Strategy.Spine.idx
```

### `Hypostructure.Graph.Strategy.SpineRows.IndependentObstructionTranslates`

#### `Hypostructure.Graph.Strategy.Spine.independentObstructionTranslatesRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/IndependentObstructionTranslates.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.instDecidableEqKey`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
DecidableEq Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.instFactSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DenseNetDeficiencyCap`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleDenseDeficiencyAtOrAboveColdRoute8Below`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DenseNetDeficiencyCap.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.denseDeficiencyAtOrAbove)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.coldRoute8Below)
```

### `Hypostructure.Graph.Strategy.SpineRows.ExactCollisionDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleExactCollisionFailsRoute8Rate`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ExactCollisionDichotomy.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.exactCollisionFails)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Rate)
```

### `Hypostructure.Graph.Strategy.SpineRows.NetChargeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleNetChargeNonNegativeCap`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NetChargeDichotomy.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNonNegative)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeCap)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8PrivateCarrierBudget`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleRoute8CensusPrivateCarrierBudget`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8PrivateCarrierBudget.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Census)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8PrivateCarrierBudget)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreExit`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleRoute8TrueResidualSmallCoreCollapse`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8SmallCoreExit.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TrueResidual)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8SmallCoreCollapse)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleRoute8TrueTwoCarrierEntryTwoCarrierExit`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TwoCarrierExit.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TrueTwoCarrierEntry)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TwoCarrierExit)
```

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleRoute8UnifiedTrueTwoCarrierEntryUnifiedTwoCarrierExit`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TwoCarrierExit.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedTrueTwoCarrierEntry)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedTwoCarrierExit)
```

### `Hypostructure.Graph.Strategy.SpineRows.ObstructionPacking`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleSelectionHssTargetCycle`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ObstructionPacking.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.selection)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.hssTargetCycle)
```

### `Hypostructure.Graph.Strategy.SpineRows.ReturnAvoidance`

#### `Hypostructure.Graph.Strategy.Spine.instIncompatibleSelectionMersenneReturn`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ReturnAvoidance.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.selection)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.mersenneReturn)
```

### `Hypostructure.Graph.Strategy.SpineRows.InterfaceReplacement`

#### `Hypostructure.Graph.Strategy.Spine.interfaceReplacementRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/InterfaceReplacement.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.key`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        Graph.Strategy.Spine.Key →
          Core.Residual.FactKey
            (Core.Strategy.ProblemInput
              (Graph.Strategy.Spine.problem BranchState Presentation presentation data.toParameters))
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_append_left`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {first second right : List α},
  first.Disjoint right → second.Disjoint right → (first ++ second).Disjoint right
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_append_right`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {left first second : List α},
  left.Disjoint first → left.Disjoint second → left.Disjoint (first ++ second)
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_cons_left`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {head : α} {tail right : List α}, head ∉ right → tail.Disjoint right → (head :: tail).Disjoint right
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_cons_right`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {left tail : List α} {head : α}, head ∉ left → left.Disjoint tail → left.Disjoint (head :: tail)
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_nil_left`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {right : List α}, [].Disjoint right
```

#### `Hypostructure.Graph.Strategy.Spine.keyDisjoint_of_all`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} [inst : DecidableEq α] {left right : List α},
  (left.all fun key => !right.contains key) = true → left.Disjoint right
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_append`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {key : α} {left right : List α}, key ∉ left → key ∉ right → key ∉ left ++ right
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_cons`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {key head : α} {tail : List α}, key ≠ head → key ∉ tail → key ∉ head :: tail
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_of_append_left`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {key : α} {left right : List α}, key ∉ left ++ right → key ∉ left
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_of_append_right`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {key : α} {left right : List α}, key ∉ left ++ right → key ∉ right
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_of_cons_tail`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} {key head : α} {tail : List α}, key ∉ head :: tail → key ∉ tail
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_of_contains`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} [inst : DecidableEq α] {key : α} {keys : List α}, keys.contains key = false → key ∉ keys
```

#### `Hypostructure.Graph.Strategy.Spine.keyFresh_of_disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} [inst : DecidableEq α] {key : α} {covering keys : List α},
  covering.Disjoint keys → covering.contains key = true → key ∉ keys
```

#### `Hypostructure.Graph.Strategy.Spine.keyNe_of_decide`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {α : Type u_1} [inst : DecidableEq α] {left right : α}, decide (left = right) = false → left ≠ right
```

#### `Hypostructure.Graph.Strategy.Spine.label`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → String
```

### `Hypostructure.Graph.Strategy.SpineRows.LiveHotBarrierCap`

#### `Hypostructure.Graph.Strategy.Spine.liveHotBarrierCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/LiveHotBarrierCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.LocalAlgebra`

#### `Hypostructure.Graph.Strategy.Spine.localAlgebraRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/LocalAlgebra.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.LocalTypeCoordinateDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.localTypeCoordinateDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/LocalTypeCoordinateDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.localTypeCoordinateRepetitive ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.localTypeCoordinateNonrepetitive ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.localTypeCoordinateRepetitive)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.localTypeCoordinateNonrepetitive) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.LowEntropyLargeBudget`

#### `Hypostructure.Graph.Strategy.Spine.lowEntropyLargeBudgetRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/LowEntropyLargeBudget.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.CubicBaseline`

#### `Hypostructure.Graph.Strategy.Spine.minDegreeBaselineRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/CubicBaseline.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.name`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → Name
```

#### `Hypostructure.Graph.Strategy.Spine.name_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (k : Graph.Strategy.Spine.Key),
  Graph.Strategy.Spine.name k =
    (`Hypostructure.Graph.Strategy.Spine.str (Graph.Strategy.Spine.label k)).num (Graph.Strategy.Spine.idx k)
```

#### `Hypostructure.Graph.Strategy.Spine.name_injective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Function.Injective Graph.Strategy.Spine.name
```

### `Hypostructure.Graph.Strategy.SpineRows.NegativeSupport`

#### `Hypostructure.Graph.Strategy.Spine.negativeSupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NegativeSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.NetChargeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NetChargeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNonNegative ∉ known →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNegative ∉ known →
                  Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNonNegative)
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNegative) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.NetChargeLocalization`

#### `Hypostructure.Graph.Strategy.Spine.netChargeLocalizationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NetChargeLocalization.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.NetDeficiencyCap`

#### `Hypostructure.Graph.Strategy.Spine.netDeficiencyCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NetDeficiencyCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.NoProperBaseline`

#### `Hypostructure.Graph.Strategy.Spine.noProperBaselineRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/NoProperBaseline.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ObstructionPacking`

#### `Hypostructure.Graph.Strategy.Spine.obstructionPackingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ObstructionPacking.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.ofIdx`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
ℕ → Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.ofIdx_idx`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (k : Graph.Strategy.Spine.Key), Graph.Strategy.Spine.ofIdx (Graph.Strategy.Spine.idx k) = k
```

### `Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppression`

#### `Hypostructure.Graph.Strategy.Spine.openPortSuppressionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/OpenPortSuppression.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.OpenPortSuppressionSafe`

#### `Hypostructure.Graph.Strategy.Spine.openPortSuppressionSafeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/OpenPortSuppressionSafe.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Basic`

#### `Hypostructure.Graph.Strategy.Spine.pairManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Basic.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (required first second :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            first ≠ required →
              second ≠ required →
                first ≠ second →
                  Core.Strategy.FactManifest (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.RemainderEntropyDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.remainderEntropyDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/RemainderEntropyDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.forcedCurvatureCost) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.remainderEntropyHigh ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.remainderEntropyLow ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.remainderEntropyHigh)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.remainderEntropyLow) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.RemainderNormalization`

#### `Hypostructure.Graph.Strategy.Spine.remainderNormalizationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/RemainderNormalization.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.RepairIdentity`

#### `Hypostructure.Graph.Strategy.Spine.repairIdentityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/RepairIdentity.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ReplacementExclusion`

#### `Hypostructure.Graph.Strategy.Spine.replacementExclusionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ReplacementExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ReturnAvoidance`

#### `Hypostructure.Graph.Strategy.Spine.returnAvoidanceDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ReturnAvoidance.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.cubicBaseline) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.mersenneReturn ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.returnAvoidance ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.mersenneReturn)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.returnAvoidance) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8BasinBurden`

#### `Hypostructure.Graph.Strategy.Spine.route8BasinBurdenRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8BasinBurden.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCore`

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierCoreRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8CarrierCore.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8CarrierCutParity`

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierCutParityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8CarrierCutParity.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDeletionWitnesses`

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierDeletionWitnessesRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8CarrierDeletionWitnesses.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8CarrierDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8CarrierDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoSmallCoreEntry)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TwoCarrierEntry ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoTwoCarrierEntry ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TwoCarrierEntry)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoTwoCarrierEntry) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8Census`

#### `Hypostructure.Graph.Strategy.Spine.route8CensusRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8Census.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8DemandAbsorption`

#### `Hypostructure.Graph.Strategy.Spine.route8DemandAbsorptionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8DemandAbsorption.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8ExtractedEntryCensus`

#### `Hypostructure.Graph.Strategy.Spine.route8ExtractedEntryCensusRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8ExtractedEntryCensus.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8FoldPeels`

#### `Hypostructure.Graph.Strategy.Spine.route8FoldPeelsRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8FoldPeels.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8JointBalance`

#### `Hypostructure.Graph.Strategy.Spine.route8JointBalanceRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8JointBalance.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8LargeBudgetDeficit`

#### `Hypostructure.Graph.Strategy.Spine.route8LargeBudgetDeficitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8LargeBudgetDeficit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8BasinBurden) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficit ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficit)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8OpenBoundarySaturated`

#### `Hypostructure.Graph.Strategy.Spine.route8OpenBoundarySaturatedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8OpenBoundarySaturated.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8PeelingDescent`

#### `Hypostructure.Graph.Strategy.Spine.route8PeelingDescentRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8PeelingDescent.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8PiecesClassified`

#### `Hypostructure.Graph.Strategy.Spine.route8PiecesClassifiedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8PiecesClassified.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8PrivateCarrierBudget`

#### `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierBudgetRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8PrivateCarrierBudget.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8QuotientDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.route8QuotientDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8QuotientDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedDeficit)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientFree ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientResidual ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientFree)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientResidual) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8RateDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.route8RateDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8RateDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              (density : Graph.Strategy.Spine.Key) →
                density = Graph.Strategy.Spine.Key.netDeficiencyCap ∨
                    density = Graph.Strategy.Spine.Key.denseDeficiencyBelow →
                  [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K density) known] →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Rate ∉ known →
                      Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8RateFails ∉ known →
                        Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Rate)
                          (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8RateFails) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8RateFromColdBelow`

#### `Hypostructure.Graph.Strategy.Spine.route8RateFromColdBelowRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8RateFromColdBelow.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8ResidualProfile`

#### `Hypostructure.Graph.Strategy.Spine.route8ResidualProfileRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8ResidualProfile.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreCollapse`

#### `Hypostructure.Graph.Strategy.Spine.route8SmallCoreCollapseRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8SmallCoreCollapse.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8CarrierCutParity)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8SmallCoreEntry ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoSmallCoreEntry ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8SmallCoreEntry)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoSmallCoreEntry) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8SmallCoreExit`

#### `Hypostructure.Graph.Strategy.Spine.route8SmallCoreExitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8SmallCoreExit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8StageOutcomeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.route8StageOutcomeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8StageOutcomeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8PeelingDescent)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRate ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRateFailed ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRate)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRateFailed) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8StageTrueEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8StageOutcomeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8TrueResidual`

#### `Hypostructure.Graph.Strategy.Spine.route8TrueResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TrueResidual.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8TrueTwoCarrierEntry`

#### `Hypostructure.Graph.Strategy.Spine.route8TrueTwoCarrierEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TrueTwoCarrierEntry.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit`

#### `Hypostructure.Graph.Strategy.Spine.route8TwoCarrierExitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TwoCarrierExit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedDeficit`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedDeficitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedDeficit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedEntryCensus`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedEntryCensusRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedEntryCensus.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedNegative`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedNegativeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedNegative.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8TwoCarrierExit`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedTwoCarrierExitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8TwoCarrierExit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleOverload`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleOverloadRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedVisibleOverload.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnifiedVisibleResidual`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedVisibleResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnifiedVisibleResidual.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8UnpaidExitFourDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.route8UnpaidTrueEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnpaidExitFourDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8UnpaidTwoCarrierRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8UnpaidExitFourDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Route8WindowBlockers`

#### `Hypostructure.Graph.Strategy.Spine.route8WindowBlockersRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Route8WindowBlockers.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.RouteEightNetDeficiencyCap`

#### `Hypostructure.Graph.Strategy.Spine.routeEightNetDeficiencyCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/RouteEightNetDeficiencyCap.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Basic`

#### `Hypostructure.Graph.Strategy.Spine.rowManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Basic.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (required produced :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            required ≠ produced →
              Core.Strategy.FactManifest (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.SameCenterOpenPortCompatibility`

#### `Hypostructure.Graph.Strategy.Spine.sameCenterOpenPortCompatibilityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/SameCenterOpenPortCompatibility.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.SingleOpenPortSuppressionWitness`

#### `Hypostructure.Graph.Strategy.Spine.singleOpenPortSuppressionWitnessRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/SingleOpenPortSuppressionWitness.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.Basic`

#### `Hypostructure.Graph.Strategy.Spine.sourceFreeManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/Basic.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
            Core.Strategy.FactManifest (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.StubSupply`

#### `Hypostructure.Graph.Strategy.Spine.stubSupplyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/StubSupply.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.SuppressedFamilyCriticalCycle`

#### `Hypostructure.Graph.Strategy.Spine.suppressedFamilyCriticalCycleRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/SuppressedFamilyCriticalCycle.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.tacticKey_fresh`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
ParserDescr
```

### `Hypostructure.Graph.Strategy.SpineRows.TargetCompleteContextUniversality`

#### `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversalityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TargetCompleteContextUniversality.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TargetRankCircuit`

#### `Hypostructure.Graph.Strategy.Spine.targetRankCircuitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TargetRankCircuit.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularCrossShoulder`

#### `Hypostructure.Graph.Strategy.Spine.triangularCrossShoulderRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularCrossShoulder.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularFanCore`

#### `Hypostructure.Graph.Strategy.Spine.triangularFanCoreRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularFanCore.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularFirstLanding`

#### `Hypostructure.Graph.Strategy.Spine.triangularFirstLandingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularFirstLanding.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularPortReturn`

#### `Hypostructure.Graph.Strategy.Spine.triangularPortReturnRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularPortReturn.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularPortTypeBRouting`

#### `Hypostructure.Graph.Strategy.Spine.triangularPortTypeBRoutingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularPortTypeBRouting.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TriangularShoulderCompletion`

#### `Hypostructure.Graph.Strategy.Spine.triangularShoulderCompletionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TriangularShoulderCompletion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeABoundedSupport`

#### `Hypostructure.Graph.Strategy.Spine.typeABoundedSupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeABoundedSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeAExclusionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFiveDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFiveDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFive ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFiveFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFive)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFiveFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedExitEntry)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFour ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourAbsent ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFour)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourAbsent) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourFiniteDescent`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescentRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourFiniteDescent.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourFreeEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourPeelingStep`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStepRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourPeelingStep.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourRetestDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourRetestDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourPeeled) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledSaturatedReceiver ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourReceiverDischarged ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledSaturatedReceiver)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourReceiverDischarged) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitOneDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitOneDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitOneReturn ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitOneFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitOneReturn)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitOneFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitSevenDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSevenDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeALowSurplus) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixFree) known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenHandoff ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenFree ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenHandoff)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenFree) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSevenEnvelopeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSevenDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFiveFree) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSix ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSix)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitSixScopeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixGlobalRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixScopeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixProperRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixScopeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitSixScopeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSix) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixProperScope ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixGlobalScope ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixProperScope)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixGlobalScope) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitThreeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitThreeCycleRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitThreeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitThreeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoFree) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeCollision ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeCollision)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitTwoDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitTwoDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitOneFree) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoTheta ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoTheta)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoFree) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAPeeledExits`

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitOneDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledVisibleEntry)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitOneReturn ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitOneFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitOneReturn)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitOneFree) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitThreeCycleRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitThreeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitTwoFree)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitThreeCollision ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitThreeFree ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitThreeCollision)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitThreeFree) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledExitTwoDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitOneFree)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitTwoTheta ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitTwoFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitTwoTheta)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledExitTwoFree) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledSilentExcessRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledSilentExitFourFreeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAExitFourRetestDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledUnsaturatedDischargeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAExitFourRetestDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAPeeledExits`

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledVisibleEntryDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledSaturatedReceiver)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledVisibleEntry ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledNoVisibleEntry ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledVisibleEntry)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAPeeledNoVisibleEntry) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPeeledVisibleExitFourFreeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPeeledExits.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAPortReturn`

#### `Hypostructure.Graph.Strategy.Spine.typeAPortReturnRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAPortReturn.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAReceiverRouting`

#### `Hypostructure.Graph.Strategy.Spine.typeAReceiverRoutingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAReceiverRouting.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeASaturationDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeASaturationDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAReceiverRouting)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAUnsaturatedReceivers ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAUnsaturatedReceivers) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeASilentExitEntry`

#### `Hypostructure.Graph.Strategy.Spine.typeASilentExitEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeASilentExitEntry.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeASupport`

#### `Hypostructure.Graph.Strategy.Spine.typeASupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeASupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAUnsaturatedDischarge`

#### `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischargeClosed`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAUnsaturatedDischarge.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data},
  Core.Strategy.Incompatible (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASupport)
    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAUnsaturatedDischarge)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischargeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAUnsaturatedDischarge.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleEntryDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAVisibleEntryDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeANoVisibleEntry ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeANoVisibleEntry) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleExitEntry`

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleExitEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAVisibleExitEntry.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeAVisibleFirstExcess`

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleFirstExcessRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeAVisibleFirstExcess.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBAssignedSupport`

#### `Hypostructure.Graph.Strategy.Spine.typeBAssignedEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBAssignedSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeBAssignedSupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBAssignedSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeReduction`

#### `Hypostructure.Graph.Strategy.Spine.typeBBridgeReductionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBBridgeReduction.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBBridgeSublinear`

#### `Hypostructure.Graph.Strategy.Spine.typeBBridgeSublinearRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBBridgeSublinear.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeBCertificateMassExclusionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBDecoratedAssignedSupport`

#### `Hypostructure.Graph.Strategy.Spine.typeBDecoratedAssignedSupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBDecoratedAssignedSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeBDecoratedEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBDecoratedAssignedSupport.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.DisjointPostLedgerComponents`

#### `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourClosedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/DisjointPostLedgerComponents.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourExclusionResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBGlobalLocalBridge`

#### `Hypostructure.Graph.Strategy.Spine.typeBDegreeFourGlobalLocalBridgeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBGlobalLocalBridge.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBDirectCycleFree`

#### `Hypostructure.Graph.Strategy.Spine.typeBDirectCycleFreeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBDirectCycleFree.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeBExcludedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBFanDegreeDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanEntry) known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.surplusAtOrBelow) known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanHeavyCentre ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanDegreeFourCentres ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanHeavyCentre)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanDegreeFourCentres) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBFanDegreeFourProfile`

#### `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeFourProfileRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBFanDegreeFourProfile.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBFanLocalDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeBFanLocalDichotomyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBFanLocalDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBGlobalLocalBridge`

#### `Hypostructure.Graph.Strategy.Spine.typeBGlobalLocalBridgeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBGlobalLocalBridge.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeBObstructionMassExclusionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBOverlapObstructionMass`

#### `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstructionMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBOverlapObstructionMass.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeBExclusion`

#### `Hypostructure.Graph.Strategy.Spine.typeBRoute8EntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeBExclusion.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.TypeSplitDichotomy`

#### `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/TypeSplitDichotomy.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.negativeSupport) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeALowSurplus ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBHighSurplus ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeALowSurplus)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBHighSurplus) previous
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.vocabulary`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.FactVocabulary
          (Graph.Strategy.Spine.problem BranchState Presentation presentation data.toParameters)
```

### `Hypostructure.Graph.Strategy.SpineRows.WedgeSupply`

#### `Hypostructure.Graph.Strategy.Spine.wedgeSupplyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/WedgeSupply.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.ObstructionPacking`

#### `Hypostructure.Graph.Strategy.Spine.windowFreeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/ObstructionPacking.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.uncompressible) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowFree ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPresent ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowFree)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPresent) previous
```

### `Hypostructure.Graph.Strategy.SpineRows.WindowPackage`

#### `Hypostructure.Graph.Strategy.Spine.windowPackageRealizationDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/WindowPackage.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.skeletonDominates) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPackageRealized ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPackageUnrealized ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPackageRealized)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.windowPackageUnrealized) previous
```

#### `Hypostructure.Graph.Strategy.Spine.windowPackageRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/WindowPackage.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitCycle`

#### `Hypostructure.Graph.Strategy.Spine.windowShadowHitCycleRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/WindowShadowHitCycle.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows.WindowShadowHitExcluded`

#### `Hypostructure.Graph.Strategy.Spine.windowShadowHitExcludedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows/WindowShadowHitExcluded.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```
<!-- END GENERATED API -->
