# Allowed Hypostructure API

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
Compiled declarations: **629**.

Category counts: **Canonical execution** 33, **Canonical exhaustive decisions** 11, **Canonical fact-only steps and branch decisions** 5, **Canonical ledger** 98, **Canonical manifest** 35, **Canonical residual domain** 16, **Canonical scope initialization** 6, **Minimum-degree cycle spine rows** 94, **Minimum-degree cycle spine vocabulary** 319, **Sealed total closure** 12.

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

#### `Hypostructure.Graph.Strategy.Spine.AmbientCubicWindow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BarrierCapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BarrierEnumerationStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BarrierOverflowStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdAmbientCubicStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdAmbientCubicStubExcessStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdExchangeBoundStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureRoutingStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdGermCandidatesStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdHotEntropyCapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdHotEntropyOverflowStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdMassStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdRoute8AtOrAboveStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdRoute8BelowStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdSelectedBranchExcessStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdStubExcessStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Data`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Type 1
```

#### `Hypostructure.Graph.Strategy.Spine.Data.BoundaryProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Type
```

#### `Hypostructure.Graph.Strategy.Spine.Data.LengthOK`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Data.boundaryProfileFintype`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(self : Graph.Strategy.Spine.Data) → Fintype self.BoundaryProfile
```

#### `Hypostructure.Graph.Strategy.Spine.Data.boundaryProfileInhabited`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(self : Graph.Strategy.Spine.Data) → Inhabited self.BoundaryProfile
```

#### `Hypostructure.Graph.Strategy.Spine.Data.bridgeMassFactor`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.capacityTokenScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.coldSignature`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.ColdCorridor.DeclaredSignature
```

#### `Hypostructure.Graph.Strategy.Spine.Data.coldSignature_windowOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.coldSignature.windowOrder = self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.curvatureBarrierRow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(self : Graph.Strategy.Spine.Data) → self.windowBarrier.Index
```

#### `Hypostructure.Graph.Strategy.Spine.Data.curvatureCost`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.dischargeScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.dischargeScale_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 0 < self.dischargeScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.entropyDenominator`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.homogeneousCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.joinSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.threshold * self.windowOrder + 2 ≤ 4 * self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(threshold : ℕ) →
  3 ≤ threshold →
    (LengthOK : ℕ → Prop) →
      (windowOrder : ℕ) →
        0 < windowOrder →
          (∀ (object : Graph.FiniteObject),
              Graph.MinimumDegreeAtLeast threshold object →
                Graph.InducedPathFree object windowOrder → Graph.HasCycleWithLength LengthOK object) →
            LengthOK 4 →
              ¬LengthOK 2 →
                (dischargeScale : ℕ) →
                  0 < dischargeScale →
                    Graph.WindowCurvature.fanPackingCap windowOrder + 1 ≤ dischargeScale * threshold →
                      dischargeScale * threshold < 2 * dischargeScale + (threshold + 2) →
                        threshold * windowOrder + 2 ≤ 4 * windowOrder →
                          (BoundaryProfile : Type) →
                            (boundaryProfileFintype : Fintype BoundaryProfile) →
                              Inhabited BoundaryProfile →
                                (routingLabelBound : ℕ) →
                                  routingLabelBound =
                                      Fintype.card
                                        (Graph.SameTokenRoutingGerms.RoutingLabel BoundaryProfile
                                          (Graph.WindowCurvature.Label windowOrder)) →
                                    Graph.TokenLoad.quadraticSafetyScale ≤
                                        2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound) →
                                      ℕ →
                                        (windowRate : ℕ) →
                                          (windowBarrier : Core.Finite.CertifiedTableAggregation.BarrierPresentation) →
                                            windowRate = windowBarrier.binaryRateFloor →
                                              (separatedScaleCount : ℕ → ℕ) →
                                                (∀ (size : ℕ), separatedScaleCount size ≤ size.log2) →
                                                  (∀ (size : ℕ), separatedScaleCount size = size.log2) →
                                                    Graph.FiniteObject.netCapWindowCost threshold dischargeScale
                                                            windowOrder *
                                                          threshold <
                                                        2 * windowRate →
                                                      (curvatureCost : ℕ) →
                                                        (curvatureBarrierRow : windowBarrier.Index) →
                                                          curvatureCost =
                                                              Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
                                                                windowBarrier.table curvatureBarrierRow →
                                                            (entropyDenominator : ℕ) →
                                                              0 < entropyDenominator →
                                                                (coldSignature : Graph.ColdCorridor.DeclaredSignature) →
                                                                  coldSignature.windowOrder = windowOrder →
                                                                    (bridgeMassFactor : ℕ) →
                                                                      threshold + 2 + dischargeScale ≤
                                                                          bridgeMassFactor * dischargeScale →
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

#### `Hypostructure.Graph.Strategy.Spine.Data.netChargeCoefficient`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.routingLabelBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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
      (Graph.SameTokenRoutingGerms.RoutingLabel self.BoundaryProfile (Graph.WindowCurvature.Label self.windowOrder))
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.spineScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.surplusScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.surplusThreshold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.three_le_threshold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 3 ≤ self.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.Data.threshold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.typeABPresentation`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.TypeAB.Presentation
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowBarrier`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Core.Finite.CertifiedTableAggregation.BarrierPresentation
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowOrder_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 0 < self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.windowRate_eq_barrier`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.windowRate = self.windowBarrier.binaryRateFloor
```

#### `Hypostructure.Graph.Strategy.Spine.DeterminationCertificate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (packing : Finset (Finset object.Vertex)) →
      object.InternalWedge (object.remainderSupport packing) →
        Set (object.InternalWedge (object.remainderSupport packing)) →
          Graph.Strategy.Spine.remainderQuotient data object packing →
            Finset (object.InternalWedge (object.remainderSupport packing)) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ExitSixDelocalizes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.HandoffAdmissible`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.HandoffProduced`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Finset object.Vertex → Prop
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

#### `Hypostructure.Graph.Strategy.Spine.HotColdWindowStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Identified`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {packing : Finset (Finset object.Vertex)} →
      (quotient : Graph.Strategy.Spine.remainderQuotient data object packing) →
        Graph.BoundaryPiece (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object quotient.support) →
          Graph.BoundaryPiece (Graph.Strategy.InterfaceReplacement.SupportAtom.boundary object quotient.support) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Input`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → Graph.Strategy.Spine.Data → Type (max (u + 1) v)
```

#### `Hypostructure.Graph.Strategy.Spine.IsHotColdWindowPartition`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    Finset (Finset object.Vertex) → Finset (Finset object.Vertex) → Finset (Finset object.Vertex) → Prop
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

#### `Hypostructure.Graph.Strategy.Spine.Key.admissibleRankQuotient`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.branchDependence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.branchKillClosed`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldCorridorState`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureDefect`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureHandoff`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermExtraction`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldHandoffTransfer`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldMass`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldStubExcess`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.curvatureDemandFloor`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.delocalizedSupport`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.dependentPairFamily`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyPackageDemand`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.functionalRankQuotient`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.highCentreNormalForm`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.incrementalSkeletonRoom`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.largeBudgetResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.largeBudgetRoute8Closed`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.maximalPacking`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeLarge`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.netChargeSmall`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.primitiveCarrierAudit`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.quantitativeOverload`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.remainderSurplusAudit`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8CarrierDeletionWitnesses`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8GlobalSqueeze`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NoTwoCarrierContradiction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PressureDescent`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Residual`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TerminalNoGo`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TerminalResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8TwoCarrierReduction`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.sparseUpperEnvelope`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.stubSupply`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.targetRankCircuit`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFour`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourFree`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSevenProduced`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitSixProper`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedHandoffSilent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedHandoffVisible`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAVisibleEntryClause`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBBridgeSublinear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDegreeFourCentres`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDegreeFourProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDirectCycle`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBExclusionCharge`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBExclusionResidualMass`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHeavyCentre`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBLocalDichotomy`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBSelectedFanCharge`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.wedgeSupply`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.windowIncidenceAudit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.windowJoinPressure`

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

#### `Hypostructure.Graph.Strategy.Spine.LargeBudgetResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.LiveHotWindow`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8BasinBurden`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8CarrierCore`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8CarrierDeletionWitnesses`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8GlobalSqueeze`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8LargeBudgetDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8NoTwoCarrierContradiction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8PressureDescent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8PrivateCarrierBudget`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8SmallCoreCollapse`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8TerminalNoGo`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8TerminalResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8TwoCarrierReduction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SelectedNoExitSixReceiverWith`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    (Finset (Finset object.Vertex) → Finset object.Vertex → object.Vertex → Finset object.Vertex → Prop) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SelectedNoExitSixWith`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) → (Finset (Finset object.Vertex) → Finset object.Vertex → Prop) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SilentCoreResidualProfile`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TargetCompleteAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  {object : Graph.FiniteObject} →
    {packing : Finset (Finset object.Vertex)} → Graph.Strategy.Spine.remainderQuotient data object packing → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeAExitFourFiniteDescentFact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
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
          Core.Strategy.ProblemInput (Graph.Strategy.Spine.problem BranchState Presentation presentation data) → Type
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.admissibleRankQuotientRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (exactResponseProfile admissibleRankQuotient :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            exactResponseProfile ≠ admissibleRankQuotient →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : exactResponseProfile.At input),
                  Graph.Strategy.Spine.Holds BranchState Presentation presentation data
                    Graph.Strategy.Spine.Key.exactResponseProfile input.object) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    Graph.Strategy.Spine.Holds BranchState Presentation presentation data
                        Graph.Strategy.Spine.Key.admissibleRankQuotient input.object →
                      admissibleRankQuotient.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.atomCompressionDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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
                  ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.atomCompression) known →
                    ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport) known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.atomCompression)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport) previous
```

#### `Hypostructure.Graph.Strategy.Spine.b2AssignmentDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeBB2Choice typeBOverlapObstruction typeBDirectCycleFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeBDirectCycleFree known] →
                    (∀ (a : typeBDirectCycleFree.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                    ∀ centre ∈ piece,
                                      Graph.IsHighCentre current.object data.threshold centre →
                                        Graph.TypeBDirectCycle.DirectCycleFree current.object data.windowOrder
                                          data.LengthOK packing centre) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ canonicalPiece,
                                  Graph.FiniteObject.NegativeNetCharge current.object canonicalPiece.vertices
                                      data.threshold data.dischargeScale ∧
                                    0 <
                                        Graph.FiniteObject.ambientSurplus current.object canonicalPiece.vertices
                                          data.threshold ∧
                                      Graph.TypeBRefinedSupport.HasDisjointChoice current.object data.threshold
                                        data.dischargeScale canonicalPiece
                                        (Graph.TypeBRefinedSupport.centres current.object data.threshold
                                          canonicalPiece.vertices)) →
                          typeBB2Choice.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃ canonicalPiece,
                                    Graph.FiniteObject.NegativeNetCharge current.object canonicalPiece.vertices
                                        data.threshold data.dischargeScale ∧
                                      0 <
                                          Graph.FiniteObject.ambientSurplus current.object canonicalPiece.vertices
                                            data.threshold ∧
                                        Nonempty
                                          (Graph.TypeBRefinedSupport.OverlapObstruction current.object data.threshold
                                            data.dischargeScale canonicalPiece)) →
                            typeBOverlapObstruction.At current) →
                          typeBB2Choice ∉ known →
                            typeBOverlapObstruction ∉ known →
                              Core.Strategy.Decision typeBB2Choice typeBOverlapObstruction previous
```

#### `Hypostructure.Graph.Strategy.Spine.barrierEnumerationDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (maximalPacking barrierCap barrierOverflow :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has maximalPacking known] →
                    (∀ (a : maximalPacking.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            packing.card = Graph.FiniteObject.windowPackingNumber current.object data.windowOrder ∧
                              ∀ (support : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder support →
                                  ∃ member ∈ packing, ¬Disjoint support member) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              packing.card = Graph.FiniteObject.windowPackingNumber current.object data.windowOrder ∧
                                (∀ (support : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder support →
                                      ∃ member ∈ packing, ¬Disjoint support member) ∧
                                  2 ^
                                        (data.windowRate *
                                            data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                                          packing.card) ≤
                                      Graph.skeletonBudget current.object ∧
                                    ∀ (family : Finset ℕ),
                                      Graph.FiniteObject.edgeCount current.object ∈ family →
                                        Graph.skeletonBudget current.object ≤
                                          Graph.variableEdgeBudget (Graph.FiniteObject.vertexCount current.object)
                                            family) →
                          barrierCap.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                packing.card = Graph.FiniteObject.windowPackingNumber current.object data.windowOrder ∧
                                  (∀ (support : Finset current.object.Vertex),
                                      Graph.FiniteObject.InducesWindow current.object data.windowOrder support →
                                        ∃ member ∈ packing, ¬Disjoint support member) ∧
                                    Graph.skeletonBudget current.object <
                                      2 ^
                                        (data.windowRate *
                                            data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                                          packing.card)) →
                            barrierOverflow.At current) →
                          barrierCap ∉ known →
                            barrierOverflow ∉ known → Core.Strategy.Decision barrierCap barrierOverflow previous
```

#### `Hypostructure.Graph.Strategy.Spine.barrierEnumerationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.boundaryDemandRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.branchDependenceRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.branchKillClosedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.bridgeFanMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.canonicalColdWindows`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex)
```

#### `Hypostructure.Graph.Strategy.Spine.canonicalHotWindows`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex)
```

#### `Hypostructure.Graph.Strategy.Spine.canonicalWindowPacking`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex)
```

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

#### `Hypostructure.Graph.Strategy.Spine.coldExternalStubCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.coldSkeletonAllowance`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.coldWindowBitRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → ℕ
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.contextOfSelection`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
          ¬Graph.HasCycleWithLength data.LengthOK input.object →
            (∀ (smaller : Graph.FiniteObject),
                (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller
                    input.object →
                  Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
              Core.MinimalCounterexampleContext
                (Graph.Strategy.Spine.problem BranchState Presentation presentation data)
                (Graph.HasCycleWithLength data.LengthOK)
                (Graph.Strategy.Spine.progress BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.contextValidityDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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
                ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect) known →
                  ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal) known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal) previous
```

#### `Hypostructure.Graph.Strategy.Spine.curvatureRankDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.targetRankCircuit) known] →
                ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureRankDrop) known →
                  ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank) known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureRankDrop)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank) previous
```

#### `Hypostructure.Graph.Strategy.Spine.curvatureTargetRankRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.degreeFourProfileRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (highCentreNormalForm typeBDegreeFourCentres typeBDegreeFourProfile :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            highCentreNormalForm ≠ typeBDegreeFourCentres →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : highCentreNormalForm.At input) (centre : input.object.Vertex),
                  Graph.IsHighCentre input.object data.threshold centre →
                    Graph.NormalForm input.object data.threshold centre) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : typeBDegreeFourCentres.At input),
                    ∃ packing,
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                        (∀ (window : Finset input.object.Vertex),
                            Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                              ∃ member ∈ packing, ¬Disjoint window member) ∧
                          ∃
                            component ∈
                              Graph.FiniteObject.canonicalPieces input.object
                                (Graph.FiniteObject.remainderSupport input.object packing),
                            have piece :=
                              Graph.FiniteObject.pieceSupport input.object
                                (Graph.FiniteObject.remainderSupport input.object packing) component;
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                              0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                ∀ centre ∈ piece,
                                  Graph.IsHighCentre input.object data.threshold centre →
                                    Graph.FiniteObject.degree input.object centre = data.threshold + 1) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                    (∀ centre ∈ piece,
                                        Graph.IsHighCentre input.object data.threshold centre →
                                          Graph.FiniteObject.degree input.object centre = data.threshold + 1) ∧
                                      ∀ centre ∈ piece,
                                        Graph.FiniteObject.degree input.object centre = data.threshold + 1 →
                                          ((∃ left right, Graph.FanCompatible input.object centre left right) ∨
                                              data.threshold - 1 ≤
                                                (Graph.triangularEndpoints input.object centre).card) ∧
                                            Graph.FiniteObject.degree input.object centre - data.threshold = 1 ∧
                                              ∀ (envelope : Finset input.object.Vertex),
                                                Graph.TypeBFanIncidence.closedCount input.object data.threshold envelope
                                                      centre ≤
                                                    data.threshold + 1 ∧
                                                  Graph.TypeBFanIncidence.scaledDeficit input.object data.threshold
                                                      data.dischargeScale envelope centre =
                                                    ↑data.dischargeScale *
                                                          ↑(Graph.TypeBFanIncidence.closedCount input.object
                                                              data.threshold envelope centre) -
                                                        ↑data.dischargeScale * ↑data.threshold +
                                                      (↑data.threshold + 2)) →
                        typeBDegreeFourProfile.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.deletionCriticalityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.delocalizationScopeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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
                ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.properDelocalization) known →
                  ¬List.Mem (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.globalDelocalization) known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.properDelocalization)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.globalDelocalization) previous
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.delocalizationSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (packing : Finset (Finset object.Vertex)) →
      Graph.Strategy.Spine.remainderQuotient data object packing → Finset object.Vertex
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.densityBudgetRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.directCycleDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeBDirectCycle typeBDirectCycleFree typeBHighSurplus :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeBHighSurplus known] →
                    (∀ (a : typeBHighSurplus.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                      ∃ centre ∈ piece,
                                        Graph.IsHighCentre current.object data.threshold centre ∧
                                          Graph.TypeBDirectCycle.DirectCycleConfiguration current.object
                                            data.windowOrder data.LengthOK packing centre) →
                          typeBDirectCycle.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                        ∀ centre ∈ piece,
                                          Graph.IsHighCentre current.object data.threshold centre →
                                            Graph.TypeBDirectCycle.DirectCycleFree current.object data.windowOrder
                                              data.LengthOK packing centre) →
                            typeBDirectCycleFree.At current) →
                          typeBDirectCycle ∉ known →
                            typeBDirectCycleFree ∉ known →
                              Core.Strategy.Decision typeBDirectCycle typeBDirectCycleFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.entropyCapDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (entropyCapActive largeBudgetResidual :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          Graph.skeletonBudget current.object <
                            Graph.Strategy.Spine.jointPackageDemand data current.object packing) →
                      entropyCapActive.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            Graph.Strategy.Spine.jointPackageDemand data current.object packing ≤
                              Graph.skeletonBudget current.object) →
                        largeBudgetResidual.At current) →
                      entropyCapActive ∉ known →
                        largeBudgetResidual ∉ known →
                          Core.Strategy.Decision entropyCapActive largeBudgetResidual previous
```

#### `Hypostructure.Graph.Strategy.Spine.entropyPackageRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (remainderEntropyHigh entropyPackageDemand :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            remainderEntropyHigh ≠ entropyPackageDemand →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : remainderEntropyHigh.At input) (packing : Finset (Finset input.object.Vertex)),
                  Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                    Graph.AtLeastEntropyRate (Graph.FiniteObject.vertexCount input.object) data.entropyDenominator
                      data.windowOrder data.threshold
                      (Graph.FiniteObject.positiveDeficiency input.object
                        (Graph.FiniteObject.remainderSupport input.object packing) data.threshold)
                      (Graph.FiniteObject.remainderSupport input.object packing).card) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∀ (packing : Finset (Finset input.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                          (2 ^
                                    (data.windowRate *
                                        data.separatedScaleCount (Graph.FiniteObject.vertexCount input.object) *
                                      packing.card)) ^
                                  data.entropyDenominator *
                                Graph.FiniteObject.vertexCount input.object ^
                                  (Graph.FiniteObject.remainderSupport input.object packing).card *
                              (2 ^
                                  (data.curvatureCost *
                                    Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing)) ^
                                data.entropyDenominator ≤
                            Graph.Strategy.Spine.jointPackageDemand data input.object packing ^
                              data.entropyDenominator) →
                      entropyPackageDemand.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.exactResponseProfileRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
          (Core.Strategy.ProblemInput (Graph.Strategy.Spine.problem BranchState Presentation presentation data))
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (fanCertificateCap :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                (∀ (centre : input.object.Vertex),
                    Graph.IsHighCentre input.object data.threshold centre →
                      ∀ (_marking : Graph.FanCertificateLabelling input.object data.windowOrder centre),
                        Graph.FiniteObject.degree input.object centre ≤
                          Graph.WindowCurvature.fanPackingCap data.windowOrder) →
                  fanCertificateCap.At input) →
              Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeBHighSurplus fanCertificateMarked fanCertificateResidual :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeBHighSurplus known] →
                    (∀ (a : typeBHighSurplus.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                      ∀ centre ∈ piece,
                                        Graph.IsHighCentre current.object data.threshold centre →
                                          Nonempty
                                            (Graph.FanCertificateLabelling current.object data.windowOrder centre)) →
                          fanCertificateMarked.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                        ∃ centre ∈ piece,
                                          Graph.IsHighCentre current.object data.threshold centre ∧
                                            IsEmpty
                                              (Graph.FanCertificateLabelling current.object data.windowOrder centre)) →
                            fanCertificateResidual.At current) →
                          fanCertificateMarked ∉ known →
                            fanCertificateResidual ∉ known →
                              Core.Strategy.Decision fanCertificateMarked fanCertificateResidual previous
```

#### `Hypostructure.Graph.Strategy.Spine.fanCertificateResidualMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.forcedCurvatureCostRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (curvatureDemandFloor curvatureFullRank forcedCurvatureCost :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            curvatureDemandFloor ≠ curvatureFullRank →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : curvatureDemandFloor.At input) (packing : Finset (Finset input.object.Vertex)),
                  Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                    data.threshold * (Graph.FiniteObject.remainderSupport input.object packing).card +
                        2 * (2 * (data.windowOrder - 1) * packing.card) ≤
                      Graph.FiniteObject.internalWedgeCount input.object
                          (Graph.FiniteObject.remainderSupport input.object packing) +
                        2 *
                          (data.threshold * (data.windowOrder * packing.card) +
                            Graph.FiniteObject.ambientSurplus input.object (Graph.FiniteObject.windowSupport packing)
                              data.threshold)) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : curvatureFullRank.At input) (packing : Finset (Finset input.object.Vertex)),
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                      Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing =
                        Graph.Strategy.Spine.remainderWedgeSupply input.object packing) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (packing : Finset (Finset input.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                            data.curvatureCost *
                                (data.threshold * (Graph.FiniteObject.remainderSupport input.object packing).card +
                                  2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
                              data.curvatureCost *
                                  Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing +
                                data.curvatureCost *
                                  (2 *
                                    (data.threshold * (data.windowOrder * packing.card) +
                                      Graph.FiniteObject.ambientSurplus input.object
                                        (Graph.FiniteObject.windowSupport packing) data.threshold))) →
                        forcedCurvatureCost.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.functionalRankQuotientRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.globalBarrierRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.handoffAbsorbing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → object.Vertex → object.Vertex → object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.handoffHighDegree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) → object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.handoffUncompressible`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.handoffWindowFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.heavyCentreDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeBHighSurplus typeBHeavyCentre typeBDegreeFourCentres :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeBHighSurplus known] →
                    (∀ (a : typeBHighSurplus.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                      ∃ centre ∈ piece,
                                        data.threshold + 1 < Graph.FiniteObject.degree current.object centre) →
                          typeBHeavyCentre.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                        ∀ centre ∈ piece,
                                          Graph.IsHighCentre current.object data.threshold centre →
                                            Graph.FiniteObject.degree current.object centre = data.threshold + 1) →
                            typeBDegreeFourCentres.At current) →
                          typeBHeavyCentre ∉ known →
                            typeBDegreeFourCentres ∉ known →
                              Core.Strategy.Decision typeBHeavyCentre typeBDegreeFourCentres previous
```

#### `Hypostructure.Graph.Strategy.Spine.heavyCentreLocalDichotomyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (highCentreNormalForm typeBHeavyCentre typeBLocalDichotomy :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            highCentreNormalForm ≠ typeBHeavyCentre →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : highCentreNormalForm.At input) (centre : input.object.Vertex),
                  Graph.IsHighCentre input.object data.threshold centre →
                    Graph.NormalForm input.object data.threshold centre) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : typeBHeavyCentre.At input),
                    ∃ packing,
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                        (∀ (window : Finset input.object.Vertex),
                            Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                              ∃ member ∈ packing, ¬Disjoint window member) ∧
                          ∃
                            component ∈
                              Graph.FiniteObject.canonicalPieces input.object
                                (Graph.FiniteObject.remainderSupport input.object packing),
                            have piece :=
                              Graph.FiniteObject.pieceSupport input.object
                                (Graph.FiniteObject.remainderSupport input.object packing) component;
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                              0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                ∃ centre ∈ piece, data.threshold + 1 < Graph.FiniteObject.degree input.object centre) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                    (∃ centre ∈ piece,
                                        data.threshold + 1 < Graph.FiniteObject.degree input.object centre) ∧
                                      ∀ centre ∈ piece,
                                        data.threshold + 1 < Graph.FiniteObject.degree input.object centre →
                                          (∃ left right, Graph.FanCompatible input.object centre left right) ∨
                                            Graph.FiniteObject.degree input.object centre - 2 ≤
                                                (Graph.triangularEndpoints input.object centre).card ∧
                                              3 ≤ (Graph.triangularEndpoints input.object centre).card) →
                        typeBLocalDichotomy.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.highCentreNormalFormRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection tightEndpoint highCentreNormalForm :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ tightEndpoint →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : tightEndpoint.At input) (dart : input.object.graph.Dart),
                    Graph.FiniteObject.degree input.object dart.toProd.1 = data.threshold ∨
                      Graph.FiniteObject.degree input.object dart.toProd.2 = data.threshold) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (centre : input.object.Vertex),
                          Graph.IsHighCentre input.object data.threshold centre →
                            Graph.NormalForm input.object data.threshold centre) →
                        highCentreNormalForm.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.hotColdPartitionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.hybridEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection fanCertificateCap fanCertificateMarked typeBHybridEntry :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ fanCertificateCap →
              selection ≠ fanCertificateMarked →
                fanCertificateCap ≠ fanCertificateMarked →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                    (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                        (a : fanCertificateCap.At input) (centre : input.object.Vertex),
                        Graph.IsHighCentre input.object data.threshold centre →
                          ∀ (_marking : Graph.FanCertificateLabelling input.object data.windowOrder centre),
                            Graph.FiniteObject.degree input.object centre ≤
                              Graph.WindowCurvature.fanPackingCap data.windowOrder) →
                      (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                          (a : fanCertificateMarked.At input),
                          ∃ packing,
                            Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                              (∀ (window : Finset input.object.Vertex),
                                  Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                      data.dischargeScale ∧
                                    0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                      ∀ centre ∈ piece,
                                        Graph.IsHighCentre input.object data.threshold centre →
                                          Nonempty
                                            (Graph.FanCertificateLabelling input.object data.windowOrder centre)) →
                        ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                            (∃ packing,
                                Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                                  (∀ (window : Finset input.object.Vertex),
                                      Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                        ∃ member ∈ packing, ¬Disjoint window member) ∧
                                    ∃
                                      component ∈
                                        Graph.FiniteObject.canonicalPieces input.object
                                          (Graph.FiniteObject.remainderSupport input.object packing),
                                      have piece :=
                                        Graph.FiniteObject.pieceSupport input.object
                                          (Graph.FiniteObject.remainderSupport input.object packing) component;
                                      Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                          data.dischargeScale ∧
                                        0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold ∧
                                          ∀ centre ∈ piece,
                                            Graph.IsHighCentre input.object data.threshold centre →
                                              ∀ (envelope windowSupport : Finset input.object.Vertex),
                                                (∀
                                                    left ∈
                                                      Graph.TypeBFanIncidence.closedNeighbours input.object
                                                        data.threshold envelope centre,
                                                    ∀
                                                      right ∈
                                                        Graph.TypeBFanIncidence.closedNeighbours input.object
                                                          data.threshold envelope centre,
                                                      left ≠ right →
                                                        ∀
                                                          shared ∈
                                                            Graph.TypeBHybridIncidence.nonHubIncidences input.object
                                                              centre left,
                                                          shared ∉
                                                            Graph.TypeBHybridIncidence.nonHubIncidences input.object
                                                              centre right) ∧
                                                  Graph.TypeBHybridIncidence.windowIncidences input.object
                                                          data.threshold envelope windowSupport centre +
                                                        Graph.TypeBHybridIncidence.nonWindowIncidences input.object
                                                          data.threshold envelope windowSupport centre =
                                                      (data.threshold - 1) *
                                                        Graph.TypeBFanIncidence.closedCount input.object data.threshold
                                                          envelope centre ∧
                                                    2 *
                                                          Graph.TypeBFanIncidence.scaledDeficit input.object
                                                            data.threshold data.dischargeScale envelope centre ≤
                                                        ↑data.dischargeScale *
                                                          (↑(Graph.TypeBHybridIncidence.windowIncidences input.object
                                                                data.threshold envelope windowSupport centre) +
                                                            ↑(Graph.TypeBHybridIncidence.nonWindowIncidences
                                                                input.object data.threshold envelope windowSupport
                                                                centre)) ∧
                                                      Graph.TypeBHybridIncidence.nonWindowDemand input.object
                                                            data.threshold data.dischargeScale envelope windowSupport
                                                            centre ≤
                                                          ↑data.dischargeScale *
                                                            ↑(Graph.TypeBHybridIncidence.nonWindowIncidences
                                                                input.object data.threshold envelope windowSupport
                                                                centre) ∧
                                                        (2 ≤
                                                            Graph.TypeBFanIncidence.closedCount input.object
                                                              data.threshold envelope centre →
                                                          0 <
                                                            Graph.TypeBFanIncidence.scaledDeficit input.object
                                                              data.threshold data.dischargeScale envelope centre)) →
                              typeBHybridEntry.At input) →
                          Core.Strategy.AtomicStrategy
                            (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.interfaceReplacementRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.jointPackageDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → ℕ
```

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
            (Core.Strategy.ProblemInput (Graph.Strategy.Spine.problem BranchState Presentation presentation data))
```

#### `Hypostructure.Graph.Strategy.Spine.label`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → String
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.largeBudgetRoute8ClosedRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.localAlgebraRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.lowEntropyLargeBudgetRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (source largeBudgetResidual :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            source ≠ largeBudgetResidual →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) (a : source.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      Graph.BelowEntropyRate (Graph.FiniteObject.vertexCount input.object) data.entropyDenominator
                        data.windowOrder data.threshold
                        (Graph.FiniteObject.positiveDeficiency input.object
                          (Graph.FiniteObject.remainderSupport input.object packing) data.threshold)
                        (Graph.FiniteObject.remainderSupport input.object packing).card) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          Graph.BelowEntropyRate (Graph.FiniteObject.vertexCount input.object) data.entropyDenominator
                            data.windowOrder data.threshold
                            (Graph.FiniteObject.positiveDeficiency input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) data.threshold)
                            (Graph.FiniteObject.remainderSupport input.object packing).card) →
                      largeBudgetResidual.At input) →
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

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.negativeSupportRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (netChargeNegative netChargeLocalization negativeSupport :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            netChargeNegative ≠ netChargeLocalization →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : netChargeNegative.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        Graph.FiniteObject.NegativeNetCharge input.object
                          (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                          data.dischargeScale) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : netChargeLocalization.At input) (packing : Finset (Finset input.object.Vertex)),
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                      Graph.FiniteObject.NegativeNetCharge input.object
                          (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                          data.dischargeScale →
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          Graph.FiniteObject.NegativeNetCharge input.object
                            (Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component)
                            data.threshold data.dischargeScale) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing),
                                Graph.FiniteObject.NegativeNetCharge input.object
                                  (Graph.FiniteObject.pieceSupport input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing) component)
                                  data.threshold data.dischargeScale) →
                        negativeSupport.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.netChargeCapRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (densityCap stubSupply netChargeLarge netChargeCap :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            [densityCap, stubSupply, netChargeLarge].Nodup →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : densityCap.At input),
                  2 *
                      (data.windowRate * data.separatedScaleCount (Graph.FiniteObject.vertexCount input.object) *
                        Graph.FiniteObject.windowPackingNumber input.object data.windowOrder) ≤
                    (Graph.dyadicScaleCount input.object + 1) *
                      (data.threshold * Graph.FiniteObject.vertexCount input.object +
                        data.surplusThreshold (Graph.FiniteObject.vertexCount input.object))) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : stubSupply.At input) (packing : Finset (Finset input.object.Vertex)),
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                      Graph.FiniteObject.positiveDeficiency input.object
                            (Graph.FiniteObject.remainderSupport input.object packing) data.threshold +
                          2 * (data.windowOrder - 1) * packing.card ≤
                        data.threshold * (data.windowOrder * packing.card) +
                          data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : netChargeLarge.At input),
                      Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold data.dischargeScale data.windowOrder
                        data.windowRate data.spineScale (Graph.FiniteObject.vertexCount input.object)) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                        (∀ (packing : Finset (Finset input.object.Vertex)),
                            Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                              packing.card = Graph.FiniteObject.windowPackingNumber input.object data.windowOrder →
                                Graph.FiniteObject.NegativeNetCharge input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                                  data.dischargeScale) →
                          netChargeCap.At input) →
                      Core.Strategy.AtomicStrategy
                        (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.netChargeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (netChargeNonNegative netChargeNegative :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          (∀ (window : Finset current.object.Vertex),
                              Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) →
                            Graph.FiniteObject.NonNegativeNetCharge current.object
                              (Graph.FiniteObject.remainderSupport current.object packing) data.threshold
                              data.dischargeScale) →
                      netChargeNonNegative.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              Graph.FiniteObject.NegativeNetCharge current.object
                                (Graph.FiniteObject.remainderSupport current.object packing) data.threshold
                                data.dischargeScale) →
                        netChargeNegative.At current) →
                      netChargeNonNegative ∉ known →
                        netChargeNegative ∉ known →
                          Core.Strategy.Decision netChargeNonNegative netChargeNegative previous
```

#### `Hypostructure.Graph.Strategy.Spine.netChargeLocalizationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (netChargeLocalization :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                (∀ (packing : Finset (Finset input.object.Vertex)),
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                      Graph.FiniteObject.NegativeNetCharge input.object
                          (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                          data.dischargeScale →
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          Graph.FiniteObject.NegativeNetCharge input.object
                            (Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component)
                            data.threshold data.dischargeScale) →
                  netChargeLocalization.At input) →
              Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.netChargeOrderDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (netChargeLarge netChargeSmall :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  (Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold data.dischargeScale data.windowOrder
                        data.windowRate data.spineScale (Graph.FiniteObject.vertexCount current.object) →
                      netChargeLarge.At current) →
                    (¬Graph.FiniteObject.SufficientlyLargeForNetCap data.threshold data.dischargeScale data.windowOrder
                            data.windowRate data.spineScale (Graph.FiniteObject.vertexCount current.object) →
                        netChargeSmall.At current) →
                      netChargeLarge ∉ known →
                        netChargeSmall ∉ known → Core.Strategy.Decision netChargeLarge netChargeSmall previous
```

#### `Hypostructure.Graph.Strategy.Spine.noProperBaselineRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.obstructionPackingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.pairManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.problem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → Graph.Strategy.Spine.Data → Core.Problem
```

#### `Hypostructure.Graph.Strategy.Spine.progress`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        Core.Progress (Graph.Strategy.Spine.problem BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.registeredHomogeneousCap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
ℕ → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.registeredSpineScale`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
ℕ → ℕ → ℕ → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.remainderCurvatureTargetRank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.remainderCurvatureTests`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) →
  (packing : Finset (Finset object.Vertex)) → Finset (object.InternalWedge (object.remainderSupport packing))
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.remainderEntropyDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (remainderEntropyHigh remainderEntropyLow :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          Graph.AtLeastEntropyRate (Graph.FiniteObject.vertexCount current.object)
                            data.entropyDenominator data.windowOrder data.threshold
                            (Graph.FiniteObject.positiveDeficiency current.object
                              (Graph.FiniteObject.remainderSupport current.object packing) data.threshold)
                            (Graph.FiniteObject.remainderSupport current.object packing).card) →
                      remainderEntropyHigh.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            Graph.BelowEntropyRate (Graph.FiniteObject.vertexCount current.object)
                              data.entropyDenominator data.windowOrder data.threshold
                              (Graph.FiniteObject.positiveDeficiency current.object
                                (Graph.FiniteObject.remainderSupport current.object packing) data.threshold)
                              (Graph.FiniteObject.remainderSupport current.object packing).card) →
                        remainderEntropyLow.At current) →
                      remainderEntropyHigh ∉ known →
                        remainderEntropyLow ∉ known →
                          Core.Strategy.Decision remainderEntropyHigh remainderEntropyLow previous
```

#### `Hypostructure.Graph.Strategy.Spine.remainderNormalizationRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.remainderQuotient`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Type (u + 2)
```

#### `Hypostructure.Graph.Strategy.Spine.remainderStates`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.remainderSupport_ssubset_delocalizationSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) {object : Graph.FiniteObject} {packing : Finset (Finset object.Vertex)}
  (quotient : Graph.Strategy.Spine.remainderQuotient data object packing),
  ¬quotient.support ⊆ object.remainderSupport packing →
    object.remainderSupport packing ⊂ Graph.Strategy.Spine.delocalizationSupport data object packing quotient
```

#### `Hypostructure.Graph.Strategy.Spine.remainderSupport_subset_delocalizationSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) {object : Graph.FiniteObject} {packing : Finset (Finset object.Vertex)}
  (quotient : Graph.Strategy.Spine.remainderQuotient data object packing),
  object.remainderSupport packing ⊆ Graph.Strategy.Spine.delocalizationSupport data object packing quotient
```

#### `Hypostructure.Graph.Strategy.Spine.remainderWedgeSupply`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) → Finset (Finset object.Vertex) → ℕ
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.repairIdentityRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.returnAvoidanceRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8BasinBurdenRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierCoreRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierDeletionWitnessesRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8GlobalSqueezeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8LargeBudgetDeficitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8PressureDescentRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierContradictionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8ResidualProfileRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8ResidualRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8SmallCoreCollapseRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8TerminalNoGoRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.route8TwoCarrierReductionRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.rowManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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

#### `Hypostructure.Graph.Strategy.Spine.sourceFreeManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
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

#### `Hypostructure.Graph.Strategy.Spine.stubSupplyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.surplusDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (surplusAbove surplusAtOrBelow :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  (data.surplusThreshold (Graph.FiniteObject.vertexCount current.object) <
                        Graph.FiniteObject.degreeSurplus current.object data.threshold →
                      surplusAbove.At current) →
                    (Graph.FiniteObject.degreeSurplus current.object data.threshold ≤
                          data.surplusThreshold (Graph.FiniteObject.vertexCount current.object) →
                        surplusAtOrBelow.At current) →
                      surplusAbove ∉ known →
                        surplusAtOrBelow ∉ known → Core.Strategy.Decision surplusAbove surplusAtOrBelow previous
```

#### `Hypostructure.Graph.Strategy.Spine.targetRankCircuitRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFiveDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeASaturatedHandoffExitFourFree typeAExitFive typeAExitFiveFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeASaturatedHandoffExitFourFree known] →
                    (∀ (a : typeASaturatedHandoffExitFourFree.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled ∧
                                            ((∃ package,
                                                ¬∃ witness,
                                                    ∃
                                                      load ∈
                                                        Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                          data.dischargeScale receiver package.outside peeled,
                                                      witness.load = load) ∨
                                              Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                  data.dischargeScale receiver peeled ∧
                                                ¬∃ witness,
                                                    witness.load ∈
                                                      Graph.ExitFour.unpeeledExcess piece data.threshold
                                                        data.dischargeScale receiver peeled)) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                receiver peeled ∧
                                              ((∃ package,
                                                    ¬∃ witness,
                                                        ∃
                                                          load ∈
                                                            Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                              data.threshold data.dischargeScale receiver
                                                              package.outside peeled,
                                                          witness.load = load) ∨
                                                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                      data.dischargeScale receiver peeled ∧
                                                    ¬∃ witness,
                                                        witness.load ∈
                                                          Graph.ExitFour.unpeeledExcess piece data.threshold
                                                            data.dischargeScale receiver peeled) ∧
                                                ∃ support,
                                                  Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                    (Graph.MinimumDegreeAtLeast data.threshold)
                                                    (Graph.HasCycleWithLength data.LengthOK) current.object support) →
                          typeAExitFive.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            ∃
                                              peeled ⊆
                                                Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                  receiver,
                                              Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                  receiver peeled ∧
                                                ((∃ package,
                                                      ¬∃ witness,
                                                          ∃
                                                            load ∈
                                                              Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                                data.threshold data.dischargeScale receiver
                                                                package.outside peeled,
                                                            witness.load = load) ∨
                                                    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                        data.dischargeScale receiver peeled ∧
                                                      ¬∃ witness,
                                                          witness.load ∈
                                                            Graph.ExitFour.unpeeledExcess piece data.threshold
                                                              data.dischargeScale receiver peeled) ∧
                                                  ¬∃ support,
                                                      Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                        (Graph.MinimumDegreeAtLeast data.threshold)
                                                        (Graph.HasCycleWithLength data.LengthOK) current.object
                                                        support) →
                            typeAExitFiveFree.At current) →
                          typeAExitFive ∉ known →
                            typeAExitFiveFree ∉ known → Core.Strategy.Decision typeAExitFive typeAExitFiveFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAExitThreeFree typeAExitFour typeAExitFourFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAExitThreeFree known] →
                    (∀ (a : typeAExitThreeFree.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          ∃ package,
                                            Graph.WindowLabelCollision.LabelCollisionFree current.object
                                              data.windowOrder data.LengthOK packing) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃ package witness,
                                              ∃
                                                load ∈
                                                  Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                    data.dischargeScale receiver package.outside ∅,
                                                witness.load = load) →
                          typeAExitFour.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃ package,
                                                ¬∃ witness,
                                                    ∃
                                                      load ∈
                                                        Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                          data.dischargeScale receiver package.outside ∅,
                                                      witness.load = load) →
                            typeAExitFourFree.At current) →
                          typeAExitFour ∉ known →
                            typeAExitFourFree ∉ known → Core.Strategy.Decision typeAExitFour typeAExitFourFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourFiniteDescentRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeASaturatedExitEntry typeAExitFourFiniteDescent :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeASaturatedExitEntry ≠ typeAExitFourFiniteDescent →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeASaturatedExitEntry.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          have piece :=
                            Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component;
                          Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                            Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                              ∃ receiver,
                                Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                  ∃ peeled ⊆ Graph.FiniteObject.routedLoads input.object piece data.threshold receiver,
                                    Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale receiver
                                      peeled) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃
                              component ∈
                                Graph.FiniteObject.canonicalPieces input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing),
                              have piece :=
                                Graph.FiniteObject.pieceSupport input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) component;
                              Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                  data.dischargeScale ∧
                                Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                  ∃ receiver,
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                      ∃
                                        startPeeled ⊆
                                          Graph.FiniteObject.routedLoads input.object piece data.threshold receiver,
                                        Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale receiver
                                            startPeeled ∧
                                          ∀ (Retained Terminal : Finset input.object.Vertex → Prop),
                                            Retained startPeeled →
                                              (∀
                                                  peeled ⊆
                                                    Graph.FiniteObject.routedLoads input.object piece data.threshold
                                                      receiver,
                                                  Retained peeled →
                                                    Graph.ExitFour.SaturatedAfter piece data.threshold
                                                        data.dischargeScale receiver peeled →
                                                      Terminal peeled ∨
                                                        ∃
                                                          load ∈
                                                            Graph.FiniteObject.routedLoads input.object piece
                                                              data.threshold receiver,
                                                          ∃ (fresh : load ∉ peeled),
                                                            Retained (Finset.cons load peeled fresh)) →
                                                (∃
                                                    finalPeeled ⊆
                                                      Graph.FiniteObject.routedLoads input.object piece data.threshold
                                                        receiver,
                                                    Retained finalPeeled ∧ Terminal finalPeeled) ∨
                                                  ∃
                                                    finalPeeled ⊆
                                                      Graph.FiniteObject.routedLoads input.object piece data.threshold
                                                        receiver,
                                                    Retained finalPeeled ∧
                                                      ¬Graph.ExitFour.SaturatedAfter piece data.threshold
                                                          data.dischargeScale receiver finalPeeled) →
                      typeAExitFourFiniteDescent.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourPeelingStepRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeAExitFour typeAExitFourPeeled :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeAExitFour ≠ typeAExitFourPeeled →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeAExitFour.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          have piece :=
                            Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component;
                          Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                            Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                              ∃ receiver,
                                Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                  Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                      receiver ∧
                                    ∃ package witness,
                                      ∃
                                        load ∈
                                          Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                            data.dischargeScale receiver package.outside ∅,
                                        witness.load = load) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃
                              component ∈
                                Graph.FiniteObject.canonicalPieces input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing),
                              have piece :=
                                Graph.FiniteObject.pieceSupport input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) component;
                              Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                  data.dischargeScale ∧
                                Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                  ∃ receiver,
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                      Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                          receiver ∧
                                        ∃ package witness,
                                          ∃
                                            load ∈
                                              Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                data.dischargeScale receiver package.outside ∅,
                                            witness.load = load ∧
                                              witness.nextPeeled ⊆
                                                  Graph.FiniteObject.routedLoads input.object piece data.threshold
                                                    receiver ∧
                                                Graph.ExitFour.residualLoad piece data.threshold receiver
                                                      witness.nextPeeled +
                                                    1 =
                                                  Graph.ExitFour.residualLoad piece data.threshold receiver ∅) →
                      typeAExitFourPeeled.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitFourRetestDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAExitFourPeeled typeASaturatedExitEntry typeAExitFourReceiverDischarged :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAExitFourPeeled known] →
                    (∀ (a : typeAExitFourPeeled.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          ∃ package witness,
                                            ∃
                                              load ∈
                                                Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                  data.dischargeScale receiver package.outside ∅,
                                              witness.load = load ∧
                                                witness.nextPeeled ⊆
                                                    Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                      receiver ∧
                                                  Graph.ExitFour.residualLoad piece data.threshold receiver
                                                        witness.nextPeeled +
                                                      1 =
                                                    Graph.ExitFour.residualLoad piece data.threshold receiver ∅) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled) →
                          typeASaturatedExitEntry.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃ package witness,
                                                ∃
                                                  load ∈
                                                    Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                      data.dischargeScale receiver package.outside ∅,
                                                  witness.load = load ∧
                                                    witness.nextPeeled ⊆
                                                        Graph.FiniteObject.routedLoads current.object piece
                                                          data.threshold receiver ∧
                                                      Graph.ExitFour.residualLoad piece data.threshold receiver
                                                              witness.nextPeeled +
                                                            1 =
                                                          Graph.ExitFour.residualLoad piece data.threshold receiver ∅ ∧
                                                        ¬Graph.ExitFour.SaturatedAfter piece data.threshold
                                                              data.dischargeScale receiver witness.nextPeeled ∧
                                                          1 +
                                                              Graph.ExitFour.residualLoad piece data.threshold receiver
                                                                witness.nextPeeled ≤
                                                            data.dischargeScale *
                                                              Graph.FiniteObject.missingPorts current.object piece
                                                                data.threshold receiver) →
                            typeAExitFourReceiverDischarged.At current) →
                          typeASaturatedExitEntry ∉ known →
                            typeAExitFourReceiverDischarged ∉ known →
                              Core.Strategy.Decision typeASaturatedExitEntry typeAExitFourReceiverDischarged previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitOneDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAVisibleEntry typeAExitOneReturn typeAExitOneFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAVisibleEntry known] →
                    (∀ (a : typeAVisibleEntry.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          Nonempty
                                            (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                              data.dischargeScale receiver ∅)) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃ package return',
                                              Graph.ShiftedCycleLength data.LengthOK return'.path.length) →
                          typeAExitOneReturn.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃ package,
                                                ∀
                                                  (return' :
                                                    Graph.VisibleEntry.AnchoredReturn current.object receiver
                                                      package.outside),
                                                  ¬Graph.ShiftedCycleLength data.LengthOK return'.path.length) →
                            typeAExitOneFree.At current) →
                          typeAExitOneReturn ∉ known →
                            typeAExitOneFree ∉ known →
                              Core.Strategy.Decision typeAExitOneReturn typeAExitOneFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSevenHandoffRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection uncompressible typeAExitSevenProduced typeAExitSevenHandoff :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            [selection, uncompressible, typeAExitSevenProduced].Nodup →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : uncompressible.At input) (support : Finset input.object.Vertex),
                    ¬Graph.Strategy.InterfaceReplacement.CompressibleSupport (Graph.MinimumDegreeAtLeast data.threshold)
                        (Graph.HasCycleWithLength data.LengthOK) input.object support) →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : typeAExitSevenProduced.At input),
                      Graph.Strategy.Spine.SelectedNoExitSixWith data input.object fun packing piece =>
                        Graph.Strategy.Spine.HandoffProduced data input.object packing piece) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                        (Graph.Strategy.Spine.SelectedNoExitSixWith data input.object fun packing piece =>
                            Graph.Strategy.Spine.HandoffAdmissible data input.object packing piece) →
                          typeAExitSevenHandoff.At input) →
                      Core.Strategy.AtomicStrategy
                        (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAExitFiveFree typeAExitSix typeAExitSixFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAExitFiveFree known] →
                    (∀ (a : typeAExitFiveFree.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled ∧
                                            ((∃ package,
                                                  ¬∃ witness,
                                                      ∃
                                                        load ∈
                                                          Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                            data.threshold data.dischargeScale receiver package.outside
                                                            peeled,
                                                        witness.load = load) ∨
                                                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                    data.dischargeScale receiver peeled ∧
                                                  ¬∃ witness,
                                                      witness.load ∈
                                                        Graph.ExitFour.unpeeledExcess piece data.threshold
                                                          data.dischargeScale receiver peeled) ∧
                                              ¬∃ support,
                                                  Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                    (Graph.MinimumDegreeAtLeast data.threshold)
                                                    (Graph.HasCycleWithLength data.LengthOK) current.object support) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                receiver peeled ∧
                                              ((∃ package,
                                                    ¬∃ witness,
                                                        ∃
                                                          load ∈
                                                            Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                              data.threshold data.dischargeScale receiver
                                                              package.outside peeled,
                                                          witness.load = load) ∨
                                                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                      data.dischargeScale receiver peeled ∧
                                                    ¬∃ witness,
                                                        witness.load ∈
                                                          Graph.ExitFour.unpeeledExcess piece data.threshold
                                                            data.dischargeScale receiver peeled) ∧
                                                (¬∃ support,
                                                      Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                        (Graph.MinimumDegreeAtLeast data.threshold)
                                                        (Graph.HasCycleWithLength data.LengthOK) current.object
                                                        support) ∧
                                                  Graph.Strategy.Spine.ExitSixDelocalizes data current.object piece) →
                          typeAExitSix.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            ∃
                                              peeled ⊆
                                                Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                  receiver,
                                              Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                  receiver peeled ∧
                                                ((∃ package,
                                                      ¬∃ witness,
                                                          ∃
                                                            load ∈
                                                              Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                                data.threshold data.dischargeScale receiver
                                                                package.outside peeled,
                                                            witness.load = load) ∨
                                                    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                        data.dischargeScale receiver peeled ∧
                                                      ¬∃ witness,
                                                          witness.load ∈
                                                            Graph.ExitFour.unpeeledExcess piece data.threshold
                                                              data.dischargeScale receiver peeled) ∧
                                                  (¬∃ support,
                                                        Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                          (Graph.MinimumDegreeAtLeast data.threshold)
                                                          (Graph.HasCycleWithLength data.LengthOK) current.object
                                                          support) ∧
                                                    ¬Graph.Strategy.Spine.ExitSixDelocalizes data current.object
                                                        piece) →
                            typeAExitSixFree.At current) →
                          typeAExitSix ∉ known →
                            typeAExitSixFree ∉ known → Core.Strategy.Decision typeAExitSix typeAExitSixFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSixScopeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAExitSix typeAExitSixProper typeAExitSixGlobal :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAExitSix known] →
                    (∀ (a : typeAExitSix.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled ∧
                                            ((∃ package,
                                                  ¬∃ witness,
                                                      ∃
                                                        load ∈
                                                          Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                            data.threshold data.dischargeScale receiver package.outside
                                                            peeled,
                                                        witness.load = load) ∨
                                                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                    data.dischargeScale receiver peeled ∧
                                                  ¬∃ witness,
                                                      witness.load ∈
                                                        Graph.ExitFour.unpeeledExcess piece data.threshold
                                                          data.dischargeScale receiver peeled) ∧
                                              (¬∃ support,
                                                    Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                                      (Graph.MinimumDegreeAtLeast data.threshold)
                                                      (Graph.HasCycleWithLength data.LengthOK) current.object support) ∧
                                                Graph.Strategy.Spine.ExitSixDelocalizes data current.object piece) →
                      ((∃ support,
                            Graph.Strategy.InterfaceReplacement.ReplacementSupport
                              (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
                              current.object support) →
                          typeAExitSixProper.At current) →
                        ((∃ representative,
                              representative.LexicographicallySmaller current.object ∧
                                Graph.MinimumDegreeAtLeast data.threshold representative ∧
                                  (Graph.HasCycleWithLength data.LengthOK representative →
                                    Graph.HasCycleWithLength data.LengthOK current.object)) →
                            typeAExitSixGlobal.At current) →
                          typeAExitSixProper ∉ known →
                            typeAExitSixGlobal ∉ known →
                              Core.Strategy.Decision typeAExitSixProper typeAExitSixGlobal previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitThreeDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAVisibleEntry typeAExitThreeCollision typeAExitThreeFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAVisibleEntry known] →
                    (∀ (a : typeAVisibleEntry.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          Nonempty
                                            (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                              data.dischargeScale receiver ∅)) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃ package,
                                              Graph.WindowLabelCollision.LabelCollision current.object data.windowOrder
                                                data.LengthOK packing) →
                          typeAExitThreeCollision.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃ package,
                                                Graph.WindowLabelCollision.LabelCollisionFree current.object
                                                  data.windowOrder data.LengthOK packing) →
                            typeAExitThreeFree.At current) →
                          typeAExitThreeCollision ∉ known →
                            typeAExitThreeFree ∉ known →
                              Core.Strategy.Decision typeAExitThreeCollision typeAExitThreeFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitTwoDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAVisibleEntry typeAExitTwoTheta typeAExitTwoFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAVisibleEntry known] →
                    (∀ (a : typeAVisibleEntry.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          Nonempty
                                            (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                              data.dischargeScale receiver ∅)) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃ package,
                                              Graph.VisibleEntry.ExitTwoThrough current.object piece data.LengthOK
                                                receiver package.outside) →
                          typeAExitTwoTheta.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃ package,
                                                ¬Graph.VisibleEntry.ExitTwoThrough current.object piece data.LengthOK
                                                    receiver package.outside) →
                            typeAExitTwoFree.At current) →
                          typeAExitTwoTheta ∉ known →
                            typeAExitTwoFree ∉ known →
                              Core.Strategy.Decision typeAExitTwoTheta typeAExitTwoFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAPortReturnRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAReceiverRoutingRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturatedExitEntryRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (source typeASaturatedExitEntry :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            source ≠ typeASaturatedExitEntry →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) (a : source.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          have piece :=
                            Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component;
                          Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                            Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                              ∃ receiver,
                                Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                  Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                    receiver) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃
                              component ∈
                                Graph.FiniteObject.canonicalPieces input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing),
                              have piece :=
                                Graph.FiniteObject.pieceSupport input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) component;
                              Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                  data.dischargeScale ∧
                                Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                  ∃ receiver,
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                      ∃
                                        peeled ⊆
                                          Graph.FiniteObject.routedLoads input.object piece data.threshold receiver,
                                        Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale receiver
                                          peeled) →
                      typeASaturatedExitEntry.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSilentExitFourDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeASaturatedHandoffSilent typeASaturatedHandoffExitFour typeASaturatedHandoffExitFourFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeASaturatedHandoffSilent known] →
                    (∀ (a : typeASaturatedHandoffSilent.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled ∧
                                            Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                              data.dischargeScale receiver peeled) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                receiver peeled ∧
                                              ((∃ package witness,
                                                  ∃
                                                    load ∈
                                                      Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                        data.dischargeScale receiver package.outside peeled,
                                                    witness.load = load) ∨
                                                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                    data.dischargeScale receiver peeled ∧
                                                  ∃ witness,
                                                    witness.load ∈
                                                      Graph.ExitFour.unpeeledExcess piece data.threshold
                                                        data.dischargeScale receiver peeled)) →
                          typeASaturatedHandoffExitFour.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            ∃
                                              peeled ⊆
                                                Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                  receiver,
                                              Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                  receiver peeled ∧
                                                ((∃ package,
                                                    ¬∃ witness,
                                                        ∃
                                                          load ∈
                                                            Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                              data.threshold data.dischargeScale receiver
                                                              package.outside peeled,
                                                          witness.load = load) ∨
                                                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                      data.dischargeScale receiver peeled ∧
                                                    ¬∃ witness,
                                                        witness.load ∈
                                                          Graph.ExitFour.unpeeledExcess piece data.threshold
                                                            data.dischargeScale receiver peeled)) →
                            typeASaturatedHandoffExitFourFree.At current) →
                          typeASaturatedHandoffExitFour ∉ known →
                            typeASaturatedHandoffExitFourFree ∉ known →
                              Core.Strategy.Decision typeASaturatedHandoffExitFour typeASaturatedHandoffExitFourFree
                                previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSilentFromFirstExcessRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeAVisibleFirstExcess typeASaturatedHandoffSilent :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeAVisibleFirstExcess ≠ typeASaturatedHandoffSilent →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeAVisibleFirstExcess.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          have piece :=
                            Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component;
                          Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                            Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                              ∃ receiver,
                                Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                  Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                      receiver ∧
                                    Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold data.dischargeScale
                                      receiver ∅) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃
                              component ∈
                                Graph.FiniteObject.canonicalPieces input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing),
                              have piece :=
                                Graph.FiniteObject.pieceSupport input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) component;
                              Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                  data.dischargeScale ∧
                                Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                  ∃ receiver,
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                      ∃
                                        peeled ⊆
                                          Graph.FiniteObject.routedLoads input.object piece data.threshold receiver,
                                        Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale receiver
                                            peeled ∧
                                          Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold data.dischargeScale
                                            receiver peeled) →
                      typeASaturatedHandoffSilent.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffSplitDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeASaturatedExitEntry typeASaturatedHandoffVisible typeASaturatedHandoffSilent :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeASaturatedExitEntry known] →
                    (∀ (a : typeASaturatedExitEntry.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                            receiver peeled) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                receiver peeled ∧
                                              Nonempty
                                                (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                                  data.dischargeScale receiver peeled)) →
                          typeASaturatedHandoffVisible.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            ∃
                                              peeled ⊆
                                                Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                  receiver,
                                              Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                  receiver peeled ∧
                                                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                  data.dischargeScale receiver peeled) →
                            typeASaturatedHandoffSilent.At current) →
                          typeASaturatedHandoffVisible ∉ known →
                            typeASaturatedHandoffSilent ∉ known →
                              Core.Strategy.Decision typeASaturatedHandoffVisible typeASaturatedHandoffSilent previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturatedHandoffVisibleExitFourDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeASaturatedHandoffVisible typeASaturatedHandoffExitFour typeASaturatedHandoffExitFourFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeASaturatedHandoffVisible known] →
                    (∀ (a : typeASaturatedHandoffVisible.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads current.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                              receiver peeled ∧
                                            Nonempty
                                              (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                                data.dischargeScale receiver peeled)) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          ∃
                                            peeled ⊆
                                              Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                receiver,
                                            Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                receiver peeled ∧
                                              ((∃ package witness,
                                                  ∃
                                                    load ∈
                                                      Graph.ExitFour.selectedVisibleUnpeeledLoads piece data.threshold
                                                        data.dischargeScale receiver package.outside peeled,
                                                    witness.load = load) ∨
                                                Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                    data.dischargeScale receiver peeled ∧
                                                  ∃ witness,
                                                    witness.load ∈
                                                      Graph.ExitFour.unpeeledExcess piece data.threshold
                                                        data.dischargeScale receiver peeled)) →
                          typeASaturatedHandoffExitFour.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            ∃
                                              peeled ⊆
                                                Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                  receiver,
                                              Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                                  receiver peeled ∧
                                                ((∃ package,
                                                    ¬∃ witness,
                                                        ∃
                                                          load ∈
                                                            Graph.ExitFour.selectedVisibleUnpeeledLoads piece
                                                              data.threshold data.dischargeScale receiver
                                                              package.outside peeled,
                                                          witness.load = load) ∨
                                                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                      data.dischargeScale receiver peeled ∧
                                                    ¬∃ witness,
                                                        witness.load ∈
                                                          Graph.ExitFour.unpeeledExcess piece data.threshold
                                                            data.dischargeScale receiver peeled)) →
                            typeASaturatedHandoffExitFourFree.At current) →
                          typeASaturatedHandoffExitFour ∉ known →
                            typeASaturatedHandoffExitFourFree ∉ known →
                              Core.Strategy.Decision typeASaturatedHandoffExitFour typeASaturatedHandoffExitFourFree
                                previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeASaturationDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeALowSurplus typeASaturatedReceiver typeAUnsaturatedReceivers :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeALowSurplus known] →
                    (∀ (a : typeALowSurplus.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                            data.dischargeScale receiver) →
                          typeASaturatedReceiver.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∀ (receiver : current.object.Vertex),
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver →
                                            1 +
                                                Graph.FiniteObject.routedLoad current.object piece data.threshold
                                                  receiver ≤
                                              data.dischargeScale *
                                                Graph.FiniteObject.missingPorts current.object piece data.threshold
                                                  receiver) →
                            typeAUnsaturatedReceivers.At current) →
                          typeASaturatedReceiver ∉ known →
                            typeAUnsaturatedReceivers ∉ known →
                              Core.Strategy.Decision typeASaturatedReceiver typeAUnsaturatedReceivers previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAUnsaturatedDischargeRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeAReceiverRouting typeAUnsaturatedReceivers typeAUnsaturatedDischarge :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeAReceiverRouting ≠ typeAUnsaturatedReceivers →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeAReceiverRouting.At input) (packing : Finset (Finset input.object.Vertex)),
                  Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                    (∀ (window : Finset input.object.Vertex),
                        Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                          ∃ member ∈ packing, ¬Disjoint window member) →
                      ∀ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                        Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 →
                          (∀ vertex ∈ piece,
                              Graph.FiniteObject.internalDegree input.object piece vertex = data.threshold →
                                ∃ receiver,
                                  Graph.FiniteObject.traceReceiver? input.object piece data.threshold vertex =
                                      some receiver ∧
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver) ∧
                            ∀ (receiver : input.object.Vertex),
                              Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver →
                                data.dischargeScale *
                                      Graph.FiniteObject.missingPorts input.object piece data.threshold receiver =
                                    data.dischargeScale *
                                      (data.threshold - 1 -
                                          Graph.FiniteObject.internalDegree input.object piece receiver +
                                        1) ∧
                                  data.dischargeScale *
                                      Graph.FiniteObject.missingPorts input.object piece data.threshold receiver ≤
                                    data.dischargeScale * data.threshold) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : typeAUnsaturatedReceivers.At input),
                    ∃ packing,
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                        (∀ (window : Finset input.object.Vertex),
                            Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                              ∃ member ∈ packing, ¬Disjoint window member) ∧
                          ∃
                            component ∈
                              Graph.FiniteObject.canonicalPieces input.object
                                (Graph.FiniteObject.remainderSupport input.object packing),
                            have piece :=
                              Graph.FiniteObject.pieceSupport input.object
                                (Graph.FiniteObject.remainderSupport input.object packing) component;
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                              Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                ∀ (receiver : input.object.Vertex),
                                  Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver →
                                    1 + Graph.FiniteObject.routedLoad input.object piece data.threshold receiver ≤
                                      data.dischargeScale *
                                        Graph.FiniteObject.missingPorts input.object piece data.threshold receiver) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing),
                                have piece :=
                                  Graph.FiniteObject.pieceSupport input.object
                                    (Graph.FiniteObject.remainderSupport input.object packing) component;
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                    piece.card ≤
                                      data.dischargeScale *
                                        Graph.FiniteObject.positiveDeficiency input.object piece data.threshold) →
                        typeAUnsaturatedDischarge.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryClauseRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeAVisibleEntry typeAVisibleEntryClause :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeAVisibleEntry ≠ typeAVisibleEntryClause →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeAVisibleEntry.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃
                          component ∈
                            Graph.FiniteObject.canonicalPieces input.object
                              (Graph.FiniteObject.remainderSupport input.object packing),
                          have piece :=
                            Graph.FiniteObject.pieceSupport input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) component;
                          Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                            Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                              ∃ receiver,
                                Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                  Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                      receiver ∧
                                    Nonempty
                                      (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                        data.dischargeScale receiver ∅)) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃
                              component ∈
                                Graph.FiniteObject.canonicalPieces input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing),
                              have piece :=
                                Graph.FiniteObject.pieceSupport input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing) component;
                              Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                  data.dischargeScale ∧
                                Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                  ∃ receiver,
                                    Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                      Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                          receiver ∧
                                        ∃ package,
                                          (∀ (load : package.SelectedLoad),
                                              ((∀ vertex ∈ (package.selectedReturn ↑load ⋯).connector.support,
                                                    vertex ≠ ↑(package.selectedResponseCoordinate load).entry →
                                                      vertex ∉ piece) ∧
                                                  Graph.VisibleEntry.IsChannel input.object piece
                                                    (package.selectedResponseCoordinate load).channel) ∧
                                                (package.selectedPieceChannel load).length =
                                                    (package.selectedResponseCoordinate load).channel.length ∧
                                                  (package.selectedContextConnector load).length =
                                                    (package.selectedResponseCoordinate load).connectorLabel) ∧
                                            (∀ (selected : package.SelectedGerm),
                                                selected ∈ package.germSchedule.values) ∧
                                              ∀ (pair : package.GermPair),
                                                pair ∈ package.germPairSchedule.values ∧
                                                  Graph.DecoratedHandoff.SeparatesAt
                                                      (Graph.ExitFour.VisibleFourUnpeeledPackage.SelectedGerm.germ
                                                          package pair.left).path
                                                      (Graph.ExitFour.VisibleFourUnpeeledPackage.SelectedGerm.germ
                                                          package pair.right).path
                                                      pair.firstSeparator.separator ∧
                                                    pair.separatorOrder =
                                                      pair.firstSeparator.separator :: pair.firstSeparator.remaining) →
                      typeAVisibleEntryClause.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleEntryDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (typeAReceiverRouting typeASaturatedReceiver typeAVisibleEntry typeAVisibleFirstExcess :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeAReceiverRouting known] →
                    [Core.Residual.FactKeys.Has typeASaturatedReceiver known] →
                      (∀ (a : typeAReceiverRouting.At current) (packing : Finset (Finset current.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) →
                              ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
                                  (∀ vertex ∈ piece,
                                      Graph.FiniteObject.internalDegree current.object piece vertex = data.threshold →
                                        ∃ receiver,
                                          Graph.FiniteObject.traceReceiver? current.object piece data.threshold vertex =
                                              some receiver ∧
                                            Graph.FiniteObject.IsReceiver current.object piece data.threshold
                                              receiver) ∧
                                    ∀ (receiver : current.object.Vertex),
                                      Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver →
                                        data.dischargeScale *
                                              Graph.FiniteObject.missingPorts current.object piece data.threshold
                                                receiver =
                                            data.dischargeScale *
                                              (data.threshold - 1 -
                                                  Graph.FiniteObject.internalDegree current.object piece receiver +
                                                1) ∧
                                          data.dischargeScale *
                                              Graph.FiniteObject.missingPorts current.object piece data.threshold
                                                receiver ≤
                                            data.dischargeScale * data.threshold) →
                        (∀ (a : typeASaturatedReceiver.At current),
                            ∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver) →
                          ((∃ packing,
                                Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                  (∀ (window : Finset current.object.Vertex),
                                      Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                        ∃ member ∈ packing, ¬Disjoint window member) ∧
                                    ∃
                                      component ∈
                                        Graph.FiniteObject.canonicalPieces current.object
                                          (Graph.FiniteObject.remainderSupport current.object packing),
                                      have piece :=
                                        Graph.FiniteObject.pieceSupport current.object
                                          (Graph.FiniteObject.remainderSupport current.object packing) component;
                                      Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                          data.dischargeScale ∧
                                        Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                          ∃ receiver,
                                            Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                              Graph.FiniteObject.Saturated current.object piece data.threshold
                                                  data.dischargeScale receiver ∧
                                                Nonempty
                                                  (Graph.ExitFour.VisibleFourUnpeeledPackage piece data.threshold
                                                    data.dischargeScale receiver ∅)) →
                              typeAVisibleEntry.At current) →
                            ((∃ packing,
                                  Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                    (∀ (window : Finset current.object.Vertex),
                                        Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                          ∃ member ∈ packing, ¬Disjoint window member) ∧
                                      ∃
                                        component ∈
                                          Graph.FiniteObject.canonicalPieces current.object
                                            (Graph.FiniteObject.remainderSupport current.object packing),
                                        have piece :=
                                          Graph.FiniteObject.pieceSupport current.object
                                            (Graph.FiniteObject.remainderSupport current.object packing) component;
                                        Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                            data.dischargeScale ∧
                                          Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                            ∃ receiver,
                                              Graph.FiniteObject.IsReceiver current.object piece data.threshold
                                                  receiver ∧
                                                Graph.FiniteObject.Saturated current.object piece data.threshold
                                                    data.dischargeScale receiver ∧
                                                  Graph.ExitFour.SilentUnpeeledExcessAt piece data.threshold
                                                      data.dischargeScale receiver ∅ ∧
                                                    piece.card ≤
                                                      ∑
                                                          other ∈
                                                            Graph.FiniteObject.receivers current.object piece
                                                              data.threshold,
                                                          (Graph.VisibleEntry.silentExcess current.object piece
                                                              data.threshold data.dischargeScale other).card +
                                                        data.dischargeScale *
                                                          Graph.FiniteObject.positiveDeficiency current.object piece
                                                            data.threshold) →
                                typeAVisibleFirstExcess.At current) →
                              typeAVisibleEntry ∉ known →
                                typeAVisibleFirstExcess ∉ known →
                                  Core.Strategy.Decision typeAVisibleEntry typeAVisibleFirstExcess previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeBBridgeSublinearRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeBExclusionResidualMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeBOverlapObstructionMassRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.typeSplitDichotomy`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (negativeSupport typeALowSurplus typeBHighSurplus :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has negativeSupport known] →
                    (∀ (a : negativeSupport.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            (∀ (window : Finset current.object.Vertex),
                                Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃
                                component ∈
                                  Graph.FiniteObject.canonicalPieces current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing),
                                Graph.FiniteObject.NegativeNetCharge current.object
                                  (Graph.FiniteObject.pieceSupport current.object
                                    (Graph.FiniteObject.remainderSupport current.object packing) component)
                                  data.threshold data.dischargeScale) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃
                                  component ∈
                                    Graph.FiniteObject.canonicalPieces current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing),
                                  have piece :=
                                    Graph.FiniteObject.pieceSupport current.object
                                      (Graph.FiniteObject.remainderSupport current.object packing) component;
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0) →
                          typeALowSurplus.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃
                                    component ∈
                                      Graph.FiniteObject.canonicalPieces current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing),
                                    have piece :=
                                      Graph.FiniteObject.pieceSupport current.object
                                        (Graph.FiniteObject.remainderSupport current.object packing) component;
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold) →
                            typeBHighSurplus.At current) →
                          typeALowSurplus ∉ known →
                            typeBHighSurplus ∉ known → Core.Strategy.Decision typeALowSurplus typeBHighSurplus previous
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
        Core.Strategy.FactVocabulary (Graph.Strategy.Spine.problem BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.wedgeSupplyRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.windowJoinPressureRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (netChargeNonNegative boundaryDemand windowJoinPressure :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            netChargeNonNegative ≠ boundaryDemand →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : netChargeNonNegative.At input) (packing : Finset (Finset input.object.Vertex)),
                  Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                    (∀ (window : Finset input.object.Vertex),
                        Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                          ∃ member ∈ packing, ¬Disjoint window member) →
                      Graph.FiniteObject.NonNegativeNetCharge input.object
                        (Graph.FiniteObject.remainderSupport input.object packing) data.threshold data.dischargeScale) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : boundaryDemand.At input) (packing : Finset (Finset input.object.Vertex)),
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                      Graph.FiniteObject.positiveDeficiency input.object
                            (Graph.FiniteObject.remainderSupport input.object packing) data.threshold ≤
                          Graph.FiniteObject.boundaryIncidence input.object
                            (Graph.FiniteObject.remainderSupport input.object packing) ∧
                        Graph.FiniteObject.boundaryIncidence input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) +
                            2 * (data.windowOrder - 1) * packing.card ≤
                          data.threshold * (data.windowOrder * packing.card) +
                            Graph.FiniteObject.ambientSurplus input.object (Graph.FiniteObject.windowSupport packing)
                              data.threshold) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (packing : Finset (Finset input.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) →
                              Graph.FiniteObject.vertexCount input.object +
                                    data.dischargeScale *
                                      Graph.FiniteObject.ambientSurplus input.object
                                        (Graph.FiniteObject.remainderSupport input.object packing) data.threshold +
                                  data.dischargeScale * (2 * (data.windowOrder - 1) * packing.card) ≤
                                data.dischargeScale * (data.threshold * (data.windowOrder * packing.card)) +
                                    data.dischargeScale *
                                      Graph.FiniteObject.ambientSurplus input.object
                                        (Graph.FiniteObject.windowSupport packing) data.threshold +
                                  data.windowOrder * packing.card) →
                        windowJoinPressure.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.windowPackageRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```
<!-- END GENERATED API -->
