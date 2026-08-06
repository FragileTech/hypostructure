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
Compiled declarations: **468**.

Category counts: **Canonical execution** 33, **Canonical fact-only steps and branch decisions** 5, **Canonical ledger** 98, **Canonical manifest** 32, **Canonical residual domain** 16, **Canonical scope initialization** 6, **Minimum-degree cycle spine rows** 61, **Minimum-degree cycle spine vocabulary** 217.

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

#### `Hypostructure.Core.Strategy.ContradictionEvidence`

- Category: Canonical execution
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/ExactExecution.lean`
- Compiled type:

```lean
Type
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
      Core.Strategy.FactManifest Residual → Type (max (max uKey uResidual) (uValue + 2))
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
      {manifest : Core.Strategy.FactManifest Residual} → Core.Strategy.FactInputs manifest → Residual
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
      {manifest : Core.Strategy.FactManifest Residual} →
        (inputs : Core.Strategy.FactInputs manifest) →
          (key : Core.Residual.FactKey Residual) →
            [Core.Residual.FactKeys.Has key manifest.Requires] → key.At inputs.current
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

#### `Hypostructure.Core.Strategy.FactManifest.Requires`

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
      (Requires Produces : Core.Residual.FactKeys Residual) →
        List.Nodup Requires → List.Nodup Produces → Produces ≠ [] → Core.Strategy.FactManifest Residual
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

#### `Hypostructure.Core.Strategy.FactManifest.requiresUnique`

- Category: Canonical manifest
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/FactManifest.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} [inst : Core.Residual.RefinementSystem Residual]
  [inst_1 : Core.Residual.FactSystem Residual] (self : Core.Strategy.FactManifest Residual), List.Nodup self.Requires
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
          ((inputs : Core.Strategy.FactInputs manifest) →
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

#### `Hypostructure.Graph.Strategy.Spine.Data.curvatureCost`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.Data.joinSlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.threshold * self.windowOrder + 2 ≤ 4 * self.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.largeOrderExponent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.largeOrderExponent_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), 0 < self.largeOrderExponent
```

#### `Hypostructure.Graph.Strategy.Spine.Data.largeOrder_dominates_surplus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  4 *
        (((self.dischargeScale * (self.threshold * self.windowOrder - 2 * (self.windowOrder - 1)) + self.windowOrder) *
              (self.largeOrderExponent + 1) +
            2 * self.windowRate * self.largeOrderExponent * self.dischargeScale) *
          self.surplusScale) *
      (((self.dischargeScale * (self.threshold * self.windowOrder - 2 * (self.windowOrder - 1)) + self.windowOrder) *
            (self.largeOrderExponent + 1) +
          2 * self.windowRate * self.largeOrderExponent * self.dischargeScale) *
        self.surplusScale) ≤
    2 ^ self.largeOrderExponent
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
                            Fintype BoundaryProfile →
                              (surplusScale windowRate : ℕ) →
                                (separatedScaleCount : ℕ → ℕ) →
                                  (∀ (size : ℕ), separatedScaleCount size ≤ size.log2) →
                                    (ℕ → ℕ) →
                                      ℕ →
                                        (entropyDenominator : ℕ) →
                                          0 < entropyDenominator →
                                            (largeOrderExponent : ℕ) →
                                              0 < largeOrderExponent →
                                                (∀ (size : ℕ),
                                                    2 ^ largeOrderExponent ≤ size →
                                                      largeOrderExponent * (size.log2 + 1) ≤
                                                        (largeOrderExponent + 1) * separatedScaleCount size) →
                                                  (dischargeScale * (threshold * windowOrder - 2 * (windowOrder - 1)) +
                                                            windowOrder) *
                                                          (largeOrderExponent + 1) *
                                                        threshold <
                                                      2 * windowRate * largeOrderExponent →
                                                    4 *
                                                            (((dischargeScale *
                                                                      (threshold * windowOrder -
                                                                        2 * (windowOrder - 1)) +
                                                                    windowOrder) *
                                                                  (largeOrderExponent + 1) +
                                                                2 * windowRate * largeOrderExponent * dischargeScale) *
                                                              surplusScale) *
                                                          (((dischargeScale *
                                                                    (threshold * windowOrder - 2 * (windowOrder - 1)) +
                                                                  windowOrder) *
                                                                (largeOrderExponent + 1) +
                                                              2 * windowRate * largeOrderExponent * dischargeScale) *
                                                            surplusScale) ≤
                                                        2 ^ largeOrderExponent →
                                                      (coldSignature : Graph.ColdCorridor.DeclaredSignature) →
                                                        coldSignature.windowOrder = windowOrder →
                                                          (bridgeMassFactor : ℕ) →
                                                            threshold + 2 + dischargeScale ≤
                                                                bridgeMassFactor * dischargeScale →
                                                              Graph.Strategy.Spine.Data
```

#### `Hypostructure.Graph.Strategy.Spine.Data.netChargeCoefficient`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.netChargeRate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data),
  (self.dischargeScale * (self.threshold * self.windowOrder - 2 * (self.windowOrder - 1)) + self.windowOrder) *
        (self.largeOrderExponent + 1) *
      self.threshold <
    2 * self.windowRate * self.largeOrderExponent
```

#### `Hypostructure.Graph.Strategy.Spine.Data.quadrilateralAccepted`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.LengthOK 4
```

#### `Hypostructure.Graph.Strategy.Spine.Data.rankDefect`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleCount_le`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (size : ℕ), self.separatedScaleCount size ≤ size.log2
```

#### `Hypostructure.Graph.Strategy.Spine.Data.separatedScaleReach`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data) (size : ℕ),
  2 ^ self.largeOrderExponent ≤ size →
    self.largeOrderExponent * (size.log2 + 1) ≤ (self.largeOrderExponent + 1) * self.separatedScaleCount size
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

#### `Hypostructure.Graph.Strategy.Spine.Data.surplusThreshold_sublinear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (size : ℕ),
  2 ^ data.largeOrderExponent ≤ size →
    (data.netChargeCoefficient * (data.largeOrderExponent + 1) +
          2 * data.windowRate * data.largeOrderExponent * data.dischargeScale) *
        data.surplusThreshold size <
      (2 * data.windowRate * data.largeOrderExponent -
          data.netChargeCoefficient * (data.largeOrderExponent + 1) * data.threshold) *
        size
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

#### `Hypostructure.Graph.Strategy.Spine.DeterminationCertificate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (packing : Finset (Finset object.Vertex)) → Graph.Strategy.Spine.remainderQuotient data object packing → Prop
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

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.Input`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → Graph.Strategy.Spine.Data → Type (max (u + 1) v)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.canonicalBlockerRoute`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldSameInterfaceTable`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.largeBudgetResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.largeOrderResidual`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.negativeSupport`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Burden`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Census`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Closed`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Descent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Free`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.selection`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.smallOrderResidual`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFiveCompression`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFiveTraceLevel`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourNoPeel`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAExitFourPeel`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAPeeledCharge`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeASaturatedReceiver`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBBridgeMass`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBDisjointAssignment`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.windowPackageCollided`

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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (branchDependence contextUniversal atomCompression delocalizedSupport :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has branchDependence known] →
                    [Core.Residual.FactKeys.Has contextUniversal known] →
                      (∀ (a : contextUniversal.At current) (packing : Finset (Finset current.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                            ∀ (quotient : Graph.Strategy.Spine.remainderQuotient data current.object packing),
                              Graph.Strategy.Spine.TargetCompleteAt data quotient) →
                        (∀ (a : branchDependence.At current),
                            ∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                ∃ quotient,
                                  Graph.Strategy.Spine.DeterminationCertificate data current.object packing quotient ∧
                                    ∀ smaller ⊂ quotient.support,
                                      ∀ (narrower : Graph.Strategy.Spine.remainderQuotient data current.object packing),
                                        narrower.support = smaller →
                                          ¬Graph.Strategy.Spine.DeterminationCertificate data current.object packing
                                              narrower) →
                          ((∃ packing,
                                Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                  ∃ quotient,
                                    Graph.Strategy.Spine.DeterminationCertificate data current.object packing quotient ∧
                                      Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                        quotient.support ⊆ Graph.FiniteObject.remainderSupport current.object packing) →
                              atomCompression.At current) →
                            ((∃ packing,
                                  Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                    ∃ quotient,
                                      Graph.Strategy.Spine.DeterminationCertificate data current.object packing
                                          quotient ∧
                                        Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                          ¬quotient.support ⊆
                                                Graph.FiniteObject.remainderSupport current.object packing ∧
                                            Graph.FiniteObject.remainderSupport current.object packing ⊂
                                              Graph.Strategy.Spine.delocalizationSupport data current.object packing
                                                quotient) →
                                delocalizedSupport.At current) →
                              atomCompression ∉ known →
                                delocalizedSupport ∉ known →
                                  Core.Strategy.Decision atomCompression delocalizedSupport previous
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
                (typeBDisjointAssignment typeBOverlapObstruction :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                            Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                              Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                  data.dischargeScale →
                                0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
                                  Nonempty
                                    (Graph.TypeBRefinedSupport.RefinedSupportAssignment current.object data.threshold
                                      data.dischargeScale piece)) →
                      typeBDisjointAssignment.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                    Nonempty
                                      (Graph.TypeBRefinedSupport.OverlapObstruction current.object data.threshold
                                        data.dischargeScale piece)) →
                        typeBOverlapObstruction.At current) →
                      typeBDisjointAssignment ∉ known →
                        typeBOverlapObstruction ∉ known →
                          Core.Strategy.Decision typeBDisjointAssignment typeBOverlapObstruction previous
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
                (barrierCap barrierOverflow :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((2 ^
                            (data.windowRate *
                                data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                              Graph.FiniteObject.windowPackingNumber current.object data.windowOrder) ≤
                          Graph.skeletonBudget current.object ∧
                        ∀ (family : Finset ℕ),
                          Graph.FiniteObject.edgeCount current.object ∈ family →
                            Graph.skeletonBudget current.object ≤
                              Graph.variableEdgeBudget (Graph.FiniteObject.vertexCount current.object) family) →
                      barrierCap.At current) →
                    (Graph.skeletonBudget current.object <
                          2 ^
                            (data.windowRate *
                                data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                              Graph.FiniteObject.windowPackingNumber current.object data.windowOrder) →
                        barrierOverflow.At current) →
                      barrierCap ∉ known →
                        barrierOverflow ∉ known → Core.Strategy.Decision barrierCap barrierOverflow previous
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (remainderNormalized surplusAtOrBelow boundaryDemand stubSupply :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            remainderNormalized ≠ surplusAtOrBelow →
              boundaryDemand ≠ remainderNormalized →
                stubSupply ≠ remainderNormalized →
                  boundaryDemand ≠ stubSupply →
                    (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                        (a : surplusAtOrBelow.At input),
                        Graph.FiniteObject.degreeSurplus input.object data.threshold ≤
                          data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                          (∀ (packing : Finset (Finset input.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                                Graph.FiniteObject.positiveDeficiency input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) data.threshold ≤
                                    Graph.FiniteObject.boundaryIncidence input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) ∧
                                  Graph.FiniteObject.boundaryIncidence input.object
                                        (Graph.FiniteObject.remainderSupport input.object packing) +
                                      2 * (data.windowOrder - 1) * packing.card ≤
                                    data.threshold * (data.windowOrder * packing.card) +
                                      Graph.FiniteObject.ambientSurplus input.object
                                        (Graph.FiniteObject.windowSupport packing) data.threshold) →
                            boundaryDemand.At input) →
                        ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                            (∀ (packing : Finset (Finset input.object.Vertex)),
                                Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                                  Graph.FiniteObject.positiveDeficiency input.object
                                        (Graph.FiniteObject.remainderSupport input.object packing) data.threshold +
                                      2 * (data.windowOrder - 1) * packing.card ≤
                                    data.threshold * (data.windowOrder * packing.card) +
                                      data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                              stubSupply.At input) →
                          Core.Strategy.AtomicStrategy
                            (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (curvatureRankDrop branchDependence :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            curvatureRankDrop ≠ branchDependence →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : curvatureRankDrop.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing <
                          Graph.Strategy.Spine.remainderWedgeSupply input.object packing -
                            data.rankDefect (Graph.Strategy.Spine.remainderWedgeSupply input.object packing) ∧
                        ∃ test determiners,
                          Core.TargetRank.Dependence
                            (Graph.Strategy.Spine.remainderQuotientSystem data input.object packing) test determiners) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          ∃ quotient,
                            Graph.Strategy.Spine.DeterminationCertificate data input.object packing quotient ∧
                              ∀ smaller ⊂ quotient.support,
                                ∀ (narrower : Graph.Strategy.Spine.remainderQuotient data input.object packing),
                                  narrower.support = smaller →
                                    ¬Graph.Strategy.Spine.DeterminationCertificate data input.object packing narrower) →
                      branchDependence.At input) →
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (typeBBridgeMass :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                ((∀ (packing : Finset (Finset input.object.Vertex)),
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                        ∀ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                          Graph.SupportComponents.Connected.ConnectedOn input.object piece →
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale →
                              0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold →
                                (∀ centre ∈ piece,
                                    Graph.IsHighCentre input.object data.threshold centre →
                                      ∀ (envelope : Finset input.object.Vertex),
                                        Graph.TypeBEnvelopeCharge.envelopeNegativePart input.object data.threshold
                                            data.dischargeScale envelope centre ≤
                                          data.bridgeMassFactor * data.dischargeScale *
                                            (Graph.FiniteObject.degree input.object centre - data.threshold)) ∧
                                  (Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object piece data.threshold
                                      data.dischargeScale →
                                    piece.card +
                                        data.dischargeScale *
                                          Graph.FiniteObject.ambientSurplus input.object piece data.threshold ≤
                                      data.dischargeScale *
                                          Graph.FiniteObject.positiveDeficiency input.object piece data.threshold +
                                        data.bridgeMassFactor * data.dischargeScale *
                                          Graph.FiniteObject.ambientSurplus input.object piece data.threshold)) ∧
                    (∀ (packing : Finset (Finset input.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                          ∀
                            (route8 :
                              Finset
                                (Graph.SupportComponents.Connected.Component input.object
                                  (Graph.FiniteObject.remainderSupport input.object packing))),
                            (∀ piece ∈ route8,
                                Graph.FiniteObject.ambientSurplus input.object
                                    (Graph.FiniteObject.pieceSupport input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) piece)
                                    data.threshold =
                                  0) →
                              (∀
                                  piece ∈
                                    Graph.FiniteObject.canonicalPieces input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing),
                                  piece ∉ route8 →
                                    Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                                      (Graph.FiniteObject.pieceSupport input.object
                                        (Graph.FiniteObject.remainderSupport input.object packing) piece)
                                      data.threshold data.dischargeScale) →
                                ∑
                                    piece ∈
                                      Graph.FiniteObject.canonicalPieces input.object
                                        (Graph.FiniteObject.remainderSupport input.object packing),
                                    ((Graph.FiniteObject.pieceSupport input.object
                                            (Graph.FiniteObject.remainderSupport input.object packing) piece).card +
                                        data.dischargeScale *
                                          Graph.FiniteObject.ambientSurplus input.object
                                            (Graph.FiniteObject.pieceSupport input.object
                                              (Graph.FiniteObject.remainderSupport input.object packing) piece)
                                            data.threshold -
                                      data.dischargeScale *
                                        Graph.FiniteObject.positiveDeficiency input.object
                                          (Graph.FiniteObject.pieceSupport input.object
                                            (Graph.FiniteObject.remainderSupport input.object packing) piece)
                                          data.threshold) ≤
                                  Graph.TypeBEnvelopeCharge.route8Deficit input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                                      data.dischargeScale route8 +
                                    data.bridgeMassFactor * data.dischargeScale *
                                      Graph.FiniteObject.degreeSurplus input.object data.threshold) ∧
                      ∀ (packing : Finset (Finset input.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                          ∀ (ordinary grouped : Finset input.object.Vertex),
                            ordinary ⊆ Graph.FiniteObject.remainderSupport input.object packing →
                              grouped ⊆ Graph.FiniteObject.remainderSupport input.object packing →
                                ∀
                                  (ordinaryRoute8 :
                                    Finset (Graph.SupportComponents.Connected.Component input.object ordinary))
                                  (groupedRoute8 :
                                    Finset (Graph.SupportComponents.Connected.Component input.object grouped)),
                                  (∀ piece ∈ ordinaryRoute8,
                                      Graph.FiniteObject.ambientSurplus input.object
                                          (Graph.FiniteObject.pieceSupport input.object ordinary piece) data.threshold =
                                        0) →
                                    (∀ piece ∈ groupedRoute8,
                                        Graph.FiniteObject.ambientSurplus input.object
                                            (Graph.FiniteObject.pieceSupport input.object grouped piece)
                                            data.threshold =
                                          0) →
                                      (∀ piece ∈ Graph.FiniteObject.canonicalPieces input.object ordinary,
                                          piece ∉ ordinaryRoute8 →
                                            Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                                              (Graph.FiniteObject.pieceSupport input.object ordinary piece)
                                              data.threshold data.dischargeScale) →
                                        (∀ piece ∈ Graph.FiniteObject.canonicalPieces input.object grouped,
                                            piece ∉ groupedRoute8 →
                                              Graph.TypeBEnvelopeCharge.BridgeResidualComponentAt input.object
                                                (Graph.FiniteObject.pieceSupport input.object grouped piece)
                                                data.threshold data.dischargeScale) →
                                          ∑ piece ∈ Graph.FiniteObject.canonicalPieces input.object ordinary,
                                                ((Graph.FiniteObject.pieceSupport input.object ordinary piece).card +
                                                    data.dischargeScale *
                                                      Graph.FiniteObject.ambientSurplus input.object
                                                        (Graph.FiniteObject.pieceSupport input.object ordinary piece)
                                                        data.threshold -
                                                  data.dischargeScale *
                                                    Graph.FiniteObject.positiveDeficiency input.object
                                                      (Graph.FiniteObject.pieceSupport input.object ordinary piece)
                                                      data.threshold) +
                                              ∑ piece ∈ Graph.FiniteObject.canonicalPieces input.object grouped,
                                                ((Graph.FiniteObject.pieceSupport input.object grouped piece).card +
                                                    data.dischargeScale *
                                                      Graph.FiniteObject.ambientSurplus input.object
                                                        (Graph.FiniteObject.pieceSupport input.object grouped piece)
                                                        data.threshold -
                                                  data.dischargeScale *
                                                    Graph.FiniteObject.positiveDeficiency input.object
                                                      (Graph.FiniteObject.pieceSupport input.object grouped piece)
                                                      data.threshold) ≤
                                            Graph.TypeBEnvelopeCharge.route8Deficit input.object ordinary data.threshold
                                                  data.dischargeScale ordinaryRoute8 +
                                                Graph.TypeBEnvelopeCharge.route8Deficit input.object grouped
                                                  data.threshold data.dischargeScale groupedRoute8 +
                                              2 *
                                                (data.bridgeMassFactor * data.dischargeScale *
                                                  Graph.FiniteObject.degreeSurplus input.object data.threshold)) →
                  typeBBridgeMass.At input) →
              Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (contextDefect contextUniversal :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∃ packing,
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                          ∃ quotient left right,
                            Graph.Strategy.Spine.Identified quotient left right ∧
                              (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
                                Graph.Response.TargetDefect (Graph.HasCycleWithLength data.LengthOK) left right)) →
                      contextDefect.At current) →
                    ((∀ (packing : Finset (Finset current.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                            ∀ (quotient : Graph.Strategy.Spine.remainderQuotient data current.object packing),
                              Graph.Strategy.Spine.TargetCompleteAt data quotient) →
                        contextUniversal.At current) →
                      contextDefect ∉ known →
                        contextUniversal ∉ known → Core.Strategy.Decision contextDefect contextUniversal previous
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (curvatureTargetRank curvatureRankDrop curvatureFullRank :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has curvatureTargetRank known] →
                    (∀ (a : curvatureTargetRank.At current) (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          ∃ independent ⊆ Graph.Strategy.Spine.remainderCurvatureTests current.object packing,
                            (Graph.Strategy.Spine.remainderQuotientSystem data current.object packing).Survives
                                ↑independent ∧
                              independent.card =
                                  Graph.Strategy.Spine.remainderCurvatureTargetRank data current.object packing ∧
                                ∀ test ∈ Graph.Strategy.Spine.remainderCurvatureTests current.object packing,
                                  test ∉ independent →
                                    ∃ determiners ⊆ ↑independent,
                                      Core.TargetRank.Dependence
                                        (Graph.Strategy.Spine.remainderQuotientSystem data current.object packing) test
                                        determiners) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              Graph.Strategy.Spine.remainderCurvatureTargetRank data current.object packing <
                                  Graph.Strategy.Spine.remainderWedgeSupply current.object packing -
                                    data.rankDefect (Graph.Strategy.Spine.remainderWedgeSupply current.object packing) ∧
                                ∃ test determiners,
                                  Core.TargetRank.Dependence
                                    (Graph.Strategy.Spine.remainderQuotientSystem data current.object packing) test
                                    determiners) →
                          curvatureRankDrop.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                Graph.Strategy.Spine.remainderWedgeSupply current.object packing -
                                    data.rankDefect (Graph.Strategy.Spine.remainderWedgeSupply current.object packing) ≤
                                  Graph.Strategy.Spine.remainderCurvatureTargetRank data current.object packing) →
                            curvatureFullRank.At current) →
                          curvatureRankDrop ∉ known →
                            curvatureFullRank ∉ known →
                              Core.Strategy.Decision curvatureRankDrop curvatureFullRank previous
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
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (curvatureDemandFloor curvatureTargetRank :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            curvatureDemandFloor ≠ curvatureTargetRank →
              ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                  (∀ (packing : Finset (Finset input.object.Vertex)),
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                        ∃ independent ⊆ Graph.Strategy.Spine.remainderCurvatureTests input.object packing,
                          (Graph.Strategy.Spine.remainderQuotientSystem data input.object packing).Survives
                              ↑independent ∧
                            independent.card =
                                Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing ∧
                              ∀ test ∈ Graph.Strategy.Spine.remainderCurvatureTests input.object packing,
                                test ∉ independent →
                                  ∃ determiners ⊆ ↑independent,
                                    Core.TargetRank.Dependence
                                      (Graph.Strategy.Spine.remainderQuotientSystem data input.object packing) test
                                      determiners) →
                    curvatureTargetRank.At input) →
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
          (highCentreNormalForm typeBDegreeFourProfile :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            highCentreNormalForm ≠ typeBDegreeFourProfile →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : highCentreNormalForm.At input) (centre : input.object.Vertex),
                  Graph.IsHighCentre input.object data.threshold centre →
                    Graph.NormalForm input.object data.threshold centre) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∀ (centre : input.object.Vertex),
                        Graph.FiniteObject.degree input.object centre = data.threshold + 1 →
                          ((∃ left right, Graph.FanCompatible input.object centre left right) ∨
                              data.threshold - 1 ≤ (Graph.triangularEndpoints input.object centre).card) ∧
                            Graph.FiniteObject.degree input.object centre - data.threshold = 1 ∧
                              ∀ (envelope : Finset input.object.Vertex),
                                Graph.TypeBFanIncidence.closedCount input.object data.threshold envelope centre ≤
                                    data.threshold + 1 ∧
                                  Graph.TypeBFanIncidence.scaledDeficit input.object data.threshold data.dischargeScale
                                      envelope centre =
                                    ↑data.dischargeScale *
                                          ↑(Graph.TypeBFanIncidence.closedCount input.object data.threshold envelope
                                              centre) -
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (noProperBaseline tightEndpoint slackIndependent :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            tightEndpoint ≠ noProperBaseline →
              slackIndependent ≠ noProperBaseline →
                tightEndpoint ≠ slackIndependent →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : noProperBaseline.At input) (subgraph : Graph.ProperSubgraph input.object),
                      ¬Graph.MinimumDegreeAtLeast data.threshold subgraph.value) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                        (∀ (dart : input.object.graph.Dart),
                            Graph.FiniteObject.degree input.object dart.toProd.1 = data.threshold ∨
                              Graph.FiniteObject.degree input.object dart.toProd.2 = data.threshold) →
                          tightEndpoint.At input) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                          (∀ (left right : input.object.Vertex),
                              data.threshold < Graph.FiniteObject.degree input.object left →
                                data.threshold < Graph.FiniteObject.degree input.object right →
                                  ¬input.object.graph.Adj left right) →
                            slackIndependent.At input) →
                        Core.Strategy.AtomicStrategy
                          (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
            {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
              (previous :
                  Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    current known) →
                (delocalizedSupport properDelocalization globalDelocalization :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has delocalizedSupport known] →
                    (∀ (a : delocalizedSupport.At current),
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            ∃ quotient,
                              Graph.Strategy.Spine.DeterminationCertificate data current.object packing quotient ∧
                                Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                  ¬quotient.support ⊆ Graph.FiniteObject.remainderSupport current.object packing ∧
                                    Graph.FiniteObject.remainderSupport current.object packing ⊂
                                      Graph.Strategy.Spine.delocalizationSupport data current.object packing quotient) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              ∃ quotient,
                                Graph.Strategy.Spine.DeterminationCertificate data current.object packing quotient ∧
                                  Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                    ¬quotient.support ⊆ Graph.FiniteObject.remainderSupport current.object packing ∧
                                      ∃ vertex,
                                        vertex ∉
                                          Graph.Strategy.Spine.delocalizationSupport data current.object packing
                                            quotient) →
                          properDelocalization.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                ∃ quotient,
                                  Graph.Strategy.Spine.DeterminationCertificate data current.object packing quotient ∧
                                    Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                      ¬quotient.support ⊆ Graph.FiniteObject.remainderSupport current.object packing ∧
                                        ∀ (vertex : current.object.Vertex),
                                          vertex ∈
                                            Graph.Strategy.Spine.delocalizationSupport data current.object packing
                                              quotient) →
                            globalDelocalization.At current) →
                          properDelocalization ∉ known →
                            globalDelocalization ∉ known →
                              Core.Strategy.Decision properDelocalization globalDelocalization previous
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (barrierCap surplusAtOrBelow densityCap :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            barrierCap ≠ surplusAtOrBelow →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : barrierCap.At input),
                  2 ^
                      (data.windowRate * data.separatedScaleCount (Graph.FiniteObject.vertexCount input.object) *
                        Graph.FiniteObject.windowPackingNumber input.object data.windowOrder) ≤
                    Graph.skeletonBudget input.object) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : surplusAtOrBelow.At input),
                    Graph.FiniteObject.degreeSurplus input.object data.threshold ≤
                      data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      2 *
                            (data.windowRate * data.separatedScaleCount (Graph.FiniteObject.vertexCount input.object) *
                              Graph.FiniteObject.windowPackingNumber input.object data.windowOrder) ≤
                          (Graph.dyadicScaleCount input.object + 1) *
                            (data.threshold * Graph.FiniteObject.vertexCount input.object +
                              data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                        densityCap.At input) →
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
                (typeBDirectCycle typeBDirectCycleFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∃ packing,
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                          ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                            Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                              Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                  data.dischargeScale ∧
                                0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                  ∃ centre ∈ piece,
                                    Graph.IsHighCentre current.object data.threshold centre ∧
                                      Graph.TypeBDirectCycle.DirectCycleConfiguration current.object data.windowOrder
                                        data.LengthOK packing centre) →
                      typeBDirectCycle.At current) →
                    ((∀ (packing : Finset (Finset current.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                            ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale →
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
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
                      data.windowOrder data.threshold (Graph.FiniteObject.remainderSupport input.object packing).card) →
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
                (fanCertificateMarked fanCertificateResidual :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                            Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                              Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                  data.dischargeScale →
                                0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
                                  ∀ centre ∈ piece,
                                    Graph.IsHighCentre current.object data.threshold centre →
                                      Nonempty (Graph.FanCertificateLabelling current.object data.windowOrder centre)) →
                      fanCertificateMarked.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
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
                      Graph.Strategy.Spine.remainderWedgeSupply input.object packing -
                          data.rankDefect (Graph.Strategy.Spine.remainderWedgeSupply input.object packing) ≤
                        Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (packing : Finset (Finset input.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                            data.curvatureCost *
                                (data.threshold * (Graph.FiniteObject.remainderSupport input.object packing).card +
                                  2 * (2 * (data.windowOrder - 1) * packing.card)) ≤
                              data.curvatureCost *
                                  (Graph.Strategy.Spine.remainderCurvatureTargetRank data input.object packing +
                                    data.rankDefect (Graph.Strategy.Spine.remainderWedgeSupply input.object packing)) +
                                data.curvatureCost *
                                  (2 *
                                    (data.threshold * (data.windowOrder * packing.card) +
                                      Graph.FiniteObject.ambientSurplus input.object
                                        (Graph.FiniteObject.windowSupport packing) data.threshold))) →
                        forcedCurvatureCost.At input) →
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
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (globalDelocalization repairIdentity globalBarrier :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            repairIdentity ≠ globalDelocalization →
              globalBarrier ≠ globalDelocalization →
                repairIdentity ≠ globalBarrier →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : globalDelocalization.At input),
                      ∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          ∃ quotient,
                            Graph.Strategy.Spine.DeterminationCertificate data input.object packing quotient ∧
                              Graph.Strategy.Spine.TargetCompleteAt data quotient ∧
                                ¬quotient.support ⊆ Graph.FiniteObject.remainderSupport input.object packing ∧
                                  ∀ (vertex : input.object.Vertex),
                                    vertex ∈
                                      Graph.Strategy.Spine.delocalizationSupport data input.object packing quotient) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                        (∀ (component : Graph.OneThreeRepair.Component),
                            ↑component.internal.card =
                              ↑component.boundary.card - 2 + 2 * ↑component.cycleRank - ↑component.surplus) →
                          repairIdentity.At input) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                          (∃ packing,
                              Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                                ∃ quotient,
                                  Graph.Strategy.Spine.DeterminationCertificate data input.object packing quotient ∧
                                    (Graph.Strategy.InterfaceReplacement.ReplacementSupport
                                        (Graph.MinimumDegreeAtLeast data.threshold)
                                        (Graph.HasCycleWithLength data.LengthOK) input.object quotient.support ∨
                                      ∃ representative,
                                        representative.LexicographicallySmaller input.object ∧
                                          Graph.MinimumDegreeAtLeast data.threshold representative ∧
                                            (Graph.HasCycleWithLength data.LengthOK representative →
                                              Graph.HasCycleWithLength data.LengthOK input.object))) →
                            globalBarrier.At input) →
                        Core.Strategy.AtomicStrategy
                          (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
                            ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale ∧
                                  0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                      ∃ centre ∈ piece,
                                        data.threshold + 1 < Graph.FiniteObject.degree current.object centre) →
                          typeBHeavyCentre.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale →
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
                                        ∀ centre ∈ piece,
                                          data.threshold < Graph.FiniteObject.degree current.object centre →
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
          (highCentreNormalForm typeBLocalDichotomy :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            highCentreNormalForm ≠ typeBLocalDichotomy →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : highCentreNormalForm.At input) (centre : input.object.Vertex),
                  Graph.IsHighCentre input.object data.threshold centre →
                    Graph.NormalForm input.object data.threshold centre) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∀ (centre : input.object.Vertex),
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
                          (a : fanCertificateMarked.At input) (packing : Finset (Finset input.object.Vertex)),
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                            ∀ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn input.object piece →
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale →
                                  0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold →
                                    ∀ centre ∈ piece,
                                      Graph.IsHighCentre input.object data.threshold centre →
                                        Nonempty (Graph.FanCertificateLabelling input.object data.windowOrder centre)) →
                        ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                            (∀ (packing : Finset (Finset input.object.Vertex)),
                                Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                                  ∀ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn input.object piece →
                                      Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                          data.dischargeScale →
                                        0 < Graph.FiniteObject.ambientSurplus input.object piece data.threshold →
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (T : Core.Target (Graph.Strategy.Spine.problem BranchState Presentation presentation data)) →
            Core.TargetInvariant
                (Graph.isomorphismEquivalenceWithPresentation (Graph.MinimumDegreeAtLeast data.threshold) BranchState
                  Presentation presentation ⋯)
                T.Predicate →
              (selection uncompressible :
                  Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                selection ≠ uncompressible →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : selection.At input), ¬T.Predicate input.object) →
                    (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                        (a : selection.At input) (smaller : Graph.FiniteObject),
                        (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller
                            input.object →
                          Graph.MinimumDegreeAtLeast data.threshold smaller → T.Predicate smaller) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                          (∀ (support : Finset input.object.Vertex),
                              ¬Graph.Strategy.InterfaceReplacement.CompressibleSupport
                                  (Graph.MinimumDegreeAtLeast data.threshold) T.Predicate input.object support) →
                            uncompressible.At input) →
                        Core.Strategy.AtomicStrategy
                          (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (localAlgebra :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                ((Graph.WindowCurvature.legalCodeList data.windowOrder).length =
                      (Graph.WindowCurvature.Labels data.windowOrder).card ∧
                    ∀ (source middle target : Graph.WindowCurvature.Label data.windowOrder),
                      Graph.WindowCurvature.curvatureTwo source middle target = true ↔
                        Graph.WindowCurvature.Safe 1 source middle ∧
                          Graph.WindowCurvature.Safe 1 middle target ∧ ¬Graph.WindowCurvature.Safe 2 source target) →
                  localAlgebra.At input) →
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
                        ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                          Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                              data.dischargeScale) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            (∀ (window : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                  ∃ member ∈ packing, ¬Disjoint window member) ∧
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale) →
                        negativeSupport.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
                        ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                          Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                              data.dischargeScale) →
                  netChargeLocalization.At input) →
              Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.netDeficiencyCapRow`

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
          (maximalPacking stubSupply densityCap largeOrderResidual netDeficiencyCap :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            maximalPacking ≠ stubSupply →
              maximalPacking ≠ densityCap →
                maximalPacking ≠ largeOrderResidual →
                  stubSupply ≠ densityCap →
                    stubSupply ≠ largeOrderResidual →
                      densityCap ≠ largeOrderResidual →
                        (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                            (a : maximalPacking.At input),
                            ∃ packing,
                              Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                                packing.card = Graph.FiniteObject.windowPackingNumber input.object data.windowOrder ∧
                                  ∀ (window : Finset input.object.Vertex),
                                    Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) →
                          (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                              (a : stubSupply.At input) (packing : Finset (Finset input.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                                Graph.FiniteObject.positiveDeficiency input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) data.threshold +
                                    2 * (data.windowOrder - 1) * packing.card ≤
                                  data.threshold * (data.windowOrder * packing.card) +
                                    data.surplusThreshold (Graph.FiniteObject.vertexCount input.object)) →
                            (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                                (a : densityCap.At input),
                                2 *
                                    (data.windowRate *
                                        data.separatedScaleCount (Graph.FiniteObject.vertexCount input.object) *
                                      Graph.FiniteObject.windowPackingNumber input.object data.windowOrder) ≤
                                  (Graph.dyadicScaleCount input.object + 1) *
                                    (data.threshold * Graph.FiniteObject.vertexCount input.object +
                                      data.surplusThreshold (Graph.FiniteObject.vertexCount input.object))) →
                              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                                  (a : largeOrderResidual.At input),
                                  2 ^ data.largeOrderExponent ≤ Graph.FiniteObject.vertexCount input.object) →
                                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                                    (∃ packing,
                                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                                          (∀ (window : Finset input.object.Vertex),
                                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                                            Graph.FiniteObject.NegativeNetCharge input.object
                                              (Graph.FiniteObject.remainderSupport input.object packing) data.threshold
                                              data.dischargeScale) →
                                      netDeficiencyCap.At input) →
                                  Core.Strategy.AtomicStrategy
                                    (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection noProperBaseline :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ noProperBaseline →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : selection.At input) (smaller : Graph.FiniteObject),
                    smaller.LexicographicallySmaller input.object →
                      Graph.MinimumDegreeAtLeast data.threshold smaller →
                        Graph.HasCycleWithLength data.LengthOK smaller) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (subgraph : Graph.ProperSubgraph input.object),
                          ¬Graph.MinimumDegreeAtLeast data.threshold subgraph.value) →
                        noProperBaseline.At input) →
                    Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.not_branchDCertificate`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data}
  [Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)]
  (object : Graph.FiniteObject),
  Graph.MinimumDegreeAtLeast data.threshold object →
    ∀ (state : BranchState object),
      ¬Graph.HasCycleWithLength data.LengthOK object →
        (∀ (smaller : Graph.FiniteObject),
            (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
              Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
          (∃ packing,
              object.IsWindowPacking data.windowOrder packing ∧
                ∃ quotient, Graph.Strategy.Spine.DeterminationCertificate data object packing quotient) →
            False
```

#### `Hypostructure.Graph.Strategy.Spine.not_contextDefect`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} (object : Graph.FiniteObject),
  (∃ packing,
      object.IsWindowPacking data.windowOrder packing ∧
        ∃ quotient left right,
          Graph.Strategy.Spine.Identified quotient left right ∧
            (left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile ∨
              Graph.Response.TargetDefect (Graph.HasCycleWithLength data.LengthOK) left right)) →
    False
```

#### `Hypostructure.Graph.Strategy.Spine.not_determinationCertificate`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data}
  [Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)]
  {object : Graph.FiniteObject},
  Graph.MinimumDegreeAtLeast data.threshold object →
    ∀ (state : BranchState object),
      ¬Graph.HasCycleWithLength data.LengthOK object →
        (∀ (smaller : Graph.FiniteObject),
            (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
              Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
          ∀ {packing : Finset (Finset object.Vertex)}
            {quotient : Graph.Strategy.Spine.remainderQuotient data object packing},
            Graph.Strategy.Spine.DeterminationCertificate data object packing quotient → False
```

#### `Hypostructure.Graph.Strategy.Spine.not_globalBarrierReading`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data}
  [Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)]
  {object : Graph.FiniteObject},
  Graph.MinimumDegreeAtLeast data.threshold object →
    ∀ (state : BranchState object),
      ¬Graph.HasCycleWithLength data.LengthOK object →
        (∀ (smaller : Graph.FiniteObject),
            (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
              Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
          ∀ {support : Finset object.Vertex},
            (Graph.Strategy.InterfaceReplacement.ReplacementSupport (Graph.MinimumDegreeAtLeast data.threshold)
                  (Graph.HasCycleWithLength data.LengthOK) object support ∨
                ∃ representative,
                  representative.LexicographicallySmaller object ∧
                    Graph.MinimumDegreeAtLeast data.threshold representative ∧
                      (Graph.HasCycleWithLength data.LengthOK representative →
                        Graph.HasCycleWithLength data.LengthOK object)) →
              False
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection maximalPacking :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ maximalPacking →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (0 < Graph.FiniteObject.windowPackingNumber input.object data.windowOrder ∧
                        ∃ packing,
                          Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                            packing.card = Graph.FiniteObject.windowPackingNumber input.object data.windowOrder ∧
                              ∀ (support : Finset input.object.Vertex),
                                Graph.FiniteObject.InducesWindow input.object data.windowOrder support →
                                  ∃ member ∈ packing, ¬Disjoint support member) →
                      maximalPacking.At input) →
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

#### `Hypostructure.Graph.Strategy.Spine.orderThresholdDichotomy`

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
                (largeOrderResidual smallOrderResidual :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  (2 ^ data.largeOrderExponent ≤ Graph.FiniteObject.vertexCount current.object →
                      largeOrderResidual.At current) →
                    (Graph.FiniteObject.vertexCount current.object < 2 ^ data.largeOrderExponent →
                        smallOrderResidual.At current) →
                      largeOrderResidual ∉ known →
                        smallOrderResidual ∉ known →
                          Core.Strategy.Decision largeOrderResidual smallOrderResidual previous
```

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
                            (Graph.FiniteObject.remainderSupport current.object packing).card) →
                      remainderEntropyHigh.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            Graph.BelowEntropyRate (Graph.FiniteObject.vertexCount current.object)
                              data.entropyDenominator data.windowOrder data.threshold
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection remainderNormalized :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ remainderNormalized →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∀ (packing : Finset (Finset input.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) →
                            ∀ support ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                              ¬Graph.FiniteObject.InducesWindow input.object data.windowOrder support ∧
                                ¬Graph.MinimumDegreeAtLeast data.threshold
                                    (Graph.FiniteObject.induce input.object support)) →
                      remainderNormalized.At input) →
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

#### `Hypostructure.Graph.Strategy.Spine.remainderQuotientSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    (packing : Finset (Finset object.Vertex)) →
      Core.TargetRank.QuotientSystem (object.InternalWedge (object.remainderSupport packing))
        (Graph.Strategy.Spine.remainderCurvatureTests object packing)
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection returnAvoidance :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ returnAvoidance →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∀ (dart : input.object.graph.Dart),
                        Disjoint (Graph.returnLengthSet input.object dart) (Graph.shiftedAcceptedSet data.LengthOK)) →
                      returnAvoidance.At input) →
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
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃
                                              outside ∈
                                                Graph.VisibleEntry.completionPorts current.object piece receiver,
                                              data.dischargeScale ≤
                                                (Graph.VisibleEntry.visibleLoadsAt current.object piece data.threshold
                                                    receiver outside).card) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃
                                                outside ∈
                                                  Graph.VisibleEntry.completionPorts current.object piece receiver,
                                                ∃ return', Graph.ShiftedCycleLength data.LengthOK return'.path.length) →
                          typeAExitOneReturn.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) →
                                  ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                      Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                          data.dischargeScale →
                                        Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
                                          ∀ (receiver : current.object.Vertex),
                                            Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver →
                                              Graph.FiniteObject.Saturated current.object piece data.threshold
                                                  data.dischargeScale receiver →
                                                ∀
                                                  outside ∈
                                                    Graph.VisibleEntry.completionPorts current.object piece receiver,
                                                  ∀
                                                    (return' :
                                                      Graph.VisibleEntry.AnchoredReturn current.object receiver
                                                        outside),
                                                    ¬Graph.ShiftedCycleLength data.LengthOK return'.path.length) →
                            typeAExitOneFree.At current) →
                          typeAExitOneReturn ∉ known →
                            typeAExitOneFree ∉ known →
                              Core.Strategy.Decision typeAExitOneReturn typeAExitOneFree previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAExitSevenDichotomy`

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
                (selection uncompressible typeASaturatedExitEntry typeAExitSevenHandoff typeAExitSevenFree :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has selection known] →
                    [Core.Residual.FactKeys.Has uncompressible known] →
                      [Core.Residual.FactKeys.Has typeASaturatedExitEntry known] →
                        (∀ (a : selection.At current), ¬Graph.HasCycleWithLength data.LengthOK current.object) →
                          (∀ (a : uncompressible.At current) (support : Finset current.object.Vertex),
                              Graph.Strategy.Spine.handoffUncompressible data current.object support) →
                            (∀ (a : typeASaturatedExitEntry.At current),
                                ∃ packing,
                                  Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                    (∀ (window : Finset current.object.Vertex),
                                        Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                          ∃ member ∈ packing, ¬Disjoint window member) ∧
                                      ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                        Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                          Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                              data.dischargeScale ∧
                                            Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                              ∃ receiver,
                                                Graph.FiniteObject.IsReceiver current.object piece data.threshold
                                                    receiver ∧
                                                  ∃
                                                    peeled ⊆
                                                      Graph.FiniteObject.routedLoads current.object piece data.threshold
                                                        receiver,
                                                    Graph.ExitFour.SaturatedAfter piece data.threshold
                                                      data.dischargeScale receiver peeled) →
                              ((∃ packing,
                                    Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                      (∀ (window : Finset current.object.Vertex),
                                          Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                                        ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                          Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                            Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                                data.dischargeScale ∧
                                              Graph.FiniteObject.ambientSurplus current.object piece data.threshold =
                                                  0 ∧
                                                Graph.Strategy.Spine.HandoffAdmissible data current.object packing
                                                  piece) →
                                  typeAExitSevenHandoff.At current) →
                                ((∀ (packing : Finset (Finset current.object.Vertex)),
                                      Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                        (∀ (window : Finset current.object.Vertex),
                                            Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                              ∃ member ∈ packing, ¬Disjoint window member) →
                                          ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                            Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                              Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                                  data.dischargeScale →
                                                Graph.FiniteObject.ambientSurplus current.object piece data.threshold =
                                                    0 →
                                                  ¬Graph.Strategy.Spine.HandoffProduced data current.object packing
                                                      piece) →
                                    typeAExitSevenFree.At current) →
                                  typeAExitSevenHandoff ∉ known →
                                    typeAExitSevenFree ∉ known →
                                      Core.Strategy.Decision typeAExitSevenHandoff typeAExitSevenFree previous
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
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃
                                              outside ∈
                                                Graph.VisibleEntry.completionPorts current.object piece receiver,
                                              data.dischargeScale ≤
                                                (Graph.VisibleEntry.visibleLoadsAt current.object piece data.threshold
                                                    receiver outside).card) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        Graph.WindowLabelCollision.LabelCollision current.object data.windowOrder
                                          data.LengthOK packing) →
                          typeAExitThreeCollision.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) →
                                  ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                      Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                          data.dischargeScale →
                                        Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
                                          Graph.WindowLabelCollision.LabelCollisionFree current.object data.windowOrder
                                            data.LengthOK packing) →
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
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                      ∃ receiver,
                                        Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                          Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver ∧
                                            ∃
                                              outside ∈
                                                Graph.VisibleEntry.completionPorts current.object piece receiver,
                                              data.dischargeScale ≤
                                                (Graph.VisibleEntry.visibleLoadsAt current.object piece data.threshold
                                                    receiver outside).card) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                                data.dischargeScale receiver ∧
                                              ∃
                                                outside ∈
                                                  Graph.VisibleEntry.completionPorts current.object piece receiver,
                                                Graph.VisibleEntry.ExitTwoThrough current.object piece data.LengthOK
                                                  receiver outside) →
                          typeAExitTwoTheta.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) →
                                  ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                      Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                          data.dischargeScale →
                                        Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
                                          ∀ (receiver : current.object.Vertex),
                                            Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver →
                                              Graph.FiniteObject.Saturated current.object piece data.threshold
                                                  data.dischargeScale receiver →
                                                ∀
                                                  outside ∈
                                                    Graph.VisibleEntry.completionPorts current.object piece receiver,
                                                  ¬Graph.VisibleEntry.ExitTwoThrough current.object piece data.LengthOK
                                                      receiver outside) →
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (selection typeAPortReturn :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            selection ≠ typeAPortReturn →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : selection.At input), ¬Graph.HasCycleWithLength data.LengthOK input.object) →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                    (a : selection.At input) (smaller : Graph.FiniteObject),
                    smaller.LexicographicallySmaller input.object →
                      Graph.MinimumDegreeAtLeast data.threshold smaller →
                        Graph.HasCycleWithLength data.LengthOK smaller) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                      (∀ (support : Finset input.object.Vertex) (receiver outside : input.object.Vertex),
                          outside ∈ Graph.VisibleEntry.completionPorts input.object support receiver →
                            Nonempty (Graph.VisibleEntry.AnchoredReturn input.object receiver outside)) →
                        typeAPortReturn.At input) →
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
      {data : Graph.Strategy.Spine.Data} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (remainderNormalized typeAReceiverRouting :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                (a : remainderNormalized.At input) (packing : Finset (Finset input.object.Vertex)),
                Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                  (∀ (window : Finset input.object.Vertex),
                      Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                        ∃ member ∈ packing, ¬Disjoint window member) →
                    ∀ support ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                      ¬Graph.FiniteObject.InducesWindow input.object data.windowOrder support ∧
                        ¬Graph.MinimumDegreeAtLeast data.threshold (Graph.FiniteObject.induce input.object support)) →
              ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                  (∀ (packing : Finset (Finset input.object.Vertex)),
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
                    typeAReceiverRouting.At input) →
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
          (typeASaturatedReceiver typeASaturatedExitEntry :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            typeASaturatedReceiver ≠ typeASaturatedExitEntry →
              (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  (a : typeASaturatedReceiver.At input),
                  ∃ packing,
                    Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                      (∀ (window : Finset input.object.Vertex),
                          Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                            ∃ member ∈ packing, ¬Disjoint window member) ∧
                        ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                          Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
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
                            ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                        ∃
                                          peeled ⊆
                                            Graph.FiniteObject.routedLoads input.object piece data.threshold receiver,
                                          Graph.ExitFour.SaturatedAfter piece data.threshold data.dischargeScale
                                            receiver peeled) →
                      typeASaturatedExitEntry.At input) →
                  Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale ∧
                                    Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                        ∃ receiver,
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver ∧
                                            Graph.FiniteObject.Saturated current.object piece data.threshold
                                              data.dischargeScale receiver) →
                          typeASaturatedReceiver.At current) →
                        ((∀ (packing : Finset (Finset current.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) →
                                  ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                      Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                          data.dischargeScale →
                                        Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
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
                        ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                          Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                            Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold data.dischargeScale ∧
                              Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                ∃ receiver,
                                  Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                    Graph.FiniteObject.Saturated input.object piece data.threshold data.dischargeScale
                                        receiver ∧
                                      ∃ outside ∈ Graph.VisibleEntry.completionPorts input.object piece receiver,
                                        data.dischargeScale ≤
                                          (Graph.VisibleEntry.visibleLoadsAt input.object piece data.threshold receiver
                                              outside).card) →
                ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                    (∃ packing,
                        Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing ∧
                          (∀ (window : Finset input.object.Vertex),
                              Graph.FiniteObject.InducesWindow input.object data.windowOrder window →
                                ∃ member ∈ packing, ¬Disjoint window member) ∧
                            ∃ piece ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                              Graph.SupportComponents.Connected.ConnectedOn input.object piece ∧
                                Graph.FiniteObject.NegativeNetCharge input.object piece data.threshold
                                    data.dischargeScale ∧
                                  Graph.FiniteObject.ambientSurplus input.object piece data.threshold = 0 ∧
                                    ∃ receiver,
                                      Graph.FiniteObject.IsReceiver input.object piece data.threshold receiver ∧
                                        Graph.FiniteObject.Saturated input.object piece data.threshold
                                            data.dischargeScale receiver ∧
                                          ∃ outside ∈ Graph.VisibleEntry.completionPorts input.object piece receiver,
                                            data.dischargeScale ≤
                                                (Graph.VisibleEntry.visibleLoadsAt input.object piece data.threshold
                                                    receiver outside).card ∧
                                              ∀ (Carrier : Type u)
                                                (entry :
                                                  Graph.Route8.Entry (Graph.HasCycleWithLength data.LengthOK) Carrier)
                                                (coordinate : input.object.Vertex → entry.Coordinate)
                                                (declared :
                                                  ∀
                                                    load ∈
                                                      Graph.FiniteObject.routedLoads input.object piece data.threshold
                                                        receiver,
                                                    coordinate load ∈ entry.coordinates),
                                                (Graph.VisibleEntry.visibleEntryFamily piece data.threshold receiver
                                                        entry coordinate outside declared).Generated
                                                    Graph.ExitFour.Clause.visibleEntry entry.coordinates
                                                    (Graph.VisibleEntry.visibleCoordinates piece data.threshold receiver
                                                      entry coordinate outside entry.coordinates) ∧
                                                  (Graph.VisibleEntry.visibleCoordinates piece data.threshold receiver
                                                        entry coordinate outside entry.coordinates).Nonempty ∧
                                                    Graph.VisibleEntry.visibleLoadsAt input.object piece data.threshold
                                                        receiver outside ⊆
                                                      (Graph.VisibleEntry.visibleEntryFamily piece data.threshold
                                                            receiver entry coordinate outside declared).declaredLoads
                                                        (Graph.VisibleEntry.visibleCoordinates piece data.threshold
                                                          receiver entry coordinate outside entry.coordinates)) →
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
                                  ∀ vertex ∈ piece,
                                    Graph.FiniteObject.internalDegree current.object piece vertex = data.threshold →
                                      ∃ receiver,
                                        Graph.FiniteObject.traceReceiver? current.object piece data.threshold vertex =
                                            some receiver ∧
                                          Graph.FiniteObject.IsReceiver current.object piece data.threshold receiver) →
                        (∀ (a : typeASaturatedReceiver.At current),
                            ∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                (∀ (window : Finset current.object.Vertex),
                                    Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                      ∃ member ∈ packing, ¬Disjoint window member) ∧
                                  ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                    Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
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
                                    ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                      Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                        Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                            data.dischargeScale ∧
                                          Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 ∧
                                            ∃ receiver,
                                              Graph.FiniteObject.IsReceiver current.object piece data.threshold
                                                  receiver ∧
                                                Graph.FiniteObject.Saturated current.object piece data.threshold
                                                    data.dischargeScale receiver ∧
                                                  ∃
                                                    outside ∈
                                                      Graph.VisibleEntry.completionPorts current.object piece receiver,
                                                    data.dischargeScale ≤
                                                      (Graph.VisibleEntry.visibleLoadsAt current.object piece
                                                          data.threshold receiver outside).card) →
                              typeAVisibleEntry.At current) →
                            ((∀ (packing : Finset (Finset current.object.Vertex)),
                                  Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                                    (∀ (window : Finset current.object.Vertex),
                                        Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                          ∃ member ∈ packing, ¬Disjoint window member) →
                                      ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                        Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                          Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                              data.dischargeScale →
                                            Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0 →
                                              piece.card ≤
                                                ∑
                                                    receiver ∈
                                                      Graph.FiniteObject.receivers current.object piece data.threshold,
                                                    (Graph.VisibleEntry.silentExcess current.object piece data.threshold
                                                        data.dischargeScale receiver).card +
                                                  data.dischargeScale *
                                                    Graph.FiniteObject.positiveDeficiency current.object piece
                                                      data.threshold) →
                                typeAVisibleFirstExcess.At current) →
                              typeAVisibleEntry ∉ known →
                                typeAVisibleFirstExcess ∉ known →
                                  Core.Strategy.Decision typeAVisibleEntry typeAVisibleFirstExcess previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeBExclusionDichotomy`

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
                (typeBExclusionCharge typeBExcluded typeBExclusionResidual :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  [Core.Residual.FactKeys.Has typeBExclusionCharge known] →
                    (∀ (a : typeBExclusionCharge.At current) (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                            Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                              Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                  data.dischargeScale →
                                0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
                                  ∃ assignment,
                                    ∀
                                      (entry :
                                        (hub : current.object.Vertex) →
                                          hub ∈ assignment.demands →
                                            Graph.TypeBRefinedSupport.CandidateEntry current.object data.threshold
                                              data.dischargeScale piece hub),
                                      (∀ (left : current.object.Vertex) (leftMember : left ∈ assignment.demands)
                                          (right : current.object.Vertex) (rightMember : right ∈ assignment.demands),
                                          left ≠ right →
                                            Disjoint (entry left leftMember).carriers
                                              (entry right rightMember).carriers) →
                                        (∀ (hub : current.object.Vertex) (member : hub ∈ assignment.demands),
                                            (entry hub member).chosen = ∅) →
                                          Graph.TypeBEnvelopeCharge.PostLedgerCore current.object piece assignment
                                              entry →
                                            Graph.FiniteObject.NonNegativeNetCharge current.object piece data.threshold
                                              data.dischargeScale) →
                      ((∀ (packing : Finset (Finset current.object.Vertex)),
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                              ∀ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece →
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                      data.dischargeScale →
                                    0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold →
                                      Graph.FiniteObject.NonNegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale) →
                          typeBExcluded.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      0 < Graph.FiniteObject.ambientSurplus current.object piece data.threshold ∧
                                        ∃ assignment entry,
                                          (∀ (left : current.object.Vertex) (leftMember : left ∈ assignment.demands)
                                              (right : current.object.Vertex)
                                              (rightMember : right ∈ assignment.demands),
                                              left ≠ right →
                                                Disjoint (entry left leftMember).carriers
                                                  (entry right rightMember).carriers) ∧
                                            ¬((∀ (hub : current.object.Vertex) (member : hub ∈ assignment.demands),
                                                  (entry hub member).chosen = ∅) ∧
                                                Graph.TypeBEnvelopeCharge.PostLedgerCore current.object piece assignment
                                                  entry)) →
                            typeBExclusionResidual.At current) →
                          typeBExcluded ∉ known →
                            typeBExclusionResidual ∉ known →
                              Core.Strategy.Decision typeBExcluded typeBExclusionResidual previous
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
                              ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                  Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                    data.dischargeScale) →
                      ((∃ packing,
                            Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                              (∀ (window : Finset current.object.Vertex),
                                  Graph.FiniteObject.InducesWindow current.object data.windowOrder window →
                                    ∃ member ∈ packing, ¬Disjoint window member) ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
                                    Graph.FiniteObject.NegativeNetCharge current.object piece data.threshold
                                        data.dischargeScale ∧
                                      Graph.FiniteObject.ambientSurplus current.object piece data.threshold = 0) →
                          typeALowSurplus.At current) →
                        ((∃ packing,
                              Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                                ∃ piece ⊆ Graph.FiniteObject.remainderSupport current.object packing,
                                  Graph.SupportComponents.Connected.ConnectedOn current.object piece ∧
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
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation data)] →
          (boundaryDemand wedgeSupply curvatureDemandFloor :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
            wedgeSupply ≠ boundaryDemand →
              curvatureDemandFloor ≠ boundaryDemand →
                wedgeSupply ≠ curvatureDemandFloor →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                      (a : boundaryDemand.At input) (packing : Finset (Finset input.object.Vertex)),
                      Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                        Graph.FiniteObject.positiveDeficiency input.object
                              (Graph.FiniteObject.remainderSupport input.object packing) data.threshold +
                            2 * (data.windowOrder - 1) * packing.card ≤
                          data.threshold * (data.windowOrder * packing.card) +
                            Graph.FiniteObject.ambientSurplus input.object (Graph.FiniteObject.windowSupport packing)
                              data.threshold) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                        (∀ (packing : Finset (Finset input.object.Vertex)),
                            Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                              ∀ support ⊆ Graph.FiniteObject.remainderSupport input.object packing,
                                data.threshold * support.card ≤
                                  Graph.FiniteObject.internalWedgeCount input.object support +
                                    2 * Graph.FiniteObject.positiveDeficiency input.object support data.threshold) →
                          wedgeSupply.At input) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation data) →
                          (∀ (packing : Finset (Finset input.object.Vertex)),
                              Graph.FiniteObject.IsWindowPacking input.object data.windowOrder packing →
                                data.threshold * (Graph.FiniteObject.remainderSupport input.object packing).card +
                                    2 * (2 * (data.windowOrder - 1) * packing.card) ≤
                                  Graph.FiniteObject.internalWedgeCount input.object
                                      (Graph.FiniteObject.remainderSupport input.object packing) +
                                    2 *
                                      (data.threshold * (data.windowOrder * packing.card) +
                                        Graph.FiniteObject.ambientSurplus input.object
                                          (Graph.FiniteObject.windowSupport packing) data.threshold)) →
                            curvatureDemandFloor.At input) →
                        Core.Strategy.AtomicStrategy
                          (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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

#### `Hypostructure.Graph.Strategy.Spine.windowPackageDichotomy`

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
                (windowPackageSeparated windowPackageCollided :
                    Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation data)) →
                  ((∀ (packing : Finset (Finset current.object.Vertex)),
                        Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing →
                          ∃ coordinateCount family,
                            2 ^
                                  (data.windowRate *
                                      data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                                    Graph.FiniteObject.windowPackingNumber current.object data.windowOrder) ≤
                                Nat.card ((coordinate : Fin coordinateCount) → family.State coordinate) ∧
                              Graph.Strategy.Spine.jointPackageDemand data current.object packing ≤
                                  Nat.card ((coordinate : Fin coordinateCount) → family.State coordinate) ∧
                                family.slots.card ≤ Graph.FiniteObject.edgeCount current.object ∧
                                  Graph.FiniteObject.edgeCount current.object ≤ family.pool.card) →
                      windowPackageSeparated.At current) →
                    ((∃ packing,
                          Graph.FiniteObject.IsWindowPacking current.object data.windowOrder packing ∧
                            ∀ (coordinateCount : ℕ)
                              (family :
                                Graph.PackedWindowRealization.SeparatedFamily current.object (Fin coordinateCount)),
                              ¬(2 ^
                                      (data.windowRate *
                                          data.separatedScaleCount (Graph.FiniteObject.vertexCount current.object) *
                                        Graph.FiniteObject.windowPackingNumber current.object data.windowOrder) ≤
                                    Nat.card ((coordinate : Fin coordinateCount) → family.State coordinate) ∧
                                  Graph.Strategy.Spine.jointPackageDemand data current.object packing ≤
                                      Nat.card ((coordinate : Fin coordinateCount) → family.State coordinate) ∧
                                    family.slots.card ≤ Graph.FiniteObject.edgeCount current.object ∧
                                      Graph.FiniteObject.edgeCount current.object ≤ family.pool.card)) →
                        windowPackageCollided.At current) →
                      windowPackageSeparated ∉ known →
                        windowPackageCollided ∉ known →
                          Core.Strategy.Decision windowPackageSeparated windowPackageCollided previous
```
<!-- END GENERATED API -->
