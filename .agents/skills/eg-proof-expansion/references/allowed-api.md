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
Compiled declarations: **255**.

Category counts: **Canonical execution** 29, **Canonical fact-only steps and branch decisions** 5, **Canonical ledger** 94, **Canonical manifest** 32, **Canonical residual domain** 17, **Canonical scope initialization** 6, **Minimum-degree cycle spine rows** 7, **Minimum-degree cycle spine vocabulary** 19, **Sealed topology** 46.

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
              (transport :
                  {key : Key} →
                    {new old : Residual} →
                      Core.Residual.RefinementSystem.Refines new old → Value key old → Value key new) →
                (∀ (key : Key) (residual : Residual) (value : Value key residual), transport ⋯ value = value) →
                  (∀ (key : Key) {new middle old : Residual}
                      (new_middle : Core.Residual.RefinementSystem.Refines new middle)
                      (middle_old : Core.Residual.RefinementSystem.Refines middle old) (value : Value key old),
                      transport ⋯ value = transport new_middle (transport middle_old value)) →
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
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Residual.FactSystem Residual] (key : Core.Residual.FactSystem.Key Residual) (residual : Residual)
  (value : Core.Residual.FactSystem.Value key residual), Core.Residual.FactSystem.transport ⋯ value = value
```

#### `Hypostructure.Core.Residual.FactSystem.transport_trans`

- Category: Canonical ledger
- Kind: `theorem`
- Source: `Hypostructure/Core/Residual/ExactLedger.lean`
- Compiled type:

```lean
∀ {Residual : Type uResidual} {inst : Core.Residual.RefinementSystem Residual}
  [self : Core.Residual.FactSystem Residual] (key : Core.Residual.FactSystem.Key Residual) {new middle old : Residual}
  (new_middle : Core.Residual.RefinementSystem.Refines new middle)
  (middle_old : Core.Residual.RefinementSystem.Refines middle old) (value : Core.Residual.FactSystem.Value key old),
  Core.Residual.FactSystem.transport ⋯ value =
    Core.Residual.FactSystem.transport new_middle (Core.Residual.FactSystem.transport middle_old value)
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

### `Hypostructure.Core.Strategy.Dag`

#### `Hypostructure.Core.Strategy.Dag.AfterCriticalModificationStructure`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → Core.StrategyData P T → Core.Strategy.Dag.RouteMode → Type (max (max uAmbient uBranch) uData)
```

#### `Hypostructure.Core.Strategy.Dag.AfterCriticalModificationStructure.interfaceReplacementClosure`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.AfterCriticalModificationStructure data mode →
          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.AfterMinimalCounterexampleSelection`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → Core.StrategyData P T → Core.Strategy.Dag.RouteMode → Type (max (max uAmbient uBranch) uData)
```

#### `Hypostructure.Core.Strategy.Dag.AfterMinimalCounterexampleSelection.targetAlgebraReduction`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.AfterMinimalCounterexampleSelection data mode →
          optParam String "" → optParam String "" → Core.Strategy.Dag.AfterTargetAlgebraReduction data mode
```

#### `Hypostructure.Core.Strategy.Dag.AfterMinimalSubobjectExclusion`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → Core.StrategyData P T → Core.Strategy.Dag.RouteMode → Type (max (max uAmbient uBranch) uData)
```

#### `Hypostructure.Core.Strategy.Dag.AfterMinimalSubobjectExclusion.criticalModificationStructure`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.AfterMinimalSubobjectExclusion data mode →
          optParam String "" → optParam String "" → Core.Strategy.Dag.AfterCriticalModificationStructure data mode
```

#### `Hypostructure.Core.Strategy.Dag.AfterTargetAlgebraReduction`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → Core.StrategyData P T → Core.Strategy.Dag.RouteMode → Type (max (max uAmbient uBranch) uData)
```

#### `Hypostructure.Core.Strategy.Dag.AfterTargetAlgebraReduction.minimalSubobjectExclusion`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.AfterTargetAlgebraReduction data mode →
          optParam String "" → optParam String "" → Core.Strategy.Dag.AfterMinimalSubobjectExclusion data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint`

- Category: Sealed topology
- Kind: `inductive`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} → Core.StrategyData P T → Core.Strategy.Dag.RouteMode → Type (max uAmbient uBranch uData)
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.atomContextObstructionDichotomy`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.atomContextObstructionDichotomies.length] →
            optParam (Fin data.atomContextObstructionDichotomies.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.atomContextObstructionDichotomies.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.autoroute`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      Core.Strategy.Dag.Blueprint data Core.Strategy.Dag.RouteMode.authoring →
        optParam String "" →
          optParam String "" →
            optParam (List String) [] → Core.Strategy.Dag.Blueprint data Core.Strategy.Dag.RouteMode.authoring
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.baselineDemandAccounting`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.baselineDemandAccountings.length] →
            optParam (Fin data.baselineDemandAccountings.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.baselineDemandAccountings.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.boundaryDemandAccounting`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.boundaryDemandAccountings.length] →
            optParam (Fin data.boundaryDemandAccountings.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.boundaryDemandAccountings.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.canonicalCapacityTokenAccounting`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.canonicalCapacityTokenAccountings.length] →
            optParam (Fin data.canonicalCapacityTokenAccountings.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.canonicalCapacityTokenAccountings.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.canonicalPairResponseAccounting`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.canonicalPairResponseAccountings.length] →
            optParam (Fin data.canonicalPairResponseAccountings.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.canonicalPairResponseAccountings.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.closedCode`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.closedCodes.length] →
            optParam (Fin data.closedCodes.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.closedCodes.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.coldBranchAggregation`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.coldBranchAggregations.length] →
            optParam (Fin data.coldBranchAggregations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.coldBranchAggregations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.compressionLinkedTargetRelativeRankDichotomy`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.compressionLinkedTargetRelativeRankDichotomies.length] →
            optParam (Fin data.compressionLinkedTargetRelativeRankDichotomies.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝
                  data.compressionLinkedTargetRelativeRankDichotomies.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.counterexampleLocalization`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.counterexampleLocalizations.length] →
            optParam (Fin data.counterexampleLocalizations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.counterexampleLocalizations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.coupledHomogeneousFibrePressure`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.coupledHomogeneousFibrePressures.length] →
            optParam (Fin data.coupledHomogeneousFibrePressures.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.coupledHomogeneousFibrePressures.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.dichotomy`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.dichotomies.length] →
            optParam (Fin data.dichotomies.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.dichotomies.length) →
              optParam (Core.Strategy.Dag.Blueprint data mode) Core.Strategy.Dag.Blueprint.root →
                optParam (Core.Strategy.Dag.Blueprint data mode) Core.Strategy.Dag.Blueprint.root →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.exactFiniteLocalAlgebra`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.exactFiniteLocalAlgebras.length] →
            optParam (Fin data.exactFiniteLocalAlgebras.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.exactFiniteLocalAlgebras.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteBarrierEnumeration`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.finiteBarrierEnumerations.length] →
            optParam (Fin data.finiteBarrierEnumerations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.finiteBarrierEnumerations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteBottleneckClassification`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.finiteBottleneckClassifications.length] →
            optParam (Fin data.finiteBottleneckClassifications.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.finiteBottleneckClassifications.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteDensityBudget`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.finiteDensityBudgets.length] →
            optParam (Fin data.finiteDensityBudgets.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.finiteDensityBudgets.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteScheduleCapacity`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.finiteScheduleCapacities.length] →
            optParam (Fin data.finiteScheduleCapacities.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.finiteScheduleCapacities.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteStateCapacity`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.finiteStateCapacities.length] →
            optParam (Fin data.finiteStateCapacities.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.finiteStateCapacities.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.finiteStateNetChargeContinuation`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
              branch) →
            (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                branch) →
              optParam String "" →
                optParam String "" →
                  optParam String "" →
                    optParam String "" → optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.homogeneousBottleneck`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.homogeneousBottlenecks.length] →
            optParam (Fin data.homogeneousBottlenecks.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.homogeneousBottlenecks.length) →
              optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) id →
                optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) id →
                  optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) id →
                    optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.label`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode → String → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.localSupplyLowerBound`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.localSupplyLowerBounds.length] →
            optParam (Fin data.localSupplyLowerBounds.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.localSupplyLowerBounds.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.minimalCounterexampleSelection`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.counterexampleReductions.length] →
            optParam (Fin data.counterexampleReductions.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.counterexampleReductions.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.AfterMinimalCounterexampleSelection data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.note`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode → String → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.obstructionPackingClosure`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.obstructionPackingClosures.length] →
            optParam (Fin data.obstructionPackingClosures.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.obstructionPackingClosures.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.orderedSurplusActivation`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.orderedSurplusActivations.length] →
            optParam (Fin data.orderedSurplusActivations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.orderedSurplusActivations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.orderedWitnessScan`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.scans.length] →
            optParam (Fin data.scans.length) (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.scans.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.proofTrace`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} → Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.ProofTrace
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.rankBudget`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.rankBudgets.length] →
            optParam (Fin data.rankBudgets.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.rankBudgets.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.responseClassifier`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.responses.length] →
            optParam (Fin data.responses.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.responses.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.root`

- Category: Sealed topology
- Kind: `constructor`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} → {mode : Core.Strategy.Dag.RouteMode} → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.route8CarrierClosure`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.route8CarrierClosures.length] →
            optParam (Fin data.route8CarrierClosures.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.route8CarrierClosures.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.scaleThresholdDichotomy`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.scaleThresholdDichotomies.length] →
            optParam (Fin data.scaleThresholdDichotomies.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.scaleThresholdDichotomies.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.supportComplementNormalization`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.supportComplementNormalizations.length] →
            optParam (Fin data.supportComplementNormalizations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.supportComplementNormalizations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.supportLocalization`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.localizations.length] →
            optParam (Fin data.localizations.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.localizations.length) →
              optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.targetOrAvoid`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
```

#### `Hypostructure.Core.Strategy.Dag.Blueprint.targetRelativeRankDichotomy`

- Category: Sealed topology
- Kind: `definition`
- Source: `Hypostructure/Core/Strategy/Dag.lean`
- Compiled type:

```lean
{P : Core.Problem} →
  {T : Core.Target P} →
    {data : Core.StrategyData P T} →
      {mode : Core.Strategy.Dag.RouteMode} →
        Core.Strategy.Dag.Blueprint data mode →
          [inst : NeZero data.targetRelativeRankDichotomies.length] →
            optParam (Fin data.targetRelativeRankDichotomies.length)
                (Hypostructure.Core.Strategy.Dag.firstFamilyIndex✝ data.targetRelativeRankDichotomies.length) →
              (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                  branch) →
                (optParam (Core.Strategy.Dag.Blueprint data mode → Core.Strategy.Dag.Blueprint data mode) fun branch =>
                    branch) →
                  optParam String "" →
                    optParam String "" →
                      optParam String "" →
                        optParam String "" →
                          optParam String "" → optParam String "" → Core.Strategy.Dag.Blueprint data mode
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
              (transport :
                  {key : Key} →
                    {new old : Core.Strategy.ProblemInput P} →
                      new.object = old.object → Value key old → Value key new) →
                (∀ (key : Key) (input : Core.Strategy.ProblemInput P) (value : Value key input),
                    transport ⋯ value = value) →
                  (∀ (key : Key) {new middle old : Core.Strategy.ProblemInput P}
                      (new_middle : new.object = middle.object) (middle_old : middle.object = old.object)
                      (value : Value key old), transport ⋯ value = transport new_middle (transport middle_old value)) →
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

#### `Hypostructure.Core.Strategy.FactVocabulary.transport_refl`

- Category: Canonical residual domain
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} (self : Core.Strategy.FactVocabulary P) (key : self.Key) (input : Core.Strategy.ProblemInput P)
  (value : self.Value key input), self.transport ⋯ value = value
```

#### `Hypostructure.Core.Strategy.FactVocabulary.transport_trans`

- Category: Canonical residual domain
- Kind: `theorem`
- Source: `Hypostructure/Core/Strategy/ProblemResidual.lean`
- Compiled type:

```lean
∀ {P : Core.Problem} (self : Core.Strategy.FactVocabulary P) (key : self.Key)
  {new middle old : Core.Strategy.ProblemInput P} (new_middle : new.object = middle.object)
  (middle_old : middle.object = old.object) (value : self.Value key old),
  self.transport ⋯ value = self.transport new_middle (self.transport middle_old value)
```

### `Hypostructure.Core.Strategy.ExactExecution`

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

#### `Hypostructure.Graph.Strategy.Spine.Holds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) →
  (Presentation : Type) → Presentation → ℕ → (ℕ → Prop) → Graph.Strategy.Spine.Key → Graph.FiniteObject → Prop
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.Input`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → ℕ → Type (max (u + 1) v)
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

#### `Hypostructure.Graph.Strategy.Spine.Key.returnAvoidance`

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

#### `Hypostructure.Graph.Strategy.Spine.Value`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (threshold : ℕ) →
        (ℕ → Prop) →
          Graph.Strategy.Spine.Key →
            Core.Strategy.ProblemInput (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold) →
              Type
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
      {threshold : ℕ} →
        {LengthOK : ℕ → Prop} →
          (input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold) →
            ¬Graph.HasCycleWithLength LengthOK input.object →
              (∀ (smaller : Graph.FiniteObject),
                  (Graph.Strategy.Spine.progress BranchState Presentation presentation threshold).Smaller smaller
                      input.object →
                    Graph.MinimumDegreeAtLeast threshold smaller → Graph.HasCycleWithLength LengthOK smaller) →
                Core.MinimalCounterexampleContext
                  (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold)
                  (Graph.HasCycleWithLength LengthOK)
                  (Graph.Strategy.Spine.progress BranchState Presentation presentation threshold)
```

#### `Hypostructure.Graph.Strategy.Spine.criticalityManifest`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {threshold : ℕ} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)] →
          (required tight slack :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)) →
            tight ≠ required →
              slack ≠ required →
                tight ≠ slack →
                  Core.Strategy.FactManifest
                    (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
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
      {threshold : ℕ} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)] →
          (noProperBaseline tightEndpoint slackIndependent :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)) →
            tightEndpoint ≠ noProperBaseline →
              slackIndependent ≠ noProperBaseline →
                tightEndpoint ≠ slackIndependent →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
                      (a : noProperBaseline.At input) (subgraph : Graph.ProperSubgraph input.object),
                      ¬Graph.MinimumDegreeAtLeast threshold subgraph.value) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold) →
                        (∀ (dart : input.object.graph.Dart),
                            Graph.FiniteObject.degree input.object dart.toProd.1 = threshold ∨
                              Graph.FiniteObject.degree input.object dart.toProd.2 = threshold) →
                          tightEndpoint.At input) →
                      ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold) →
                          (∀ (left right : input.object.Vertex),
                              threshold < Graph.FiniteObject.degree input.object left →
                                threshold < Graph.FiniteObject.degree input.object right →
                                  ¬input.object.graph.Adj left right) →
                            slackIndependent.At input) →
                        Core.Strategy.AtomicStrategy
                          (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
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
      (threshold : ℕ) →
        (ℕ → Prop) →
          Core.Residual.FactSystem
            (Core.Strategy.ProblemInput (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold))
```

#### `Hypostructure.Graph.Strategy.Spine.instDecidableEqKey`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
DecidableEq Graph.Strategy.Spine.Key
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
      (threshold : ℕ) →
        (LengthOK : ℕ → Prop) →
          Graph.Strategy.Spine.Key →
            Core.Residual.FactKey
              (Core.Strategy.ProblemInput
                (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold))
```

#### `Hypostructure.Graph.Strategy.Spine.name`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key → Name
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

#### `Hypostructure.Graph.Strategy.Spine.noProperBaselineRow`

- Category: Minimum-degree cycle spine rows
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
{BranchState : Graph.FiniteObject → Type v} →
  {Presentation : Type} →
    {presentation : Presentation} →
      {threshold : ℕ} →
        {LengthOK : ℕ → Prop} →
          [inst :
              Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)] →
            (selection noProperBaseline :
                Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)) →
              selection ≠ noProperBaseline →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
                    (a : selection.At input), ¬Graph.HasCycleWithLength LengthOK input.object) →
                  (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
                      (a : selection.At input) (smaller : Graph.FiniteObject),
                      smaller.LexicographicallySmaller input.object →
                        Graph.MinimumDegreeAtLeast threshold smaller → Graph.HasCycleWithLength LengthOK smaller) →
                    ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold) →
                        (∀ (subgraph : Graph.ProperSubgraph input.object),
                            ¬Graph.MinimumDegreeAtLeast threshold subgraph.value) →
                          noProperBaseline.At input) →
                      Core.Strategy.AtomicStrategy
                        (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.problem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) → (Presentation : Type) → Presentation → ℕ → Core.Problem
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
      (threshold : ℕ) → Core.Progress (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold)
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
      {threshold : ℕ} →
        {LengthOK : ℕ → Prop} →
          [inst :
              Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)] →
            (selection returnAvoidance :
                Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)) →
              selection ≠ returnAvoidance →
                (∀ (input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
                    (a : selection.At input), ¬Graph.HasCycleWithLength LengthOK input.object) →
                  ((input : Graph.Strategy.Spine.Input BranchState Presentation presentation threshold) →
                      (∀ (dart : input.object.graph.Dart),
                          Disjoint (Graph.returnLengthSet input.object dart) (Graph.shiftedAcceptedSet LengthOK)) →
                        returnAvoidance.At input) →
                    Core.Strategy.AtomicStrategy
                      (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
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
      {threshold : ℕ} →
        [inst : Core.Residual.FactSystem (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)] →
          (required produced :
              Core.Residual.FactKey (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)) →
            required ≠ produced →
              Core.Strategy.FactManifest (Graph.Strategy.Spine.Input BranchState Presentation presentation threshold)
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
      (threshold : ℕ) →
        (ℕ → Prop) →
          Core.Strategy.FactVocabulary (Graph.Strategy.Spine.problem BranchState Presentation presentation threshold)
```
<!-- END GENERATED API -->
