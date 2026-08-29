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
Compiled declarations: **1178**.

Category counts: **Canonical execution** 33, **Canonical exhaustive decisions** 11, **Canonical fact-only steps and branch decisions** 5, **Canonical ledger** 98, **Canonical manifest** 35, **Canonical residual domain** 16, **Canonical scope initialization** 6, **Minimum-degree cycle spine rows** 120, **Minimum-degree cycle spine vocabulary** 820, **Sealed topology** 6, **Sealed total closure** 12, **Typed partial topology and sealed completion** 16.

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

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanB2ChoiceStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanB2ObstructionMassStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanB2ObstructionStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanB2PaidStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanCertificateCapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanCertificateMarkedStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanCertificateResidualMassStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanCertificateResidualStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanDataStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanDegreeFourCentresStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanDegreeFourProfileStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanDirectCycleFreeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanDirectCycleStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanEnvelopeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanEnvelopeWitness`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object →
      object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanHeavyCentreStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanHybridEntryStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermFanLocalDichotomyStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.AbsorbedGermSplitStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ActiveColdGermAtSelectedStubStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object →
      Graph.Strategy.Spine.ColdGermOccurrence data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ActiveColdGermStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
        (Graph.HasCycleWithLength data.LengthOK) object →
      Prop
```

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

#### `Hypostructure.Graph.Strategy.Spine.BlockedAprioriConditionalFibre`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.blockedClassAt data object →
      Graph.Strategy.Spine.blockedCoordinate data object → Set (Graph.Strategy.Spine.blockedAprioriClassAt data object)
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedBarrierFailureStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedGraphFibreMonotonicityAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Graph.Strategy.Spine.blockedCoordinate data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedPairCodeUnrealizedStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedPairEntropySandwichStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedPairEntropySetupStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedRelativeFibreBoundAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Graph.Strategy.Spine.blockedCoordinate data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedScaleAdditivityStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedStateFibreBoundAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Graph.Strategy.Spine.blockedCoordinate data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.BlockedSurvivingConditionalFibre`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.blockedClassAt data object →
      Graph.Strategy.Spine.blockedCoordinate data object → Set (Graph.Strategy.Spine.blockedAprioriClassAt data object)
```

#### `Hypostructure.Graph.Strategy.Spine.CanonicalDecompositionCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Type
```

#### `Hypostructure.Graph.Strategy.Spine.CanonicalNeutralConfigurationStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.CanonicalReplacementSwapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.CanonicalReplacementTrivialStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.ColdCorridorStateStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdCrossWindowHalfEdge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.ColdDeclaredHandoffSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdEligibleHalfEdge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.ColdExchangeBoundStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureCompressionStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureCycleStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectEquivalentStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectRoutesStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectStatement.equivalent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdFailureDefectStatement data object →
    Graph.Strategy.Spine.ColdFailureDefectEquivalentStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectStatement.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdFailureDefectRoutesStatement data object →
    Graph.Strategy.Spine.ColdFailureDefectEquivalentStatement data object →
      Graph.Strategy.Spine.ColdFailureDefectStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureDefectStatement.routes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdFailureDefectStatement data object →
    Graph.Strategy.Spine.ColdFailureDefectRoutesStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureRoutingStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureRoutingStatement.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
      data.LengthOK object →
    Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement data object →
      Graph.Strategy.Spine.ColdFailureRoutingStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureRoutingStatement.sparseSurvivor`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
    Graph.SurvivesSparseExits (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
      data.LengthOK object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFailureRoutingStatement.surviving`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
    Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureCompressionAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    {windows component : Finset object.Vertex} →
      (corridor : Graph.ColdCorridor.Corridor object windows component) →
        (presentation : Graph.ColdCorridor.Presentation data.coldSignature object) →
          (corridor.Segment → presentation.Segment) → corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureCycleAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    {windows component : Finset object.Vertex} →
      (corridor : Graph.ColdCorridor.Corridor object windows component) → corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureDefectAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    {windows component : Finset object.Vertex} →
      (corridor : Graph.ColdCorridor.Corridor object windows component) →
        (presentation : Graph.ColdCorridor.Presentation data.coldSignature object) →
          (corridor.Segment → presentation.Segment) → corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    {windows component : Finset object.Vertex} →
      (corridor : Graph.ColdCorridor.Corridor object windows component) →
        (presentation : Graph.ColdCorridor.Presentation data.coldSignature object) →
          (corridor.Segment → presentation.Segment) →
            Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object →
              (Finset object.Vertex → Prop) → corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent.compression`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {windows component : Finset object.Vertex}
  {corridor : Graph.ColdCorridor.Corridor object windows component}
  {presentation : Graph.ColdCorridor.Presentation data.coldSignature object}
  {index : corridor.Segment → presentation.Segment}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment},
  Graph.Strategy.Spine.ColdFirstFailureCompressionAt data object corridor presentation index segment →
    Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff segment
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent.cycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {windows component : Finset object.Vertex}
  {corridor : Graph.ColdCorridor.Corridor object windows component}
  {presentation : Graph.ColdCorridor.Presentation data.coldSignature object}
  {index : corridor.Segment → presentation.Segment}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment},
  Graph.Strategy.Spine.ColdFirstFailureCycleAt data object corridor segment →
    Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff segment
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent.defect`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {windows component : Finset object.Vertex}
  {corridor : Graph.ColdCorridor.Corridor object windows component}
  {presentation : Graph.ColdCorridor.Presentation data.coldSignature object}
  {index : corridor.Segment → presentation.Segment}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment},
  Graph.Strategy.Spine.ColdFirstFailureDefectAt data object corridor presentation index segment →
    Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff segment
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent.germ`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {windows component : Finset object.Vertex}
  {corridor : Graph.ColdCorridor.Corridor object windows component}
  {presentation : Graph.ColdCorridor.Presentation data.coldSignature object}
  {index : corridor.Segment → presentation.Segment}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment},
  Graph.Strategy.Spine.ColdFirstFailureGermAt data object corridor presentation index germ segment →
    Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff segment
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureEvent.handoff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {windows component : Finset object.Vertex}
  {corridor : Graph.ColdCorridor.Corridor object windows component}
  {presentation : Graph.ColdCorridor.Presentation data.coldSignature object}
  {index : corridor.Segment → presentation.Segment}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {Handoff : Finset object.Vertex → Prop} {segment : corridor.Segment},
  Graph.Strategy.Spine.ColdFirstFailureHandoffAt object corridor Handoff segment →
    Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff segment
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureGermAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    {windows component : Finset object.Vertex} →
      (corridor : Graph.ColdCorridor.Corridor object windows component) →
        (presentation : Graph.ColdCorridor.Presentation data.coldSignature object) →
          (corridor.Segment → presentation.Segment) →
            Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
                (Graph.HasCycleWithLength data.LengthOK) object →
              corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureGermOccurrence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureGermOccurrence.holds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {occurrence : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object}
  {epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object},
  Graph.Strategy.Spine.ColdFirstFailureGermOccurrence data object occurrence epsilon →
    let germ := Graph.Strategy.Spine.coldOccurrenceIncidence data object occurrence epsilon;
    let corridor := Graph.Strategy.Spine.coldOccurrenceCorridorAt data object occurrence epsilon;
    let presentation := Graph.Strategy.Spine.coldOccurrencePresentationAt data object occurrence epsilon;
    let index := Graph.Strategy.Spine.coldOccurrenceIndexAt data object occurrence epsilon;
    ∃ first,
      Graph.Strategy.Spine.ColdFirstFailureGermAt data object corridor presentation index germ first ∧
        ∀ (earlier : corridor.Segment),
          ↑earlier < ↑first →
            ¬Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ occurrence.Handoff
                earlier
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureGermOccurrence.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {occurrence : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object}
  {epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object},
  (let germ := Graph.Strategy.Spine.coldOccurrenceIncidence data object occurrence epsilon;
    let corridor := Graph.Strategy.Spine.coldOccurrenceCorridorAt data object occurrence epsilon;
    let presentation := Graph.Strategy.Spine.coldOccurrencePresentationAt data object occurrence epsilon;
    let index := Graph.Strategy.Spine.coldOccurrenceIndexAt data object occurrence epsilon;
    ∃ first,
      Graph.Strategy.Spine.ColdFirstFailureGermAt data object corridor presentation index germ first ∧
        ∀ (earlier : corridor.Segment),
          ↑earlier < ↑first →
            ¬Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ occurrence.Handoff
                earlier) →
    Graph.Strategy.Spine.ColdFirstFailureGermOccurrence data object occurrence epsilon
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureHandoffAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) →
  {windows component : Finset object.Vertex} →
    (corridor : Graph.ColdCorridor.Corridor object windows component) →
      (Finset object.Vertex → Prop) → corridor.Segment → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureHandoffOccurrence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData.Handoff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData.handoffAbsent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object) (support : Finset object.Vertex),
  ¬self.Handoff support
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (Handoff : Finset object.Vertex → Prop) →
      (∀ (support : Finset object.Vertex), ¬Handoff support) →
        (state : Graph.Strategy.Spine.ColdCorridorStateStatement data object) →
          (let Eligible := Graph.Strategy.Spine.ColdEligibleHalfEdge data object;
            let incidence := Classical.choose state;
            let stateOne := ⋯;
            let componentAt := Classical.choose stateOne;
            let stateTwo := ⋯;
            let corridorAt := Classical.choose stateTwo;
            let stateTail := ⋯;
            let presentationAt := Classical.choose stateTail;
            let indexAt := Classical.choose ⋯;
            ∀ (epsilon : Eligible),
              let germ := incidence epsilon;
              let corridor := corridorAt epsilon;
              let presentation := presentationAt epsilon;
              let index := indexAt epsilon;
              ∃ first,
                Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff first ∧
                  ∀ (earlier : corridor.Segment),
                    ↑earlier < ↑first →
                      ¬Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ Handoff
                          earlier) →
            Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData.occurs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object),
  let Eligible := Graph.Strategy.Spine.ColdEligibleHalfEdge data object;
  let incidence := Classical.choose ⋯;
  let stateOne := ⋯;
  let componentAt := Classical.choose stateOne;
  let stateTwo := ⋯;
  let corridorAt := Classical.choose stateTwo;
  let stateTail := ⋯;
  let presentationAt := Classical.choose stateTail;
  let indexAt := Classical.choose ⋯;
  ∀ (epsilon : Eligible),
    let germ := incidence epsilon;
    let corridor := corridorAt epsilon;
    let presentation := presentationAt epsilon;
    let index := indexAt epsilon;
    ∃ first,
      Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ self.Handoff first ∧
        ∀ (earlier : corridor.Segment),
          ↑earlier < ↑first →
            ¬Graph.Strategy.Spine.ColdFirstFailureEvent data object corridor presentation index germ self.Handoff
                earlier
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceData.state`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object),
  Graph.Strategy.Spine.ColdCorridorStateStatement data object
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstFailureOccurrenceStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdFirstHighHandoffStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.ColdGermFamilyPositiveStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdGermFamilyWitness`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      (Graph.Strategy.Spine.ColdGermOccurrence data object →
          Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
            (Graph.HasCycleWithLength data.LengthOK) object) →
        Finset (Graph.Strategy.Spine.ColdGermOccurrence data object) →
          Finset (Graph.Strategy.Spine.ColdGermOccurrence data object) → ℕ → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdGermOccurrence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.ColdGermOccurrence.stub`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.ColdGermOccurrence data object → object.Vertex × object.Vertex
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

#### `Hypostructure.Graph.Strategy.Spine.ColdMassBoundedStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdMassLinearStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.ColdPositiveGermStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdReturnCorridorsStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.ColdSelectedHalfEdge`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.ColdStubExcessStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement.holds`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement data object →
    ∃ occurrence,
      ∀ (epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object),
        Graph.Strategy.Spine.ColdFirstFailureGermOccurrence data object occurrence epsilon
```

#### `Hypostructure.Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  (∃ occurrence,
      ∀ (epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object),
        Graph.Strategy.Spine.ColdFirstFailureGermOccurrence data object occurrence epsilon) →
    Graph.Strategy.Spine.ColdSurvivingFirstFailureStatement data object
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

#### `Hypostructure.Graph.Strategy.Spine.Data.baselineDeficitSafety`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), Graph.baselineDeficitCoefficient self.threshold ≤ self.surplusScale
```

#### `Hypostructure.Graph.Strategy.Spine.Data.boundaryProfileFintype`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) → Fintype data.BoundaryProfile
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
∀ (data : Graph.Strategy.Spine.Data), data.coldSignature.windowOrder = data.windowOrder
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

#### `Hypostructure.Graph.Strategy.Spine.Data.densitySlack`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
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
(threshold : ℕ) →
  threshold = 3 →
    3 ≤ threshold →
      (LengthOK : ℕ → Prop) →
        (∀ (length : ℕ), LengthOK length ↔ Core.DyadicLength.PowerOfTwoLength length) →
          (windowOrder : ℕ) →
            0 < windowOrder →
              (Graph.WindowCurvature.Labels windowOrder).card = 399 →
                List.take 7 (Graph.WindowCurvature.sizeDistribution windowOrder) = [13, 60, 122, 122, 63, 17, 2] →
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
                                  (routingLabelBound : ℕ) →
                                    routingLabelBound =
                                        Fintype.card
                                          (Graph.SameTokenRoutingGerms.RoutingLabel (Fin threshold → Fin threshold)
                                            (Graph.WindowCurvature.Label windowOrder)) →
                                      Graph.TokenLoad.quadraticSafetyScale ≤
                                          2 * (1 + 2 * Graph.SameTokenBlockerRoles.sameTokenRoleBound) →
                                        (surplusScale : ℕ) →
                                          Graph.baselineDeficitCoefficient threshold ≤ surplusScale →
                                            (windowRate : ℕ) →
                                              (windowBarrier :
                                                  Core.Finite.CertifiedTableAggregation.BarrierPresentation) →
                                                (windowBarrierLabel :
                                                    Fin windowBarrier.size → Graph.WindowCurvature.Label windowOrder) →
                                                  (∀ (index : Fin windowBarrier.size),
                                                      windowBarrierLabel index ∈
                                                        Graph.WindowCurvature.Labels windowOrder) →
                                                    Function.Injective windowBarrierLabel →
                                                      (∀ label ∈ Graph.WindowCurvature.Labels windowOrder,
                                                          ∃ index, windowBarrierLabel index = label) →
                                                        (∀ (row : windowBarrier.Index)
                                                            (source target : Fin windowBarrier.size),
                                                            (windowBarrier.profile.row
                                                                    (windowBarrier.table.counts.leftLength row)
                                                                    source).getLsb
                                                                target =
                                                              decide
                                                                (Graph.WindowCurvature.Safe
                                                                  (windowBarrier.table.counts.leftLength row)
                                                                  (windowBarrierLabel source)
                                                                  (windowBarrierLabel target))) →
                                                          (∀ (row : windowBarrier.Index)
                                                              (source target : Fin windowBarrier.size),
                                                              (windowBarrier.profile.row
                                                                      (windowBarrier.table.counts.rightLength row)
                                                                      source).getLsb
                                                                  target =
                                                                decide
                                                                  (Graph.WindowCurvature.Safe
                                                                    (windowBarrier.table.counts.rightLength row)
                                                                    (windowBarrierLabel source)
                                                                    (windowBarrierLabel target))) →
                                                            (∀ (row : windowBarrier.Index)
                                                                (source target : Fin windowBarrier.size),
                                                                (windowBarrier.profile.row
                                                                        (windowBarrier.table.counts.leftLength row +
                                                                          windowBarrier.table.counts.rightLength row)
                                                                        source).getLsb
                                                                    target =
                                                                  decide
                                                                    (Graph.WindowCurvature.Safe
                                                                      (windowBarrier.table.counts.leftLength row +
                                                                        windowBarrier.table.counts.rightLength row)
                                                                      (windowBarrierLabel source)
                                                                      (windowBarrierLabel target))) →
                                                              windowRate = windowBarrier.binaryRateFloor →
                                                                (separatedScaleCount : ℕ → ℕ) →
                                                                  (∀ (size : ℕ), separatedScaleCount size ≤ size.log2) →
                                                                    (∀ (size : ℕ),
                                                                        separatedScaleCount size = size.log2) →
                                                                      Graph.FiniteObject.netCapWindowCost threshold
                                                                              dischargeScale windowOrder *
                                                                            threshold <
                                                                          2 * windowRate →
                                                                        (curvatureCost : ℕ) →
                                                                          (curvatureBarrierRow : windowBarrier.Index) →
                                                                            curvatureCost =
                                                                                Core.Finite.CertifiedTableAggregation.binaryRowRateFloor
                                                                                  windowBarrier.table
                                                                                  curvatureBarrierRow →
                                                                              (entropyDenominator : ℕ) →
                                                                                0 < entropyDenominator →
                                                                                  (bridgeMassFactor : ℕ) →
                                                                                    threshold + 2 + dischargeScale ≤
                                                                                        bridgeMassFactor *
                                                                                          dischargeScale →
                                                                                      1 + dischargeScale * threshold +
                                                                                            2 * dischargeScale ≤
                                                                                          bridgeMassFactor *
                                                                                            dischargeScale →
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
      (Graph.SameTokenRoutingGerms.RoutingLabel (Fin self.threshold → Fin self.threshold)
        (Graph.WindowCurvature.Label self.windowOrder))
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

#### `Hypostructure.Graph.Strategy.Spine.Data.three_le_windowOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data), 3 ≤ data.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.Data.threshold`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.Data.threshold_eq_three`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (self : Graph.Strategy.Spine.Data), self.threshold = 3
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

#### `Hypostructure.Graph.Strategy.Spine.DecoratedTypeBAssignedSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.DenseColdCorridorsTerminalStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.DenseDeficiencyBelowStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
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
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) → Finset object.Vertex → object.Vertex → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) →
  {Coordinate : Type u} → Finset Coordinate → Finset (Finset (object.Vertex × object.Vertex)) → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.failedNext`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))}
  (self : Graph.Strategy.Spine.FirstFailedPairExtension object family free),
  ¬2 ^ (family.card + (self.index + 1)) ≤ Graph.skeletonBudget object
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.index`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {Coordinate : Type u} →
    {family : Finset Coordinate} →
      {free : Finset (Finset (object.Vertex × object.Vertex))} →
        Graph.Strategy.Spine.FirstFailedPairExtension object family free → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.index_lt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))}
  (self : Graph.Strategy.Spine.FirstFailedPairExtension object family free), self.index < free.card
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {Coordinate : Type u} →
    {family : Finset Coordinate} →
      {free : Finset (Finset (object.Vertex × object.Vertex))} →
        (index : ℕ) →
          (index_lt : index < free.card) →
            (pair : Finset (object.Vertex × object.Vertex)) →
              pair = free.toList.get ⟨index, ⋯⟩ →
                pair ∈ free →
                  (∀ length ≤ index, 2 ^ (family.card + length) ≤ Graph.skeletonBudget object) →
                    ¬2 ^ (family.card + (index + 1)) ≤ Graph.skeletonBudget object →
                      Graph.Strategy.Spine.FirstFailedPairExtension object family free
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.pair`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {Coordinate : Type u} →
    {family : Finset Coordinate} →
      {free : Finset (Finset (object.Vertex × object.Vertex))} →
        Graph.Strategy.Spine.FirstFailedPairExtension object family free → Finset (object.Vertex × object.Vertex)
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.pair_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))}
  (self : Graph.Strategy.Spine.FirstFailedPairExtension object family free), self.pair = free.toList.get ⟨self.index, ⋯⟩
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.pair_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))}
  (self : Graph.Strategy.Spine.FirstFailedPairExtension object family free), self.pair ∈ free
```

#### `Hypostructure.Graph.Strategy.Spine.FirstFailedPairExtension.realizedThrough`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))}
  (self : Graph.Strategy.Spine.FirstFailedPairExtension object family free),
  ∀ length ≤ self.index, 2 ^ (family.card + length) ≤ Graph.skeletonBudget object
```

#### `Hypostructure.Graph.Strategy.Spine.FreePairCodeUnrealizedStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.FreePairEntropySandwichStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandConfiguration`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object) →
      Graph.CanonicalPiece germ.atom.interface → Graph.TwoStrand.Configuration → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object) →
      Graph.CanonicalPiece germ.atom.interface → Graph.TwoStrand.Configuration → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.attachments_distinct`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.left ≠ self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.boundary_agrees`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config)
  (boundary : germ.atom.interface.Vertex),
  self.embedding (Sum.inl boundary) = germ.atom.pieceIntoAmbient (Sum.inl boundary)
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.embedding`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config →
            germ.atom.interface.Vertex ⊕ representative.toPiece.Internal ↪ object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.firstSegment_internallyDisjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.firstStrand.support.tail.Disjoint self.windowSegment.reverse.support.tail
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.firstSegment_nondegenerate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  1 < self.firstStrand.length ∨ 1 < self.windowSegment.length
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.firstStrand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config) →
            object.graph.Walk self.left self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.firstStrand_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.firstStrand.IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.firstStrand_length`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.firstStrand.length = config.length
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.gap_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  config.gap = (↑(germ.record.offsets 0)).dist ↑(germ.record.offsets 1)
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.gap_lt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  config.gap < data.windowOrder
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.interface_attachments`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  ∃ x y,
    x ≠ y ∧ germ.atom.pieceIntoAmbient (Sum.inl x) = self.left ∧ germ.atom.pieceIntoAmbient (Sum.inl y) = self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.interface_two`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  germ.atom.interface.vertexCount = 2
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.left`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.leftFirst`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.leftFirst_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.leftFirst ∈ object.externalNeighbours self.window self.left
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.leftSecond`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.leftSecond_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.leftSecond ∈ object.externalNeighbours self.window self.left
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.leftStubs_distinct`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.leftFirst ≠ self.leftSecond
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.left_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.left ∈ self.window
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.length_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  config.length = representative.size + 1
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.length_le`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  config.length ≤ Graph.Strategy.Spine.twoStrandEnumerationBound data
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          germ.atom.interface.vertexCount = 2 →
            (embedding : germ.atom.interface.Vertex ⊕ representative.toPiece.Internal ↪ object.Vertex) →
              (∀ (boundary : germ.atom.interface.Vertex),
                  embedding (Sum.inl boundary) = germ.atom.pieceIntoAmbient (Sum.inl boundary)) →
                SimpleGraph.map (⇑embedding) representative.toPiece.graph ≤ object.graph →
                  (∀ (internal : representative.toPiece.Internal), embedding (Sum.inr internal) ∉ germ.support) →
                    config.length = representative.size + 1 →
                      config.length ≤ Graph.Strategy.Spine.twoStrandEnumerationBound data →
                        config.gap = (↑(germ.record.offsets 0)).dist ↑(germ.record.offsets 1) →
                          config.gap < data.windowOrder →
                            (window : Finset object.Vertex) →
                              window ∈ Graph.Strategy.Spine.canonicalColdWindows data object →
                                Graph.Strategy.Spine.AmbientCubicWindow data object window →
                                  (left right : object.Vertex) →
                                    left ∈ window →
                                      right ∈ window →
                                        left ≠ right →
                                          (∃ x y,
                                              x ≠ y ∧
                                                germ.atom.pieceIntoAmbient (Sum.inl x) = left ∧
                                                  germ.atom.pieceIntoAmbient (Sum.inl y) = right) →
                                            (leftFirst leftSecond : object.Vertex) →
                                              leftFirst ∈ object.externalNeighbours window left →
                                                leftSecond ∈ object.externalNeighbours window left →
                                                  leftFirst ≠ leftSecond →
                                                    (rightFirst rightSecond : object.Vertex) →
                                                      rightFirst ∈ object.externalNeighbours window right →
                                                        rightSecond ∈ object.externalNeighbours window right →
                                                          rightFirst ≠ rightSecond →
                                                            (origin :
                                                                Graph.Strategy.Spine.ColdGermOccurrence data object) →
                                                              Graph.Strategy.Spine.ActiveColdGermAtSelectedStubStatement
                                                                  data object germ origin →
                                                                origin.stub ∈
                                                                    Graph.ColdCorridor.selectedStubs object window →
                                                                  origin.stub = (left, leftFirst) ∨
                                                                      origin.stub = (left, leftSecond) ∨
                                                                        origin.stub = (right, rightFirst) ∨
                                                                          origin.stub = (right, rightSecond) →
                                                                    (firstStrand secondStrand windowSegment :
                                                                        object.graph.Walk left right) →
                                                                      firstStrand.IsPath →
                                                                        secondStrand.IsPath →
                                                                          windowSegment.IsPath →
                                                                            firstStrand.support.tail.Disjoint
                                                                                secondStrand.reverse.support.tail →
                                                                              firstStrand.support.tail.Disjoint
                                                                                  windowSegment.reverse.support.tail →
                                                                                secondStrand.support.tail.Disjoint
                                                                                    windowSegment.reverse.support.tail →
                                                                                  1 < firstStrand.length ∨
                                                                                      1 < secondStrand.length →
                                                                                    1 < firstStrand.length ∨
                                                                                        1 < windowSegment.length →
                                                                                      1 < secondStrand.length ∨
                                                                                          1 < windowSegment.length →
                                                                                        firstStrand.length =
                                                                                            config.length →
                                                                                          secondStrand.length =
                                                                                              config.length →
                                                                                            windowSegment.length =
                                                                                                config.gap →
                                                                                              Graph.Strategy.Spine.GenuineSecondStrandWitness
                                                                                                data object germ
                                                                                                representative config
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.origin`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config →
            Graph.Strategy.Spine.ColdGermOccurrence data object
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.origin_active`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  Graph.Strategy.Spine.ActiveColdGermAtSelectedStubStatement data object germ self.origin
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.origin_is_pair_stub`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.origin.stub = (self.left, self.leftFirst) ∨
    self.origin.stub = (self.left, self.leftSecond) ∨
      self.origin.stub = (self.right, self.rightFirst) ∨ self.origin.stub = (self.right, self.rightSecond)
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.origin_mem_window`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.origin.stub ∈ Graph.ColdCorridor.selectedStubs object self.window
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.pair_nondegenerate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  1 < self.firstStrand.length ∨ 1 < self.secondStrand.length
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.representative_internal_outside`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config)
  (internal : representative.toPiece.Internal), self.embedding (Sum.inr internal) ∉ germ.support
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.representative_maps`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  SimpleGraph.map (⇑self.embedding) representative.toPiece.graph ≤ object.graph
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.right`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.rightFirst`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.rightFirst_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.rightFirst ∈ object.externalNeighbours self.window self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.rightSecond`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.rightSecond_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.rightSecond ∈ object.externalNeighbours self.window self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.rightStubs_distinct`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.rightFirst ≠ self.rightSecond
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.right_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.right ∈ self.window
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.secondSegment_internallyDisjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.secondStrand.support.tail.Disjoint self.windowSegment.reverse.support.tail
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.secondSegment_nondegenerate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  1 < self.secondStrand.length ∨ 1 < self.windowSegment.length
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.secondStrand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config) →
            object.graph.Walk self.left self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.secondStrand_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.secondStrand.IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.secondStrand_length`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.secondStrand.length = config.length
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.strands_internallyDisjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.firstStrand.support.tail.Disjoint self.secondStrand.reverse.support.tail
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.window`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.windowSegment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object} →
      {representative : Graph.CanonicalPiece germ.atom.interface} →
        {config : Graph.TwoStrand.Configuration} →
          (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config) →
            object.graph.Walk self.left self.right
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.windowSegment_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.windowSegment.IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.windowSegment_length`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.windowSegment.length = config.gap
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.window_cubic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  Graph.Strategy.Spine.AmbientCubicWindow data object self.window
```

#### `Hypostructure.Graph.Strategy.Spine.GenuineSecondStrandWitness.window_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {germ :
    Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
      (Graph.HasCycleWithLength data.LengthOK) object}
  {representative : Graph.CanonicalPiece germ.atom.interface} {config : Graph.TwoStrand.Configuration}
  (self : Graph.Strategy.Spine.GenuineSecondStrandWitness data object germ representative config),
  self.window ∈ Graph.Strategy.Spine.canonicalColdWindows data object
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

#### `Hypostructure.Graph.Strategy.Spine.IsBlockedSurvivingState`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  data.windowBarrier.Index →
    Option
        (Graph.WindowCurvature.Label data.windowOrder ×
          Graph.WindowCurvature.Label data.windowOrder × Graph.WindowCurvature.Label data.windowOrder) →
      Prop
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

#### `Hypostructure.Graph.Strategy.Spine.Key.absorbedConfigurationResidual`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.blockedPairCodeUnrealized`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.branchDependence`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldFailureDefectRoute`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldGermExtraction`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.coldPositiveGerm`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.cubicBaseline`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.cycleRankConstraint`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.densePackingOverflow`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.entropyCapBound`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.freePairCodeUnrealized`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.pairDemandReturns`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.pairSystemRealizability`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.primitiveCarrierAudit`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.replacementExclusion`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Census`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Key
```

#### `Hypostructure.Graph.Strategy.Spine.Key.route8Deficit`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8ExtractedEntryCensus`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8NoTwoCarrierContradiction`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PeeledDemandResidual`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8PiecesClassified`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8RateFails`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8StageRateFailed`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.route8VisibleExitFourRouting`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.sameCenterOpenPortCompatibility`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.separatedTesters`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.triangularFanCore`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeAVisibleFirstExcess`

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

#### `Hypostructure.Graph.Strategy.Spine.Key.typeBHandoff`

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

#### `Hypostructure.Graph.Strategy.Spine.LargeBudgetResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.NeutralEqualLengthTerminalConfigurationAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object) →
      Graph.CanonicalPiece germ.atom.interface → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.NeutralEqualLengthTerminalConfigurationStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairConditionalFactorizationResidualStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairConditionalFactorizationStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.backward`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {returns : Graph.Strategy.Spine.PairDemandReturns data object} →
      returns.ConnectorRoutes → object.graph.Walk returns.rightDemand.2 returns.leftDemand.1
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.backward_inside`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {returns : Graph.Strategy.Spine.PairDemandReturns data object} (self : returns.ConnectorRoutes),
  ∀ vertex ∈ self.backward.support, vertex ∈ returns.overlap.system.first.failedPairConnector
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.backward_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {returns : Graph.Strategy.Spine.PairDemandReturns data object} (self : returns.ConnectorRoutes), self.backward.IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.forward`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {returns : Graph.Strategy.Spine.PairDemandReturns data object} →
      returns.ConnectorRoutes → object.graph.Walk returns.leftDemand.2 returns.rightDemand.1
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.forward_inside`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {returns : Graph.Strategy.Spine.PairDemandReturns data object} (self : returns.ConnectorRoutes),
  ∀ vertex ∈ self.forward.support, vertex ∈ returns.overlap.system.first.failedPairConnector
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.forward_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {returns : Graph.Strategy.Spine.PairDemandReturns data object} (self : returns.ConnectorRoutes), self.forward.IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.ConnectorRoutes.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {returns : Graph.Strategy.Spine.PairDemandReturns data object} →
      (forward : object.graph.Walk returns.leftDemand.2 returns.rightDemand.1) →
        (backward : object.graph.Walk returns.rightDemand.2 returns.leftDemand.1) →
          forward.IsPath →
            backward.IsPath →
              (∀ vertex ∈ forward.support, vertex ∈ returns.overlap.system.first.failedPairConnector) →
                (∀ vertex ∈ backward.support, vertex ∈ returns.overlap.system.first.failedPairConnector) →
                  returns.ConnectorRoutes
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.connectorRoutes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (returns : Graph.Strategy.Spine.PairDemandReturns data object) → returns.ConnectorRoutes
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.demandEnds_mem_connector`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object),
  returns.leftDemand.1 ∈ returns.overlap.system.first.failedPairConnector ∧
    returns.leftDemand.2 ∈ returns.overlap.system.first.failedPairConnector ∧
      returns.rightDemand.1 ∈ returns.overlap.system.first.failedPairConnector ∧
        returns.rightDemand.2 ∈ returns.overlap.system.first.failedPairConnector
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.demands_ne`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairDemandReturns data object), self.leftDemand ≠ self.rightDemand
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.leftDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → object.Vertex × object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.leftDemand_adj`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object),
  object.graph.Adj returns.leftDemand.1 returns.leftDemand.2
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.leftReturn_length_le`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object),
  (⋯.canonicalPairReturnPath returns.leftDemand ⋯).length ≤ returns.returnBound
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.left_active`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairDemandReturns data object), self.leftDemand ∈ object.excessPorts data.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (overlap : Graph.Strategy.Spine.PairFailureOverlap data object) →
      (leftDemand rightDemand : object.Vertex × object.Vertex) →
        leftDemand ≠ rightDemand →
          overlap.system.first.firstFailure.pair =
              Graph.Strategy.Spine.PairOverlapFirstFailure.demandPair object leftDemand rightDemand →
            (left_active : leftDemand ∈ object.excessPorts data.threshold) →
              (right_active : rightDemand ∈ object.excessPorts data.threshold) →
                (returnBound : ℕ) →
                  returnBound =
                      max (⋯.canonicalPairReturnPath leftDemand left_active).length
                        (⋯.canonicalPairReturnPath rightDemand right_active).length →
                    Graph.Strategy.Spine.PairDemandReturns data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.of`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairFailureOverlap data object → Graph.Strategy.Spine.PairDemandReturns data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.overlap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairDemandReturns data object → Graph.Strategy.Spine.PairFailureOverlap data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.pair_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairDemandReturns data object),
  self.overlap.system.first.firstFailure.pair =
    Graph.Strategy.Spine.PairOverlapFirstFailure.demandPair object self.leftDemand self.rightDemand
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.returnBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.returnBound_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairDemandReturns data object),
  self.returnBound =
    max (⋯.canonicalPairReturnPath self.leftDemand ⋯).length (⋯.canonicalPairReturnPath self.rightDemand ⋯).length
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.returnBound_lt_vertexCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object), returns.returnBound < object.vertexCount
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.rightDemand`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → object.Vertex × object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.rightDemand_adj`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object),
  object.graph.Adj returns.rightDemand.1 returns.rightDemand.2
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.rightReturn_length_le`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (returns : Graph.Strategy.Spine.PairDemandReturns data object),
  (⋯.canonicalPairReturnPath returns.rightDemand ⋯).length ≤ returns.returnBound
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.right_active`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairDemandReturns data object), self.rightDemand ∈ object.excessPorts data.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.PairDemandReturns.systemBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.connected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairFailureOverlap data object),
  Graph.SupportComponents.Connected.ConnectedOn object (self.system.overlapSupport self.family)
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.factorization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairFailureOverlap data object), self.system.ConditionalFactorization
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.family`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairFailureOverlap data object) → Finset ↥self.system.first.pairSet
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.minimal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairFailureOverlap data object), self.system.minimalObstruction self.family
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      (family : Finset ↥system.first.pairSet) →
        system.ConditionalFactorization →
          system.minimalObstruction family →
            (∃ left ∈ family, ∃ right ∈ family, left ≠ right ∧ system.toSkeletonModel.Overlaps left right) →
              Graph.SupportComponents.Connected.ConnectedOn object (system.overlapSupport family) →
                Graph.Strategy.Spine.PairFailureOverlap data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.overlapWitness`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairFailureOverlap data object),
  ∃ left ∈ self.family, ∃ right ∈ self.family, left ≠ right ∧ self.system.toSkeletonModel.Overlaps left right
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlap.system`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairFailureOverlap data object → Graph.Strategy.Spine.PairOverlapSystem data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairFailureOverlapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementCoveredStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementEarlyOutcome.sparseExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
        data.LengthOK object →
      Graph.Strategy.Spine.PairIncrementEarlyOutcome data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementEarlyOutcome.typeB`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.TypeBFanEntryStatement data object → Graph.Strategy.Spine.PairIncrementEarlyOutcome data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementEarlyOutcomeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairSerialDemandSystem data object → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementOutcome.arithmetic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → Graph.Strategy.Spine.PairIncrementOutcome serial
```

#### `Hypostructure.Graph.Strategy.Spine.PairIncrementOutcome.early`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairIncrementEarlyOutcome data object → Graph.Strategy.Spine.PairIncrementOutcome serial
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.Coordinate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapFirstFailure data object → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.active`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
    data.LengthOK object data.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.baselineFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object) → Finset self.Coordinate
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.baselineRealization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object) →
      Graph.BaselineCodeRealization object self.baselineFamily
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.coordinateSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object) → self.Coordinate → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.demandPair`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(object : Graph.FiniteObject) →
  object.Vertex × object.Vertex → object.Vertex × object.Vertex → Finset (object.Vertex × object.Vertex)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.exists_failedPair_demands`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (first : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  ∃ left right,
    left ≠ right ∧ first.firstFailure.pair = Graph.Strategy.Spine.PairOverlapFirstFailure.demandPair object left right
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.failedPairConnector`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapFirstFailure data object → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.failedPairConnector_connectedOn`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (first : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  Graph.SupportComponents.Connected.ConnectedOn object first.failedPairConnector
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.failedPair_card`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (first : Graph.Strategy.Spine.PairOverlapFirstFailure data object), first.firstFailure.pair.card = 2
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.failedPair_mem_portPairSchedule`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (first : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  first.firstFailure.pair ∈ object.portPairSchedule data.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.firstFailure`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object) →
      Graph.Strategy.Spine.FirstFailedPairExtension object self.baselineFamily self.pairSet
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (active :
        Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
          data.LengthOK object data.threshold) →
      (Coordinate : Type u) →
        (baselineFamily : Finset Coordinate) →
          (Coordinate → Finset object.Vertex) →
            Graph.BaselineCodeRealization object baselineFamily →
              (pairSet : Finset (Finset (object.Vertex × object.Vertex))) →
                pairSet.Nonempty →
                  pairSet ⊆ object.portPairSchedule data.threshold →
                    (∀ pair ∈ pairSet,
                        ¬Graph.SparsePairDEProfileObstructionAt (Graph.pairResponseActivation active)
                              (object.portPairSchedule data.threshold) pair ∧
                          ¬Graph.SparsePairDEResponseObstructionAt (Graph.pairResponseActivation active)
                              (object.portPairSchedule data.threshold) pair) →
                      (firstFailure : Graph.Strategy.Spine.FirstFailedPairExtension object baselineFamily pairSet) →
                        (responseSupport : Finset object.Vertex) →
                          (Graph.pairResponseActivation active).pairSupport firstFailure.pair = some responseSupport →
                            (Graph.pairResponseActivation active).pairSeed firstFailure.pair ⊆ responseSupport →
                              Graph.SupportComponents.Connected.ConnectedOn object responseSupport →
                                Graph.Strategy.Spine.PairOverlapFirstFailure data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.of`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (active :
        Graph.ActiveSurplusDemands (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
          data.LengthOK object data.threshold) →
      (Coordinate : Type u) →
        (baselineFamily : Finset Coordinate) →
          (Coordinate → Finset object.Vertex) →
            Graph.BaselineCodeRealization object baselineFamily →
              (pairSet : Finset (Finset (object.Vertex × object.Vertex))) →
                pairSet.Nonempty →
                  pairSet ⊆ object.portPairSchedule data.threshold →
                    (∀ pair ∈ pairSet,
                        ¬Graph.SparsePairDEProfileObstructionAt (Graph.pairResponseActivation active)
                              (object.portPairSchedule data.threshold) pair ∧
                          ¬Graph.SparsePairDEResponseObstructionAt (Graph.pairResponseActivation active)
                              (object.portPairSchedule data.threshold) pair) →
                      Graph.Strategy.Spine.FirstFailedPairExtension object baselineFamily pairSet →
                        object.graph.Connected → Graph.Strategy.Spine.PairOverlapFirstFailure data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.pairSeed_subset_responseSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  (Graph.pairResponseActivation ⋯).pairSeed self.firstFailure.pair ⊆ self.responseSupport
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.pairSet`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairOverlapFirstFailure data object → Finset (Finset (object.Vertex × object.Vertex))
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.pairSet_blockerFree`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  ∀ pair ∈ self.pairSet,
    ¬Graph.SparsePairDEProfileObstructionAt (Graph.pairResponseActivation ⋯) (object.portPairSchedule data.threshold)
          pair ∧
      ¬Graph.SparsePairDEResponseObstructionAt (Graph.pairResponseActivation ⋯) (object.portPairSchedule data.threshold)
          pair
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.pairSet_nonempty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object), self.pairSet.Nonempty
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.pairSet_subset_schedule`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  self.pairSet ⊆ object.portPairSchedule data.threshold
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.portReturns`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapFirstFailure data object → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.responseSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapFirstFailure data object → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.responseSupport_connected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  Graph.SupportComponents.Connected.ConnectedOn object self.responseSupport
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailure.responseSupport_selected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapFirstFailure data object),
  (Graph.pairResponseActivation ⋯).pairSupport self.firstFailure.pair = some self.responseSupport
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapFirstFailureStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.ConditionalFactorization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapSystem data object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.PairwiseSeparated`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥system.first.pairSet → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.Skeleton`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairOverlapSystem data object → Type
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.conditionalFibre`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → system.Skeleton → Set system.Skeleton
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.conditionalValues`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      (family : Finset ↥system.first.pairSet) →
        Fin family.card ≃ ↥family →
          system.Skeleton → Fin family.card → Set (Graph.Strategy.Spine.PairResponseState data)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.failedFamily`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥self.first.pairSet
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.failedFamily_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object),
  self.failedFamily = {pair | self.rank pair < self.first.firstFailure.index + 1}
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.failedFamily_nonempty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object), self.failedFamily.Nonempty
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.failedFamily_obstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object),
  let model :=
    { BaseCoordinate := self.first.Coordinate, baselineFamily := self.first.baselineFamily,
      baseline := self.first.baselineRealization, pairSet := self.first.pairSet, pairSet_nonempty := ⋯,
      pairSet_subset_schedule := ⋯, responseSupport := self.responseSupport, responseSupport_selected := ⋯,
      responseSupport_connected := ⋯ };
  self.failedFamily.Nonempty ∧ ¬model.RealizingOrder self.failedFamily
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.familyUnion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      Finset ↥system.first.pairSet → Finset ↥system.first.pairSet → Finset ↥system.first.pairSet
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.fibreValues`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      Finset ↥system.first.pairSet →
        system.Skeleton → ↥system.first.pairSet → Set (Graph.Strategy.Spine.PairResponseState data)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.first`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairOverlapSystem data object → Graph.Strategy.Spine.PairOverlapFirstFailure data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.minimalObstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥system.first.pairSet → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (first : Graph.Strategy.Spine.PairOverlapFirstFailure data object) →
      (responseSupport : ↥first.pairSet → Finset object.Vertex) →
        (responseSupport_selected :
            ∀ (pair : ↥first.pairSet),
              (Graph.pairResponseActivation ⋯).pairSupport ↑pair = some (responseSupport pair)) →
          (responseSupport_connected :
              ∀ (pair : ↥first.pairSet), Graph.SupportComponents.Connected.ConnectedOn object (responseSupport pair)) →
            (rank : ↥first.pairSet → ℕ) →
              Function.Injective rank →
                (failedFamily : Finset ↥first.pairSet) →
                  failedFamily = {pair | rank pair < first.firstFailure.index + 1} →
                    failedFamily.Nonempty →
                      (let model :=
                          { BaseCoordinate := first.Coordinate, baselineFamily := first.baselineFamily,
                            baseline := first.baselineRealization, pairSet := first.pairSet, pairSet_nonempty := ⋯,
                            pairSet_subset_schedule := ⋯, responseSupport := responseSupport,
                            responseSupport_selected := responseSupport_selected,
                            responseSupport_connected := responseSupport_connected };
                        failedFamily.Nonempty ∧ ¬model.RealizingOrder failedFamily) →
                        Graph.Strategy.Spine.PairOverlapSystem data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.obstruction`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥system.first.pairSet → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.outsideCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      system.Skeleton → Finset (Sym2 (Fin object.vertexCount)) × (↥system.toSkeletonModel.baselineFamily → Bool)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.overlapSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥system.first.pairSet → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.overlaps`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → ↥system.first.pairSet → ↥system.first.pairSet → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.rank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → (self : Graph.Strategy.Spine.PairOverlapSystem data object) → ↥self.first.pairSet → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.rank_injective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object), Function.Injective self.rank
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.realizingOrder`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) → Finset ↥system.first.pairSet → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.refinedFibre`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      Finset ↥system.first.pairSet → system.Skeleton → Set system.Skeleton
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.response`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      system.Skeleton → ↥system.first.pairSet → Graph.Strategy.Spine.PairResponseState data
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.responseSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairOverlapSystem data object) → ↥self.first.pairSet → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.responseSupport_connected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object) (pair : ↥self.first.pairSet),
  Graph.SupportComponents.Connected.ConnectedOn object (self.responseSupport pair)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.responseSupport_selected`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairOverlapSystem data object) (pair : ↥self.first.pairSet),
  (Graph.pairResponseActivation ⋯).pairSupport ↑pair = some (self.responseSupport pair)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystem.toSkeletonModel`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      Graph.SparsePairSkeletonModel (Graph.pairResponseActivation ⋯) (object.portPairSchedule data.threshold)
```

#### `Hypostructure.Graph.Strategy.Spine.PairOverlapSystemStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairPowerOfTwoCycleStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairResponseState`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Type (u_1 + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairSerialDemandSystem data object → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.base`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → Fin serial.cells → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.base_mem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial) (index : Fin serial.cells),
  self.base index ∈ serial.lengths index
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.criterion`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial), self.modulus - (self.smear + 1) < orderOf 2
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.frequent`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → Finset (Fin serial.cells)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.increment`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial),
  ∀ index ∈ self.frequent, self.base index + self.modulus ∈ serial.lengths index
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      (base : Fin serial.cells → ℕ) →
        (base_mem : ∀ (index : Fin serial.cells), base index ∈ serial.lengths index) →
          (modulus : ℕ) →
            (modulus_neZero : NeZero modulus) →
              (frequent : Finset (Fin serial.cells)) →
                (increment : ∀ index ∈ frequent, base index + modulus ∈ serial.lengths index) →
                  (smear : ℕ) →
                    (offsets : ∀ residue ≤ smear, residue ∈ serial.offsets) →
                      smear + 1 ≤ modulus →
                        modulus - (smear + 1) < orderOf 2 →
                          (let spectrum :=
                              serial.toSystem.spectrum base base_mem modulus frequent increment smear offsets;
                            spectrum.ScaleSpanning) →
                            Graph.Strategy.Spine.PairSerialArithmetic serial
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.modulus`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.modulus_neZero`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial), NeZero self.modulus
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.offsets`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial), ∀ residue ≤ self.smear, residue ∈ serial.offsets
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.smear`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.spanning`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial),
  let spectrum := serial.toSystem.spectrum self.base ⋯ self.modulus self.frequent ⋯ self.smear ⋯;
  spectrum.ScaleSpanning
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.spectrum`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object} →
      Graph.Strategy.Spine.PairSerialArithmetic serial → Graph.SerialSystem.Spectrum
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmetic.wide`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  {serial : Graph.Strategy.Spine.PairSerialDemandSystem data object}
  (self : Graph.Strategy.Spine.PairSerialArithmetic serial), self.smear + 1 ≤ self.modulus
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialArithmeticStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.FiniteObject → ℕ → Type u
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle.isCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {length : ℕ} (self : Graph.Strategy.Spine.PairSerialCycle object length),
  self.walk.IsCycle
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle.length_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {length : ℕ} (self : Graph.Strategy.Spine.PairSerialCycle object length),
  self.walk.length = length
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {length : ℕ} →
    (vertex : object.Vertex) →
      (walk : object.graph.Walk vertex vertex) →
        walk.IsCycle → walk.length = length → Graph.Strategy.Spine.PairSerialCycle object length
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle.vertex`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} → {length : ℕ} → Graph.Strategy.Spine.PairSerialCycle object length → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialCycle.walk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {length : ℕ} → (self : Graph.Strategy.Spine.PairSerialCycle object length) → object.graph.Walk self.vertex self.vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.cell_internal_disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells) (left : ℕ)
  (leftMem : left ∈ self.lengths index) (right : ℕ) (rightMem : right ∈ self.lengths index),
  left ≠ right →
    ∀ vertex ∈ (self.piece index left leftMem).support,
      vertex ∈ (self.piece index right rightMem).support →
        vertex = self.interfaces index.castSucc ∨ vertex = self.interfaces index.succ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.cells`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairSerialDemandSystem data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.cells_internal_disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (leftIndex rightIndex : Fin self.cells),
  leftIndex ≠ rightIndex →
    ∀ (left : ℕ) (leftMem : left ∈ self.lengths leftIndex) (right : ℕ) (rightMem : right ∈ self.lengths rightIndex),
      ∀ vertex ∈ (self.piece leftIndex left leftMem).support,
        vertex ∈ (self.piece rightIndex right rightMem).support →
          (vertex = self.interfaces leftIndex.castSucc ∨ vertex = self.interfaces leftIndex.succ) ∧
            (vertex = self.interfaces rightIndex.castSucc ∨ vertex = self.interfaces rightIndex.succ)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.cells_pos`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object), 0 < self.cells
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.closing`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairSerialDemandSystem data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.closing_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object), self.closing = self.routes.backward.length + 2
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.closing_internal_disjoint`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells) (length : ℕ)
  (member : length ∈ self.lengths index),
  ∀ vertex ∈ self.routes.backward.support, vertex ∈ (self.piece index length member).support → False
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.end_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object),
  self.interfaces (Fin.last self.cells) = self.returns.rightDemand.1
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.increments_bounded`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells),
  ∀ left ∈ self.lengths index, ∀ right ∈ self.lengths index, left.dist right ≤ self.returns.systemBound
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.interfaces`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) → Fin (self.cells + 1) → object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.lengths`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) → Fin self.cells → Finset ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.lengths_nonempty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells),
  (self.lengths index).Nonempty
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (returns : Graph.Strategy.Spine.PairDemandReturns data object) →
      (cells : ℕ) →
        0 < cells →
          (interfaces : Fin (cells + 1) → object.Vertex) →
            (lengths : Fin cells → Finset ℕ) →
              (∀ (index : Fin cells), (lengths index).Nonempty) →
                (piece :
                    (index : Fin cells) →
                      (length : ℕ) →
                        length ∈ lengths index →
                          object.graph.Walk (interfaces index.castSucc) (interfaces index.succ)) →
                  (∀ (index : Fin cells) (length : ℕ) (member : length ∈ lengths index),
                      (piece index length member).IsPath) →
                    (∀ (index : Fin cells) (length : ℕ) (member : length ∈ lengths index),
                        (piece index length member).length = length) →
                      (∀ (index : Fin cells) (length : ℕ) (member : length ∈ lengths index),
                          ∀ vertex ∈ (piece index length member).support,
                            vertex ∈ returns.overlap.system.overlapSupport returns.overlap.family) →
                        (∀ (index : Fin cells) (left : ℕ) (leftMem : left ∈ lengths index) (right : ℕ)
                            (rightMem : right ∈ lengths index),
                            left ≠ right →
                              ∀ vertex ∈ (piece index left leftMem).support,
                                vertex ∈ (piece index right rightMem).support →
                                  vertex = interfaces index.castSucc ∨ vertex = interfaces index.succ) →
                          (∀ (leftIndex rightIndex : Fin cells),
                              leftIndex ≠ rightIndex →
                                ∀ (left : ℕ) (leftMem : left ∈ lengths leftIndex) (right : ℕ)
                                  (rightMem : right ∈ lengths rightIndex),
                                  ∀ vertex ∈ (piece leftIndex left leftMem).support,
                                    vertex ∈ (piece rightIndex right rightMem).support →
                                      (vertex = interfaces leftIndex.castSucc ∨ vertex = interfaces leftIndex.succ) ∧
                                        (vertex = interfaces rightIndex.castSucc ∨
                                          vertex = interfaces rightIndex.succ)) →
                            (routes : returns.ConnectorRoutes) →
                              interfaces ⟨0, ⋯⟩ = returns.leftDemand.2 →
                                interfaces (Fin.last cells) = returns.rightDemand.1 →
                                  (closing : ℕ) →
                                    closing = routes.backward.length + 2 →
                                      (∀ (index : Fin cells) (length : ℕ) (member : length ∈ lengths index),
                                          ∀ vertex ∈ routes.backward.support,
                                            vertex ∈ (piece index length member).support → False) →
                                        (offsets : Finset ℕ) →
                                          offsets.Nonempty →
                                            (∀ (index : Fin cells),
                                                ∀ left ∈ lengths index,
                                                  ∀ right ∈ lengths index, left.dist right ≤ returns.systemBound) →
                                              (∀ (choice : Fin cells → ℕ),
                                                  (∀ (index : Fin cells), choice index ∈ lengths index) →
                                                    ∀ offset ∈ offsets,
                                                      Graph.Strategy.Spine.PairSerialRealized object
                                                        (closing + ∑ index, choice index + offset)) →
                                                Graph.Strategy.Spine.PairSerialDemandSystem data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.offsets`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairSerialDemandSystem data object → Finset ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.offsets_nonempty`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object), self.offsets.Nonempty
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.piece`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) →
      (index : Fin self.cells) →
        (length : ℕ) →
          length ∈ self.lengths index → object.graph.Walk (self.interfaces index.castSucc) (self.interfaces index.succ)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.piece_inside`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells) (length : ℕ)
  (member : length ∈ self.lengths index),
  ∀ vertex ∈ (self.piece index length member).support,
    vertex ∈ self.returns.overlap.system.overlapSupport self.returns.overlap.family
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.piece_isPath`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells) (length : ℕ)
  (member : length ∈ self.lengths index), (self.piece index length member).IsPath
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.piece_length`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (index : Fin self.cells) (length : ℕ)
  (member : length ∈ self.lengths index), (self.piece index length member).length = length
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.realized_route`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) (choice : Fin self.cells → ℕ),
  (∀ (index : Fin self.cells), choice index ∈ self.lengths index) →
    ∀ offset ∈ self.offsets,
      Graph.Strategy.Spine.PairSerialRealized object (self.closing + ∑ index, choice index + offset)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.returns`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.PairSerialDemandSystem data object → Graph.Strategy.Spine.PairDemandReturns data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.routes`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (self : Graph.Strategy.Spine.PairSerialDemandSystem data object) → self.returns.ConnectorRoutes
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.start_eq`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject}
  (self : Graph.Strategy.Spine.PairSerialDemandSystem data object), self.interfaces ⟨0, ⋯⟩ = self.returns.leftDemand.2
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystem.toSystem`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (serial : Graph.Strategy.Spine.PairSerialDemandSystem data object) → Graph.SerialSystem.System serial.cells
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialDemandSystemStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairSerialRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.FiniteObject → ℕ → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemEarlyOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemEarlyOutcome.sparseExit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.SparseSurplusExit (Graph.MinimumDegreeAtLeast data.threshold) (Graph.HasCycleWithLength data.LengthOK)
        data.LengthOK object →
      Graph.Strategy.Spine.PairSystemEarlyOutcome data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemEarlyOutcome.targetCycle`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.HasCycleWithLength data.LengthOK object → Graph.Strategy.Spine.PairSystemEarlyOutcome data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemEarlyOutcome.typeB`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    Graph.Strategy.Spine.TypeBFanEntryStatement data object → Graph.Strategy.Spine.PairSystemEarlyOutcome data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemEarlyOutcomeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemRealizabilityOutcome`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} → Graph.Strategy.Spine.PairDemandReturns data object → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemRealizabilityOutcome.early`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {returns : Graph.Strategy.Spine.PairDemandReturns data object} →
      Graph.Strategy.Spine.PairSystemEarlyOutcome data object →
        Graph.Strategy.Spine.PairSystemRealizabilityOutcome returns
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemRealizabilityOutcome.serial`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    {returns : Graph.Strategy.Spine.PairDemandReturns data object} →
      (system : Graph.Strategy.Spine.PairSerialDemandSystem data object) →
        system.returns = returns → Graph.Strategy.Spine.PairSystemRealizabilityOutcome returns
```

#### `Hypostructure.Graph.Strategy.Spine.PairSystemRealizabilityStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.PairUncoveredResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type (u + 1)
```

#### `Hypostructure.Graph.Strategy.Spine.PairUncoveredResidual.factorization`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (system : Graph.Strategy.Spine.PairOverlapSystem data object) →
      ¬system.ConditionalFactorization → Graph.Strategy.Spine.PairUncoveredResidual data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairUncoveredResidual.incrementArithmetic`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (serial : Graph.Strategy.Spine.PairSerialDemandSystem data object) →
      ¬Nonempty (Graph.Strategy.Spine.PairIncrementOutcome serial) →
        Graph.Strategy.Spine.PairUncoveredResidual data object
```

#### `Hypostructure.Graph.Strategy.Spine.PairUncoveredResidual.systemRealizability`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{data : Graph.Strategy.Spine.Data} →
  {object : Graph.FiniteObject} →
    (returns : Graph.Strategy.Spine.PairDemandReturns data object) →
      ¬Nonempty (Graph.Strategy.Spine.PairSystemRealizabilityOutcome returns) →
        Graph.Strategy.Spine.PairUncoveredResidual data object
```

#### `Hypostructure.Graph.Strategy.Spine.RefinedLexicographicallySmaller`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.FiniteObject → Graph.FiniteObject → Prop
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

#### `Hypostructure.Graph.Strategy.Spine.Route8CarrierCutParity`

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

#### `Hypostructure.Graph.Strategy.Spine.Route8DemandAbsorptionStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8ExtractedEntryCensusFact`

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

#### `Hypostructure.Graph.Strategy.Spine.Route8NoSmallCoreEntry`

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

#### `Hypostructure.Graph.Strategy.Spine.Route8PeeledDemandResidualStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.Route8QuotientFreeStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.Route8SmallCoreEntry`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8StageRateFailedFact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8Survives`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    (packing : Finset (Finset object.Vertex)) →
      Graph.SupportComponents.Connected.Component object (object.remainderSupport packing) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8TerminalNoGo`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8TrueResidual`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8UnifiedDeficitFact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8UnifiedEntryCensusFact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8UnifiedEntryFacts`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Graph.Route8Census.Index object → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8UnifiedNegative`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.Route8WindowBlockersStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SameCenterOpenPortCompatibilityStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SameTokenTypeBHandoffEnvelopeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SameTokenTypeBHandoffStatement`

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

#### `Hypostructure.Graph.Strategy.Spine.SelectionMinimality`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `inductive`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(Graph.FiniteObject → Type v) →
  (Presentation : Type) → Presentation → Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.SelectionMinimality.mk`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `constructor`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  (∀ (smaller : Graph.FiniteObject),
      (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
        Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
    (∀ (smaller : Graph.FiniteObject),
        (Graph.Strategy.Spine.refinedProgress BranchState Presentation presentation data).Smaller smaller object →
          Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller) →
      Graph.Strategy.Spine.SelectionMinimality BranchState Presentation presentation data object
```

#### `Hypostructure.Graph.Strategy.Spine.SelectionMinimality.refinedMinimal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.SelectionMinimality BranchState Presentation presentation data object →
    ∀ (smaller : Graph.FiniteObject),
      (Graph.Strategy.Spine.refinedProgress BranchState Presentation presentation data).Smaller smaller object →
        Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller
```

#### `Hypostructure.Graph.Strategy.Spine.SelectionMinimality.sizeMinimal`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {BranchState : Graph.FiniteObject → Type v} {Presentation : Type} {presentation : Presentation}
  {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject},
  Graph.Strategy.Spine.SelectionMinimality BranchState Presentation presentation data object →
    ∀ (smaller : Graph.FiniteObject),
      (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
        Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller
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

#### `Hypostructure.Graph.Strategy.Spine.TriangularFanCoreStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TwoStrandSurvivorStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeAExitFourFiniteDescentFact`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBAssignedCentres`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Finset object.Vertex → Finset object.Vertex → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBAssignedCentres.centres_subset`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject) {packing : Finset (Finset object.Vertex)}
  {piece centres : Finset object.Vertex},
  Graph.Strategy.Spine.TypeBAssignedCentres data object packing piece centres →
    Graph.TypeBRefinedSupport.centres object data.threshold piece ⊆ centres
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBAssignedCentres.high`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject) {packing : Finset (Finset object.Vertex)}
  {piece centres : Finset object.Vertex},
  Graph.Strategy.Spine.TypeBAssignedCentres data object packing piece centres →
    ∀ centre ∈ centres, Graph.IsHighCentre object data.threshold centre
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBB2ChoiceStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBB2ObstructionStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanCertificateCapStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanCertificateMarkedStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanCertificateResidualMassStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanCertificateResidualStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanDegreeFourCentresStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanDegreeFourProfileStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanDirectCycleFreeStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanDirectCycleStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanEntryStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanHeavyCentreStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanHybridEntryStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanLocalDichotomyStatement`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBFanSupportWith`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) →
    (Finset (Finset object.Vertex) → Finset object.Vertex → Finset object.Vertex → Prop) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBSublinearHypotheses`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.TypeBSupportWith`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data →
  (object : Graph.FiniteObject) → (Finset (Finset object.Vertex) → Finset object.Vertex → Prop) → Prop
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

#### `Hypostructure.Graph.Strategy.Spine.WindowFamilyRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Prop
```

#### `Hypostructure.Graph.Strategy.Spine.WindowFamilyRealized.mono`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {data : Graph.Strategy.Spine.Data} {object : Graph.FiniteObject} {smaller larger : Finset (Finset object.Vertex)},
  smaller ⊆ larger →
    Graph.Strategy.Spine.WindowFamilyRealized data object larger →
      Graph.Strategy.Spine.WindowFamilyRealized data object smaller
```

#### `Hypostructure.Graph.Strategy.Spine.WindowPackageRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → Prop
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.absorbedConfigurationResidualRow`

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
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.degreeProfileFibres)
                      known] →
                  [Core.Residual.FactKeys.Has
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.targetCompleteContextUniversality) known] →
                    [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.maximalPacking)
                          known] →
                      Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.atomCompression ∉ known →
                        Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.delocalizedSupport ∉ known →
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBDirectCycleFree)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBB2Choice ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBOverlapObstruction ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBB2Choice)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBOverlapObstruction) previous
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
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.barrierLegs`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) → data.windowBarrier.Index → ℕ × ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedAprioriBarrierCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.blockedAprioriClassAt data object →
      Finset (Sym2 (Fin object.vertexCount)) ×
        (Graph.Strategy.Spine.blockedCoordinate data object →
          Option
            (Graph.WindowCurvature.Label data.windowOrder ×
              Graph.WindowCurvature.Label data.windowOrder × Graph.WindowCurvature.Label data.windowOrder))
```

#### `Hypostructure.Graph.Strategy.Spine.blockedAprioriClassAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type
```

#### `Hypostructure.Graph.Strategy.Spine.blockedAprioriCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedAprioriCountAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) → data.windowBarrier.Index → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedBarrierCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.blockedClassAt data object →
      Finset (Sym2 (Fin object.vertexCount)) ×
        (Graph.Strategy.Spine.blockedCoordinate data object →
          Option
            (Graph.WindowCurvature.Label data.windowOrder ×
              Graph.WindowCurvature.Label data.windowOrder × Graph.WindowCurvature.Label data.windowOrder))
```

#### `Hypostructure.Graph.Strategy.Spine.blockedClassAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type
```

#### `Hypostructure.Graph.Strategy.Spine.blockedCoordinate`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → Type
```

#### `Hypostructure.Graph.Strategy.Spine.blockedEncodingRank`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Graph.Strategy.Spine.blockedCoordinate data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedEncodingRank_injective`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject),
  Function.Injective (Graph.Strategy.Spine.blockedEncodingRank data object)
```

#### `Hypostructure.Graph.Strategy.Spine.blockedSurvivingCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedSurvivingCountAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) → data.windowBarrier.Index → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.blockedWindowLabels`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset (Fin object.vertexCount))
```

### `Hypostructure.Graph.Strategy.SpineRows`

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

#### `Hypostructure.Graph.Strategy.Spine.bridgelessRow`

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

#### `Hypostructure.Graph.Strategy.Spine.canonicalDecompositionCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.FiniteObject → Graph.Strategy.Spine.CanonicalDecompositionCode
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

#### `Hypostructure.Graph.Strategy.Spine.coldAmbientCubicSupport`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.coldCorridorWindows`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.coldCrossWindowHalfEdgeFintype`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Fintype (Graph.Strategy.Spine.ColdCrossWindowHalfEdge data object)
```

#### `Hypostructure.Graph.Strategy.Spine.coldEligibleHalfEdgeFintype`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Fintype (Graph.Strategy.Spine.ColdEligibleHalfEdge data object)
```

#### `Hypostructure.Graph.Strategy.Spine.coldExternalStubCount`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.coldInteriorBranchExcess`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrenceComponentAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object → Finset object.Vertex
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrenceCorridorAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (occurrence : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object) →
      (epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object) →
        Graph.ColdCorridor.Corridor object (Graph.Strategy.Spine.coldCorridorWindows data object)
          (Classical.choose ⋯ epsilon)
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrenceIncidence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object →
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrenceIndexAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    (occurrence : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object) →
      (epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object) →
        (Classical.choose ⋯ epsilon).Segment → (Classical.choose ⋯ epsilon).Segment
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrencePresentationAt`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object → Graph.ColdCorridor.Presentation data.coldSignature object
```

#### `Hypostructure.Graph.Strategy.Spine.coldOccurrenceStateFacts`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject)
  (occurrence : Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object)
  (epsilon : Graph.Strategy.Spine.ColdEligibleHalfEdge data object),
  have germ := Classical.choose ⋯ epsilon;
  have component := Classical.choose ⋯ epsilon;
  let corridor := Classical.choose ⋯ epsilon;
  let presentation := Classical.choose ⋯ epsilon;
  have index := Classical.choose ⋯ epsilon;
  Graph.ColdCorridor.IsOutsideComponent object (Graph.Strategy.Spine.coldCorridorWindows data object) component ∧
    corridor.entryStub = ((↑epsilon).2, (↑epsilon).1) ∧
      Function.Injective index ∧
        Graph.ColdCorridor.Corridor.FirstFailureGermWitness ⋯ ⋯ corridor presentation index germ
```

#### `Hypostructure.Graph.Strategy.Spine.coldRoutedCandidates`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      Finset (Graph.Strategy.Spine.ColdGermOccurrence data object)
```

#### `Hypostructure.Graph.Strategy.Spine.coldRoutedClassified`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      Graph.Strategy.Spine.ColdFirstFailureOccurrenceData data object
```

#### `Hypostructure.Graph.Strategy.Spine.coldRoutedCrossIncidence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      Graph.Strategy.Spine.ColdCrossWindowHalfEdge data object →
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
```

#### `Hypostructure.Graph.Strategy.Spine.coldRoutedOccurrenceIncidence`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      Graph.Strategy.Spine.ColdGermOccurrence data object →
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object
```

#### `Hypostructure.Graph.Strategy.Spine.coldRoutedTraceEnd`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Graph.Strategy.Spine.ColdFailureRoutingStatement data object →
      Graph.Strategy.Spine.ColdEligibleHalfEdge data object → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.coldSelectedHalfEdgeFintype`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) → Fintype (Graph.Strategy.Spine.ColdSelectedHalfEdge data object)
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
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextDefect)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.contextUniversal) previous
```

#### `Hypostructure.Graph.Strategy.Spine.cubicBaselineRow`

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
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureRankDrop ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.curvatureFullRank ∉ known →
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
      {data : Graph.Strategy.Spine.Data} →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.cycleRankConstraintRow`

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

#### `Hypostructure.Graph.Strategy.Spine.degreeProfileFibresRow`

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
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.properDelocalization ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.globalDelocalization ∉ known →
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

#### `Hypostructure.Graph.Strategy.Spine.denseNetDeficiencyCapRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.fanCertificateMarked)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBDirectCycle ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBDirectCycleFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBDirectCycle)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBDirectCycleFree) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyPackageDemand)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapActive ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.largeBudgetResidual ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.entropyCapActive)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.largeBudgetResidual) previous
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
      (data : Graph.Strategy.Spine.Data) →
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

#### `Hypostructure.Graph.Strategy.Spine.exactCollisionDichotomy`

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
              Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeCap ∉ known →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.exactCollisionFails ∉ known →
                  Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeCap)
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.exactCollisionFails) previous
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.exists_maximal_windowFamilyRealized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (data : Graph.Strategy.Spine.Data) (object : Graph.FiniteObject),
  ∃ hot ⊆ Graph.Strategy.Spine.canonicalWindowPacking data object,
    (Graph.Strategy.Spine.WindowFamilyRealized data object hot ∨
        hot = ∅ ∧ ¬Graph.Strategy.Spine.WindowFamilyRealized data object ∅) ∧
      ∀ other ⊆ Graph.Strategy.Spine.canonicalWindowPacking data object,
        Graph.Strategy.Spine.WindowFamilyRealized data object other → other.card ≤ hot.card
```

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

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.firstFailedPairExtensionOf`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
{object : Graph.FiniteObject} →
  {Coordinate : Type u} →
    {family : Finset Coordinate} →
      {free : Finset (Finset (object.Vertex × object.Vertex))} →
        Graph.BaselineCodeRealization object family →
          ¬2 ^ (family.card + free.card) ≤ Graph.skeletonBudget object →
            Graph.Strategy.Spine.FirstFailedPairExtension object family free
```

### `Hypostructure.Graph.Strategy.SpineRows`

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
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
```

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.freeSide_nonempty_of_baseline_realized`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ {object : Graph.FiniteObject} {Coordinate : Type u} {family : Finset Coordinate}
  {free : Finset (Finset (object.Vertex × object.Vertex))} (realization : Graph.BaselineCodeRealization object family),
  ¬2 ^ (family.card + free.card) ≤ Graph.skeletonBudget object → free.Nonempty
```

#### `Hypostructure.Graph.Strategy.Spine.germCanonicalRepresentative`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  {object : Graph.FiniteObject} →
    (germ :
        Graph.ColdCorridor.BoundedGerm data.coldSignature (Graph.MinimumDegreeAtLeast data.threshold)
          (Graph.HasCycleWithLength data.LengthOK) object) →
      Graph.CanonicalPiece germ.atom.interface
```

### `Hypostructure.Graph.Strategy.SpineRows`

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
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → object.Vertex → Prop
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
      {data : Graph.Strategy.Spine.Data} →
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
Graph.Strategy.Spine.Data → Graph.FiniteObject → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.liveHotBarrierCapRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.maximalPacking) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNonNegative ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNegative ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNonNegative)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.netChargeNegative) previous
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
      (data : Graph.Strategy.Spine.Data) →
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
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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

#### `Hypostructure.Graph.Strategy.Spine.refinedProgress`

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

#### `Hypostructure.Graph.Strategy.Spine.refinedProgress_smaller_iff`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (BranchState : Graph.FiniteObject → Type v) (Presentation : Type) (presentation : Presentation)
  (data : Graph.Strategy.Spine.Data) {smaller larger : Graph.FiniteObject},
  (Graph.Strategy.Spine.refinedProgress BranchState Presentation presentation data).Smaller smaller larger ↔
    Graph.Strategy.Spine.RefinedLexicographicallySmaller smaller larger
```

#### `Hypostructure.Graph.Strategy.Spine.refinedProgress_smaller_of_size_smaller`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
∀ (BranchState : Graph.FiniteObject → Type v) (Presentation : Type) (presentation : Presentation)
  (data : Graph.Strategy.Spine.Data) {smaller larger : Graph.FiniteObject},
  (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller larger →
    (Graph.Strategy.Spine.refinedProgress BranchState Presentation presentation data).Smaller smaller larger
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

#### `Hypostructure.Graph.Strategy.Spine.replacementExclusionRow`

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

#### `Hypostructure.Graph.Strategy.Spine.retainedCode`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex) → ℕ
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

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierCutParityRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8CarrierDichotomy`

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
              Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TwoCarrierEntry ∉ known →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoTwoCarrierEntry ∉ known →
                  Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8TwoCarrierEntry)
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoTwoCarrierEntry) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8CensusRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8DemandAbsorptionRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8ExtractedCores`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Finset object.Vertex)
```

#### `Hypostructure.Graph.Strategy.Spine.route8ExtractedDeficit`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → ℕ
```

#### `Hypostructure.Graph.Strategy.Spine.route8ExtractedEntries`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Graph.Route8Census.Index object)
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.route8ExtractedEntryCensusRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficit ∉ known →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails ∉ known →
                  Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficit)
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8LargeBudgetDeficitFails) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8NoTwoCarrierContradictionRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8PeeledDemandResidualRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8PeelingDescentRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8PiecesClassifiedRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8PrivateCarrierBudgetRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8QuotientDichotomy`

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
              Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientFree ∉ known →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientResidual ∉ known →
                  Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientFree)
                    (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8QuotientResidual) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8RateDichotomy`

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
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.selection) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Rate ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8RateFails ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8Rate)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8RateFails) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8RateFromColdBelowRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8CarrierCore) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8SmallCoreEntry ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoSmallCoreEntry ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8SmallCoreEntry)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8NoSmallCoreEntry) previous
```

#### `Hypostructure.Graph.Strategy.Spine.route8SmallCoreExitRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8StageOutcomeDichotomy`

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
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8PeelingDescent)
                    known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedEntryCensus)
                      known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedTrueTwoCarrierEntry ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRateFailed ∉ known →
                      Core.Strategy.Decision
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8UnifiedTrueTwoCarrierEntry)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.route8StageRateFailed) previous
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

#### `Hypostructure.Graph.Strategy.Spine.route8TrueResidualRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8TrueTwoCarrierEntryRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedComponents`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(data : Graph.Strategy.Spine.Data) →
  (object : Graph.FiniteObject) →
    Finset
      (Graph.SupportComponents.Connected.Component object
        (object.remainderSupport (Graph.Strategy.Spine.canonicalWindowPacking data object)))
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedDeficitRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedEntries`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → (object : Graph.FiniteObject) → Finset (Graph.Route8Census.Index object)
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedEntryCensusRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedNegativeRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8UnifiedTerminalNoGoRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8VisibleRoutingRow`

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

#### `Hypostructure.Graph.Strategy.Spine.route8WindowBlockersRow`

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

#### `Hypostructure.Graph.Strategy.Spine.routeEightNetDeficiencyCapRow`

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

#### `Hypostructure.Graph.Strategy.Spine.sameCenterOpenPortCompatibilityRow`

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

#### `Hypostructure.Graph.Strategy.Spine.selectionMinimalityCoeFun`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
(BranchState : Graph.FiniteObject → Type v) →
  (Presentation : Type) →
    (presentation : Presentation) →
      (data : Graph.Strategy.Spine.Data) →
        (object : Graph.FiniteObject) →
          CoeFun (Graph.Strategy.Spine.SelectionMinimality BranchState Presentation presentation data object) fun x =>
            ∀ (smaller : Graph.FiniteObject),
              (Graph.Strategy.Spine.progress BranchState Presentation presentation data).Smaller smaller object →
                Graph.MinimumDegreeAtLeast data.threshold smaller → Graph.HasCycleWithLength data.LengthOK smaller
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.separatedTestersRow`

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

#### `Hypostructure.Graph.Strategy.Spine.targetCompleteContextUniversalityRow`

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

#### `Hypostructure.Graph.Strategy.Spine.targetRankCircuitRow`

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

#### `Hypostructure.Graph.Strategy.Spine.triangularFanCoreRow`

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

#### `Hypostructure.Graph.Strategy.Spine.twoStrandEnumerationBound`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → ℕ
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.typeABoundedSupportRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeAExclusionRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedExitEntry)
                    known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFour ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFour)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourPeeled) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourReceiverDischarged ∉ known →
                    Core.Strategy.Decision
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedHandoffExitFourFree)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitFourReceiverDischarged) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixFree) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenProduced ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenProduced)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSevenFree) previous
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
        Core.Strategy.AtomicStrategy (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSix) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixProper ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixGlobal ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixProper)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitSixGlobal) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeCollision ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeCollision)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitThreeFree) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoTheta ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoFree ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoTheta)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAExitTwoFree) previous
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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeALowSurplus) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAUnsaturatedReceivers ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAUnsaturatedReceivers) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeASilentExitEntryRow`

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
        {current : Graph.Strategy.Spine.Input BranchState Presentation presentation data} →
          {known : Core.Residual.FactKeys (Graph.Strategy.Spine.Input BranchState Presentation presentation data)} →
            (previous :
                Core.Residual.ExactLedger (Graph.Strategy.Spine.Input BranchState Presentation presentation data)
                  current known) →
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAReceiverRouting)
                    known] →
                [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeASaturatedReceiver)
                      known] →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry ∉ known →
                    Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleFirstExcess ∉ known →
                      Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleEntry)
                        (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeAVisibleFirstExcess) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeAVisibleExitEntryRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeBAssignedSupportRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeBBridgeReductionRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeBDecoratedAssignedSupportRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeDichotomy`

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
              [Core.Residual.FactKeys.Has (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanEntry) known] →
                Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanHeavyCentre ∉ known →
                  Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanDegreeFourCentres ∉ known →
                    Core.Strategy.Decision (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanHeavyCentre)
                      (Graph.Strategy.Spine.K Graph.Strategy.Spine.Key.typeBFanDegreeFourCentres) previous
```

#### `Hypostructure.Graph.Strategy.Spine.typeBFanDegreeFourProfileRow`

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

#### `Hypostructure.Graph.Strategy.Spine.typeBFanLocalDichotomyRow`

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

### `Hypostructure.Graph.Strategy.SpineVocabulary`

#### `Hypostructure.Graph.Strategy.Spine.windowPackageBits`

- Category: Minimum-degree cycle spine vocabulary
- Kind: `definition`
- Source: `Hypostructure/Graph/Strategy/SpineVocabulary.lean`
- Compiled type:

```lean
Graph.Strategy.Spine.Data → Graph.FiniteObject → ℕ
```

### `Hypostructure.Graph.Strategy.SpineRows`

#### `Hypostructure.Graph.Strategy.Spine.windowPackageRow`

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

#### `Hypostructure.Graph.isomorphismEquivalenceWithPresentation.congr_simp`

- Category: Minimum-degree cycle spine rows
- Kind: `theorem`
- Source: `Hypostructure/Graph/Strategy/SpineRows.lean`
- Compiled type:

```lean
∀ (Baseline : Graph.FiniteObject → Prop) (BranchState : Graph.FiniteObject → Type v) (Presentation : Type)
  (presentation : Presentation) (baselineInvariant : Graph.FiniteObject.IsomorphismInvariant Baseline),
  Graph.isomorphismEquivalenceWithPresentation Baseline BranchState Presentation presentation baselineInvariant =
    Graph.isomorphismEquivalenceWithPresentation Baseline BranchState Presentation presentation baselineInvariant
```
<!-- END GENERATED API -->
