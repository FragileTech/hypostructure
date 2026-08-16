import { L } from "../LeanCode";
import { ApiReference, ReferenceLegend, type ApiModule } from "./ApiReference";

const LEDGER: ApiModule = {
  title: "Hypostructure.Core.Residual",
  paths: ["hypostructure/Hypostructure/Core/Residual/ExactLedger.lean"],
  intro:
    "The residual domain classes, the fact vocabulary, key lists and value bundles, the audit records, and the ledger itself.",
  entries: [
    {
      name: "RefinementSystem",
      kind: "class",
      audience: "application",
      signature: `
        class RefinementSystem (Residual : Type) where
          Subject : Type
          subject : Residual -> Subject
          Refines : Residual -> Residual -> Prop
          refl : (residual : Residual) -> Refines residual residual
          trans : {new middle old : Residual} ->
            Refines new middle -> Refines middle old -> Refines new old
          subject_eq : {new old : Residual} -> Refines new old ->
            subject new = subject old`,
      note: "The laws of residual restriction for one domain. Instantiated once per residual type.",
    },
    {
      name: "RefinementSystem.subjectOf",
      kind: "def",
      audience: "application",
      signature: `
        def RefinementSystem.subjectOf [system : RefinementSystem Residual]
            (residual : Residual) : system.Subject`,
      note: "The subject of a residual, with the instance named.",
    },
    {
      name: "closureFactName",
      kind: "def",
      audience: "application",
      signature: `
        def closureFactName : Lean.Name := \`Hypostructure.Core.Strategy.contradiction`,
      note: "The one reserved semantic name that marks a closed branch.",
    },
    {
      name: "AutomaticClosureReason",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive AutomaticClosureReason where
          | incompatibleFacts (left right : Lean.Name)
          | impossibleFact (fact : Lean.Name)
          | emptyResidual`,
      note: "Why a branch closed automatically; recorded inside the closure evidence.",
    },
    {
      name: "ClosureEvidence",
      kind: "structure",
      audience: "application",
      signature: `
        structure ClosureEvidence where
          reason : AutomaticClosureReason
          contradiction : False`,
      note: "The value of every domain's closure key.",
    },
    {
      name: "FactSystem",
      kind: "class",
      audience: "application",
      signature: `
        class FactSystem (Residual : Type) [RefinementSystem Residual] where
          Key : Type
          keyDecidableEq : DecidableEq Key
          name : Key -> Lean.Name
          name_injective : Function.Injective name
          Value : Key -> Residual -> Sort _
          value_subsingleton : (key : Key) -> (residual : Residual) ->
            Subsingleton (Value key residual)
          transport : {key : Key} -> {new old : Residual} ->
            RefinementSystem.Refines new old -> Value key old -> Value key new
          closureKey : Key
          closure_name : name closureKey = closureFactName
          closureValue : (residual : Residual) ->
            ClosureEvidence -> Value closureKey residual
          closureEvidence : (residual : Residual) ->
            Value closureKey residual -> ClosureEvidence`,
      note: "The unique fact vocabulary of one residual domain. Instantiated once per residual type.",
    },
    {
      name: "FactKey",
      kind: "abbrev",
      audience: "application",
      signature: `
        abbrev FactKey (Residual : Type) [RefinementSystem Residual]
            [system : FactSystem Residual] := system.Key`,
      note: "A semantic fact key from the domain's sole vocabulary.",
    },
    {
      name: "FactKey.name",
      kind: "def",
      audience: "application",
      signature: `
        def FactKey.name (key : FactKey Residual) : Lean.Name`,
      note: "The injective audit name of a key.",
    },
    {
      name: "FactKey.At",
      kind: "abbrev",
      audience: "application",
      signature: `
        abbrev FactKey.At (key : FactKey Residual) (residual : Residual) :=
          system.Value key residual`,
      note: "The statement a key makes at a residual — the type of its value.",
    },
    {
      name: "FactKey.transport",
      kind: "def",
      audience: "application",
      signature: `
        def FactKey.transport {key : FactKey Residual} {new old : Residual}
            (refinement : RefinementSystem.Refines new old) (value : key.At old) : key.At new`,
      note: "Carry one value along a refinement.",
    },
    {
      name: "FactSystem.transport_refl",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem FactSystem.transport_refl (key : FactKey Residual) (residual : Residual)
            (value : key.At residual) :
            FactKey.transport (RefinementSystem.refl residual) value = value`,
      note: "Transport along the identity is the identity (by subsingleton elimination).",
    },
    {
      name: "FactSystem.transport_trans",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem FactSystem.transport_trans (key : FactKey Residual) {new middle old : Residual}
            (new_middle : RefinementSystem.Refines new middle)
            (middle_old : RefinementSystem.Refines middle old) (value : key.At old) :
            FactKey.transport (RefinementSystem.trans new_middle middle_old) value =
              FactKey.transport new_middle (FactKey.transport middle_old value)`,
      note: "Transport composes.",
    },
    {
      name: "FactKey.no_data_channel",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem FactKey.no_data_channel {Observation : Sort w} {key : FactKey Residual}
            {residual : Residual} (read : key.At residual -> Observation)
            (left right : key.At residual) : read left = read right`,
      note: "Every reading of a fact value is constant in that value.",
    },
    {
      name: "FactKeys",
      kind: "abbrev",
      audience: "application",
      signature: `
        abbrev FactKeys (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] :=
          List (FactKey Residual)`,
      note: "A type-level list of exact keys: the shape of the ledger's fact index.",
    },
    {
      name: "FactKeys.names",
      kind: "def",
      audience: "application",
      signature: `
        def FactKeys.names (keys : FactKeys Residual) : List Lean.Name`,
      note: "The audit names of a key list. Simp lemmas: names_nil, names_cons, names_append.",
    },
    {
      name: "FactKeys.Member",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive FactKeys.Member (key : FactKey Residual) : FactKeys Residual -> Type _ where
          | head : Member key (key :: tail)
          | tail : Member key tail -> Member key (other :: tail)`,
      note: "A structural position of one exact key in a fact list.",
    },
    {
      name: "FactKeys.Member.ofMem",
      kind: "def",
      audience: "application",
      signature: `
        def FactKeys.Member.ofMem {key : FactKey Residual} : {keys : FactKeys Residual} ->
          key ∈ keys -> Member key keys`,
      note: "Ordinary list membership to the structural witness. Also: Member.appendLeft, Member.appendRight.",
    },
    {
      name: "FactKeys.Has",
      kind: "class",
      audience: "application",
      signature: `
        class FactKeys.Has (key : FactKey Residual) (keys : FactKeys Residual) where
          member : Member key keys`,
      note: "The availability check. Instances cover the head and tail of a cons and both sides of an append, so it is found by instance search on literal indices.",
    },
    {
      name: "FactKeys.Values",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive FactKeys.Values (residual : Residual) : FactKeys Residual -> Type _ where
          | nil : Values residual []
          | cons {key : FactKey Residual} {tail : FactKeys Residual}
              (value : key.At residual) (rest : Values residual tail) :
              Values residual (key :: tail)`,
      note: "Values for exactly the keys in a fact index. Built by executors as their produced bundle.",
    },
    {
      name: "FactKeys.Values.get",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def FactKeys.Values.get {residual : Residual} (key : FactKey Residual)
            {keys : FactKeys Residual} [found : Has key keys] (values : Values residual keys) :
            key.At residual`,
      note: "Read one value of a bundle by key.",
    },
    {
      name: "CommitInfo",
      kind: "structure",
      audience: "application",
      signature: `
        structure CommitInfo where
          producer : Lean.Name
          checks : Nat := 0
          work : Nat := 0`,
      note: "Proof-free audit coordinates retained for every commit.",
    },
    {
      name: "CommitRecord",
      kind: "structure",
      audience: "application",
      signature: `
        structure CommitRecord where
          produced : List Lean.Name
          info : CommitInfo`,
      note: "One commit as the audit sees it: the produced key names and its info.",
    },
    {
      name: "AuditSnapshot",
      kind: "structure",
      audience: "application",
      signature: `
        structure AuditSnapshot where
          facts : List Lean.Name
          commits : List CommitRecord`,
      note: "The complete proof-free view of a branch. Facts newest-first, commits chronological.",
    },
    {
      name: "ExactLedger",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive ExactLedger (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] :
            Residual -> FactKeys Residual -> Type where
          | private seed ...
          | private step ...
          | private scope ...`,
      note: "The sole residual and proof-history carrier. All constructors are private; use the accessors below.",
    },
    {
      name: "ExactLedger.root",
      kind: "def",
      audience: "framework",
      signature: `
        def ExactLedger.root (_authority : FrameworkToken) (residual : Residual) :
            ExactLedger Residual residual []`,
      note: "A branch with a residual and no facts.",
    },
    {
      name: "ExactLedger.currentOf",
      kind: "def",
      audience: "application",
      signature: `
        def ExactLedger.currentOf {current : Residual} {known : FactKeys Residual}
            (_history : ExactLedger Residual current known) : Residual`,
      note: "The active residual, read off the index.",
    },
    {
      name: "ExactLedger.append",
      kind: "def",
      audience: "framework",
      signature: `
        def ExactLedger.append {previousResidual : Residual} {known produced : FactKeys Residual}
            (_authority : FrameworkToken)
            (previous : ExactLedger Residual previousResidual known)
            (next : Residual)
            (refinement : RefinementSystem.Refines next previousResidual)
            (facts : FactKeys.Values next produced)
            (producedNonempty : produced ≠ [])
            (producedUnique : produced.Nodup)
            (fresh : List.Disjoint produced known)
            (info : CommitInfo) :
            ExactLedger Residual next (produced ++ known)`,
      note: "The framework commit. Result index is definitionally produced ++ known.",
    },
    {
      name: "ExactLedger.initializeScope",
      kind: "def",
      audience: "framework",
      signature: `
        def ExactLedger.initializeScope {previousResidual : Residual} {produced : FactKeys Residual}
            (_authority : FrameworkToken)
            (previous : ExactLedger Residual previousResidual [])
            (next : Residual)
            (facts : FactKeys.Values next produced)
            (producedNonempty : produced ≠ [])
            (producedUnique : produced.Nodup)
            (info : CommitInfo) :
            ExactLedger Residual next produced`,
      note: "First-scope initialization; accepts only an empty index, so it is impossible after any fact exists.",
    },
    {
      name: "ExactLedger.currentOf_root / currentOf_append",
      kind: "theorem",
      audience: "application",
      signature: `
        @[simp] theorem ExactLedger.currentOf_root (residual : Residual) :
            currentOf (root exactLedgerInternal% residual) = residual

        @[simp] theorem ExactLedger.currentOf_append ... :
            currentOf (append exactLedgerInternal% previous next refinement facts
              producedNonempty producedUnique fresh info) = next`,
      note: "Simp lemmas: the residual index after root and append, by rfl.",
    },
    {
      name: "ExactLedger.get",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def ExactLedger.get {current : Residual} {known : FactKeys Residual}
            (history : ExactLedger Residual current known)
            (key : FactKey Residual) [FactKeys.Has key known] : key.At current`,
      note: "Retrieve a fact by exact key, at the active residual. Use at framework-owned closure boundaries.",
    },
    {
      name: "ExactLedger.getPresent",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def ExactLedger.getPresent {current : Residual} {known : FactKeys Residual}
            (history : ExactLedger Residual current known)
            (key : FactKey Residual) (present : key ∈ known) : key.At current`,
      note: "Retrieve a fact from a proposition-level membership proof.",
    },
    {
      name: "ExactLedger.refine",
      kind: "def",
      audience: "framework",
      signature: `
        noncomputable def ExactLedger.refine {current next : Residual} {known : FactKeys Residual}
            (_authority : FrameworkToken)
            (history : ExactLedger Residual current known)
            (refinement : RefinementSystem.Refines next current) :
            ExactLedger Residual next known`,
      note: "Reindex the history through a proved refinement. Not a commit; preserves the fact index and audit trail.",
    },
    {
      name: "ExactLedger.audit",
      kind: "def",
      audience: "application",
      signature: `
        def ExactLedger.audit {current : Residual} {known : FactKeys Residual}
            (history : ExactLedger Residual current known) : AuditSnapshot`,
      note: "The proof-free history: fact names and chronological commits.",
    },
    {
      name: "ExactLedger.audit_complete",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem ExactLedger.audit_complete (history : ExactLedger Residual current known) :
            (audit history).facts =
              (audit history).commits.reverse.flatMap (fun record => record.produced)`,
      note: "Every fact is accounted for by exactly one chronological commit.",
    },
    {
      name: "ExactLedger.audit_facts_unique",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem ExactLedger.audit_facts_unique (history : ExactLedger Residual current known) :
            (audit history).facts.Nodup`,
      note: "No semantic fact occurs twice.",
    },
    {
      name: "ExactLedger.audit_commits_nonempty",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem ExactLedger.audit_commits_nonempty (history : ExactLedger Residual current known) :
            (audit history).commits.Forall fun record => record.produced ≠ []`,
      note: "Every commit contributes at least one fact.",
    },
    {
      name: "ExactLedger.publishFact",
      kind: "def",
      audience: "framework",
      signature: `
        def ExactLedger.publishFact {current : Residual} {known : FactKeys Residual}
            (_authority : FrameworkToken)
            (previous : ExactLedger Residual current known)
            (key : FactKey Residual) (value : key.At current)
            (fresh : key ∉ known := by decide)
            (producer : Lean.Name := key.name) :
            ExactLedger Residual current (key :: known)`,
      note: "Publish one fact, preserving the residual definitionally.",
    },
    {
      name: "ExactLedger.latestInfo?",
      kind: "def",
      audience: "application",
      signature: `
        def ExactLedger.latestInfo? {current : Residual} {known : FactKeys Residual}
            (history : ExactLedger Residual current known) : Option CommitInfo`,
      note: "The newest audit record; none at the root.",
    },
    {
      name: "FrameworkToken",
      kind: "structure",
      audience: "framework",
      signature: `
        structure FrameworkToken where
          private mk ::

        syntax (name := exactLedgerInternalToken) "exactLedgerInternal%" : term`,
      note: "The unforgeable authority. exactLedgerInternal% elaborates only inside Hypostructure.* modules.",
    },
  ],
};

const MANIFEST: ApiModule = {
  title: "Hypostructure.Core.Strategy — manifests and sealed inputs",
  paths: ["hypostructure/Hypostructure/Core/Strategy/FactManifest.lean"],
  intro:
    "What a step requires and produces, and the sealed view an executor reads.",
  entries: [
    {
      name: "FactRequirements",
      kind: "structure",
      audience: "application",
      signature: `
        structure FactRequirements (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] where
          Requires : FactKeys Residual
          requiresUnique : Requires.Nodup`,
      note: "The prerequisite contract, shared by steps and decisions.",
    },
    {
      name: "FactManifest",
      kind: "structure",
      audience: "application",
      signature: `
        structure FactManifest (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
            extends FactRequirements Residual where
          Produces : FactKeys Residual
          producesUnique : Produces.Nodup
          producesNonempty : Produces ≠ []`,
      note: "The input/output contract of one step.",
    },
    {
      name: "FactManifest.requiredNames / producedNames",
      kind: "def",
      audience: "application",
      signature: `
        def FactManifest.requiredNames (manifest : FactManifest Residual) : List Lean.Name
        def FactManifest.producedNames (manifest : FactManifest Residual) : List Lean.Name`,
      note: "Audit names of the two key lists.",
    },
    {
      name: "FactKeys.Available",
      kind: "class",
      audience: "application",
      signature: `
        class FactKeys.Available (required known : FactKeys Residual) where
          private mk ::
          private values : {current : Residual} ->
            ExactLedger Residual current known -> FactKeys.Values current required`,
      note: "Readiness: found by instance search when every required key Has an entry in known. Constructor private.",
    },
    {
      name: "FactInputs",
      kind: "structure",
      audience: "application",
      signature: `
        structure FactInputs (requirements : FactRequirements Residual) where
          private mk ::
          current : Residual
          private facts : FactKeys.Values current requirements.Requires`,
      note: "The sealed view an executor receives: the current residual and exactly the declared facts.",
    },
    {
      name: "FactInputs.ofLedger",
      kind: "def",
      audience: "framework",
      signature: `
        noncomputable def FactInputs.ofLedger {current : Residual} {known : FactKeys Residual}
            (_authority : FrameworkToken)
            (requirements : FactRequirements Residual)
            [available : FactKeys.Available requirements.Requires known]
            (history : ExactLedger Residual current known) : FactInputs requirements`,
      note: "Build the sealed view from the ledger. Used by AtomicCT.run.",
    },
    {
      name: "FactInputs.get",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def FactInputs.get {requirements : FactRequirements Residual}
            (inputs : FactInputs requirements) (key : FactKey Residual)
            [FactKeys.Has key requirements.Requires] : key.At inputs.current`,
      note: "Read one declared prerequisite inside an executor. Undeclared keys are rejected at elaboration.",
    },
  ],
};

const EXECUTION: ApiModule = {
  title: "Hypostructure.Core.Strategy — atomic execution",
  paths: ["hypostructure/Hypostructure/Core/Strategy/ExactExecution.lean"],
  intro:
    "The one step type, its sealed executor, and the run that appends to the ledger.",
  entries: [
    {
      name: "AtomicResult",
      kind: "structure",
      audience: "application",
      signature: `
        structure AtomicResult (manifest : FactManifest Residual) (next : Residual) where
          facts : FactKeys.Values next manifest.Produces
          checks : Nat := 0
          work : Nat := 0`,
      note: "The complete output of one execution: the produced bundle at the new residual, plus audit counters.",
    },
    {
      name: "AtomicCT",
      kind: "structure",
      audience: "application",
      signature: `
        structure AtomicCT (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] where
          private mk ::
          id : Lean.Name
          manifest : FactManifest Residual
          private next : FactInputs manifest.toFactRequirements -> Residual
          private refines : (inputs : FactInputs manifest.toFactRequirements) ->
            RefinementSystem.Refines (next inputs) inputs.current
          private execute : (inputs : FactInputs manifest.toFactRequirements) ->
            AtomicResult manifest (next inputs)`,
      note: "A sealed step. Only id and manifest are public.",
    },
    {
      name: "AtomicCT.create",
      kind: "abbrev",
      audience: "framework",
      signature: `
        abbrev AtomicCT.create (_authority : FrameworkToken)
            (id : Lean.Name) (manifest : FactManifest Residual)
            (next : FactInputs manifest.toFactRequirements -> Residual)
            (refines : (inputs : FactInputs manifest.toFactRequirements) ->
              RefinementSystem.Refines (next inputs) inputs.current)
            (execute : (inputs : FactInputs manifest.toFactRequirements) ->
              AtomicResult manifest (next inputs)) : AtomicCT Residual`,
      note: "The construction boundary. Applications use registered combinators such as factOnly.",
    },
    {
      name: "AtomicCT.outputResidual",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def AtomicCT.outputResidual {current : Residual} {known : FactKeys Residual}
            (ct : AtomicCT Residual) [FactKeys.Available ct.manifest.Requires known]
            (previous : ExactLedger Residual current known) : Residual`,
      note: "The residual a step selects from a ledger; the residual index of run's result.",
    },
    {
      name: "AtomicCT.run",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def AtomicCT.run {current : Residual} {known : FactKeys Residual}
            (ct : AtomicCT Residual)
            [FactKeys.Available ct.manifest.Requires known]
            (previous : ExactLedger Residual current known)
            (fresh : List.Disjoint ct.manifest.Produces known := by decide) :
            ExactLedger Residual (ct.outputResidual previous)
              (ct.manifest.Produces ++ known)`,
      note: "Run and atomically append a step. The only application-side write.",
    },
    {
      name: "AtomicStrategy",
      kind: "abbrev",
      audience: "application",
      signature: `
        abbrev AtomicStrategy (Residual : Type) [RefinementSystem Residual] [FactSystem Residual] :=
          AtomicCT Residual`,
      note: "A synonym for AtomicCT, kept from an older CT/Strategy distinction: same inputs, executor and output.",
    },
  ],
};

const CLOSURE: ApiModule = {
  title: "Hypostructure.Core.Strategy — closing a branch",
  paths: ["hypostructure/Hypostructure/Core/Strategy/ExactExecution.lean"],
  intro:
    "Registered impossibility and incompatibility, the two closers that publish the domain's closure key from them, and the elimination of a closed history.",
  entries: [
    {
      name: "Incompatible",
      kind: "class",
      audience: "application",
      signature: `
        class Incompatible (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
            (left right : FactKey Residual) where
          contradiction : (residual : Residual) ->
            left.At residual -> right.At residual -> False`,
      note: "Registered semantic incompatibility of two facts. Declared as an instance by the application.",
    },
    {
      name: "Impossible",
      kind: "class",
      audience: "application",
      signature: `
        class Impossible (Residual : Type) [RefinementSystem Residual] [FactSystem Residual]
            (key : FactKey Residual) where
          contradiction : (residual : Residual) -> key.At residual -> False`,
      note: "Registered semantic impossibility of a single fact: a branch that commits it is uninhabited.",
    },
    {
      name: "closeImpossible",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def closeImpossible {current : Residual} {known : FactKeys Residual}
            (previous : ExactLedger Residual current known)
            (key : FactKey Residual)
            [FactKeys.Has key known]
            [Impossible Residual key]
            (fresh : system.closureKey ∉ known := by decide) :
            ExactLedger Residual current (system.closureKey :: known)`,
      note: "Close from one impossible fact visible on this branch; publishes the closure key with reason impossibleFact.",
    },
    {
      name: "closeIncompatible",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def closeIncompatible {current : Residual} {known : FactKeys Residual}
            (previous : ExactLedger Residual current known)
            (left right : FactKey Residual)
            [FactKeys.Has left known]
            [FactKeys.Has right known]
            [Incompatible Residual left right]
            (fresh : system.closureKey ∉ known := by decide) :
            ExactLedger Residual current (system.closureKey :: known)`,
      note: "Close from two incompatible facts visible on this branch; publishes the closure key with reason incompatibleFacts.",
    },
    {
      name: "ExactLedger.elimClosed",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem ExactLedger.elimClosed {current : Residual} {known : FactKeys Residual}
            (history : ExactLedger Residual current known)
            (present : FactKeys.Has system.closureKey known) : False`,
      note: "Eliminate a history carrying the domain's closure fact. The contradiction is the stored evidence; nothing is recomputed.",
    },
  ],
};

const FACT_ONLY: ApiModule = {
  title: "Hypostructure.Core.Strategy — fact-only steps and decisions",
  paths: ["hypostructure/Hypostructure/Core/Strategy/FactOnlyStrategy.lean"],
  intro: "The two shapes that recur in every assembly: a step that only adds facts, and a two-way decision.",
  entries: [
    {
      name: "factOnly",
      kind: "def",
      audience: "application",
      signature: `
        @[reducible] noncomputable def factOnly
            (id : Lean.Name) (manifest : FactManifest Residual)
            (derive : (inputs : FactInputs manifest.toFactRequirements) →
              FactKeys.Values inputs.current manifest.Produces)
            (checks : Nat := 0) (work : Nat := 0) :
            AtomicStrategy Residual`,
      note: "A step that preserves the residual and commits exactly the facts it derives.",
    },
    {
      name: "Decision",
      kind: "inductive",
      audience: "application",
      signature: `
        inductive Decision {current : Residual} {known : FactKeys Residual}
            (left right : FactKey Residual)
            (_previous : ExactLedger Residual current known) where
          | left (history : ExactLedger Residual current (left :: known))
          | right (history : ExactLedger Residual current (right :: known))`,
      note: "The outcome of a two-way decision; each arm's ledger carries only its own fact.",
    },
    {
      name: "Decision.run",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def Decision.run {current : Residual} {known : FactKeys Residual}
            (previous : ExactLedger Residual current known)
            (left right : FactKey Residual)
            (id : Lean.Name)
            (alternatives : Sum (left.At current) (right.At current))
            (leftFresh : left ∉ known := by decide)
            (rightFresh : right ∉ known := by decide) :
            Decision left right previous`,
      note: "Commit whichever arm the exhaustive alternative returns.",
    },
  ],
};

const MODULES = [LEDGER, MANIFEST, EXECUTION, CLOSURE, FACT_ONLY];

export function LedgerApiPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Reference</p>
        <h1>Ledger and execution API</h1>
        <p className="docs-lead">
          Every public declaration of the ledger, manifest, execution and
          closure modules, as it stands in the live sources. Universe annotations and
          the repeated <L>{"{Residual : Type} [RefinementSystem Residual] [FactSystem Residual]"}</L>{" "}
          binders are left out of the signatures; everything else is verbatim.
        </p>
        <ReferenceLegend />
      </header>
      <ApiReference modules={MODULES} />
    </>
  );
}
