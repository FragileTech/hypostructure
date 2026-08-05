import Hypostructure.Core.Prelude

/-!
# Canonical refinement ledger

`ExactLedger` is the only residual and proof-history carrier.  It is one
indexed type: the current residual and the complete branch-local fact set are
part of its type, and every commit retains its literal predecessor.  A commit
can only refine the residual and prepend a nonempty, duplicate-free bundle of
facts to the inherited fact index.

Each residual domain has exactly one `FactSystem`.  Consequently a semantic
key determines one value schema; two unrelated facts cannot impersonate one
another by reusing a display name.  Lookup is by exact key and is independent
of producer, row, and predecessor depth.
-/

namespace Hypostructure.Core.Residual

universe uResidual uSubject uKey uValue

/-! ## Framework authority

The constructors of the canonical history and of atomic executors are not an
application API.  A public but uninhabited-from-outside token type lets those
operations remain usable across Core modules without exporting a value that
an application can manufacture.  The elaborator below emits Core's private
token only while compiling a `Hypostructure.*` framework or fixture module;
proof applications such as `HypostructureErdos64EG.*` are rejected.
-/

/-- Unforgeable authority required by framework-only construction
operations.  Its sole constructor and sole value are private. -/
structure FrameworkToken where
  private mk ::

private def frameworkToken : FrameworkToken :=
  .mk

/-- Internal term emitted only inside framework-owned modules. -/
syntax (name := exactLedgerInternalToken) "exactLedgerInternal%" : term

open Lean Lean.Elab Lean.Elab.Term in
elab_rules : term
  | `(exactLedgerInternal%) => do
      let moduleName := (← getEnv).mainModule.toString
      unless moduleName.startsWith "Hypostructure." do
        throwError "the canonical ledger construction token is internal to framework modules"
      pure (mkConst ``frameworkToken)

/-- The one reserved semantic name that marks a closed branch. -/
def closureFactName : Lean.Name :=
  `Hypostructure.Core.Strategy.contradiction

inductive AutomaticClosureReason where
  | incompatibleFacts (left right : Lean.Name)
  | emptyResidual
  deriving Repr, DecidableEq

/-- Every domain's distinguished closure key carries this evidence. -/
structure ClosureEvidence where
  reason : AutomaticClosureReason
  contradiction : False

/-- Domain-independent laws for residual restriction.  The orientation is
`Refines next previous`: execution may preserve or restrict a residual, never
replace it by an unrelated state. -/
class RefinementSystem (Residual : Type uResidual) where
  Subject : Type uSubject
  subject : Residual -> Subject
  Refines : Residual -> Residual -> Prop
  refl : (residual : Residual) -> Refines residual residual
  trans : {new middle old : Residual} ->
    Refines new middle -> Refines middle old -> Refines new old
  subject_eq : {new old : Residual} -> Refines new old ->
    subject new = subject old

namespace RefinementSystem

def subjectOf {Residual : Type uResidual} [system : RefinementSystem Residual]
    (residual : Residual) : system.Subject :=
  system.subject residual

end RefinementSystem

/-- The unique fact vocabulary for one residual domain.  `Key` has decidable
equality so routing tests the exact semantic key.  Injective names provide
stable diagnostics and audit output without serving as a type cast. -/
class FactSystem
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual] where
  Key : Type uKey
  keyDecidableEq : DecidableEq Key
  name : Key -> Lean.Name
  name_injective : Function.Injective name
  Value : Key -> Residual -> Sort (uValue + 1)
  transport : {key : Key} -> {new old : Residual} ->
    RefinementSystem.Refines new old -> Value key old -> Value key new
  transport_refl : (key : Key) -> (residual : Residual) ->
    (value : Value key residual) ->
    transport (RefinementSystem.refl residual) value = value
  transport_trans : (key : Key) -> {new middle old : Residual} ->
    (new_middle : RefinementSystem.Refines new middle) ->
    (middle_old : RefinementSystem.Refines middle old) ->
    (value : Value key old) ->
    transport (RefinementSystem.trans new_middle middle_old) value =
      transport new_middle (transport middle_old value)
  closureKey : Key
  closure_name : name closureKey = closureFactName
  closureValue : (residual : Residual) ->
    ClosureEvidence -> Value closureKey residual
  closureEvidence : (residual : Residual) ->
    Value closureKey residual -> ClosureEvidence

instance
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    DecidableEq system.Key :=
  system.keyDecidableEq

/-- A semantic fact key from the domain's sole fact vocabulary. -/
abbrev FactKey
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :=
  system.Key

namespace FactKey

def name
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (key : FactKey Residual) : Lean.Name :=
  system.name key

abbrev At
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (key : FactKey Residual) (residual : Residual) :=
  system.Value key residual

def transport
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {new old : Residual}
    (refinement : RefinementSystem.Refines new old)
    (value : key.At old) : key.At new :=
  system.transport refinement value

end FactKey

/-! ## Exact heterogeneous fact bundles -/

/-- A type-level list of exact semantic keys. -/
abbrev FactKeys
    (Residual : Type uResidual)
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :=
  List (FactKey Residual)

namespace FactKeys

def names
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] (keys : FactKeys Residual) : List Lean.Name :=
  keys.map FactKey.name

@[simp] theorem names_nil
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    names ([] : FactKeys Residual) = [] := rfl

@[simp] theorem names_cons
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] (key : FactKey Residual)
    (tail : FactKeys Residual) :
    names (key :: tail) = key.name :: names tail := rfl

@[simp] theorem names_append
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] (left right : FactKeys Residual) :
    names (left ++ right) = names left ++ names right := by
  simp [names]

/-- A structural position of one exact key in a fact list. -/
inductive Member
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (key : FactKey Residual) : FactKeys Residual -> Type _ where
  | head : Member key (key :: tail)
  | tail : Member key tail -> Member key (other :: tail)

namespace Member

/-- Convert ordinary list membership into the structural witness used by the
ledger.  This is the bridge for compilers whose readiness checker already
returns a proposition-level membership proof; it does not inspect or alter
the ledger. -/
def ofMem
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} : {keys : FactKeys Residual} ->
      key ∈ keys -> Member key keys
  | [], absent => False.elim (by simpa using absent)
  | item :: rest, present => by
      by_cases same : key = item
      · subst item
        exact .head
      · exact .tail (ofMem (by simpa [same] using present))

def appendLeft
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {left : FactKeys Residual}
    (right : FactKeys Residual) : Member key left -> Member key (left ++ right)
  | .head => .head
  | .tail member => .tail (appendLeft right member)

def appendRight
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {right : FactKeys Residual}
    (left : FactKeys Residual) : Member key right -> Member key (left ++ right)
  | member => by
      induction left with
      | nil => exact member
      | cons _ tail ih => exact .tail ih

end Member

class Has
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (key : FactKey Residual) (keys : FactKeys Residual) where
  member : Member key keys

instance (priority := high)
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {key : FactKey Residual}
    {tail : FactKeys Residual} : Has key (key :: tail) where
  member := .head

instance (priority := low)
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {key other : FactKey Residual}
    {tail : FactKeys Residual} [found : Has key tail] :
    Has key (other :: tail) where
  member := .tail found.member

instance (priority := 10)
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {left right : FactKeys Residual}
    [found : Has key right] : Has key (left ++ right) where
  member := Member.appendRight left found.member

instance (priority := 20)
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {key : FactKey Residual} {left right : FactKeys Residual}
    [found : Has key left] : Has key (left ++ right) where
  member := Member.appendLeft right found.member

/-- Values for exactly the keys in a fact index. -/
inductive Values
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] (residual : Residual) :
    FactKeys Residual -> Type (max uResidual uKey (uValue + 2)) where
  | nil : Values residual []
  | cons {key : FactKey Residual} {tail : FactKeys Residual}
      (value : key.At residual) (rest : Values residual tail) :
      Values residual (key :: tail)

namespace Values

private noncomputable def getAt
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {residual : Residual}
    {key : FactKey Residual} {keys : FactKeys Residual}
    (member : Member key keys) (values : Values residual keys) :
    key.At residual := by
  induction member with
  | head =>
      cases values with
      | cons value _ => exact value
  | tail _ ih =>
      cases values with
      | cons _ rest => exact ih rest

noncomputable def get
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {residual : Residual}
    (key : FactKey Residual) {keys : FactKeys Residual}
    [found : Has key keys] (values : Values residual keys) :
    key.At residual :=
  getAt found.member values

private noncomputable def transport
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {new old : Residual}
    (refinement : RefinementSystem.Refines new old) :
    {keys : FactKeys Residual} -> Values old keys -> Values new keys
  | [], .nil => .nil
  | _ :: _, .cons value rest =>
      .cons (FactKey.transport refinement value) (transport refinement rest)

private noncomputable def append
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {residual : Residual} :
    {left right : FactKeys Residual} ->
      Values residual left -> Values residual right ->
        Values residual (left ++ right)
  | [], _, .nil, rightValues => rightValues
  | _ :: _, _, .cons value rest, rightValues =>
      .cons value (append rest rightValues)

end Values
end FactKeys

/-! ## The sole persistent history type -/

/-- Proof-free audit coordinates retained for every commit. -/
structure CommitInfo where
  producer : Lean.Name
  checks : Nat := 0
  work : Nat := 0
  deriving Repr, DecidableEq

/-- Public, proof-free record of one atomic commit.  `produced` lists the exact
semantic keys appended by that commit; it contains no theorem payload. -/
structure CommitRecord where
  produced : List Lean.Name
  info : CommitInfo
  deriving Repr, DecidableEq

/-- Complete proof-free audit view of one branch.  Facts are newest-first and
commits are chronological from the root. -/
structure AuditSnapshot where
  /-- Every fact proved on the branch; all remain queryable at the active
  residual because every post-initialization transition is a refinement. -/
  facts : List Lean.Name
  commits : List CommitRecord
  deriving Repr, DecidableEq

/-- The sole residual and proof-history carrier.  The two indices expose the
active residual and every fact available on this branch. -/
inductive ExactLedger
    (Residual : Type uResidual) [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    Residual -> FactKeys Residual -> Type (max uResidual (uKey + 1) (uValue + 2)) where
  | private seed (current : Residual) : ExactLedger Residual current []
  | private step
      {previousResidual : Residual} {known produced : FactKeys Residual}
      (previous : ExactLedger Residual previousResidual known)
      (current : Residual)
      (refinement : RefinementSystem.Refines current previousResidual)
      (facts : FactKeys.Values current produced)
      (producedNonempty : produced ≠ [])
      (producedUnique : produced.Nodup)
      (fresh : List.Disjoint produced known)
      (info : CommitInfo) :
      ExactLedger Residual current (produced ++ known)
  | private scope
      {previousResidual : Residual} {produced : FactKeys Residual}
      (previous : ExactLedger Residual previousResidual [])
      (current : Residual)
      (facts : FactKeys.Values current produced)
      (producedNonempty : produced ≠ [])
      (producedUnique : produced.Nodup)
      (info : CommitInfo) :
      ExactLedger Residual current produced

namespace ExactLedger

def root
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    (_authority : FrameworkToken) (residual : Residual) :
    ExactLedger Residual residual [] :=
  .seed residual

/-- The active residual is an index, not a value travelling beside history. -/
def currentOf
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {current : Residual} {known : FactKeys Residual}
    (_history : ExactLedger Residual current known) : Residual :=
  current

/-- Framework commit.  Its result index is definitionally the new facts
followed by every inherited fact, so dropping history is unrepresentable. -/
def append
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {previousResidual : Residual} {known produced : FactKeys Residual}
    (_authority : FrameworkToken)
    (previous : ExactLedger Residual previousResidual known)
    (next : Residual)
    (refinement : RefinementSystem.Refines next previousResidual)
    (facts : FactKeys.Values next produced)
    (producedNonempty : produced ≠ [])
    (producedUnique : produced.Nodup)
    (fresh : List.Disjoint produced known)
    (info : CommitInfo) :
    ExactLedger Residual next (produced ++ known) :=
  .step previous next refinement facts producedNonempty producedUnique fresh info

/-- Initialize the first fact-bearing residual scope while retaining the
literal empty predecessor.  Requiring an exactly empty input history makes
this operation unusable after any fact has been proved.  Every later residual
change must use `refine` or `append` and therefore prove `Refines next current`;
no committed fact can ever be archived or dropped. -/
def initializeScope
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {previousResidual : Residual} {produced : FactKeys Residual}
    (_authority : FrameworkToken)
    (previous : ExactLedger Residual previousResidual [])
    (next : Residual)
    (facts : FactKeys.Values next produced)
    (producedNonempty : produced ≠ [])
    (producedUnique : produced.Nodup)
    (info : CommitInfo) :
    ExactLedger Residual next produced :=
  .scope previous next facts producedNonempty producedUnique info

@[simp] theorem currentOf_root
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] (residual : Residual) :
    currentOf (root exactLedgerInternal% residual) = residual := rfl

@[simp] theorem currentOf_append
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {previousResidual : Residual} {known produced : FactKeys Residual}
    (previous : ExactLedger Residual previousResidual known)
    (next : Residual)
    (refinement : RefinementSystem.Refines next previousResidual)
    (facts : FactKeys.Values next produced)
    (producedNonempty : produced ≠ [])
    (producedUnique : produced.Nodup)
    (fresh : List.Disjoint produced known)
    (info : CommitInfo) :
    currentOf (append exactLedgerInternal% previous next refinement facts producedNonempty
      producedUnique fresh info) = next := rfl

/-- Internal materialization of the current-residual value of every inherited
fact.  The bundle is deliberately not public: consumers can retrieve facts
only through exact semantic keys. -/
private noncomputable def materialize
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    {current : Residual} -> {known : FactKeys Residual} ->
      ExactLedger Residual current known -> FactKeys.Values current known
  | _, _, .seed _ => .nil
  | _, _, .step previous _ refinement facts _ _ _ _ =>
      FactKeys.Values.append facts
        (FactKeys.Values.transport refinement (materialize previous))
  | _, _, .scope _ _ facts _ _ _ => facts

/-- Internal history-preserving transport through a proved residual
refinement.  Every original commit and every original fact remains present;
only its value is transported to the refined cursor. -/
private noncomputable def transportHistory
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {next : Residual} : {current : Residual} -> {known : FactKeys Residual} ->
      RefinementSystem.Refines next current ->
      ExactLedger Residual current known -> ExactLedger Residual next known
  | _, _, refinement, .seed _ =>
      .seed next
  | _, _, refinement,
      .step previous _ previousRefinement facts producedNonempty
        producedUnique fresh info =>
      .step
        (transportHistory
          (RefinementSystem.trans refinement previousRefinement) previous)
        next (RefinementSystem.refl next)
        (FactKeys.Values.transport refinement facts)
        producedNonempty producedUnique fresh info
  | _, _, refinement,
      .scope previous _ facts producedNonempty producedUnique info =>
      .scope previous next (FactKeys.Values.transport refinement facts)
        producedNonempty producedUnique info

/-- Internal chronological audit traversal.  It follows the literal retained
predecessor, so a commit cannot disappear from the public audit view. -/
private def commitTrail
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    {current : Residual} -> {known : FactKeys Residual} ->
      ExactLedger Residual current known -> List CommitRecord
  | _, _, .seed _ => []
  | _, _, .step (produced := produced) previous _ _ _ _ _ _ info =>
      commitTrail previous ++ [{ produced := produced.names, info }]
  | _, _, .scope (produced := produced) previous _ _ _ _ info =>
      commitTrail previous ++ [{ produced := produced.names, info }]

/-- Retrieve a fact without naming its producer, row, or predecessor depth. -/
noncomputable def get
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known)
    (key : FactKey Residual) [FactKeys.Has key known] : key.At current :=
  FactKeys.Values.get key (materialize history)

/-- Retrieve a fact from a proposition-level readiness proof.  The semantic
key still determines the value schema, and absence is an elaboration error
because callers must supply `key ∈ known`. -/
noncomputable def getPresent
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known)
    (key : FactKey Residual) (present : key ∈ known) : key.At current :=
  FactKeys.Values.getAt (FactKeys.Member.ofMem present) (materialize history)

/-- Reindex the one canonical history through a proved refinement.  This is
not a commit and cannot publish a theorem: it preserves the exact fact index
and the complete chronological audit trail definitionally. -/
noncomputable def refine
    {Residual : Type uResidual}
    [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current next : Residual} {known : FactKeys Residual}
    (_authority : FrameworkToken)
    (history : ExactLedger Residual current known)
    (refinement : RefinementSystem.Refines next current) :
    ExactLedger Residual next known :=
  transportHistory refinement history

/-- Inspect the complete proof history without exposing constructors, fact
bundles, predecessor cursors, or proof terms. -/
def audit
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known) : AuditSnapshot :=
  { facts := known.names
    commits := commitTrail history }

private theorem knownKeys_nodup
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    : {current : Residual} -> {known : FactKeys Residual} ->
      (history : ExactLedger Residual current known) -> known.Nodup
  | _, _, .seed _ => by simp
  | _, _, .step previous _ _ _ _ producedUnique fresh _ =>
      producedUnique.append (knownKeys_nodup previous) fresh
  | _, _, .scope _ _ _ _ producedUnique _ => producedUnique

private theorem commitTrail_produced_nonempty
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    : {current : Residual} -> {known : FactKeys Residual} ->
      (history : ExactLedger Residual current known) ->
      (commitTrail history).Forall fun record => record.produced ≠ []
  | _, _, .seed _ => by simp [commitTrail]
  | _, _, .step (produced := produced) previous _ _ _ producedNonempty _ _ _ => by
      have producedNamesNonempty : produced.names ≠ [] := by
        simpa [FactKeys.names] using producedNonempty
      simpa [commitTrail, producedNamesNonempty] using
        commitTrail_produced_nonempty previous
  | _, _, .scope (produced := produced) previous _ _ producedNonempty _ _ => by
      have producedNamesNonempty : produced.names ≠ [] := by
        simpa [FactKeys.names] using producedNonempty
      simpa [commitTrail, producedNamesNonempty] using
        commitTrail_produced_nonempty previous

/-- Every fact is accounted for by exactly one chronological commit.  Because
initialization requires an empty history and all later commits append, reversing
the commit list recovers the complete newest-first fact index. -/
theorem audit_complete
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] :
    {current : Residual} → {known : FactKeys Residual} →
    (history : ExactLedger Residual current known) →
      (audit history).facts =
        (audit history).commits.reverse.flatMap
          (fun record => record.produced)
  | _, _, .seed _ => rfl
  | _, _, .step previous _ _ _ _ _ _ _ => by
      simp only [audit, commitTrail, FactKeys.names_append,
        List.reverse_append, List.reverse_singleton, List.flatMap_append,
        List.flatMap_singleton]
      congr 1
      simpa only [audit] using audit_complete previous
  | _, _, .scope previous _ _ _ _ _ => by
      simp only [audit, commitTrail, List.reverse_append,
        List.reverse_singleton, List.flatMap_append, List.flatMap_singleton]
      have emptyHistory := audit_complete previous
      change [] = (commitTrail previous).reverse.flatMap
        (fun record => record.produced) at emptyHistory
      rw [← emptyHistory]
      simp

/-- No semantic fact occurs twice in an exact ledger. -/
theorem audit_facts_unique
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [system : FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known) :
    (audit history).facts.Nodup :=
  (knownKeys_nodup history).map system.name_injective

/-- Every audit commit contributes at least one semantic fact. -/
theorem audit_commits_nonempty
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual]
    {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known) :
    (audit history).commits.Forall fun record => record.produced ≠ [] :=
  commitTrail_produced_nonempty history

/-- Publish one fact while preserving the residual definitionally. -/
def publishFact
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {current : Residual} {known : FactKeys Residual}
    (_authority : FrameworkToken)
    (previous : ExactLedger Residual current known)
    (key : FactKey Residual) (value : key.At current)
    (fresh : key ∉ known := by decide)
    (producer : Lean.Name := key.name) :
    ExactLedger Residual current (key :: known) :=
  append exactLedgerInternal% previous current (RefinementSystem.refl current)
    (.cons value .nil) (by simp) (by simp) (by simpa) { producer }

/-- The newest audit record, absent only at the root. -/
def latestInfo?
    {Residual : Type uResidual} [RefinementSystem.{uResidual, uSubject} Residual]
    [FactSystem.{uResidual, uSubject, uKey, uValue} Residual] {current : Residual} {known : FactKeys Residual}
    (history : ExactLedger Residual current known) : Option CommitInfo :=
  match history with
  | .seed _ => none
  | .step _ _ _ _ _ _ _ info => some info
  | .scope _ _ _ _ _ info => some info

end ExactLedger
end Hypostructure.Core.Residual
