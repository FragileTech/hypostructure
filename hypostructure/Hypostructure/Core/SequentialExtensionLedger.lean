import Hypostructure.Core.Finite.Enumeration

/-!
# Sequential compatible-extension ledger

Domain-generic (Graph and PDE alike): the recurring "sequential window scan"
pattern behind a hot/cold density or entropy cap.  Given an ordered schedule
of `Window`s and a running `Aggregate` with an invariant `Valid`, scan the
schedule left to right; at each window, either extend the aggregate (the
window is "hot") or reject it because no valid extension exists (the window
is "cold").  The result is an exhaustive, proof-carrying split: either every
scheduled window was retained (`cold = []`), or some concrete rejected
window witnesses the cold outcome.

This is exactly the shape a paper-style "window density" or "realized
remainder" argument needs before any numeric transport (entropy, density,
powered budget) can run on the resulting counts — and it is independent of
any particular application: neither `Window` nor `Aggregate` is assumed to
carry graph or PDE structure. -/

namespace Hypostructure.Core.SequentialExtensionLedger

universe u v

/-- Local extension contract for one sequential aggregate scan. -/
structure Profile : Type (max (u + 1) (v + 1)) where
  Window : Type u
  windows : Core.Finite.Enumeration Window
  Aggregate : Type v
  Valid : Aggregate -> Prop
  initial : Aggregate
  initialValid : Valid initial
  Extension : Aggregate -> Window -> Type (max u v)
  extend : {aggregate : Aggregate} -> {window : Window} ->
    Extension aggregate window -> Aggregate
  extendValid : {aggregate : Aggregate} -> {window : Window} -> Valid aggregate ->
    (extension : Extension aggregate window) -> Valid (extend extension)

/-- A proof-carrying sequential run.  The aggregate index forces the tail of
an accepted step to start at the actual extended aggregate; a rejected step
definitionally retains the old aggregate. -/
inductive Ledger (profile : Profile.{u, v}) : profile.Aggregate ->
    List profile.Window -> Type (max (u + 1) (v + 1)) where
  | nil {aggregate} (valid : profile.Valid aggregate) : Ledger profile aggregate []
  | accept {aggregate window tail}
      (valid : profile.Valid aggregate)
      (extension : profile.Extension aggregate window)
      (rest : Ledger profile (profile.extend extension) tail) :
      Ledger profile aggregate (window :: tail)
  | reject {aggregate window tail}
      (valid : profile.Valid aggregate)
      (absent : ¬ Nonempty (profile.Extension aggregate window))
      (rest : Ledger profile aggregate tail) :
      Ledger profile aggregate (window :: tail)

namespace Ledger

/-- The windows accepted (extended) along this run. -/
def hot {profile aggregate windows} : Ledger profile aggregate windows ->
    List profile.Window
  | .nil _ => []
  | @accept _ _ window _ _ _ rest => window :: rest.hot
  | .reject _ _ rest => rest.hot

/-- The windows rejected along this run. -/
def cold {profile aggregate windows} : Ledger profile aggregate windows ->
    List profile.Window
  | .nil _ => []
  | .accept _ _ rest => rest.cold
  | @reject _ _ window _ _ _ rest => window :: rest.cold

/-- The aggregate value reached at the end of the run. -/
def finalAggregate {profile aggregate windows} :
    Ledger profile aggregate windows -> profile.Aggregate
  | @nil _ aggregate _ => aggregate
  | .accept _ _ rest => rest.finalAggregate
  | .reject _ _ rest => rest.finalAggregate

theorem finalValid {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) :
    profile.Valid ledger.finalAggregate := by
  induction ledger with
  | nil valid => exact valid
  | accept _ _ _ ih => exact ih
  | reject _ _ _ ih => exact ih

/-- Transport a proof-relevant witness owned by the aggregate through the
exact accepted/rejected run: accepted steps use the extension's transport
map, rejected steps definitionally retain the same aggregate and witness. -/
def finalWitness {profile aggregate windows}
    (Witness : profile.Aggregate -> Type*)
    (transport : {current : profile.Aggregate} -> {window : profile.Window} ->
      (extension : profile.Extension current window) ->
        Witness current -> Witness (profile.extend extension)) :
    (ledger : Ledger profile aggregate windows) ->
      Witness aggregate -> Witness ledger.finalAggregate
  | .nil _, witness => witness
  | .accept _ extension rest, witness =>
      rest.finalWitness Witness transport (transport extension witness)
  | .reject _ _ rest, witness =>
      rest.finalWitness Witness transport witness

theorem length_partition {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) :
    ledger.hot.length + ledger.cold.length = windows.length := by
  induction ledger with
  | nil => simp [hot, cold]
  | accept _ _ _ ih => simp [hot, cold]; omega
  | reject _ _ _ ih => simp [hot, cold]; omega

theorem hot_sublist {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) : ledger.hot.Sublist windows := by
  induction ledger with
  | nil => exact .slnil
  | accept _ _ _ ih => exact .cons_cons _ ih
  | reject _ _ _ ih => exact .cons _ ih

theorem cold_sublist {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) : ledger.cold.Sublist windows := by
  induction ledger with
  | nil => exact .slnil
  | accept _ _ _ ih => exact .cons _ ih
  | reject _ _ _ ih => exact .cons_cons _ ih

theorem hot_nodup {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) (nodup : windows.Nodup) :
    ledger.hot.Nodup := ledger.hot_sublist.nodup nodup

theorem cold_nodup {profile aggregate windows}
    (ledger : Ledger profile aggregate windows) (nodup : windows.Nodup) :
    ledger.cold.Nodup := ledger.cold_sublist.nodup nodup

/-- Exhaustive hot/cold split for one completed ledger: either every
scheduled window was retained, or some concrete rejected window is
exhibited. -/
inductive HotColdOutcome {profile : Profile.{u, v}} {aggregate windows}
    (ledger : Ledger profile aggregate windows) : Type (max (u + 1) (v + 1)) where
  | hot (cold_empty : ledger.cold = []) : HotColdOutcome ledger
  | cold (window : profile.Window) (member : window ∈ ledger.cold) :
      HotColdOutcome ledger

/-- Decide the hot/cold outcome by inspecting only the already-produced
rejection list; this performs no further extension search. -/
def hotColdOutcome {profile : Profile.{u, v}} {aggregate windows}
    (ledger : Ledger profile aggregate windows) : HotColdOutcome ledger :=
  match coldEq : ledger.cold with
  | [] => .hot coldEq
  | window :: _ => .cold window (by simp [coldEq])

/-- On the hot outcome, the retained list has the full scheduled length. -/
theorem hot_length_eq_windows_length {profile : Profile.{u, v}} {aggregate windows}
    (ledger : Ledger profile aggregate windows) (cold_empty : ledger.cold = []) :
    ledger.hot.length = windows.length := by
  have partition := ledger.length_partition
  simpa [cold_empty] using partition

/-- Every rejected witness is one of the originally scheduled windows. -/
theorem coldOutcome_mem_windows {profile : Profile.{u, v}} {aggregate windows}
    (ledger : Ledger profile aggregate windows) {window : profile.Window}
    (member : window ∈ ledger.cold) : window ∈ windows :=
  ledger.cold_sublist.subset member

end Ledger

/-- Run the sequential scan: at each scheduled window, greedily accept an
extension when one exists (any witness, via classical choice — the outcome
depends only on `Nonempty`, never on which witness is picked), otherwise
reject and continue. -/
noncomputable def run (profile : Profile) :
    Ledger profile profile.initial profile.windows.values := by
  let rec go (windows : List profile.Window) (aggregate : profile.Aggregate)
      (valid : profile.Valid aggregate) : Ledger profile aggregate windows :=
    match windows with
    | [] => .nil valid
    | window :: tail => by
        classical
        by_cases available : Nonempty (profile.Extension aggregate window)
        · let extension := Classical.choice available
          exact .accept valid extension
            (go tail (profile.extend extension) (profile.extendValid valid extension))
        · exact .reject valid available (go tail aggregate valid)
  exact go profile.windows.values profile.initial profile.initialValid

/-- The runner performs exactly one local extension decision per scheduled
window. -/
def checks (profile : Profile) : Nat := profile.windows.values.length

theorem checks_exact (profile : Profile) :
    checks profile = profile.windows.values.length := rfl

end Hypostructure.Core.SequentialExtensionLedger
