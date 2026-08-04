import Mathlib.Data.List.GetD

/-!
# Canonical deletion-fan threshold and incidence accounting

This module is deliberately domain-neutral.  It turns an already computed
finite load schedule into the canonical high-load schedule and splits each
finite port schedule at the same threshold.  It contains no routing hook,
classifier, or application-supplied conclusion.
-/

namespace Hypostructure.Core.Strategy.Official.Features.DeletionFanAccounting

universe u v

/-- One finite load row. -/
structure LoadRow (α : Type u) where
  item : α
  load : Nat

/-- The framework-owned strict-threshold selection. -/
def highRows (threshold : Nat) (rows : List (LoadRow α)) :
    List (LoadRow α) :=
  rows.filter fun row => threshold < row.load

@[simp] theorem mem_highRows_iff {threshold : Nat} {rows : List (LoadRow α)}
    {row : LoadRow α} :
    row ∈ highRows threshold rows ↔ row ∈ rows ∧ threshold < row.load := by
  simp [highRows]

/-- The complementary schedule.  Keeping both sides in one ledger prevents a
domain adapter from silently dropping a row which is not high. -/
def ordinaryRows (threshold : Nat) (rows : List (LoadRow α)) :
    List (LoadRow α) :=
  rows.filter fun row => decide (row.load ≤ threshold)

@[simp] theorem mem_ordinaryRows_iff
    {threshold : Nat} {rows : List (LoadRow α)} {row : LoadRow α} :
    row ∈ ordinaryRows threshold rows ↔
      row ∈ rows ∧ row.load ≤ threshold := by
  simp [ordinaryRows]

/-- Proof-relevant threshold ledger computed from one literal source
schedule.  Neither side can be supplied independently. -/
structure ThresholdLedger (α : Type u) where
  threshold : Nat
  source : List (LoadRow α)
  high : List (LoadRow α)
  ordinary : List (LoadRow α)
  high_eq : high = highRows threshold source
  ordinary_eq : ordinary = ordinaryRows threshold source

def deriveThresholdLedger (threshold : Nat) (rows : List (LoadRow α)) :
    ThresholdLedger α where
  threshold := threshold
  source := rows
  high := highRows threshold rows
  ordinary := ordinaryRows threshold rows
  high_eq := rfl
  ordinary_eq := rfl

namespace ThresholdLedger

theorem source_classified (ledger : ThresholdLedger α)
    (row : LoadRow α) (member : row ∈ ledger.source) :
    row ∈ ledger.high ∨ row ∈ ledger.ordinary := by
  rw [ledger.high_eq, ledger.ordinary_eq]
  by_cases high : ledger.threshold < row.load
  · exact Or.inl ((mem_highRows_iff).2 ⟨member, high⟩)
  · exact Or.inr ((mem_ordinaryRows_iff).2
      ⟨member, Nat.le_of_not_gt high⟩)

theorem high_disjoint_ordinary (ledger : ThresholdLedger α) :
    List.Disjoint ledger.high ledger.ordinary := by
  intro row high ordinary
  rw [ledger.high_eq, mem_highRows_iff] at high
  rw [ledger.ordinary_eq, mem_ordinaryRows_iff] at ordinary
  exact (Nat.not_lt_of_ge ordinary.2) high.2

end ThresholdLedger

/-- Canonical base ports: the first `threshold` entries. -/
def basePorts (threshold : Nat) (ports : List β) : List β :=
  ports.take threshold

/-- Canonical excess ports: all entries after the first `threshold`. -/
def excessPorts (threshold : Nat) (ports : List β) : List β :=
  ports.drop threshold

theorem base_append_excess (threshold : Nat) (ports : List β) :
    basePorts threshold ports ++ excessPorts threshold ports = ports := by
  exact List.take_append_drop threshold ports

theorem base_length (threshold : Nat) (ports : List β)
    (enough : threshold ≤ ports.length) :
    (basePorts threshold ports).length = threshold := by
  simp [basePorts, List.length_take, Nat.min_eq_left enough]

theorem excess_length (threshold : Nat) (ports : List β) :
    (excessPorts threshold ports).length = ports.length - threshold := by
  simp [excessPorts]

theorem base_nodup (threshold : Nat) {ports : List β}
    (nodup : ports.Nodup) :
    (basePorts threshold ports).Nodup :=
  nodup.take

theorem excess_nodup (threshold : Nat) {ports : List β}
    (nodup : ports.Nodup) :
    (excessPorts threshold ports).Nodup :=
  nodup.drop

/-- Exact static work: one load inspection, one port inspection, and one
outside-incidence inspection per generated row. -/
def checks (loads ports outsideIncidences : Nat) : Nat :=
  loads + ports + outsideIncidences

structure Work (loads ports outsideIncidences : Nat) where
  bound : Nat
  exact : bound = checks loads ports outsideIncidences

def exactWork (loads ports outsideIncidences : Nat) :
    Work loads ports outsideIncidences :=
  ⟨checks loads ports outsideIncidences, rfl⟩

end Hypostructure.Core.Strategy.Official.Features.DeletionFanAccounting
