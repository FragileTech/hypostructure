import Hypostructure.Core.Strategy.Official.Schema

/-! Shared, framework-owned evidence for official finite strategies. -/

namespace Hypostructure.Core.Strategy.Official.Strategies

/-- Static work is computed from the inspected canonical slot. -/
structure StaticWork (checks : Nat) where
  bound : Nat
  checks_le : checks ≤ bound

def exactWork (checks : Nat) : StaticWork checks :=
  { bound := checks, checks_le := le_rfl }

theorem mem_map_fst {α β : Type} {x : α} {rows : List (α × β)}
    (h : ∃ y, (x, y) ∈ rows) : x ∈ rows.map Prod.fst := by
  obtain ⟨y, hy⟩ := h
  exact List.mem_map.mpr ⟨(x, y), hy, rfl⟩

end Hypostructure.Core.Strategy.Official.Strategies
