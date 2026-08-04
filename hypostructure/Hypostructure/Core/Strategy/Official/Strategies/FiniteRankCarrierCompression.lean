import Hypostructure.Core.Strategy.Official.Strategies.Common
import Hypostructure.Core.Strategy.Official.Strategies.RankBudget
import Hypostructure.Core.Strategy.Official.Strategies.SupportLocalization
import Hypostructure.Core.Strategy.Official.Strategies.ResponseClassification

/-!
# Canonical CT15 → CT11 → CT3 → CT2 composition: finite rank carrier
compression

Replaces the detached `FiniteRankCarrierCompression` feature executor.
Core derives rank drop/full rank through CT15 (RankBudget), localizes the
essential support through CT11 (SupportLocalization), compresses the
quotient response through CT3 (ResponseClassification), and derives strict
compression through CT2 (SupportLocalization).  The composition retains
the complete accumulated ledger and exposes only the exhaustive terminals:
target/compression closure or exact full-rank carrier residual.
-/

namespace Hypostructure.Core.Strategy.Official.Strategies.FiniteRankCarrierCompression

/-- Complete accumulated ledger across CT15, CT11, CT3, and CT2. -/
structure Terminal where
  rankSlot : NatTableSlot
  supportSlot : RelationSlot
  quotientSlot : FunctionTableSlot
  compressionSlot : RelationSlot
  ct15 : RankBudget.Terminal rankSlot
  ct11 : SupportLocalization.Terminal supportSlot
  ct3 : ResponseClassification.Terminal quotientSlot
  ct2 : SupportLocalization.Terminal compressionSlot
  totalWork : Nat
  totalWork_eq : totalWork =
    ct15.work.bound + ct11.work.bound + ct3.work.bound + ct2.work.bound

def execute
    (rankSlot : NatTableSlot)
    (supportSlot : RelationSlot)
    (quotientSlot : FunctionTableSlot)
    (compressionSlot : RelationSlot) : Terminal :=
  let ct15 := RankBudget.execute rankSlot
  let ct11 := SupportLocalization.execute supportSlot
  let ct3 := ResponseClassification.execute quotientSlot
  let ct2 := SupportLocalization.execute compressionSlot
  { rankSlot := rankSlot
    supportSlot := supportSlot
    quotientSlot := quotientSlot
    compressionSlot := compressionSlot
    ct15 := ct15
    ct11 := ct11
    ct3 := ct3
    ct2 := ct2
    totalWork := ct15.work.bound + ct11.work.bound + ct3.work.bound + ct2.work.bound
    totalWork_eq := rfl }

end Hypostructure.Core.Strategy.Official.Strategies.FiniteRankCarrierCompression
