import Hypostructure.Core.Strategy.Official.CapabilityFlow

namespace Hypostructure.Fixtures.OfficialCapabilityFlow

open Core.Strategy.Official
open Core.Strategy.OfficialRegistry
open Core.Strategy.Official.CapabilityFlow

def validRankChain : Program :=
  .chain ⟨"resource then complement"⟩
    (.invoke ⟨"resource"⟩ ⟨.derivedResourceAccounting, 0⟩)
    (.chain ⟨"complement then rank"⟩
      (.invoke ⟨"complement"⟩ ⟨.supportComplement, 0⟩)
      (.invoke ⟨"rank"⟩ ⟨.functionalRankSplit, 0⟩))

example : valid validRankChain = true := by native_decide

def forgedRank : Program :=
  .invoke ⟨"rank without complement"⟩ ⟨.functionalRankSplit, 0⟩

example : valid forgedRank = false := by native_decide

def siblingLeak : Program :=
  .join ⟨"no sibling leakage"⟩
    [(.invoke ⟨"resource"⟩ ⟨.derivedResourceAccounting, 0⟩), .done]
    (.invoke ⟨"complement"⟩ ⟨.supportComplement, 0⟩)

example : valid siblingLeak = false := by native_decide

def emptyJoin : Program :=
  .join ⟨"forbidden empty join"⟩ [] .done

example : valid emptyJoin = false := by native_decide

/-- A fan certificate can only be consumed after the receiver machine has
produced its typed fan terminal; it cannot be injected as an arbitrary graph
table or used as an unattached DAG node. -/
def forgedDecoratedFan : Program :=
  .invoke ⟨"fan without receiver terminal"⟩ ⟨.decoratedFan, 0⟩

example : valid forgedDecoratedFan = false := by native_decide

def receiverToDecoratedFan : Program :=
  .chain ⟨"receiver fan terminal"⟩
    (.chain ⟨"receiver inputs"⟩
      (.invoke ⟨"support"⟩ ⟨.supportLocalization, 0⟩)
      (.chain ⟨"response"⟩
        (.invoke ⟨"response"⟩ ⟨.responseClassification, 0⟩)
        (.invoke ⟨"receiver"⟩ ⟨.receiverSaturation, 0⟩)))
    (.branch ⟨"receiver exits"⟩ ⟨.receiverExhaustion, 0⟩
      [(.invoke ⟨"fan"⟩ ⟨.decoratedFan, 0⟩), .done])

example : valid receiverToDecoratedFan = true := by native_decide

end Hypostructure.Fixtures.OfficialCapabilityFlow
