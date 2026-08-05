import Hypostructure.Graph.ColdCorridor
import Hypostructure.Core.DyadicLength

/-!
# Fixture: the short self-return filter, computed

`lem:cold-short-self-return-filter` is the statement that, for a cold-window
outside self-return of outside length `ℓ` smeared over the window offsets, the
tested interval `[ℓ, ℓ+12]` avoids the accepted lengths only for

  `ℓ ∈ {17,18,19,33,34,35,36,37,38,39}`   for `1 ≤ ℓ ≤ 39`,
  `ℓ ∈ {17,18,19}`                        for `1 ≤ ℓ ≤ 32`.

`Graph.ColdCorridor.survivingLengths` computes that set from the accepted-length
predicate and the smear width alone.  This fixture evaluates it at the dyadic
length family, at the smear width of a window of order thirteen, and at the two
ranges the lemma states -- so the manuscript's two lists are *checked* here
rather than written into a definition, and no declaration in
`Hypostructure.Graph` contains them.

The two bounds are the lemma's own: `39` is the external-stub count
`δ·order − 2(order−1)` of `lem:cold-window-stub-excess` at `δ = 3`,
`order = 13`, and `32` is the largest accepted length inside it.
-/

namespace Hypostructure.Fixtures.ColdCorridorShortSelfReturn

open Hypostructure
open Hypostructure.Core.DyadicLength

/-- The smear width of a window of order thirteen: the offsets `{0,…,12}`
test the interval `[ℓ, ℓ+12]`. -/
def smear : Nat := 13 - 1

/-- `lem:cold-short-self-return-filter`, first display: for `1 ≤ ℓ ≤ 39` the
smear interval avoids the accepted lengths exactly on the displayed set. -/
example :
    Graph.ColdCorridor.survivingLengths PowerOfTwoLength smear 39 =
      [17, 18, 19, 33, 34, 35, 36, 37, 38, 39] := by
  decide

/-- `lem:cold-short-self-return-filter`, second display: restricted to
`1 ≤ ℓ ≤ 32` the only surviving lengths are `17, 18, 19`. -/
example :
    Graph.ColdCorridor.survivingLengths PowerOfTwoLength smear 32 =
      [17, 18, 19] := by
  decide

/-- The characterization theorem reads the computed list back as the surviving
condition: `20` is not in the list because `[20,32]` contains `32`. -/
example : ¬ Graph.ColdCorridor.SurvivesSmear PowerOfTwoLength smear 20 := by
  intro survives
  have accepted : PowerOfTwoLength 32 := by decide
  exact survives 32 (by norm_num) (by norm_num [smear]) accepted

/-- And `17` is in the list because `[17,29]` contains none of them. -/
example : Graph.ColdCorridor.SurvivesSmear PowerOfTwoLength smear 17 := by
  have member : (17 : Nat) ∈
      Graph.ColdCorridor.survivingLengths PowerOfTwoLength smear 39 := by decide
  exact (Graph.ColdCorridor.mem_survivingLengths_iff.1 member).2

end Hypostructure.Fixtures.ColdCorridorShortSelfReturn
