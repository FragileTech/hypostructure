import Hypostructure.Graph.BaselineSpineDemand
import Hypostructure.Graph.DeclaredRankQuotient
import Hypostructure.Graph.NamedSurplusExits
import Hypostructure.Graph.SparsePairResponse

/-!
# The sparse pair dependence dichotomy and the entropy sandwich

`lem:sparse-pair-dependence-exit`, `lem:mixed-sparse-spine-dependence`,
`prop:sparse-pair-independence-dichotomy`, `cor:sparse-pair-entropy-saturation`,
`prop:sparse-entropy-sandwich` and `prop:sparse-entropy-sandwich-with-blockers`.

The six statements are two theorems and their readings.

**The dichotomy.**  All three dependence statements run the same case analysis
over an inclusion-minimal determination certificate, and that analysis is
`AttemptedQuotient.route`.  At an object that survives the sparse surplus exits
and admits no proper-support replacement, the two exit alternatives are
discharged — a smaller closed representative is the delocalization exit, and a
replacement is `lem:replacement` — so what remains is exactly the manuscript's
blocker alternative: two realizations the attempted determination identifies
which are separated, either by their boundary degree profiles, which is the
blocker of type (d), or by a boundaried context, which is the blocker of type
(e).  That is `blockerSeparation_of_reducing`, and it is
`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence` at
once: neither proof inspects which coordinates the family holds, which is why
the manuscript gives them the same four cases.

`prop:sparse-pair-independence-dichotomy` is registered at its concrete branch
decision.  The baseline-family instance is proved directly inside node `[129]`
from its incoming survivor fact; this module exposes no detached universal
survival theorem or quotient-system carrier.

**The sandwich.**  `prop:sparse-entropy-sandwich-with-blockers` writes

  `|Π_free| ≤ E_spine(n) + (½σ(G) + 1) log₂ n`,

and its proof is three inequalities: the entropy count on the mixed family
`ℐ_spine ∪ {r_π : π ∈ Π_free}`, the baseline demand `|ℐ_spine| ≥ B₀(n) −
E_spine(n)`, and `lem:incremental-skeleton-room`.  `entropySandwich` below is
that composition with the logarithms cleared, in the same discipline
`def:baseline-spine-demand` is already stated in:

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`,  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`,

whose logarithm is the manuscript's display, because `m − m₀ ≤ ½σ(G) + 1` is
`lem:sparse-slack-surplus` at the branch.  `prop:sparse-entropy-sandwich` is the
same statement at the *full* pair schedule, and
`cor:sparse-pair-entropy-saturation` is its `ℐ_spine = ∅` reading,
`2^{C(|𝒜₀|,2)} ≤ C(N,m)`.

The theorem below is the reusable cancellation step, so its two inputs are the
two inequalities it cancels.  At node `[131]` the concrete mixed family, its
full-rank proof, its entropy count, and this cancellation must be derived inside
the atomic executor from facts on the incoming exact ledger and published as
the node's semantic output.  None of them is transported in a detached package.

The asymptotic tail of `prop:sparse-entropy-sandwich` — *"consequently, if
`E_spine(n) = O(n)` and `|𝒜₀| ≥ c₁σ(G)`, then `σ(G) = O(√n)`"* — is not stated
here.  It is a consequence of the displayed inequality at a branch that supplies
the two rate hypotheses, and it belongs to the node that supplies them.
-/

namespace Hypostructure.Graph

open Hypostructure.Graph.Strategy.InterfaceReplacement

universe u v

/-! ## The dependence dichotomy -/

/-- The canonical two ends of the shoulder chord named by a selected surplus
port.  A chord in the sparse ledger is named by its port `(h,x)`; this map reads
the actual shoulder pair selected by that port.  The fallback is used only off
the selected active family and is never charged by the blocker ledger. -/
noncomputable def pairResponseChordEnds
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (demand : object.Vertex × object.Vertex) :
    object.Vertex × object.Vertex := by
  classical
  if member : demand ∈ object.excessPorts threshold then
    let shoulders := active.shoulderPair demand member
    exact (shoulders.choose, shoulders.choose_spec.choose)
  else
    exact demand

/-- Clause (f), at one literal pair.  A chord is named by its selected surplus
port.  The full compatible suppression family is indexed by `pair`, while
`chords` is exactly the (possibly proper) subset of its added shoulder chords
used by the accepted cycle.  The endpoint clause identifies those names with
the actual shoulders of the compatible configurations; hence this predicate
contains precisely concrete suppressed-family chord sets, not a flag saying
that some obstruction exists. -/
noncomputable def SparsePairSuppressionChordObstruction
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold)
    (pair chords : Finset (object.Vertex × object.Vertex)) : Prop := by
  classical
  exact pair ⊆ object.excessPorts threshold ∧
    ∃ (family : TightVertexSuppression.CompatibleFamily object)
      (certificate : Graph.CycleCertificate family.suppressed LengthOK),
      (Finset.univ.image (fun index : family.Index =>
          ((family.configuration index).center,
            (family.configuration index).vertex)) = pair) ∧
        (∀ index : family.Index,
          pairResponseChordEnds active
              ((family.configuration index).center,
                (family.configuration index).vertex) =
                ((family.configuration index).left,
                  (family.configuration index).right) ∨
            pairResponseChordEnds active
              ((family.configuration index).center,
                (family.configuration index).vertex) =
                ((family.configuration index).right,
                  (family.configuration index).left)) ∧
        (family.usedChords certificate.walk).image (fun index =>
          ((family.configuration index).center,
            (family.configuration index).vertex)) = chords

/-- The active-family certificate determines the concrete response activation
used by `def:sparse-pair-response`.  Clauses (d) and (e) are populated by the
failed quotient at `[132]`; clause (f) is already the exact finite family of
actual compatible-suppression chord sets belonging to each pair. -/
noncomputable def pairResponseActivation
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    object.DemandActivation (object.PairCoordinate)
      (object.Vertex × object.Vertex) := by
  classical
  let supportOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      let port := object.surplusPortOfMem member
      let shoulders := active.shoulderPair demand member
      let left := shoulders.choose
      let right := shoulders.choose_spec.choose
      let description := shoulders.choose_spec.choose_spec.1
      let distinct := shoulders.choose_spec.choose_spec.2
      let activated := active.activated demand member left right description distinct
      port.declaredSupport activated.1 activated.2.1
    else ∅
  let returnOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      let port := object.surplusPortOfMem member
      let shoulders := active.shoulderPair demand member
      let left := shoulders.choose
      let right := shoulders.choose_spec.choose
      let description := shoulders.choose_spec.choose_spec.1
      let distinct := shoulders.choose_spec.choose_spec.2
      let activated := active.activated demand member left right description distinct
      port.returnSupport activated.1
    else ∅
  let bufferOf := fun demand : object.Vertex × object.Vertex =>
    if member : demand ∈ object.excessPorts threshold then
      (object.surplusPortOfMem member).support
    else ∅
  exact {
    declaredSupport := supportOf
    returnSupport := returnOf
    localBuffer := bufferOf
    profileObstructions := fun _ => ∅
    responseObstructions := fun _ => ∅
    chordObstructions := fun pair =>
      (object.excessPorts threshold).powerset.filter fun chords =>
        SparsePairSuppressionChordObstruction active pair chords }

/-- The active-family fact constructs the concrete response activation. -/
theorem existsPairResponseActivation
    {Baseline Target : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {threshold : Nat}
    (active : ActiveSurplusDemands Baseline Target LengthOK object threshold) :
    Nonempty (object.DemandActivation (object.PairCoordinate)
      (object.Vertex × object.Vertex)) :=
  ⟨pairResponseActivation active⟩

/-- Clause (d) at a specified pair: a functional attempted quotient is
rank-reducing, has an inclusion-minimal determination certificate for that
pair's actual response coordinate, and identifies two different boundary
degree profiles. -/
def SparsePairDEProfileObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  let coordinate := FiniteObject.DemandActivation.pairCoordinate pair
    ((activation.pairSupport pair).getD ∅)
  ∃ attempt : AttemptedQuotient Baseline
      (Graph.HasCycleWithLength LengthOK) object family coordinateSupport,
    attempt.toRankQuotient.FunctionalOn ↑family ∧
      ¬ Set.InjOn attempt.label ↑family ∧
      (∃ determiners : Finset object.PairCoordinate,
        coordinate ∈ family ∧
          determiners ⊆ family ∧
          coordinate ∉ determiners ∧
          attempt.toRankQuotient.Determines coordinate ↑determiners ∧
          ∀ candidate ⊆ determiners,
            attempt.toRankQuotient.Determines coordinate ↑candidate →
              determiners ⊆ candidate) ∧
      ∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile

/-- Clause (e) at a specified pair, with the same literal minimal
determination certificate.  Its final witness is exactly either a distinguishing
target context or the target-complete proper-support replacement supplied by
the attempted quotient. -/
def SparsePairDEResponseObstructionAt
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (pair : Finset (object.Vertex × object.Vertex)) : Prop :=
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  let coordinate := FiniteObject.DemandActivation.pairCoordinate pair
    ((activation.pairSupport pair).getD ∅)
  ∃ attempt : AttemptedQuotient Baseline
      (Graph.HasCycleWithLength LengthOK) object family coordinateSupport,
    attempt.toRankQuotient.FunctionalOn ↑family ∧
      ¬ Set.InjOn attempt.label ↑family ∧
      (∃ determiners : Finset object.PairCoordinate,
        coordinate ∈ family ∧
          determiners ⊆ family ∧
          coordinate ∉ determiners ∧
          attempt.toRankQuotient.Determines coordinate ↑determiners ∧
          ∀ candidate ⊆ determiners,
            attempt.toRankQuotient.Determines coordinate ↑candidate →
              determiners ⊆ candidate) ∧
      ((∃ left right, attempt.Identifies left right ∧
          Response.TargetDefect (Graph.HasCycleWithLength LengthOK) left right) ∨
        ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
          attempt.support)

/-- A concrete type-(d) or type-(e) obstruction carried by its actual pair in
`Π`.  The pair is part of the local predicate, so this cannot be discharged by
an obstruction belonging to a different coordinate. -/
def HasSparsePairDEBlocker
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) : Prop :=
  ∃ pair ∈ pairs,
    SparsePairDEProfileObstructionAt
        (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair ∨
      SparsePairDEResponseObstructionAt
        (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair

/-- The declared coordinate used to record the certified pair obstruction. -/
noncomputable def sparsePairDECoordinate
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (certificate : HasSparsePairDEBlocker
      (Baseline := Baseline) (LengthOK := LengthOK) activation pairs) :
    object.PairCoordinate :=
  FiniteObject.DemandActivation.pairCoordinate certificate.choose
    ((activation.pairSupport certificate.choose).getD ∅)

/-- Install every concrete type-(d)/(e) obstruction into the same activation
used to define the pair-response family.  This is a canonical definition of the
full finite blocker family; it does not depend on which witness exposed the
blocked branch. -/
noncomputable def recordSparsePairDEBlockers
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex))) :
    object.DemandActivation (object.PairCoordinate) Chord := by
  classical
  exact {
    declaredSupport := activation.declaredSupport
    returnSupport := activation.returnSupport
    localBuffer := activation.localBuffer
    profileObstructions := fun pair =>
      if SparsePairDEProfileObstructionAt
          (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair then
        {FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)}
      else ∅
    responseObstructions := fun pair =>
      if SparsePairDEResponseObstructionAt
          (Baseline := Baseline) (LengthOK := LengthOK) activation pairs pair then
        {FiniteObject.DemandActivation.pairCoordinate pair
          ((activation.pairSupport pair).getD ∅)}
      else ∅
    chordObstructions := activation.chordObstructions }

theorem recordedSparsePairDEBlocker_nonempty
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (certificate : HasSparsePairDEBlocker
      (Baseline := Baseline) (LengthOK := LengthOK) activation pairs) :
    ∃ pair ∈ pairs,
      ((recordSparsePairDEBlockers (Baseline := Baseline) (LengthOK := LengthOK)
        activation pairs).blockers pair).Nonempty := by
  classical
  let pair := certificate.choose
  have pairMem := certificate.choose_spec.1
  let coordinate := sparsePairDECoordinate activation pairs certificate
  refine ⟨pair, pairMem, ?_⟩
  rcases certificate.choose_spec.2 with profile | response
  · exact ((recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs).exists_blocks_iff_blockers_nonempty pair).mp
      ⟨.boundaryProfile,
        (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) activation pairs).blocks_boundaryProfile
          (coordinate := coordinate)
          (by
            change coordinate ∈
              (if SparsePairDEProfileObstructionAt
                  (Baseline := Baseline) (LengthOK := LengthOK)
                  activation pairs pair then {coordinate} else ∅)
            rw [if_pos profile]
            simp)⟩
  · exact ((recordSparsePairDEBlockers (Baseline := Baseline)
      (LengthOK := LengthOK) activation pairs).exists_blocks_iff_blockers_nonempty pair).mp
      ⟨.targetResponse,
        (recordSparsePairDEBlockers (Baseline := Baseline)
          (LengthOK := LengthOK) activation pairs).blocks_targetResponse
          (coordinate := coordinate)
          (by
            change coordinate ∈
              (if SparsePairDEResponseObstructionAt
                  (Baseline := Baseline) (LengthOK := LengthOK)
                  activation pairs pair then {coordinate} else ∅)
            rw [if_pos response]
            simp)⟩

/-- **`lem:sparse-pair-dependence-exit`.**

For the concrete response family `ℛ_Π`, failure to survive its declared
admissible quotient system produces exactly one of the paper's outcomes: a
sparse surplus exit, or a certified type-(d)/(e) blocker on a member of `Π`.
The four cases and their order are inherited directly from
`AttemptedQuotient.route`. -/
theorem sparsePairDependence_exit_or_blocker
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate Chord : Type u}
    (activation : object.DemandActivation Coordinate Chord)
    (pairs : Finset (Finset (object.Vertex × object.Vertex)))
    (attempt :
      let family := activation.pairFamily pairs
      let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
        letI := object.vertices.decEq
        exact DeclaredSignature.Coordinate.support
      AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK) object
        family coordinateSupport)
    (reducing :
      let family := activation.pairFamily pairs
      ¬ Set.InjOn attempt.label ↑family)
    (functional :
      let family := activation.pairFamily pairs
      attempt.toRankQuotient.FunctionalOn ↑family) :
    SparseSurplusExit Baseline (Graph.HasCycleWithLength LengthOK) LengthOK object ∨
      HasSparsePairDEBlocker (Baseline := Baseline) (LengthOK := LengthOK)
        activation pairs := by
  classical
  let family := activation.pairFamily pairs
  let coordinateSupport : object.PairCoordinate → Finset object.Vertex := by
    letI := object.vertices.decEq
    exact DeclaredSignature.Coordinate.support
  change ¬ Set.InjOn attempt.label ↑family at reducing
  change attempt.toRankQuotient.FunctionalOn ↑family at functional
  let quotient := attempt.toRankQuotient
  let candidates : Finset (Finset object.PairCoordinate) :=
    family.powerset.filter fun independent =>
      Set.InjOn attempt.label ↑independent
  have candidatesNonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨independent, independentMember, maximum⟩ :=
    Finset.exists_mem_eq_sup candidates candidatesNonempty Finset.card
  have independentFacts : independent ⊆ family ∧
      Set.InjOn attempt.label ↑independent := by
    simpa [candidates] using independentMember
  obtain ⟨coordinate, coordinateMember, coordinateOutside⟩ :
      ∃ coordinate ∈ family, coordinate ∉ independent := by
    by_contra absent
    push Not at absent
    have equal : independent = family :=
      Finset.Subset.antisymm independentFacts.1 absent
    apply reducing
    rw [← equal]
    exact independentFacts.2
  let candidate := insert coordinate independent
  have candidateSubset : candidate ⊆ family := by
    intro member membership
    simp only [candidate, Finset.mem_insert] at membership
    rcases membership with rfl | membership
    · exact coordinateMember
    · exact independentFacts.1 membership
  have candidateNotInjective : ¬ Set.InjOn attempt.label ↑candidate := by
    intro candidateInjective
    have candidateMember : candidate ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨candidateSubset, candidateInjective⟩
    have bound := Finset.le_sup (f := Finset.card) candidateMember
    rw [maximum] at bound
    have larger : independent.card < candidate.card := by
      simp [candidate, coordinateOutside]
    omega
  have candidateReducing :
      ¬ quotient.LabelInjectiveOn
        (insert coordinate (↑independent : Set object.PairCoordinate)) := by
    change ¬ Set.InjOn attempt.label
      (insert coordinate (↑independent : Set object.PairCoordinate))
    simpa [candidate] using candidateNotInjective
  obtain ⟨determiners, finite, determinersSubset, determines⟩ :=
    functional independentFacts.1 coordinateMember coordinateOutside
      independentFacts.2 candidateReducing
  let certificates : Finset (Finset object.PairCoordinate) :=
    finite.toFinset.powerset.filter fun certificate =>
      quotient.Determines coordinate ↑certificate
  have certificatesNonempty : certificates.Nonempty := by
    refine ⟨finite.toFinset, ?_⟩
    simp [certificates, quotient, determines]
  obtain ⟨minimalDeterminers, minimal⟩ :=
    certificates.exists_minimal certificatesNonempty
  have minimalFacts : minimalDeterminers ⊆ finite.toFinset ∧
      quotient.Determines coordinate ↑minimalDeterminers := by
    simpa [certificates] using minimal.1
  have minimalSubsetFamily : minimalDeterminers ⊆ family := by
    intro determiner membership
    exact independentFacts.1 (determinersSubset (by
      simpa using minimalFacts.1 membership))
  have coordinateNotMinimal : coordinate ∉ minimalDeterminers := by
    intro membership
    exact coordinateOutside (determinersSubset (by
      simpa using minimalFacts.1 membership))
  have inclusionMinimal : ∀ other ⊆ minimalDeterminers,
      quotient.Determines coordinate ↑other → minimalDeterminers ⊆ other := by
    intro other subset otherDetermines
    apply minimal.2
    · simp only [certificates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨subset.trans minimalFacts.1, otherDetermines⟩
    · exact subset
  obtain ⟨pair, pairMem, pairEq⟩ : ∃ pair ∈ pairs,
      FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅) = coordinate := by
    change coordinate ∈ pairs.image (fun pair =>
      FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅)) at coordinateMember
    exact Finset.mem_image.mp coordinateMember
  subst coordinate
  have determination :
      ∃ determiners : Finset object.PairCoordinate,
        FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅) ∈ family ∧
          determiners ⊆ family ∧
          FiniteObject.DemandActivation.pairCoordinate pair
              ((activation.pairSupport pair).getD ∅) ∉ determiners ∧
          quotient.Determines
              (FiniteObject.DemandActivation.pairCoordinate pair
                ((activation.pairSupport pair).getD ∅)) ↑determiners ∧
          ∀ candidate ⊆ determiners,
            quotient.Determines
                (FiniteObject.DemandActivation.pairCoordinate pair
                  ((activation.pairSupport pair).getD ∅)) ↑candidate →
              determiners ⊆ candidate := by
    refine ⟨minimalDeterminers, ?_, minimalSubsetFamily,
      coordinateNotMinimal, minimalFacts.2, inclusionMinimal⟩
    change FiniteObject.DemandActivation.pairCoordinate pair
        ((activation.pairSupport pair).getD ∅) ∈
      pairs.image (fun candidate =>
        FiniteObject.DemandActivation.pairCoordinate candidate
          ((activation.pairSupport candidate).getD ∅))
    exact Finset.mem_image_of_mem _ pairMem
  rcases attempt.route reducing with profiles | defect | replacement |
      ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inr ⟨pair, pairMem, Or.inl
      ⟨attempt, functional, reducing, determination, profiles⟩⟩
  · exact Or.inr ⟨pair, pairMem, Or.inr
      ⟨attempt, functional, reducing, determination, Or.inl defect⟩⟩
  · exact Or.inr ⟨pair, pairMem, Or.inr
      ⟨attempt, functional, reducing, determination, Or.inr replacement⟩⟩
  · exact Or.inl (.delocalization representative smaller baseline transfer)

/-- **`lem:sparse-pair-dependence-exit` and `lem:mixed-sparse-spine-dependence`,
at a survivor.**

> Suppose the coordinate family `ℛ_Π` does not survive every admissible rank
> quotient.  Then either `G` has a sparse surplus exit, or some `π ∈ Π` has a
> sparse surplus blocker of type (d) or (e).

The two exit alternatives the manuscript's proof produces are discharged by the
survivor's own hypotheses — the whole-graph case is the delocalization exit, and
the proper-support case is `lem:replacement` — so what a rank-reducing attempted
determination leaves is precisely the blocker: two realizations it identifies
which are separated by their boundary degree profiles (type (d)) or by a
boundaried context (type (e)).

Both witnesses are the concrete finite objects `def:surplus-blockers` names,
which is what `DemandActivation.blocks_boundaryProfile` and
`blocks_targetResponse` record on the ledger. -/
theorem blockerSeparation_of_reducing
    {Baseline : FiniteObject.{u} → Prop} {LengthOK : Nat → Prop}
    {object : FiniteObject.{u}} {Coordinate : Type u}
    {family : Finset Coordinate}
    {coordinateSupport : Coordinate → Finset object.Vertex}
    (survives : SurvivesSparseExits Baseline
      (Graph.HasCycleWithLength LengthOK) LengthOK object)
    (noReplacement : ∀ support : Finset object.Vertex,
      ¬ ReplacementSupport Baseline (Graph.HasCycleWithLength LengthOK) object
        support)
    (attempt : AttemptedQuotient Baseline (Graph.HasCycleWithLength LengthOK)
      object family coordinateSupport)
    (reducing : ¬ Set.InjOn attempt.label ↑family) :
    (∃ left right, attempt.Identifies left right ∧
        left.boundaryDegreeProfile ≠ right.boundaryDegreeProfile) ∨
      (∃ left right, attempt.Identifies left right ∧
        Response.TargetDefect (Graph.HasCycleWithLength LengthOK) left right) := by
  rcases attempt.route reducing with profiles | defect | replacement |
    ⟨representative, smaller, baseline, transfer⟩
  · exact Or.inl profiles
  · exact Or.inr defect
  · exact absurd replacement (noReplacement _)
  · exact absurd (SparseSurplusExit.delocalization representative smaller baseline
      transfer) survives

/-! ## The entropy sandwich -/

/-- **`prop:sparse-entropy-sandwich-with-blockers`, with the logarithms
cleared.**

  `2^{|ℐ_spine| + |Π_free|} ≤ C(N,m)`  and  `C(N,m₀) ≤ 2^{|ℐ_spine| + E}`
  ⟹ `2^{|Π_free|} ≤ 2^{E} · n^{m − m₀}`.

Taking `log₂` gives the manuscript's

  `|Π_free| ≤ E_spine(n) + (m − m₀)·log₂ n`,

and `m − m₀ ≤ ½σ(G) + 1` is the branch's own slack identity, which is why the
display carries `(½σ(G) + 1) log₂ n`.

The proof is the manuscript's three steps and nothing else: the entropy count on
the mixed family, `lem:incremental-skeleton-room` at the object's own edge count,
and the baseline demand.  The spine count cancels because it appears on both
sides, which is the sense in which the sandwich charges only the *free* pairs. -/
theorem entropySandwich (object : FiniteObject.{u})
    {baselineDegree spineCount freeCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + freeCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ freeCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) := by
  have room := skeletonBudget_le_cubicBaselineBudget_mul_pow object baseline above
  have chain :
      2 ^ spineCount * 2 ^ freeCount ≤
        2 ^ spineCount *
          (2 ^ deficit *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
    calc 2 ^ spineCount * 2 ^ freeCount
        = 2 ^ (spineCount + freeCount) := by rw [pow_add]
      _ ≤ skeletonBudget object := entropy
      _ ≤ cubicBaselineBudget object.vertexCount baselineDegree *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) := room
      _ ≤ 2 ^ (spineCount + deficit) *
            object.vertexCount ^
              (object.edgeCount -
                cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
          Nat.mul_le_mul_right _ demand
      _ = 2 ^ spineCount *
            (2 ^ deficit *
              object.vertexCount ^
                (object.edgeCount -
                  cubicBaselineEdgeCount object.vertexCount baselineDegree)) := by
          rw [pow_add, Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left chain (Nat.two_pow_pos spineCount)

/-- **`prop:sparse-entropy-sandwich`**: the same bound at the *full* pair
schedule.

The manuscript states it for `C(|𝒜₀|,2)` rather than for `|Π_free|`, under the
stronger hypothesis that *no* pair has a blocker — in which case `Π_free` is the
whole schedule.  So it is `entropySandwich` read at `freeCount = C(|𝒜₀|,2)`, and
nothing is proved twice. -/
theorem entropySandwich_of_unblocked (object : FiniteObject.{u})
    {baselineDegree spineCount pairCount deficit : Nat}
    (baseline : 2 ≤ baselineDegree)
    (above : cubicBaselineEdgeCount object.vertexCount baselineDegree ≤
      object.edgeCount)
    (entropy : 2 ^ (spineCount + pairCount) ≤ skeletonBudget object)
    (demand : cubicBaselineBudget object.vertexCount baselineDegree ≤
      2 ^ (spineCount + deficit)) :
    2 ^ pairCount ≤
      2 ^ deficit *
        object.vertexCount ^
          (object.edgeCount -
            cubicBaselineEdgeCount object.vertexCount baselineDegree) :=
  entropySandwich object baseline above entropy demand

/-- **`cor:sparse-pair-entropy-saturation`, with the logarithm cleared.**

> If `G` survives the sparse surplus exits and no pair in `C(𝒜₀,2)` has a sparse
> surplus blocker, then `C(|𝒜₀|,2) ≤ log₂ C(C(n,2), m)`.

This is the entropy count at `ℐ_spine = ∅`: `2^{C(|𝒜₀|,2)} ≤ C(N,m)`, which is
`Graph.skeletonBudget` at the object's own order and edge count.  The manuscript
derives it from `prop:sparse-pair-independence-dichotomy` together with
`lem:independent-target-entropy` and `lem:skeleton-dominates`, and that is
exactly the composition the `entropy` hypothesis names. -/
theorem entropySaturation_of_unblocked (object : FiniteObject.{u})
    {pairCount : Nat}
    (entropy : 2 ^ (0 + pairCount) ≤ skeletonBudget object) :
    2 ^ pairCount ≤ skeletonBudget object := by
  simpa using entropy

end Hypostructure.Graph
