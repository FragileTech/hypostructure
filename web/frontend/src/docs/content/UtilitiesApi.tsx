import { ApiReference, ReferenceLegend, type ApiModule } from "./ApiReference";

const CEIL_SQRT: ApiModule = {
  title: "Hypostructure.Core.CeilSqrt",
  paths: ["hypostructure/Hypostructure/Core/CeilSqrt.lean"],
  intro:
    "The integer ceiling square root: a scale basis a problem can register a threshold against, computed from Lean's certified integer square root.",
  entries: [
    {
      name: "ceilSqrt",
      kind: "def",
      audience: "application",
      signature: `
        def ceilSqrt (size : Nat) : Nat :=
          if Nat.sqrt size ^ 2 = size then Nat.sqrt size else Nat.sqrt size + 1

        @[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0`,
      note: "Integer ceiling of the square root.",
    },
    {
      name: "le_ceilSqrt_sq / ceilSqrt_le_sqrt_succ",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem le_ceilSqrt_sq (size : Nat) : size ≤ ceilSqrt size ^ 2
        theorem ceilSqrt_le_sqrt_succ (size : Nat) : ceilSqrt size ≤ Nat.sqrt size + 1`,
      note: "The ceiling square root covers the source size, and exceeds the floor by at most one.",
    },
    {
      name: "log2_le_ceilSqrt",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem log2_le_ceilSqrt (size : Nat) : Nat.log2 size ≤ ceilSqrt size`,
      note: "The binary logarithm is bounded by the integer ceiling square root.",
    },
    {
      name: "mul_ceilSqrt_le",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem mul_ceilSqrt_le (scale rate size : Nat)
            (dominates : scale * scale ≤ rate * rate * size) :
            scale * ceilSqrt size ≤ rate * size + scale`,
      note: "A √n-scaled quantity is eventually below any positive linear one; the additive scale is the ceiling's own rounding.",
    },
  ],
};

const DYADIC: ApiModule = {
  title: "Hypostructure.Core.DyadicLength",
  paths: ["hypostructure/Hypostructure/Core/DyadicLength.lean"],
  intro:
    "Executable dyadic length algebra on Nat: a decidable, bounded-exponent predicate for powers of two, kept equivalent to the unbounded form external theorems are stated in.",
  entries: [
    {
      name: "PowerOfTwoLength",
      kind: "def",
      audience: "application",
      signature: `
        def PowerOfTwoLength (length : Nat) : Prop :=
          ∃ exponent : Fin (length + 1), 2 ≤ exponent.1 ∧ length = 2 ^ exponent.1

        instance powerOfTwoLengthDecidable (length : Nat) : Decidable (PowerOfTwoLength length)`,
      note: "Executable predicate for lengths that are powers of two with exponent at least two.",
    },
    {
      name: "powerOfTwoLength_iff / powerOfTwoLength_of_exists",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem powerOfTwoLength_iff (length : Nat) :
            PowerOfTwoLength length ↔ ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent

        theorem powerOfTwoLength_of_exists {length : Nat}
            (witness : ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent) :
            PowerOfTwoLength length`,
      note: "The executable predicate is equivalent to the unbounded exponent form; the bridge external theorems consume.",
    },
    {
      name: "powerOfTwoLength_four",
      kind: "theorem",
      audience: "application",
      signature: `
        theorem powerOfTwoLength_four : PowerOfTwoLength 4`,
      note: "Four is the first accepted dyadic length.",
    },
    {
      name: "MersenneLength / mersenneLength_iff / MersenneSet",
      kind: "def",
      audience: "application",
      signature: `
        def MersenneLength (length : Nat) : Prop := PowerOfTwoLength (length + 1)
        instance mersenneLengthDecidable (length : Nat) : Decidable (MersenneLength length)

        theorem mersenneLength_iff (length : Nat) :
            MersenneLength length ↔ ∃ exponent : Nat, 2 ≤ exponent ∧ length = 2 ^ exponent - 1

        def MersenneSet : Set Nat := {length | MersenneLength length}`,
      note: "Lengths whose successor is an accepted dyadic length: exactly 2^k − 1 for k ≥ 2.",
    },
  ],
};

const TARGET_RANK: ApiModule = {
  title: "Hypostructure.Core.TargetRank",
  paths: ["hypostructure/Hypostructure/Core/TargetRank.lean"],
  intro:
    "Target rank of a finite coordinate family under an admissible quotient system: relabellings, label-injectivity, survival of subfamilies, and the maximum surviving size. Nothing here knows what a coordinate is.",
  entries: [
    {
      name: "RankQuotient",
      kind: "structure",
      audience: "application",
      signature: `
        structure RankQuotient (Coordinate : Type u) where
          Label : Type v
          Value : Type v
          Realization : Type v
          label : Coordinate → Label
          value : Realization → Label → Value`,
      note: "A quotient relabels the declared coordinates and assigns each realization a value per label.",
    },
    {
      name: "RankQuotient.response",
      kind: "def",
      audience: "application",
      signature: `
        def RankQuotient.response (quotient : RankQuotient Coordinate)
            (realization : quotient.Realization) (coordinate : Coordinate) : quotient.Value`,
      note: "The value of a declared coordinate in one realization.",
    },
    {
      name: "RankQuotient.LabelInjectiveOn / RankReducingOn",
      kind: "def",
      audience: "application",
      signature: `
        def RankQuotient.LabelInjectiveOn (quotient : RankQuotient Coordinate)
            (family : Set Coordinate) : Prop := Set.InjOn quotient.label family

        def RankQuotient.RankReducingOn (quotient : RankQuotient Coordinate)
            (family : Set Coordinate) : Prop := ¬ quotient.LabelInjectiveOn family

        theorem RankQuotient.LabelInjectiveOn.mono (subset : smaller ⊆ larger)
            (injective : quotient.LabelInjectiveOn larger) : quotient.LabelInjectiveOn smaller
        theorem RankQuotient.RankReducingOn.mono (subset : smaller ⊆ larger)
            (reducing : quotient.RankReducingOn smaller) : quotient.RankReducingOn larger`,
      note: "Label-injective on a subfamily: every coordinate retained and no two identified. Rank-reducing is its negation.",
    },
    {
      name: "RankQuotient.Determines / FunctionalOn",
      kind: "def",
      audience: "application",
      signature: `
        def RankQuotient.Determines (quotient : RankQuotient Coordinate)
            (coordinate : Coordinate) (determiners : Set Coordinate) : Prop

        def RankQuotient.FunctionalOn (quotient : RankQuotient Coordinate)
            (family : Set Coordinate) : Prop`,
      note: "Determination: a coordinate's quotient value is a function of the values on a set of determiners. Functional: whenever a subfamily is label-injective but adding one coordinate breaks that, the added coordinate is determined by a finite subfamily.",
    },
    {
      name: "QuotientSystem",
      kind: "structure",
      audience: "application",
      signature: `
        structure QuotientSystem (Coordinate : Type u) (family : Finset Coordinate) where
          Member : RankQuotient Coordinate → Prop
          functional : ∀ {q}, Member q → q.FunctionalOn ↑family
          State : Type v
          targetComplete : State → Prop
          response : State → Coordinate → Bool
          existsTargetComplete : ∃ state, targetComplete state`,
      note: "The admissible quotient system used to compute target rank; membership is left abstract, so every theorem below holds for every such system.",
    },
    {
      name: "QuotientSystem.Survives",
      kind: "def",
      audience: "application",
      signature: `
        def QuotientSystem.Survives (system : QuotientSystem Coordinate family)
            (subfamily : Set Coordinate) : Prop

        theorem QuotientSystem.Survives.mono (subset : smaller ⊆ larger)
            (survives : system.Survives larger) : system.Survives smaller
        theorem QuotientSystem.survives_empty (system) : system.Survives (∅ : Set Coordinate)`,
      note: "Independent target-testability: every Boolean assignment on the subfamily is realized by a target-complete state.",
    },
    {
      name: "targetRank",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def survivingSubfamilies (system : QuotientSystem Coordinate family) :
            Finset (Finset Coordinate)
        noncomputable def targetRank (system : QuotientSystem Coordinate family) : Nat :=
          (survivingSubfamilies system).sup Finset.card

        theorem card_le_targetRank (subset : subfamily ⊆ family)
            (survives : system.Survives ↑subfamily) : subfamily.card ≤ targetRank system
        theorem targetRank_le_card (system) : targetRank system ≤ family.card
        theorem exists_attaining (system) :
            ∃ independent ⊆ family, system.Survives ↑independent ∧ independent.card = targetRank system
        theorem targetRank_eq_card_iff_survives (system) :
            targetRank system = family.card ↔ system.Survives ↑family`,
      note: "The maximum size of a subfamily that survives every functional admissible quotient of the system, and its basic bounds.",
    },
    {
      name: "QuotientSystem.Dependence",
      kind: "structure",
      audience: "application",
      signature: `
        structure QuotientSystem.Dependence (system : QuotientSystem Coordinate family)
            (coordinate : Coordinate) (determiners : Set Coordinate) : Prop where
          determined : coordinate ∈ family
          supported : determiners ⊆ ↑family
          proper : coordinate ∉ determiners
          witness : ∃ quotient, system.Member quotient ∧
            quotient.RankReducingOn ↑family ∧ quotient.Determines coordinate determiners`,
      note: "A target-dependence: a coordinate whose value some rank-reducing member of the system determines from a proper subfamily of the others.",
    },
  ],
};

const TABLES: ApiModule = {
  title: "Hypostructure.Core.Finite.CertifiedTableAggregation",
  paths: ["hypostructure/Hypostructure/Core/Finite/CertifiedTableAggregation.lean"],
  intro:
    "Executable projections from a certified finite table: applications name the table and an index family; Core computes cardinalities, column products and the derived binary rate, so no table-derived numeral is ever copied into a step declaration.",
  entries: [
    {
      name: "product / rowCount",
      kind: "def",
      audience: "application",
      signature: `
        def product {ι} [Fintype ι] (column : ι -> Nat) : Nat := ∏ i, column i
        def rowCount (ι) [Fintype ι] : Nat := Fintype.card ι`,
      note: "Product of a finite column; cardinality of the index family.",
    },
    {
      name: "safeProduct / flatProduct",
      kind: "def",
      audience: "application",
      signature: `
        def safeProduct (table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
          product table.counts.storedSafe
        def flatProduct (table : CertifiedTable profile Length lengthValue relation Index) : Nat :=
          product table.counts.storedFlat`,
      note: "The products of the certified safe-count and flat-count columns.",
    },
    {
      name: "BarrierPresentation",
      kind: "structure",
      audience: "application",
      signature: `
        structure BarrierPresentation where
          size : Nat
          profile : Profile size
          Length : Type u
          lengthValue : Length -> Nat
          relation : Length -> Fin size -> Fin size -> Bool
          Index : Type u
          indexFintype : Fintype Index
          table : CertifiedTable profile Length lengthValue relation Index
          flatPositive : 0 < flatProduct table
          improves : flatProduct table ≤ safeProduct table`,
      note: "A public presentation of one certified finite barrier table: the semantic table once, with positivity and improvement travelling with it.",
    },
    {
      name: "binaryRateFloor",
      kind: "def",
      audience: "application",
      signature: `
        def binaryRateFloor (table) : Nat :=
          if flatProduct table = 0 then 0 else Nat.log2 ((safeProduct table - 1) / flatProduct table)
        def BarrierPresentation.binaryRateFloor (presentation : BarrierPresentation) : Nat

        theorem two_pow_binaryRateFloor_mul_flatProduct_le (table)
            (flatPositive : 0 < flatProduct table) (improves : flatProduct table ≤ safeProduct table) :
            2 ^ binaryRateFloor table * flatProduct table ≤ safeProduct table
        theorem BarrierPresentation.two_pow_binaryRateFloor_mul_flatProduct_le (presentation) :
            2 ^ presentation.binaryRateFloor * flatProduct presentation.table ≤ safeProduct presentation.table`,
      note: "The binary rate a certified table sustains, floored safely so it underestimates the real rate; the inequality is the guarantee, with no numeral in it.",
    },
    {
      name: "binaryRowRateFloor",
      kind: "def",
      audience: "application",
      signature: `
        def binaryRowRateFloor (table) (index : Index) : Nat

        theorem two_pow_binaryRowRateFloor_mul_storedFlat_le (table) (index : Index)
            (flatPositive : 0 < table.counts.storedFlat index)
            (improves : table.counts.storedFlat index ≤ table.counts.storedSafe index) :
            2 ^ binaryRowRateFloor table index * table.counts.storedFlat index ≤
              table.counts.storedSafe index`,
      note: "The same safe floor for one certified row.",
    },
  ],
};

const FINITE: ApiModule = {
  title: "Hypostructure.Core.Finite — schedules, partitions, selections",
  paths: [
    "hypostructure/Hypostructure/Core/Finite/Enumeration.lean",
    "hypostructure/Hypostructure/Core/Finite/Partition.lean",
    "hypostructure/Hypostructure/Core/Finite/ConnectedPartition.lean",
    "hypostructure/Hypostructure/Core/Finite/MaximalSelection.lean",
    "hypostructure/Hypostructure/Core/Finite/EssentialCarrier.lean",
  ],
  intro:
    "Exact finite schedules and the generic operations over them: partitions by a decidable predicate, ordered label partitions, maximal conflict-free selection, and inclusion-minimal complete carriers. Order is proof-relevant execution metadata; set-like reasoning is delegated to Mathlib.",
  entries: [
    {
      name: "Enumeration",
      kind: "structure",
      audience: "application",
      signature: `
        structure Enumeration (α : Type u) where
          values : List α
          nodup : values.Nodup
          decEq : DecidableEq α

        def Enumeration.ofNodupList [DecidableEq α] (values : List α) (nodup : values.Nodup) : Enumeration α
        def Enumeration.card (schedule : Enumeration α) : Nat := schedule.values.length
        def Enumeration.get (schedule : Enumeration α) (index : Fin schedule.card) : α
        def Enumeration.toFinset (schedule : Enumeration α) : Finset α
        noncomputable def Enumeration.indexOfMember (schedule) (value : α) (member : value ∈ schedule.values) : Fin schedule.card
        def Enumeration.map / product / subtype ...`,
      note: "An explicit deterministic schedule for the exact finite family owned by a residual. It does not claim the ambient type is finite.",
    },
    {
      name: "CompleteEnumeration / DependentEnumeration",
      kind: "structure",
      audience: "application",
      signature: `
        structure CompleteEnumeration (α : Type u) extends Enumeration α where
          complete : forall value : α, value ∈ values

        structure DependentEnumeration (index : Type u) (fibre : index -> Type v) where
          indices : Enumeration index
          fibres : (i : index) -> Enumeration (fibre i)
        def DependentEnumeration.flatten (schedule : DependentEnumeration index fibre) :
            Enumeration (Sigma fibre)`,
      note: "The stronger claim that every inhabitant is scheduled; and index-major flattening of a family of schedules.",
    },
    {
      name: "Partition.run",
      kind: "def",
      audience: "application",
      signature: `
        structure Partition.Result (schedule : Enumeration α) (predicate : α -> Prop) where
          accepted : Enumeration {v // predicate v}
          rejected : Enumeration {v // Not (predicate v)}
          card_partition : accepted.card + rejected.card = schedule.card

        def Partition.run (schedule : Enumeration α) (predicate : α -> Prop)
            [DecidablePred predicate] : Partition.Result schedule predicate`,
      note: "The retained/discarded split of one schedule by a decidable predicate, in schedule order, with the lossless cardinality identity.",
    },
    {
      name: "Partition.PaidDiscard",
      kind: "structure",
      audience: "application",
      signature: `
        structure Partition.PaidDiscard (schedule : Enumeration α) (predicate : α -> Prop) (resource : Nat) where
          partition : Partition.Result schedule predicate
          rejected_le_resource : partition.rejected.card <= resource

        def Partition.paidDiscard ... : PaidDiscard schedule predicate resource`,
      note: "A discard certificate registered against the rejected schedule, paid for by a caller-provided resource law.",
    },
    {
      name: "OrderedPartition / ConnectedPartition",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def OrderedPartition.labels (schedule : Enumeration Carrier) (labelOf : Carrier -> Label) : List Label
        noncomputable def OrderedPartition.members (schedule) (labelOf) (label : Label) : Finset Carrier

        noncomputable def ConnectedPartition.order (schedule : Enumeration Carrier) (labelOf : Carrier -> Label) : List Label
        noncomputable def ConnectedPartition.members (schedule) (labelOf) (label : Label) : Finset Carrier
        def ConnectedPartition.checks (schedule : Enumeration Carrier) : Nat := schedule.card`,
      note: "Deduplicated label order from one scan, member sets per label, disjointness and coverage, and a linear scan budget.",
    },
    {
      name: "MaximalSelection",
      kind: "def",
      audience: "application",
      signature: `
        noncomputable def MaximalSelection.chooseMaximal [DecidableEq α] [LE α] [IsTrans α (· ≤ ·)]
            (candidates : Finset α) (nonempty : candidates.Nonempty) : α

        structure MaximalSelection.Profile (schedule : Enumeration α) (conflict : α → α → Prop)
            [DecidableRel conflict] where
          selected : List α
          selected_nodup : selected.Nodup
          pairwiseCompatible : ...
          maximal : ∀ item ∈ schedule.values, ∃ selectedItem ∈ selected,
            conflict item selectedItem ∨ item = selectedItem

        def MaximalSelection.Profile.packingNumber (profile) : Nat := profile.selected.length`,
      note: "A maximal conflict-free selection from a schedule; the producer belongs to the domain, Core owns the shape and work interface.",
    },
    {
      name: "EssentialCarrier.Profile",
      kind: "structure",
      audience: "application",
      signature: `
        structure EssentialCarrier.Profile where
          Carrier : Type u
          schedule : Enumeration Carrier
          Complete : Finset Carrier -> Prop
          completeDecidable : DecidablePred Complete
          fullComplete : Complete schedule.toFinset

        noncomputable def EssentialCarrier.Profile.minimumCard (profile) : Nat
        noncomputable def EssentialCarrier.Profile.core (profile) : Finset profile.Carrier
        theorem EssentialCarrier.Profile.core_complete (profile) : profile.Complete profile.core
        theorem EssentialCarrier.Profile.core_card (profile) : profile.core.card = profile.minimumCard
        theorem EssentialCarrier.Profile.erase_not_complete (profile) (carrier) (mem : carrier ∈ profile.core) :
            ¬ profile.Complete (profile.core.erase carrier)`,
      note: "An inclusion-minimal finite carrier for any decidable completeness predicate; every selected carrier is essential.",
    },
  ],
};

const MODULES = [CEIL_SQRT, DYADIC, TARGET_RANK, TABLES, FINITE];

export function UtilitiesApiPage() {
  return (
    <>
      <header className="docs-header">
        <p className="hero-eyebrow">Reference</p>
        <h1>Utility modules</h1>
        <p className="docs-lead">
          Domain-neutral arithmetic and finite combinatorics whose results
          become fact values. Nothing here touches the ledger; a step calls into
          these from its derivation, or a problem registers data built from
          them. Main entry points only; some binders are elided.
        </p>
        <ReferenceLegend />
      </header>
      <ApiReference modules={MODULES} />
    </>
  );
}
