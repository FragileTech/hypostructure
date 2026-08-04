import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Dependent-owner glue capacity

Domain-generic (Graph and PDE alike): the recurring "many independent local
choices, glued into one global object with an injective finite code, bound
the product of local choice counts by the code capacity" pattern — a Kraft-
style counting argument.  Everything here is symbolic cardinality transport
(`Nat.card`); no finite family is ever scanned or enumerated, matching the
fact that the source argument performs no local check at all.

`Profile` is the plain many-owner glue; `BaseProfile` additionally carries
one symbolic base state (e.g. an ambient completion) alongside the
dependent local choices, gluing both into the same code universe. -/

namespace Hypostructure.Core.DependentOwnerGlueCapacity

open scoped BigOperators

universe u v w z b

/-- The values actually realized by a projection of an existing carrier. -/
def RealizedProjection (Global : Type w) (Base : Type b)
    (project : Global -> Base) :=
  {base : Base // ∃ global : Global, project global = base}

noncomputable instance realizedProjectionFinite
    (Global : Type w) (Base : Type b) (project : Global -> Base)
    [Finite Base] : Finite (RealizedProjection Global Base project) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Every incoming global state yields its canonical realized projection. -/
def realizedProjectionValue {Global : Type w} {Base : Type b}
    (project : Global -> Base) (global : Global) :
    RealizedProjection Global Base project :=
  ⟨project global, ⟨global, rfl⟩⟩

@[simp] theorem realizedProjectionValue_val
    {Global : Type w} {Base : Type b}
    (project : Global -> Base) (global : Global) :
    (realizedProjectionValue project global).1 = project global := rfl

/-- A many-owner semantic glue whose choices are recoverable and whose glued
objects have an injective finite code. -/
structure Profile where
  Owner : Type u
  finiteOwner : Finite Owner
  Local : Owner -> Type v
  finiteLocal : forall owner, Finite (Local owner)
  Global : Type w
  Code : Type z
  finiteCode : Finite Code
  glue : (forall owner, Local owner) -> Global
  restrict : Global -> forall owner, Local owner
  recover : forall choice owner, restrict (glue choice) owner = choice owner
  code : Global -> Code
  codeInjectiveOnGlue : forall left right,
    code (glue left) = code (glue right) -> glue left = glue right

attribute [instance] Profile.finiteOwner Profile.finiteLocal Profile.finiteCode

namespace Profile

variable (profile : Profile)

/-- Sum a natural owner weight over the profile's finite owner type. -/
noncomputable def weightSum (weight : profile.Owner -> Nat) : Nat := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  exact ∑ owner, weight owner

theorem weightSum_add (left right : profile.Owner -> Nat) :
    profile.weightSum (fun owner => left owner + right owner) =
      profile.weightSum left + profile.weightSum right := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  simp [weightSum, Finset.sum_add_distrib]

theorem weightSum_mono {left right : profile.Owner -> Nat}
    (pointwise : forall owner, left owner ≤ right owner) :
    profile.weightSum left ≤ profile.weightSum right := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  exact Finset.sum_le_sum fun owner _ => pointwise owner

theorem glue_injective : Function.Injective profile.glue := by
  intro left right equal
  funext owner
  calc
    left owner = profile.restrict (profile.glue left) owner :=
      (profile.recover left owner).symm
    _ = profile.restrict (profile.glue right) owner :=
        congrArg (fun g => profile.restrict g owner) equal
    _ = right owner := profile.recover right owner

theorem code_glue_injective :
    Function.Injective (fun choice => profile.code (profile.glue choice)) := by
  intro left right equal
  exact profile.glue_injective (profile.codeInjectiveOnGlue left right equal)

/-- Exact dependent product capacity, proved by cardinality transport only. -/
theorem localProduct_le_codeCard :
    Nat.card (forall owner, profile.Local owner) ≤ Nat.card profile.Code :=
  Nat.card_le_card_of_injective _ profile.code_glue_injective

/-- Aggregate ownerwise powered lower bounds through the recoverable
dependent glue; never materializes the Cartesian choice family. -/
theorem base_pow_sumWeight_le_codeCard_pow
    (base exponent : Nat) (weight : profile.Owner -> Nat)
    (localLower : forall owner,
      base ^ weight owner ≤ Nat.card (profile.Local owner) ^ exponent) :
    base ^ profile.weightSum weight ≤ Nat.card profile.Code ^ exponent := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    Fintype.ofFinite _
  change base ^ (∑ owner, weight owner) ≤ Nat.card profile.Code ^ exponent
  have productLower :
      base ^ (∑ owner, weight owner) ≤
        (∏ owner, Nat.card (profile.Local owner)) ^ exponent := by
    calc
      base ^ (∑ owner, weight owner) =
          ∏ owner, base ^ weight owner :=
        (Finset.prod_pow_eq_pow_sum Finset.univ weight base).symm
      _ ≤ ∏ owner, Nat.card (profile.Local owner) ^ exponent :=
        Finset.prod_le_prod' (fun owner _ => localLower owner)
      _ = (∏ owner, Nat.card (profile.Local owner)) ^ exponent :=
        Finset.prod_pow Finset.univ exponent
          (fun owner => Nat.card (profile.Local owner))
  have productCard :
      (∏ owner, Nat.card (profile.Local owner)) =
        Nat.card (forall owner, profile.Local owner) := by
    simp only [Nat.card_eq_fintype_card]
    exact (@Fintype.card_pi profile.Owner profile.Local _ _ _).symm
  rw [productCard] at productLower
  exact productLower.trans
    (Nat.pow_le_pow_left profile.localProduct_le_codeCard exponent)

end Profile

/-! ## One symbolic base state plus dependent local choices

The common capacity contract for a state family that must coexist with
every choice in a dependent local product.  The base family is kept
symbolic through `Finite`; the theorem never enumerates the Cartesian
product of base states and local choices. -/

/-- Recoverable gluing of one symbolic base state with one dependent family
of local choices into a common finite code universe. -/
structure BaseProfile where
  Base : Type b
  finiteBase : Finite Base
  Owner : Type u
  finiteOwner : Finite Owner
  Local : Owner -> Type v
  finiteLocal : forall owner, Finite (Local owner)
  Global : Type w
  Code : Type z
  finiteCode : Finite Code
  glue : Base -> (forall owner, Local owner) -> Global
  recoverBase : Global -> Base
  recoverLocal : Global -> forall owner, Local owner
  recoverBase_glue : forall base choice, recoverBase (glue base choice) = base
  recoverLocal_glue : forall base choice owner,
    recoverLocal (glue base choice) owner = choice owner
  code : Global -> Code
  codeInjectiveOnGlue : forall leftBase rightBase leftChoice rightChoice,
    code (glue leftBase leftChoice) = code (glue rightBase rightChoice) ->
      glue leftBase leftChoice = glue rightBase rightChoice

attribute [instance] BaseProfile.finiteBase BaseProfile.finiteOwner
  BaseProfile.finiteLocal BaseProfile.finiteCode

namespace BaseProfile

variable (profile : BaseProfile)

noncomputable def weightSum (weight : profile.Owner -> Nat) : Nat := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  exact ∑ owner, weight owner

/-- The common code recovers both the symbolic base and every local choice. -/
theorem code_glue_injective :
    Function.Injective (fun pair : profile.Base × (forall owner, profile.Local owner) =>
      profile.code (profile.glue pair.1 pair.2)) := by
  rintro ⟨leftBase, leftChoice⟩ ⟨rightBase, rightChoice⟩ equal
  have glued := profile.codeInjectiveOnGlue
    leftBase rightBase leftChoice rightChoice equal
  apply Prod.ext
  · simpa only [profile.recoverBase_glue] using
      congrArg profile.recoverBase glued
  · funext owner
    simpa only [profile.recoverLocal_glue] using
      congrArg (fun global => profile.recoverLocal global owner) glued

/-- Exact symbolic joint capacity.  No base list or product schedule is
constructed. -/
theorem base_mul_localProduct_le_codeCard :
    Nat.card profile.Base * Nat.card (forall owner, profile.Local owner) ≤
      Nat.card profile.Code := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ profile.code_glue_injective

/-- Aggregate ownerwise powered lower bounds while retaining the independent
symbolic base factor. -/
theorem base_pow_mul_base_pow_sumWeight_le_codeCard_pow
    (base exponent : Nat) (weight : profile.Owner -> Nat)
    (localLower : forall owner,
      base ^ weight owner ≤ Nat.card (profile.Local owner) ^ exponent) :
    Nat.card profile.Base ^ exponent *
        base ^ profile.weightSum weight ≤
      Nat.card profile.Code ^ exponent := by
  classical
  letI : Fintype profile.Owner := Fintype.ofFinite profile.Owner
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    Fintype.ofFinite _
  have localProductLower :
      base ^ (∑ owner, weight owner) ≤
        Nat.card (forall owner, profile.Local owner) ^ exponent := by
    calc
      base ^ (∑ owner, weight owner) =
          ∏ owner, base ^ weight owner :=
        (Finset.prod_pow_eq_pow_sum Finset.univ weight base).symm
      _ ≤ ∏ owner, Nat.card (profile.Local owner) ^ exponent :=
        Finset.prod_le_prod' (fun owner _ => localLower owner)
      _ = (∏ owner, Nat.card (profile.Local owner)) ^ exponent :=
        Finset.prod_pow Finset.univ exponent
          (fun owner => Nat.card (profile.Local owner))
      _ = Nat.card (forall owner, profile.Local owner) ^ exponent := by
        have productCard :
            (∏ owner, Nat.card (profile.Local owner)) =
              Nat.card (forall owner, profile.Local owner) := by
          simp only [Nat.card_eq_fintype_card]
          exact (@Fintype.card_pi profile.Owner profile.Local _ _ _).symm
        rw [productCard]
  have multiplied := Nat.mul_le_mul_left
    (Nat.card profile.Base ^ exponent) localProductLower
  calc
    Nat.card profile.Base ^ exponent *
        base ^ profile.weightSum weight =
        Nat.card profile.Base ^ exponent *
          base ^ (∑ owner, weight owner) := rfl
    _ ≤ Nat.card profile.Base ^ exponent *
        Nat.card (forall owner, profile.Local owner) ^ exponent := multiplied
    _ = (Nat.card profile.Base *
        Nat.card (forall owner, profile.Local owner)) ^ exponent := by
      rw [Nat.mul_pow]
    _ ≤ Nat.card profile.Code ^ exponent :=
      Nat.pow_le_pow_left profile.base_mul_localProduct_le_codeCard exponent

/-- Capacity transport is certificate-only. -/
def checks (_profile : BaseProfile) : Nat := 0

@[simp] theorem checks_eq_zero : profile.checks = 0 := rfl

end BaseProfile

end Hypostructure.Core.DependentOwnerGlueCapacity
