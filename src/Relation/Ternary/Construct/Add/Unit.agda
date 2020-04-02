open import Relation.Ternary.Core

module Relation.Ternary.Construct.Add.Unit {a} {A : Set a} (div : Rel₃ A) where 

open import Data.Maybe
open import Data.Product
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Respect.Propositional

instance _ = div

module _ where

  data Split? : Maybe A → Maybe A → Maybe A → Set a where
    nothing  : Split? nothing nothing nothing
    right : ∀ {a} → Split? nothing (just a) (just a)
    left : ∀ {a} → Split? (just a) nothing (just a)
    split    : ∀ {a b ab} → a ∙ b ≣ ab → Split? (just a) (just b) (just ab)

  instance maybes : Rel₃ (Maybe A)
  Rel₃._∙_≣_ maybes = Split?

module _ {{_ : IsPartialSemigroup _≡_ div}} where

  instance maybe-semigroup : IsPartialSemigroup _≡_ maybes

  IsPartialSemigroup.≈-equivalence maybe-semigroup = isEquivalence

  IsPartialSemigroup.∙-assocᵣ maybe-semigroup right left  = -, right , left
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup left left  = -, left , nothing
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup (split x) left = -, split x , left
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup right (split x) = -, right , split x
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup left (split x) = -, split x , right
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup (split x₁) (split x)
    with _ , x₂ , x₃ ← ∙-assocᵣ x₁ x                             = -, split x₂ , split x₃
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup nothing nothing    = -, nothing , nothing
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup nothing right   = -, right , right

  IsPartialSemigroup.∙-assocₗ maybe-semigroup nothing nothing = -, nothing , nothing
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right right     = -, nothing , right
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right left      = -, right , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right (split x) = -, right , split x
  IsPartialSemigroup.∙-assocₗ maybe-semigroup left nothing    = -, left , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) right = -, left , split x
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) left  = -, split x , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) (split x₁)
    with _ , x₃ , x₂ ← ∙-assocₗ x x₁                          = -, split x₃ , split x₂

  instance maybe-monoid : IsPartialMonoid _≡_ maybes nothing
  IsPartialMonoid.emptiness maybe-monoid            = record {}
  IsPartialMonoid.ε-unique maybe-monoid refl        = refl
  IsPartialMonoid.∙-idˡ maybe-monoid {nothing}      = nothing
  IsPartialMonoid.∙-idˡ maybe-monoid {just x}       = right
  IsPartialMonoid.∙-idʳ maybe-monoid {nothing}      = nothing
  IsPartialMonoid.∙-idʳ maybe-monoid {just x}       = left
  IsPartialMonoid.∙-id⁻ˡ maybe-monoid nothing = refl
  IsPartialMonoid.∙-id⁻ˡ maybe-monoid right   = refl
  IsPartialMonoid.∙-id⁻ʳ maybe-monoid nothing = refl
  IsPartialMonoid.∙-id⁻ʳ maybe-monoid left    = refl

module _ {{_ : IsCommutative div}} where

  instance maybe-comm : IsCommutative maybes
  IsCommutative.∙-comm maybe-comm nothing   = nothing
  IsCommutative.∙-comm maybe-comm right     = left
  IsCommutative.∙-comm maybe-comm left      = right
  IsCommutative.∙-comm maybe-comm (split x) = split (∙-comm x)
