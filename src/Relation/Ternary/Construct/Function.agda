open import Relation.Ternary.Core

module Relation.Ternary.Construct.Function {a b} {A : Set a} {B : Set b} {{rb : Rel₃ B}} where

open import Data.Product

open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  F = A → B

instance →-rel : Rel₃ F
Rel₃._∙_≣_ →-rel f g h = ∀ a → f a ∙ g a ≣ h a

module _ {e} {_≈_ : B → B → Set e} {{sgb : IsPartialSemigroup _≈_ rb}} where

  _≈→_ : F → F → Set _
  f ≈→ g = ∀ a → f a ≈ g a

  instance →-semigroup : IsPartialSemigroup _≈→_ →-rel
  IsPartialSemigroup.≈-equivalence →-semigroup = ≈→-isEquivalence
    where
      ≈→-isEquivalence : IsEquivalence _≈→_
      IsEquivalence.refl ≈→-isEquivalence _          = ≈-refl
      IsEquivalence.sym ≈→-isEquivalence eq a        = ≈-sym (eq a)
      IsEquivalence.trans ≈→-isEquivalence eq₁ eq₂ a = ≈-trans (eq₁ a) (eq₂ a)

  Respect.coe (IsPartialSemigroup.∙-respects-≈ →-semigroup) eq σ a = coe (eq a) (σ a)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ →-semigroup) eq σ a = coe (eq a) (σ a)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ →-semigroup) eq σ a = coe (eq a) (σ a)

  IsPartialSemigroup.∙-assocᵣ →-semigroup σ₁ σ₂ =
   -, (λ a → proj₁ (proj₂ (∙-assocᵣ (σ₁ a) (σ₂ a))))
    , (λ a → proj₂ (proj₂ (∙-assocᵣ (σ₁ a) (σ₂ a))))
  IsPartialSemigroup.∙-assocₗ →-semigroup σ₁ σ₂ =
   -, (λ a → proj₁ (proj₂ (∙-assocₗ (σ₁ a) (σ₂ a))))
    , (λ a → proj₂ (proj₂ (∙-assocₗ (σ₁ a) (σ₂ a))))

module _ {{cb : IsCommutative rb}} where

  instance →-commutative : IsCommutative →-rel
  IsCommutative.∙-comm →-commutative σ₁ a = ∙-comm (σ₁ a)

module _ {e} {_≈_ : B → B → Set e} {u} {{cb : IsPartialMonoid _≈_ rb u}} where

  instance →-empty : Emptiness {A = F} (λ _ → u)
  →-empty = record {}

  instance →-monoid : IsPartialMonoid _≈→_ →-rel (λ _ → u)
  IsPartialMonoid.∙-idˡ →-monoid a = ∙-idˡ
  IsPartialMonoid.∙-idʳ →-monoid a = ∙-idʳ
  IsPartialMonoid.∙-id⁻ˡ →-monoid σ a = ∙-id⁻ˡ (σ a)
  IsPartialMonoid.∙-id⁻ʳ →-monoid σ a = ∙-id⁻ʳ (σ a)
