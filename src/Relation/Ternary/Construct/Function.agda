{-# OPTIONS --without-K --safe #-}

open import Relation.Ternary.Core

module Relation.Ternary.Construct.Function {a b} {A : Set a} {B : Set b} {{rb : Rel₃ B}} where

open import Data.Product

open import Algebra.Structures
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  F = A → B

instance →-rel : Rel₃ F
Rel₃._∙_≣_ →-rel f g h = ∀ a → f a ∙ g a ≣ h a

module Pointwise {e} (_≈_ : B → B → Set e) where

  _≈→_ : F → F → Set _
  f ≈→ g = ∀ a → f a ≈ g a
  
  ≈→-isEquivalence : {{_ : IsEquivalence _≈_}} → IsEquivalence _≈→_
  IsEquivalence.refl ≈→-isEquivalence _          = ≈-refl
  IsEquivalence.sym ≈→-isEquivalence eq a        = ≈-sym (eq a)
  IsEquivalence.trans ≈→-isEquivalence eq₁ eq₂ a = ≈-trans (eq₁ a) (eq₂ a)

module _ {e} {_≈_ : B → B → Set e} {{sgb : IsPartialSemigroup _≈_ rb}} where
  open Pointwise _≈_

  instance →-semigroup : IsPartialSemigroup _≈→_ →-rel
  IsPartialSemigroup.≈-equivalence →-semigroup = ≈→-isEquivalence

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
  open Pointwise _≈_

  instance →-empty : Emptiness {A = F} (λ _ → u)
  →-empty = record {}

  instance →-monoid : IsPartialMonoid _≈→_ →-rel (λ _ → u)
  IsPartialMonoid.∙-idˡ →-monoid a = ∙-idˡ
  IsPartialMonoid.∙-idʳ →-monoid a = ∙-idʳ
  IsPartialMonoid.∙-id⁻ˡ →-monoid σ a = ∙-id⁻ˡ (σ a)
  IsPartialMonoid.∙-id⁻ʳ →-monoid σ a = ∙-id⁻ʳ (σ a)

module _ {e} {_≈_ : B → B → Set e} {op} {{_ : IsEquivalence _≈_}} {{sgb : IsTotal _≈_ rb op}} where
  open Pointwise _≈_
  private
    op' : F → F → F
    op' f g x = op (f x) (g x)

  -- these don't belong here, I suppose
  lift-magma : IsMagma _≈_ op → IsMagma _≈→_ op'
  IsMagma.isEquivalence (lift-magma x) = ≈→-isEquivalence
  IsMagma.∙-cong (lift-magma x) feq geq a = x .IsMagma.∙-cong (feq a) (geq a)

  lift-semigroup : IsSemigroup _≈_ op → IsSemigroup _≈→_ op'
  IsSemigroup.isMagma (lift-semigroup sg) = lift-magma (sg .IsSemigroup.isMagma)
  IsSemigroup.assoc (lift-semigroup sg) x y z a = sg .IsSemigroup.assoc (x a) (y a) (z a)

  instance lift-monoid : ∀ {unit} {{m : IsMonoid _≈_ op unit}} → IsMonoid _≈→_ op' (λ _ → unit)
  IsMonoid.isSemigroup (lift-monoid {{m}}) = lift-semigroup (m .IsMonoid.isSemigroup)
  proj₁ (IsMonoid.identity (lift-monoid ⦃ m = m ⦄)) x a = proj₁ (m .IsMonoid.identity) (x a)
  proj₂ (IsMonoid.identity (lift-monoid ⦃ m = m ⦄)) x a = proj₂ (m .IsMonoid.identity) (x a)

  instance →-total : IsTotal _≈→_ →-rel op' 
  IsTotal.∙-parallel →-total σ₁ σ₂ x = ∙-parallel (σ₁ x) (σ₂ x)
