{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Total {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Function using (_∘_)
open import Algebra

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Relation.Ternary.Core using (Rel₃; coe)
open import Relation.Ternary.Structures.PartialSemigroup _≈_
open import Relation.Ternary.Structures.PartialMonoid _≈_

open IsMonoid {{...}}

record IsTotal (rel : Rel₃ A) (_∙_ : A → A → A) (unit : A) : Set (suc a ⊔ e) where
  open Rel₃ rel hiding (_∙_)

  field
    ∙-∙ₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → (Φₑ ∙ Φ₁) ∙ Φ₂ ≣ (Φₑ ∙ Φ)
    ∙-∙ᵣ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∙ (Φₑ ∙ Φ₂) ≣ (Φₑ ∙ Φ)

  ∙-∙ : ∀ {Φₗ Φᵣ : A}
      → {{_ : IsPartialMonoid rel unit}} {{_ : IsMonoid _≈_ _∙_ unit}}
      → Φₗ ∙ Φᵣ ≣ (Φₗ ∙ Φᵣ)
  ∙-∙ {Φₗ} {Φᵣ} = coe (identityʳ Φₗ) (∙-∙ₗ ∙-idˡ)

open IsTotal {{...}} public
