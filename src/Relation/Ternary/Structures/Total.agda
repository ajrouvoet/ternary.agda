{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Total {a} {A : Set a} where

open import Level
open import Function using (_∘_)
open import Algebra

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Relation.Ternary.Core using (Rel₃; coe)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

open IsMonoid {{...}}

record IsTotal {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) unit (_∙_ : A → A → A) : Set (suc a ⊔ e) where
  open Rel₃ rel hiding (_∙_)

  field
    ∙-∙ₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → (Φₑ ∙ Φ₁) ∙ Φ₂ ≣ (Φₑ ∙ Φ)
    ∙-∙ᵣ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∙ (Φₑ ∙ Φ₂) ≣ (Φₑ ∙ Φ)
    overlap {{op-monoid}} : IsMonoid _≈_ _∙_ unit

  ∙-∙ : ∀ {Φₗ Φᵣ : A}
      → {{_ : IsPartialMonoid _≈_ rel unit}} 
      → Φₗ ∙ Φᵣ ≣ (Φₗ ∙ Φᵣ)
  ∙-∙ {Φₗ} {Φᵣ} = coe (identityʳ Φₗ) (∙-∙ₗ ∙-idˡ)

open IsTotal {{...}} public
