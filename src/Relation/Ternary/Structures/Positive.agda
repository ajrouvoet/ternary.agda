{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Positive
  {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Exactly; Commutative)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

record IsPositive {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) ε : Set (a ⊔ e) where
  open Rel₃ rel

  field
    positivity : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≈ ε × Φ₂ ≈ ε

  positivityˡ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≈ ε
  positivityˡ = proj₁ ∘ positivity

  positivityʳ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₂ ≈ ε
  positivityʳ = proj₂ ∘ positivity
