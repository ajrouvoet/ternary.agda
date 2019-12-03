{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Positive
  {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Relation.Ternary.Core using (Rel₃; Respect; coe; Exactly; Commutative)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open IsEquivalence {{...}}

record IsPositive {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) ε : Set (a ⊔ e) where
  open Rel₃ rel

  field
    positive′ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≈ ε × Φ₂ ≈ ε

  module _ {{ _ : IsPartialMonoid _≈_ rel ε }} where 
    positive : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≡ ε × Φ₂ ≡ ε
    positive σ with positive′ σ
    ... | eq₁ , eq₂ = P.sym (ε-unique (sym eq₁)) , P.sym (ε-unique (sym eq₂))

    positiveˡ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≡ ε
    positiveˡ = proj₁ ∘ positive

    positiveʳ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₂ ≡ ε
    positiveʳ = proj₂ ∘ positive

open IsPositive {{...}} public
