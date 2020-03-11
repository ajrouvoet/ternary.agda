{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Positive {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Ternary.Core using (Rel₃)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open import Relation.Nullary
open IsPartialSemigroup

-- Positivity means that split off fragments are not bigger than their source.
-- With ε as the smallest element.
record IsPositive {e} s (_≈_ : A → A → Set e) (rel : Rel₃ A) ε : Set (a ⊔ e ⊔ suc s) where
  open Rel₃ rel

  field
    {_≤ₐ_}   : A → A → Set s
    is-empty : Decidable (_≈ ε)
    orderₐ   : IsPreorder _≈_ _≤ₐ_

    positiveˡ : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ≤ₐ Φ
    positiveʳ : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₂ ≤ₐ Φ
    ε-least   : ∀ {Φ} → Φ ≤ₐ ε → Φ ≈ ε

  open IsPreorder orderₐ

  ε-split′ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≈ ε × Φ₂ ≈ ε
  ε-split′ {Φ₁} {Φ₂} σ with is-empty Φ₁ | is-empty Φ₂
  ... | yes z | yes z' = z , z'
  ... | no  z | _      = ⊥-elim (z (ε-least (positiveˡ σ)))
  ... | yes _ | no z   = ⊥-elim (z (ε-least (positiveʳ σ)))

  module WithMonoid (isPartialMonoid : IsPartialMonoid _≈_ rel ε) where 
    open IsPartialMonoid isPartialMonoid
    open IsEquivalence (isPartialSemigroup .≈-equivalence)

    ε-split : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → (Φ₁ , Φ₂) ≡ (ε , ε)
    ε-split σ with ε-split′ σ
    ... | eq₁ , eq₂ with ε-unique (sym eq₁) | ε-unique (sym eq₂)
    ... | P.refl | P.refl = P.refl
