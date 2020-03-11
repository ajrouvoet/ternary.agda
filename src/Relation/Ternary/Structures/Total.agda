{-# OPTIONS --safe --without-K #-}
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

record IsTotal {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (_++_ : A → A → A) : Set (suc a ⊔ e) where
  open Rel₃ rel

  field
    ∙-parallel : ∀ {a b c d ab cd} → a ∙ b ≣ ab → c ∙ d ≣ cd → (a ++ c) ∙ (b ++ d) ≣ (ab ++ cd)

  module WithMonoid {unit}
    (monoid          : IsMonoid _≈_ _++_ unit)
    (isPartialMonoid : IsPartialMonoid _≈_ rel unit) where

    open IsMonoid monoid
    open IsPartialMonoid isPartialMonoid
    open IsPartialSemigroup isPartialSemigroup

    ∙-∙ₗₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → (Φₑ ++ Φ₁) ∙ Φ₂ ≣ (Φₑ ++ Φ)
    ∙-∙ₗₗ {Φ₁} {Φ₂} {Φ} {Φₑ} σ with ∙-parallel {a = Φₑ} {b = unit} {c = Φ₁} ∙-idʳ σ
    ... | z = coe (identityˡ _) z

    ∙-∙ₗᵣ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → (Φ₁ ++ Φₑ) ∙ Φ₂ ≣ (Φ ++ Φₑ)
    ∙-∙ₗᵣ {Φ₁} {Φ₂} {Φ} {Φₑ} σ with ∙-parallel {a = Φ₁} {b = Φ₂} {c = Φₑ} σ ∙-idʳ
    ... | z = coe (identityʳ _) z 

    ∙-∙ᵣₗ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∙ (Φₑ ++ Φ₂) ≣ (Φₑ ++ Φ)
    ∙-∙ᵣₗ {Φ₁} {Φ₂} {Φ} {Φₑ} σ with ∙-parallel {a = unit} {b = Φₑ} ∙-idˡ σ
    ... | z = coe (identityˡ _) z

    ∙-∙ᵣᵣ : ∀ {Φ₁ Φ₂ Φ Φₑ} → Φ₁ ∙ Φ₂ ≣ Φ → Φ₁ ∙ (Φ₂ ++ Φₑ) ≣ (Φ ++ Φₑ)
    ∙-∙ᵣᵣ {Φ₁} {Φ₂} {Φ} {Φₑ} σ with ∙-parallel {d = Φₑ} σ ∙-idˡ
    ... | z = coe (identityʳ _) z

    ∙-∙ : ∀ {Φₗ Φᵣ : A} → Φₗ ∙ Φᵣ ≣ (Φₗ ++ Φᵣ)
    ∙-∙ {Φₗ} {Φᵣ} with ∙-parallel {a = Φₗ} {b = unit} {c = unit} {d = Φᵣ} ∙-idʳ ∙-idˡ
    ... | z = coe (identityʳ _) (coe (identityˡ _) z)
