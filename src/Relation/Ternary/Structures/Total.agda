{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Total {a} {A : Set a} where

open import Level
open import Function using (_∘_)
open import Data.Product
open import Algebra

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Relation.Ternary.Core using (Rel₃; coe)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

open IsPartialMonoid    {{...}}
open IsPartialSemigroup {{...}}
open Emptiness {{...}}

record IsTotal {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) (_++_ : A → A → A) : Set (suc a ⊔ e) where
  open Rel₃ rel

  field
    ∙-parallel  : ∀ {a b c d ab cd} → a ∙ b ≣ ab → c ∙ d ≣ cd → (a ++ c) ∙ (b ++ d) ≣ (ab ++ cd)
    -- ∙-parallel⁻ : ∀ {xs ys zs₂} zs₁ → xs ∙ ys ≣ (zs₁ ++ zs₂) →
    --               Σ[ parts ∈ A × A × A × A ]
    --                 let xs₁ , xs₂ , ys₁ , ys₂ = parts
    --                  in xs₁ ∙ xs₂ ≣ xs
    --                   × ys₁ ∙ ys₂ ≣ ys
    --                   × xs₁ ∙ ys₁ ≣ zs₁
    --                   × xs₂ ∙ ys₂ ≣ zs₂

  module _ {unit} {{_ : IsMonoid _≈_ _++_ unit}} {{_ : IsPartialMonoid _≈_ rel unit}} where

    open IsMonoid {{...}}
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
    ∙-∙ {Φₗ} {Φᵣ} with ∙-parallel {a = Φₗ} {b = ε} {c = ε} {d = Φᵣ} ∙-idʳ ∙-idˡ
    ... | z =
      coe {{∙-respects-≈ˡ}} (identityʳ _)
        (coe {{∙-respects-≈ʳ}} (identityˡ _) z)

    pair : ∀ {p q} {P : Pred A p} {Q : Pred A q} {Φ₁ Φ₂} → P Φ₁ → Q Φ₂ → (P ✴ Q) (Φ₁ ++ Φ₂)
    pair px qx = px ∙⟨ ∙-∙ ⟩ qx

open IsTotal {{...}} public
