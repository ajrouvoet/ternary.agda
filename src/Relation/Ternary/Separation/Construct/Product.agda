{-# OPTIONS --without-K --safe #-}

module Relation.Ternary.Separation.Construct.Product where

open import Level
open import Data.Product

open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Separation
open import Data.Product.Relation.Binary.Pointwise.NonDependent

module _ {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂} where

  _×-⊎_ : RawSep C₁ → RawSep C₂ → RawSep (C₁ × C₂)
  R₁ ×-⊎ R₂ =
    let
      module R₁ = RawSep R₁
      module R₂ = RawSep R₂
    in record
    { _⊎_≣_ = λ Φ₁ Φ₂ Φ →
        (proj₁ Φ₁) R₁.⊎ (proj₁ Φ₂) ≣ proj₁ Φ
      × (proj₂ Φ₁) R₂.⊎ (proj₂ Φ₂) ≣ proj₂ Φ }

  instance ×-rawsep : ⦃ _ : RawSep C₁ ⦄ ⦃ _ : RawSep C₂ ⦄ → RawSep (C₁ × C₂)
  ×-rawsep ⦃ R₁ ⦄ ⦃ R₂ ⦄ = R₁ ×-⊎ R₂

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}}
  ⦃ s₁ : IsSep R₁ ⦄ ⦃ s₂ : IsSep R₂ ⦄
  where

  instance ×-isSep : IsSep (R₁ ×-⊎ R₂)
  ×-isSep = record
    { ⊎-comm  = λ where (l , r) → ⊎-comm l , ⊎-comm r
    ; ⊎-assoc = λ where
      (l₁  , r₁) (l₂ , r₂) →
        let
          _ , l₃ , l₄ = ⊎-assoc l₁ l₂
          _ , r₃ , r₄ = ⊎-assoc r₁ r₂
        in -, (l₃ , r₃) , l₄ , r₄ }

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
  ⦃ s₁ : HasUnit⁺ R₁ u₁ ⦄ ⦃ s₂ : HasUnit⁺ R₂ u₂ ⦄
  where

  instance ×-hasUnit⁺ : HasUnit⁺ _ (u₁ , u₂) 
  ×-hasUnit⁺ = record { ⊎-idˡ = ⊎-idˡ , ⊎-idˡ }


module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
  ⦃ s₁ : HasUnit⁻ R₁ u₁ ⦄ ⦃ s₂ : HasUnit⁻ R₂ u₂ ⦄
  where

  instance ×-hasUnit⁻ : HasUnit⁻ _ (u₁ , u₂) 
  ×-hasUnit⁻ = record
    { ⊎-id⁻ˡ = λ where
      (fst , snd) → cong₂ _,_ (⊎-id⁻ˡ fst) (⊎-id⁻ˡ snd)
    }

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
  ⦃ s₁ : IsUnitalSep R₁ u₁ ⦄ ⦃ s₂ : IsUnitalSep R₂ u₂ ⦄
  where

  instance ×-isUnitalSep : IsUnitalSep ×-rawsep (u₁ , u₂)
  ×-isUnitalSep = unital

module _
  {ℓ₁ ℓ₂}
  {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  ⦃ sep₁ : RawSep C₁ ⦄ ⦃ sep₂ : RawSep C₂ ⦄
  ⦃ s₁ : HasConcat sep₁ ⦄ ⦃ s₂ : HasConcat sep₂ ⦄
  where

  private
    module S₁ = HasConcat s₁
    module S₂ = HasConcat s₂

  instance ×-concat : HasConcat ×-rawsep
  ×-concat = record
    { _∙_ = (λ where (a , b) (c , d) → (a S₁.∙ c , b S₂.∙ d))
    ; ⊎-∙ₗ = λ where (p , q) → ⊎-∙ₗ p , ⊎-∙ₗ q }

{- Some useful type-formers for this instance -}
module _ {ℓ} {A : Set ℓ} {{ r : RawSep A }} {u} {{s : IsUnitalSep r u}} where

  data Π₁ {p} (P : Pred A p) : Pred (A × A) (ℓ ⊔ p) where
    fst : ∀ {a} → P a → Π₁ P (a , ε)

  data Π₂ {p} (P : Pred A p) : Pred (A × A) (ℓ ⊔ p) where
    snd : ∀ {a} → P a → Π₂ P (ε , a)
