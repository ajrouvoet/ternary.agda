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
  {ℓ₁ ℓ₂ e₁ e₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
  {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂}
  ⦃ s₁ : HasUnit _≈₁_ R₁ u₁ ⦄ ⦃ s₂ : HasUnit _≈₂_ R₂ u₂ ⦄
  where

  instance ×-hasUnit : HasUnit (Pointwise _≈₁_ _≈₂_) ×-rawsep (u₁ , u₂) 
  HasUnit.⊎-idˡ ×-hasUnit = ⊎-idˡ , ⊎-idˡ
  HasUnit.ε-unique ×-hasUnit (fst , snd) with ε-unique fst | ε-unique snd
  ... | refl | refl = refl
  HasUnit.⊎-id⁻ˡ ×-hasUnit (fst , snd) = (⊎-id⁻ˡ fst) , (⊎-id⁻ˡ snd)

module _
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
  ⦃ s₁ : HasUnit _≡_ R₁ u₁ ⦄ ⦃ s₂ : HasUnit _≡_ R₂ u₂ ⦄
  where

  instance ×-hasUnit-≡ : HasUnit _≡_ ×-rawsep (u₁ , u₂) 
  HasUnit.⊎-idˡ ×-hasUnit-≡ = ⊎-idˡ , ⊎-idˡ
  HasUnit.ε-unique ×-hasUnit-≡ refl = refl
  HasUnit.⊎-id⁻ˡ ×-hasUnit-≡ (fst , snd) with ⊎-id⁻ˡ fst | ⊎-id⁻ˡ snd
  ... | refl | refl = refl

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
module _ {a b e} {B : Set b} {A : Set a} {{ r : RawSep A }} {u} {eq : A → A → Set e}
  {{s : HasUnit eq r u}} where

  data Π₁ {p} (P : Pred B p) : Pred (B × A) (a ⊔ b ⊔ p) where
    fst : ∀ {b : B} → P b → Π₁ P (b , ε)

  data Π₂ {p} (P : Pred B p) : Pred (A × B) (a ⊔ b ⊔ p) where
    snd : ∀ {b : B} → P b → Π₂ P (ε , b)
