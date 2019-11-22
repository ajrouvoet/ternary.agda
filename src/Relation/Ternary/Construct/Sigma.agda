{-# OPTIONS --without-K --safe #-}

module Relation.Ternary.Separation.Construct.Sigma where

open import Level
open import Data.Product

open import Function
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Separation
open import Data.Product.Relation.Binary.Pointwise.NonDependent

module _
  {ℓ₁ ℓ₂} {C : Set ℓ₁} {P : C → Set ℓ₂}
  {{R : RawSep C}}
  (J : ∀ {c₁ c₂ c : C} → (RawSep._⊎_≣_ R c₁ c₂ c) → P c₁ → P c₂ → P c)
  where

  Σ⊎ : RawSep (Σ C P)
  RawSep._⊎_≣_ Σ⊎ (c₁ , p₁) (c₂ , p₂) (c , p) =
    let module R = RawSep R in
    Σ[ σ ∈ (c₁ R.⊎ c₂ ≣ c) ] (J σ p₁ p₂ ≡ p)

  module Σ-IsSep
    {{s₁ : IsSep R}}
    (j-comm  : ∀ {c₁ c₂ c : C} {p₁ p₂} {σ : c₁ ⊎ c₂ ≣ c} → J σ p₁ p₂ ≡ J (⊎-comm σ) p₂ p₁)
    (j-assoc : ∀ {c₁ c₂ c : C} {p₁ p₂} {σ : c₁ ⊎ c₂ ≣ c} →
      J σ₁ p₁ (J σ₂))
    where

    instance ×-isSep : IsSep Σ⊎
    IsSep.⊎-comm ×-isSep (fst , refl) = ⊎-comm fst , sym j-comm
    IsSep.⊎-assoc ×-isSep (σ₁ , refl) (σ₂ , refl) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in
      -, (σ₃ , {!!}) , (σ₄ , {!!})

-- module _
--   {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
--   {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
--   ⦃ s₁ : HasUnit⁺ R₁ u₁ ⦄ ⦃ s₂ : HasUnit⁺ R₂ u₂ ⦄
--   where

--   instance ×-hasUnit⁺ : HasUnit⁺ _ (u₁ , u₂) 
--   ×-hasUnit⁺ = record { ⊎-idˡ = ⊎-idˡ , ⊎-idˡ }


-- module _
--   {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
--   {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
--   ⦃ s₁ : HasUnit⁻ R₁ u₁ ⦄ ⦃ s₂ : HasUnit⁻ R₂ u₂ ⦄
--   where

--   instance ×-hasUnit⁻ : HasUnit⁻ _ (u₁ , u₂) 
--   ×-hasUnit⁻ = record
--     { ⊎-id⁻ˡ = λ where
--       (fst , snd) → cong₂ _,_ (⊎-id⁻ˡ fst) (⊎-id⁻ˡ snd)
--     }

-- module _
--   {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
--   {{R₁ : RawSep C₁}} {{R₂ : RawSep C₂}} {u₁ u₂}
--   ⦃ s₁ : IsUnitalSep R₁ u₁ ⦄ ⦃ s₂ : IsUnitalSep R₂ u₂ ⦄
--   where

--   instance ×-isUnitalSep : IsUnitalSep ×-rawsep (u₁ , u₂)
--   ×-isUnitalSep = unital

-- module _
--   {ℓ₁ ℓ₂}
--   {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
--   ⦃ sep₁ : RawSep C₁ ⦄ ⦃ sep₂ : RawSep C₂ ⦄
--   ⦃ s₁ : HasConcat sep₁ ⦄ ⦃ s₂ : HasConcat sep₂ ⦄
--   where

--   private
--     module S₁ = HasConcat s₁
--     module S₂ = HasConcat s₂

--   instance ×-concat : HasConcat ×-rawsep
--   ×-concat = record
--     { _∙_ = (λ where (a , b) (c , d) → (a S₁.∙ c , b S₂.∙ d))
--     ; ⊎-∙ₗ = λ where (p , q) → ⊎-∙ₗ p , ⊎-∙ₗ q }

-- {- Some useful type-formers for this instance -}
-- module _ {a b} {B : Set b} {A : Set a} {{ r : RawSep A }} {u} {{s : HasUnit⁺ r u}} where

--   data Π₁ {p} (P : Pred B p) : Pred (B × A) (a ⊔ b ⊔ p) where
--     fst : ∀ {b : B} → P b → Π₁ P (b , ε)

--   data Π₂ {p} (P : Pred B p) : Pred (A × B) (a ⊔ b ⊔ p) where
--     snd : ∀ {b : B} → P b → Π₂ P (ε , b)
