{-# OPTIONS --safe #-}

module Relation.Ternary.Construct.Product
  {ℓ₁ ℓ₂} {C₁ : Set ℓ₁} {C₂ : Set ℓ₂}
  where

open import Level
open import Data.Product

open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PEq
open import Data.Product.Relation.Binary.Pointwise.NonDependent

open import Relation.Ternary.Core
open import Relation.Ternary.Structures

_×-∙_ : Rel₃ C₁ → Rel₃ C₂ → Rel₃ (C₁ × C₂)
R₁ ×-∙ R₂ =
  let
    module R₁ = Rel₃ R₁
    module R₂ = Rel₃ R₂
  in record
  { _∙_≣_ = λ Φ₁ Φ₂ Φ →
      (proj₁ Φ₁) R₁.∙ (proj₁ Φ₂) ≣ proj₁ Φ
    × (proj₂ Φ₁) R₂.∙ (proj₂ Φ₂) ≣ proj₂ Φ }

instance ×-rel : {{_ : Rel₃ C₁}} {{_ : Rel₃ C₂}} → Rel₃ (C₁ × C₂)
×-rel {{R₁}} {{R₂}} = R₁ ×-∙ R₂

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {{s₁ : IsPartialSemigroup _≈₁_ R₁}} {{s₂ : IsPartialSemigroup _≈₂_ R₂}}
  where

  instance ×-equiv : IsEquivalence (Pointwise _≈₁_ _≈₂_)
  ×-equiv = ×-isEquivalence ≈-equivalence ≈-equivalence

  instance ×-isSG : IsPartialSemigroup (Pointwise _≈₁_ _≈₂_) (R₁ ×-∙ R₂)

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ×-isSG) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ×-isSG) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ×-isSG) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂

  IsPartialSemigroup.∙-assocᵣ ×-isSG (l₁  , r₁) (l₂ , r₂) =
    let
      _ , l₃ , l₄ = ∙-assocᵣ l₁ l₂
      _ , r₃ , r₄ = ∙-assocᵣ r₁ r₂
    in -, (l₃ , r₃) , l₄ , r₄

  IsPartialSemigroup.∙-assocₗ ×-isSG (l₁  , r₁) (l₂ , r₂) =
    let
      _ , l₃ , l₄ = ∙-assocₗ l₁ l₂
      _ , r₃ , r₄ = ∙-assocₗ r₁ r₂
    in -, (l₃ , r₃) , l₄ , r₄

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}} {u₁ u₂}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {{s₁ : IsPartialMonoid _≈₁_ R₁ u₁}} {{s₂ : IsPartialMonoid _≈₂_ R₂ u₂}}
  where

  instance ×-IsPartialMonoid : IsPartialMonoid (Pointwise _≈₁_ _≈₂_) ×-rel (u₁ , u₂) 
  IsPartialMonoid.ε-unique ×-IsPartialMonoid (fst , snd) with ε-unique fst | ε-unique snd
  ... | refl | refl = refl

  IsPartialMonoid.∙-idˡ ×-IsPartialMonoid = ∙-idˡ , ∙-idˡ
  IsPartialMonoid.∙-idʳ ×-IsPartialMonoid = ∙-idʳ , ∙-idʳ

  IsPartialMonoid.∙-id⁻ˡ ×-IsPartialMonoid (fst , snd) = (∙-id⁻ˡ fst) , (∙-id⁻ˡ snd)
  IsPartialMonoid.∙-id⁻ʳ ×-IsPartialMonoid (fst , snd) = (∙-id⁻ʳ fst) , (∙-id⁻ʳ snd)

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  {{s₁ : IsCommutative R₁}} {{s₂ : IsCommutative R₂}}
  where

  instance ×-isCommutative : IsCommutative ×-rel
  IsCommutative.∙-comm ×-isCommutative (fst , snd) = ∙-comm fst , ∙-comm snd

--   module _
--     {{sep₁ : Rel₃ C₁}} {{sep₂ : Rel₃ C₂}}
--     {{s₁ : HasConcat _≈₁_ sep₁}} {{s₂ : HasConcat _≈₂_ sep₂}}
--     where

--     private
--       module S₁ = HasConcat s₁
--       module S₂ = HasConcat s₂

--     instance ×-concat : HasConcat (Pointwise _≈₁_ _≈₂_) ×-rel
--     ×-concat = record
--       { _∙_ = (λ where (a , b) (c , d) → (a S₁.∙ c , b S₂.∙ d))
--       ; ∙-∙ₗ = λ where (p , q) → ∙-∙ₗ p , ∙-∙ₗ q }

{- Some useful type-formers for this instance -}
module _
  {e}
  {{r : Rel₃ C₁}}
  {_≈ₐ_ : C₁ → C₁ → Set e}
  {u} {{s : IsPartialMonoid _≈ₐ_ r u}} where

  data Π₁ {p} (P : Pred C₂ p) : Pred (C₂ × C₁) (ℓ₁ ⊔ ℓ₂ ⊔ p) where
    fst : ∀ {b : C₂} → P b → Π₁ P (b , ε)

  data Π₂ {p} (P : Pred C₂ p) : Pred (C₁ × C₂) (ℓ₁ ⊔ ℓ₂ ⊔ p) where
    snd : ∀ {b : C₂} → P b → Π₂ P (ε , b)

-- module Propositional
--   {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}} {u₁ u₂}
--   {{s₁ : HasUnit _≡_ R₁ u₁}} {{s₂ : HasUnit _≡_ R₂ u₂}}
--   where

--   ×-isSep-≡ : IsPartialSemigroup _≡_ (R₁ ×-∙ R₂)
--   IsPartialSemigroup.≈-equivalence ×-isSep-≡ = isEquivalence
--   IsPartialSemigroup.∙-respects-≈ ×-isSep-≡  refl σ = σ
--   IsPartialSemigroup.∙-respects-≈ˡ ×-isSep-≡ refl σ = σ
--   IsPartialSemigroup.∙-comm ×-isSep-≡ (l , r) = ∙-comm l , ∙-comm r
--   IsPartialSemigroup.∙-assoc ×-isSep-≡ (l₁  , r₁) (l₂ , r₂) =
--     let
--       _ , l₃ , l₄ = ∙-assoc l₁ l₂
--       _ , r₃ , r₄ = ∙-assoc r₁ r₂
--     in -, (l₃ , r₃) , l₄ , r₄

--   ×-hasUnit-≡ : HasUnit _≡_ ×-rel (u₁ , u₂) 
--   HasUnit.isSep ×-hasUnit-≡         = ×-isSep-≡
--   HasUnit.∙-idˡ ×-hasUnit-≡         = ∙-idˡ {{×-hasUnit}}
--   HasUnit.ε-unique ×-hasUnit-≡ refl = refl
--   HasUnit.∙-id⁻ˡ ×-hasUnit-≡ σ      = ≡×≡⇒≡ (∙-id⁻ˡ σ)
