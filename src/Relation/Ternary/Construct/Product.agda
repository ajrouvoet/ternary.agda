{-# OPTIONS --safe --without-K #-}

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
open import Relation.Ternary.Structures.Syntax

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
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {{ eq₁ : IsEquivalence _≈₁_ }} {{ eq₂ : IsEquivalence _≈₂_ }} where

  _≈_ = Pointwise _≈₁_ _≈₂_

  instance ×-equiv : IsEquivalence _≈_
  ×-equiv = ×-isEquivalence eq₁ eq₂

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {{s₁ : IsPartialSemigroup _≈₁_ R₁}} {{s₂ : IsPartialSemigroup _≈₂_ R₂}}
  where

  instance ×-isSemigroup : IsPartialSemigroup _≈_ (R₁ ×-∙ R₂)

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ×-isSemigroup) (eq₁ , eq₂) (σ₁ , σ₂) =
    coe eq₁ σ₁ , coe eq₂ σ₂

  IsPartialSemigroup.∙-assocᵣ ×-isSemigroup (l₁  , r₁) (l₂ , r₂) =
    let
      _ , l₃ , l₄ = ∙-assocᵣ l₁ l₂
      _ , r₃ , r₄ = ∙-assocᵣ r₁ r₂
    in -, (l₃ , r₃) , l₄ , r₄

  IsPartialSemigroup.∙-assocₗ ×-isSemigroup (l₁  , r₁) (l₂ , r₂) =
    let
      _ , l₃ , l₄ = ∙-assocₗ l₁ l₂
      _ , r₃ , r₄ = ∙-assocₗ r₁ r₂
    in -, (l₃ , r₃) , l₄ , r₄

module _ {u₁ u₂} {{_ : Emptiness {A = C₁} u₁}} {{_ : Emptiness {A = C₂} u₂}} where

  instance ×-emptiness : Emptiness (u₁ , u₂)
  ×-emptiness = record {}

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}} {u₁ u₂}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {{s₁ : IsPartialMonoid _≈₁_ R₁ u₁}} {{s₂ : IsPartialMonoid _≈₂_ R₂ u₂}}
  where

  instance ×-isPartialMonoid : IsPartialMonoid (Pointwise _≈₁_ _≈₂_) ×-rel (u₁ , u₂) 
  IsPartialMonoid.ε-unique ×-isPartialMonoid (fst , snd) with ε-unique fst | ε-unique snd
  ... | refl | refl = refl

  IsPartialMonoid.∙-idˡ ×-isPartialMonoid = ∙-idˡ , ∙-idˡ
  IsPartialMonoid.∙-idʳ ×-isPartialMonoid = ∙-idʳ , ∙-idʳ

  IsPartialMonoid.∙-id⁻ˡ ×-isPartialMonoid (fst , snd) = (∙-id⁻ˡ fst) , (∙-id⁻ˡ snd)
  IsPartialMonoid.∙-id⁻ʳ ×-isPartialMonoid (fst , snd) = (∙-id⁻ʳ fst) , (∙-id⁻ʳ snd)

module _
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  {{s₁ : IsCommutative R₁}} {{s₂ : IsCommutative R₂}}
  where

  instance ×-isCommutative : IsCommutative ×-rel
  IsCommutative.∙-comm ×-isCommutative (fst , snd) = ∙-comm fst , ∙-comm snd

module _ 
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {u₁ u₂}
  {{p₁ : IsPositive e₁ _≈₁_ R₁ u₁}}
  {{p₂ : IsPositive e₂ _≈₂_ R₂ u₂}}
  where

  open import Relation.Nullary

  instance ×-isPositive : IsPositive _ (Pointwise _≈₁_ _≈₂_) ×-rel (u₁ , u₂)

  IsPositive._≤ₐ_      ×-isPositive = Pointwise (IsPositive._≤ₐ_ p₁) (IsPositive._≤ₐ_ p₂)

  IsPositive.is-empty ×-isPositive (x , y) with is-empty x | is-empty y
  ... | yes p | yes q = yes (p , q)
  ... | yes p | no ¬q = no λ where (p , q) → ¬q q
  ... | no ¬p | _     = no λ where (p , q) → ¬p p

  IsPositive.orderₐ    ×-isPositive = ×-isPreorder orderₐ orderₐ

  IsPositive.positiveˡ ×-isPositive (σ₁ , σ₂) = positiveˡ σ₁ , positiveˡ σ₂
  IsPositive.positiveʳ ×-isPositive (σ₁ , σ₂) = positiveʳ σ₁ , positiveʳ σ₂ 

  IsPositive.ε-least   ×-isPositive (σ₁ , σ₂) = ε-least σ₁ , ε-least σ₂

module _
  {{∥₁ ∣₁ ▹₁ : Rel₃ C₁}} {{∥₂ ∣₂ ▹₂ : Rel₃ C₂}}
  {e₁ e₂} {_≈₁_ : C₁ → C₁ → Set e₁} {_≈₂_ : C₂ → C₂ → Set e₂} 
  {u₁ u₂}
  {{j₁ : IsJoinoid _≈₁_ ▹₁ ∥₁ ∣₁ u₁}} {{j₂ : IsJoinoid _≈₂_ ▹₂ ∥₂ ∣₂ u₂}} where

  instance ×-joinoid : IsJoinoid (Pointwise _≈₁_ _≈₂_) (×-rel {{▹₁}} {{▹₂}}) (×-rel {{∥₁}} {{∥₂}}) (×-rel {{∣₁}} {{∣₂}}) (u₁ , u₂)

  IsJoinoid.▹-distrib-∣ʳ ×-joinoid (σ₁₁ , σ₁₂) (σ₂₁ , σ₂₂) =
    let _ , _ , τ₁ , τ₂ , τ₃ = ▹-distrib-∣ʳ σ₁₁ σ₂₁ in
    let _ , _ , χ₁ , χ₂ , χ₃ = ▹-distrib-∣ʳ σ₁₂ σ₂₂ in
    -, -, (τ₁ , χ₁) , (τ₂ , χ₂) , τ₃ , χ₃
  IsJoinoid.▹-distrib-∣ˡ ×-joinoid (σ₁₁ , σ₁₂) (σ₂₁ , σ₂₂) (σ₃₁ , σ₃₂) =
    let _ , τ₁ , τ₂ = ▹-distrib-∣ˡ σ₁₁ σ₂₁ σ₃₁ in
    let _ , χ₁ , χ₂ = ▹-distrib-∣ˡ σ₁₂ σ₂₂ σ₃₂ in
    -, (τ₁ , χ₁) , (τ₂ , χ₂)

  IsJoinoid.∥-distrib-∣ʳ ×-joinoid (σ₁₁ , σ₁₂) (σ₂₁ , σ₂₂) =
    let _ , _ , τ₁ , τ₂ , τ₃ = ∥-distrib-∣ʳ σ₁₁ σ₂₁ in
    let _ , _ , χ₁ , χ₂ , χ₃ = ∥-distrib-∣ʳ σ₁₂ σ₂₂ in
    -, -, (τ₁ , χ₁) , (τ₂ , χ₂) , τ₃ , χ₃
  IsJoinoid.∥-distrib-∣ˡ ×-joinoid (σ₁₁ , σ₁₂) (σ₂₁ , σ₂₂) (σ₃₁ , σ₃₂) =
    let _ , τ₁ , τ₂ = ∥-distrib-∣ˡ σ₁₁ σ₂₁ σ₃₁ in
    let _ , χ₁ , χ₂ = ∥-distrib-∣ˡ σ₁₂ σ₂₂ σ₃₂ in
    -, (τ₁ , χ₁) , (τ₂ , χ₂)

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
module _ {u} {{_ : Emptiness {A = C₂} u}} where

  data Π₁  {p} (P : Pred C₁ p) : Pred (C₁ × C₂) (ℓ₁ ⊔ ℓ₂ ⊔ p) where
    fst : ∀ {b} → P b → Π₁ P (b , ε)

{- Some useful type-formers for this instance -}
module _ {u} {{_ : Emptiness {A = C₁} u}} where

  data Π₂ {p} (P : Pred C₂ p) : Pred (C₁ × C₂) (ℓ₁ ⊔ ℓ₂ ⊔ p) where
    snd : ∀ {b} → P b → Π₂ P (ε , b)

module _
  {e} {{r : Rel₃ C₂}}
  {_≈₂_ : C₂ → C₂ → Set e} {u} {{s : IsPartialMonoid _≈₂_ r u}}
  {e₁ p} {_≈₁_ : C₁ → C₁ → Set e₁} where

  instance Π₁-respect-≈ : ∀ {P : Pred C₁ p} {{_ : Respect _≈₁_ P }} → Respect (Pointwise _≈₁_ _≈₂_) (Π₁ P)
  Respect.coe Π₁-respect-≈ (eq₁ , eq₂) (fst px) with ε-unique eq₂
  ... | refl = fst (coe eq₁ px)

module _
  {e} {{r : Rel₃ C₁}}
  {_≈₁_ : C₁ → C₁ → Set e} {u} {{s : IsPartialMonoid _≈₁_ r u}}
  {e₂ p} {_≈₂_ : C₂ → C₂ → Set e₂} where

  instance Π₂-respect-≈ : ∀ {P : Pred C₂ p} {{_ : Respect _≈₂_ P }} → Respect (Pointwise _≈₁_ _≈₂_) (Π₂ P)
  Respect.coe Π₂-respect-≈ (eq₁ , eq₂) (snd px) with ε-unique eq₁
  ... | refl = snd (coe eq₂ px)

module Propositional
  {{R₁ : Rel₃ C₁}} {{R₂ : Rel₃ C₂}}
  where

  open import Relation.Ternary.Respect.Propositional

  module _ {{_ : IsPartialSemigroup _≡_ R₁}} {{_ : IsPartialSemigroup _≡_ R₂}} where

    ×-isPartialSemigroup : IsPartialSemigroup _≡_ (R₁ ×-∙ R₂)
    IsPartialSemigroup.≈-equivalence ×-isPartialSemigroup = isEquivalence
    IsPartialSemigroup.∙-assocₗ ×-isPartialSemigroup (l₁  , r₁) (l₂ , r₂) =
      let
        _ , l₃ , l₄ = ∙-assocₗ l₁ l₂
        _ , r₃ , r₄ = ∙-assocₗ r₁ r₂
      in -, (l₃ , r₃) , l₄ , r₄
    IsPartialSemigroup.∙-assocᵣ ×-isPartialSemigroup (l₁  , r₁) (l₂ , r₂) =
      let
        _ , l₃ , l₄ = ∙-assocᵣ l₁ l₂
        _ , r₃ , r₄ = ∙-assocᵣ r₁ r₂
      in -, (l₃ , r₃) , l₄ , r₄

  module _ {ε₁ ε₂} {{_ : IsPartialMonoid _≡_ R₁ ε₁}} {{_ : IsPartialMonoid _≡_ R₂ ε₂}} where

    ×-isPartialMonoid-≡ : IsPartialMonoid _≡_ (R₁ ×-∙ R₂) (ε₁ , ε₂)
    IsPartialMonoid.isSemigroup ×-isPartialMonoid-≡ = ×-isPartialSemigroup
    IsPartialMonoid.ε-unique ×-isPartialMonoid-≡ refl = refl
    IsPartialMonoid.∙-idˡ ×-isPartialMonoid-≡ = ∙-idˡ , ∙-idˡ
    IsPartialMonoid.∙-idʳ ×-isPartialMonoid-≡ = ∙-idʳ , ∙-idʳ
    IsPartialMonoid.∙-id⁻ˡ ×-isPartialMonoid-≡ (σ₁ , σ₂) with ∙-id⁻ˡ σ₁ | ∙-id⁻ˡ σ₂
    ... | refl | refl = refl
    IsPartialMonoid.∙-id⁻ʳ ×-isPartialMonoid-≡ (σ₁ , σ₂) with ∙-id⁻ʳ σ₁ | ∙-id⁻ʳ σ₂
    ... | refl | refl = refl
