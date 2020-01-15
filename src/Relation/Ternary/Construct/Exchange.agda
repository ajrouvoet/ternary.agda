-- The Exchange PRSA
--
-- This proof relevant separation algebra balances multiple "accounts"
-- that can /each/ both supply (/up/) and demand (/down/) some amount of an underlying
-- PRSA A.
-- At every node in the splitting tree, two accounts can "exchange" some amount,
-- meaning that the demand on the left can be fulfilled by some supply on the right and vice versa.

module Relation.Ternary.Construct.Exchange {ℓ e} {A : Set ℓ} (_≈ₐ_ : A → A → Set e) where

open import Level hiding (Lift)
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open IsEquivalence {{...}}

open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module _ where

  record Account : Set ℓ where
    constructor _↕_
    field
      up   : A
      down : A

    pair : A × A
    pair = up , down

  open Account public

  open import Data.Product.Relation.Binary.Pointwise.NonDependent
  _≈_ : Account → Account → Set _
  a ≈ b = Pointwise _≈ₐ_ _≈ₐ_ (pair a) (pair b)

module _ {uₐ} {{sep : Rel₃ A }} {{_ : IsPartialMonoid _≈ₐ_ sep uₐ}} where

  data Down (P : Pred A ℓ) : Pred Account ℓ where
    ↓ : ∀ {x} → P x → Down P (uₐ ↕ x)

  data Up (P : Pred A ℓ) : Pred Account ℓ where
    ↑ : ∀ {x} → P x → Up P (x ↕ uₐ)

module _
  {{ sep : Rel₃ A }}
  {{ _ : IsPartialSemigroup _≈ₐ_ sep }}
  {{ _ : IsCrosssplittable _≈ₐ_ sep }}
  {{ _ : IsCommutative sep }}
  where

  open import Relation.Ternary.Construct.Product hiding (_≈_)

  instance account-equiv : IsEquivalence _≈_
  IsEquivalence.refl account-equiv  = refl , refl
  IsEquivalence.sym account-equiv   = map sym sym
  IsEquivalence.trans account-equiv (e₁ , e₂) (e₃ , e₄) = trans e₁ e₃ , trans e₂ e₄

  -- lifted pointwise product split
  _×∙_≣_ : (l r t : Account) → Set ℓ
  (u₁ ↕ d₁) ×∙ (u₂ ↕ d₂) ≣ (u ↕ d) = (u₁ , d₁) ∙ (u₂ , d₂) ≣ (u , d)

  -- subtract some amount from both sides of the balance
  _/_≣_ : Account → A → Account → Set ℓ
  ud₁ / e ≣ ud₂ = ud₂ ×∙ (e ↕ e) ≣ ud₁

  data Split : Account → Account → Account → Set ℓ where
    ex : ∀ {e₁ e₂ u₁ d₁ u₂ d₂ u₁' d₁' u₂' d₂' ud} →

         -- bind e₁ and e₂ in oposite side
         (u₁ ↕ d₂) / e₁ ≣ (u₁' ↕ d₂') →
         (u₂ ↕ d₁) / e₂ ≣ (u₂' ↕ d₁') →

         -- add the remaining supply and demand
         (u₁' ↕ d₁') ×∙ (u₂' ↕ d₂') ≣ ud →

         Split (u₁ ↕ d₁) (u₂ ↕ d₂) ud

  instance exchange-rel : Rel₃ Account
  exchange-rel = record { _∙_≣_ = Split }

  instance exchange-comm : IsCommutative exchange-rel
  IsCommutative.∙-comm exchange-comm (ex x₁ x₂ σ) = ex x₂ x₁ (∙-comm σ)

  instance exchange-isSemigroup : IsPartialSemigroup _≈_ exchange-rel

  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ exchange-isSemigroup) (eq₁ , eq₂) (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) σ)
    = ex (coe eq₁ x₁₁ , x₁₂) (x₂₁ , coe eq₂ x₂₂) σ 
  Respect.coe (IsPartialSemigroup.∙-respects-≈  exchange-isSemigroup) (eq₁ , eq₂) (ex x₁ x₂ (σ₁ , σ₂))
    = ex x₁ x₂ (coe eq₁ σ₁ , coe eq₂ σ₂)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ exchange-isSemigroup) (eq₁ , eq₂) (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) σ)
    = ex (x₁₁ , coe eq₂ x₁₂) (coe eq₁ x₂₁ , x₂₂) σ 

  IsPartialSemigroup.∙-assocᵣ exchange-isSemigroup
    (ex {a>b}  {b>a}  {a↑}  {a↓}  {b↑} {b↓} {a↑'}  {a↓'}  {b↑'} {b↓'} x₁ x₂ σ₁)
    (ex {ab>c} {c>ab} {ab↑} {ab↓} {c↑} {c↓} {ab↑'} {ab↓'} {c↑'} {c↓'} x₃ x₄ σ₂)
    with cross (proj₁ σ₁) (proj₁ x₃) | cross (proj₂ σ₁) (proj₂ x₄)
  ... | (a↑'' , a>c , b↑'' , b>c) , z₁ , z₂ , z₃ , z₄
      | (a↓'' , c>a , b↓'' , c>b) , m₁ , m₂ , m₃ , m₄
      with ∙-assocᵣ z₃ (proj₁ σ₂) | ∙-assocᵣ z₁ (proj₁ x₁)
         | recombine z₂ (proj₁ x₂) | ∙-assocᵣ (∙-comm m₄) (∙-comm (proj₁ x₄))
         | ∙-assocᵣ m₃ (proj₂ σ₂) | ∙-assocᵣ m₁ (proj₂ x₂)
         | recombine m₂ (proj₂ x₁) | ∙-assocᵣ (∙-comm z₄) (∙-comm (proj₂ x₃))
  ... | bc↑ , z₅ , σ₃ | a>bc , x₅ , k₃ | _ , k₁ , k₂ | _ , x₆ , x₇
      | bc↓ , σ₄ , m₅ | bc>a , y₁ , k₄ | _ , y₃ , y₄ | _ , y₅ , y₆
      with uncross (∙-comm k₁) x₇ (∙-comm k₄) σ₃
         | uncross (∙-comm y₆) y₃ (∙-comm m₅) k₃
  ... | _  , x₈ , x₉ | _ , y₇ , y₈ =
    -, ex (x₅ , y₈) (∙-comm x₉ , y₁) (z₅  , σ₄)
     , ex (k₂ , ∙-comm y₅) (∙-comm x₆ , y₄) (x₈ , ∙-comm y₇)

  IsPartialSemigroup.∙-assocₗ exchange-isSemigroup σ₁ σ₂ =
    let _ , σ₃ , σ₄ = ∙-assocᵣ (∙-comm σ₂) (∙-comm σ₁) in -, ∙-comm σ₄ , ∙-comm σ₃

module _
  {{ sep : Rel₃ A }} {eps}
  {{ cs⁻ : IsCrosssplittable _≈ₐ_ sep }}
  {{ _   : IsPositive _≈ₐ_ sep eps }}
  {{ un  : IsPartialMonoid _≈ₐ_ sep eps }}
  {{ _   : IsCommutative sep }}
  where

  open import Relation.Ternary.Construct.Product hiding (_≈_)

  exchange-isMonoidˡ : IsPartialMonoidˡ _≈_ exchange-rel (eps ↕ eps)
  IsPartialMonoidˡ.ε-uniq exchange-isMonoidˡ (eq₁ , eq₂) with ε-unique eq₁ | ε-unique eq₂
  ... | PEq.refl | PEq.refl = PEq.refl
  IsPartialMonoidˡ.identityˡ exchange-isMonoidˡ = ex (∙-idˡ , ∙-idʳ) (∙-idʳ , ∙-idˡ) (∙-idˡ )
  IsPartialMonoidˡ.identity⁻ˡ exchange-isMonoidˡ (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) (σ₁ , σ₂)) with positive x₁₁ | positive x₂₂
  ... | PEq.refl , PEq.refl | PEq.refl , PEq.refl =
    trans (sym (∙-id⁻ʳ x₂₁)) (∙-id⁻ˡ σ₁) , trans (sym (∙-id⁻ʳ x₁₂)) (∙-id⁻ˡ σ₂)

  instance exchange-isMonoid : IsPartialMonoid _≈_ exchange-rel (eps ↕ eps)
  exchange-isMonoid = IsPartialMonoidˡ.partialMonoidˡ exchange-isMonoidˡ
