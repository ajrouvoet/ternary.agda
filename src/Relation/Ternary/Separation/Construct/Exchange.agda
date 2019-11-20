-- The Exchange PRSA
--
-- This proof relevant separation algebra balances multiple "accounts"
-- that can /each/ both supply (/up/) and demand (/down/) some amount of an underlying
-- PRSA A.
-- At every node in the splitting tree, two accounts can "exchange" some amount,
-- meaning that the demand on the left can be fulfilled by some supply on the right and vice versa.

module Relation.Ternary.Separation.Construct.Exchange {ℓ e} {A : Set ℓ} (_≈ₐ_ : A → A → Set e) where

open import Level hiding (Lift)
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
open IsEquivalence {{...}}

open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Morphisms

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

module _ {uₐ} {{sep : RawSep A }} {{_ : HasUnit _≈ₐ_ sep uₐ}} where

  data ○ (P : Pred A ℓ) : Pred Account ℓ where
    consumer : ∀ {x} → P x → ○ P (uₐ ↕ x)

module _
  {{ sep : RawSep A }}
  {{_ : HasCrossSplit⁺ _≈ₐ_ sep}}
  {{_ : HasCrossSplit⁻ _≈ₐ_ sep}} where

  open import Relation.Ternary.Separation.Construct.Product

  instance account-equiv : IsEquivalence _≈_
  IsEquivalence.refl account-equiv  = refl , refl
  IsEquivalence.sym account-equiv   = map sym sym
  IsEquivalence.trans account-equiv (e₁ , e₂) (e₃ , e₄) = trans e₁ e₃ , trans e₂ e₄

  -- lifted pointwise product split
  _×⊎_≣_ : (l r t : Account) → Set ℓ
  (u₁ ↕ d₁) ×⊎ (u₂ ↕ d₂) ≣ (u ↕ d) = (u₁ , d₁) ⊎ (u₂ , d₂) ≣ (u , d)

  -- subtract some amount from both sides of the balance
  _/_≣_ : Account → A → Account → Set ℓ
  ud₁ / e ≣ ud₂ = ud₂ ×⊎ (e ↕ e) ≣ ud₁

  data Split : Account → Account → Account → Set ℓ where
    ex : ∀ {e₁ e₂ u₁ d₁ u₂ d₂ u₁' d₁' u₂' d₂' ud} →

         -- bind e₁ and e₂ in oposite side
         (u₁ ↕ d₂) / e₁ ≣ (u₁' ↕ d₂') →
         (u₂ ↕ d₁) / e₂ ≣ (u₂' ↕ d₁') →

         -- add the remaining supply and demand
         (u₁' ↕ d₁') ×⊎ (u₂' ↕ d₂') ≣ ud →

         Split (u₁ ↕ d₁) (u₂ ↕ d₂) ud

  instance exchange-raw : RawSep Account
  exchange-raw = record { _⊎_≣_ = Split }

  instance exchange-is-sep : IsSep _≈_ exchange-raw

  IsSep.⊎-respects-≈ˡ exchange-is-sep (eq₁ , eq₂) (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) σ)
    = ex (⊎-respects-≈ eq₁ x₁₁ , x₁₂) (x₂₁ , ⊎-respects-≈ eq₂ x₂₂) σ 
  IsSep.⊎-respects-≈  exchange-is-sep (eq₁ , eq₂) (ex x₁ x₂ (σ₁ , σ₂))
    = ex x₁ x₂ (⊎-respects-≈ eq₁ σ₁ , ⊎-respects-≈ eq₂ σ₂)

  IsSep.⊎-comm exchange-is-sep (ex x₁ x₂ σ) = ex x₂ x₁ (⊎-comm σ)

  -- A visualization of this proof is included in the notes of this repository
  IsSep.⊎-assoc exchange-is-sep
    (ex {a>b}  {b>a}  {a↑}  {a↓}  {b↑} {b↓} {a↑'}  {a↓'}  {b↑'} {b↓'} x₁ x₂ σ₁)
    (ex {ab>c} {c>ab} {ab↑} {ab↓} {c↑} {c↓} {ab↑'} {ab↓'} {c↑'} {c↓'} x₃ x₄ σ₂)
    with cross (proj₁ σ₁) (proj₁ x₃) | cross (proj₂ σ₁) (proj₂ x₄)
  ... | (a↑'' , a>c , b↑'' , b>c) , z₁ , z₂ , z₃ , z₄
      | (a↓'' , c>a , b↓'' , c>b) , m₁ , m₂ , m₃ , m₄
      with ⊎-assoc z₃ (proj₁ σ₂) | ⊎-assoc z₁ (proj₁ x₁)
         | recombine z₂ (proj₁ x₂) | ⊎-assoc (⊎-comm m₄) (⊎-comm (proj₁ x₄))
         | ⊎-assoc m₃ (proj₂ σ₂) | ⊎-assoc m₁ (proj₂ x₂)
         | recombine m₂ (proj₂ x₁) | ⊎-assoc (⊎-comm z₄) (⊎-comm (proj₂ x₃))
  ... | bc↑ , z₅ , σ₃ | a>bc , x₅ , k₃ | _ , k₁ , k₂ | _ , x₆ , x₇
      | bc↓ , σ₄ , m₅ | bc>a , y₁ , k₄ | _ , y₃ , y₄ | _ , y₅ , y₆
      with uncross (⊎-comm k₁) x₇ (⊎-comm k₄) σ₃
         | uncross (⊎-comm y₆) y₃ (⊎-comm m₅) k₃
  ... | _  , x₈ , x₉ | _ , y₇ , y₈ =
    -, ex (x₅ , y₈) (⊎-comm x₉ , y₁) (z₅  , σ₄)
     , ex (k₂ , ⊎-comm y₅) (⊎-comm x₆ , y₄) (x₈ , ⊎-comm y₇)

module _
  {{ sep : RawSep A }} {eps}
  {{ cs⁻ : HasCrossSplit⁻ _≈ₐ_ sep }}
  {{ cs⁺ : HasCrossSplit⁺ _≈ₐ_ sep }}
  {{ _  : IsPositive _≈ₐ_ sep eps }}
  {{ un  : HasUnit _≈ₐ_ sep eps }}
  where

  open import Relation.Ternary.Separation.Construct.Product

  instance exchange-has-unit : HasUnit _≈_ exchange-raw (eps ↕ eps)
  HasUnit.ε-unique exchange-has-unit ρ with ε-unique (proj₁ ρ) | ε-unique (proj₂ ρ)
  ... | PEq.refl | PEq.refl = PEq.refl

  HasUnit.⊎-idˡ exchange-has-unit =
    ex (⊎-idˡ , ⊎-idʳ) (⊎-idʳ , ⊎-idˡ) (⊎-idˡ {{×-hasUnit}})

  HasUnit.⊎-id⁻ˡ exchange-has-unit (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) (σ₁ , σ₂)) with ⊎-ε x₁₁ | ⊎-ε x₂₂
  ... | PEq.refl , PEq.refl | PEq.refl , PEq.refl =
    trans (sym (⊎-id⁻ʳ x₂₁)) (⊎-id⁻ˡ σ₁) , trans (sym (⊎-id⁻ʳ x₁₂)) (⊎-id⁻ˡ σ₂)
