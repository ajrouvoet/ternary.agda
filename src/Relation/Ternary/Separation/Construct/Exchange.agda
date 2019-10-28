module Relation.Ternary.Separation.Construct.Exchange where

open import Level hiding (Lift)
open import Data.Product

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Morphisms

module _ {ℓ} (A : Set ℓ) where

  record Balance : Set ℓ where
    constructor _↕_
    field
      up   : A
      down : A

  open Balance public

module _ {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {{ cs : HasCrossSplit sep }} where

  open import Relation.Ternary.Separation.Construct.Product

  -- lifted pointwise product split
  _×⊎_≣_ : (l r t : Balance A) → Set ℓ
  (u₁ ↕ d₁) ×⊎ (u₂ ↕ d₂) ≣ (u ↕ d) = (u₁ , d₁) ⊎ (u₂ , d₂) ≣ (u , d)

  -- subtract some amount from both sides of the balance
  _/_≣_ : Balance A → A → Balance A → Set ℓ
  ud₁ / e ≣ ud₂ = ud₂ ×⊎ (e ↕ e) ≣ ud₁

  data Split : Balance A → Balance A → Balance A → Set ℓ where
    ex : ∀ {e₁ e₂ u₁ d₁ u₂ d₂ u₁' d₁' u₂' d₂' ud} →

         -- bind e₁ and e₂ in oposite side
         (u₁ ↕ d₂) / e₁ ≣ (u₁' ↕ d₂') →
         (u₂ ↕ d₁) / e₂ ≣ (u₂' ↕ d₁') →

         -- add the remaining supply and demand
         (u₁' ↕ d₁') ×⊎ (u₂' ↕ d₂') ≣ ud →

         Split (u₁ ↕ d₁) (u₂ ↕ d₂) ud

  exchange-raw : RawSep (Balance A)
  exchange-raw = record { _⊎_≣_ = Split }

  instance exchange-is-sep : IsSep exchange-raw

  IsSep.⊎-comm exchange-is-sep (ex x₁ x₂ σ) = ex x₂ x₁ (⊎-comm σ)

  -- TODO fix names
  -- A visualization of this proof is included in the notes of this repository
  IsSep.⊎-assoc exchange-is-sep
    (ex {e₁ = e_a>b} {e₂ = e_b>a} {a↑} {a↓} {b↑} {b↓} {a↑'} {a↓'} {b↑'} {b↓'} x₁ x₂ σ₁)
    (ex {e_ab>c} {e_c>ab} {ab↑} {ab↓} {c↑} {c↓} {ab↑'} {ab↓'} {c↑'} {c↓'}  x₃ x₄ σ₂)
    with cross (proj₁ σ₁) (proj₁ x₃) | cross (proj₂ σ₁) (proj₂ x₄)
  ... | (a↑'' , e_a>c , b↑'' , e_b>c) , z₁ , z₂ , z₃ , z₄
      | (a↓'' , e_c>a , b↓'' , e_c>b) , m₁ , m₂ , m₃ , m₄
      with ⊎-assoc z₃ (proj₁ σ₂) | ⊎-assoc z₁ (proj₁ x₁) | recombine z₂ (proj₁ x₂) | ⊎-assoc (⊎-comm m₄) (⊎-comm (proj₁ x₄))
         | ⊎-assoc m₃ (proj₂ σ₂) | ⊎-assoc m₁ (proj₂ x₂) | recombine m₂ (proj₂ x₁) | ⊎-assoc (⊎-comm z₄) (⊎-comm (proj₂ x₃))
  ... | bc↑ , z₅ , σ₃ | a>bc , x₅ , k₃ | _ , k₁ , k₂ | _ , x₆ , x₇
      | bc↓ , σ₄ , m₅ | bc>a , y₁ , k₄ | _ , y₃ , y₄ | _ , y₅ , y₆
      with uncross (⊎-comm k₁) x₇ (⊎-comm k₄) σ₃ | uncross (⊎-comm y₆) y₃ (⊎-comm m₅) k₃
  ... | _  , x₈ , x₉ | _ , y₇ , y₈ =
    -, ex (x₅ , y₈) (⊎-comm x₉ , y₁) (z₅  , σ₄)
     , ex (k₂ , ⊎-comm y₅) (⊎-comm x₆ , y₄) (x₈ , ⊎-comm y₇)

module _
  {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {eps}
  {{ cs : HasCrossSplit sep }} {{ _ : IsPositive sep eps }}where

  open import Relation.Ternary.Separation.Construct.Product

  instance exchange-has-unit : IsUnitalSep exchange-raw (eps ↕ eps)
  IsUnitalSep.⊎-idˡ exchange-has-unit    = ex (⊎-idˡ , ⊎-idʳ) (⊎-idʳ , ⊎-idˡ) ⊎-idˡ
  IsUnitalSep.⊎-id⁻ˡ exchange-has-unit (ex (x₁₁ , x₁₂) (x₂₁ , x₂₂) (σ₁ , σ₂)) with ⊎-ε x₁₁ | ⊎-ε x₂₂
  ... | refl , refl | refl , refl with ⊎-id⁻ˡ σ₁ | ⊎-id⁻ˡ σ₂ | ⊎-id⁻ʳ x₂₁ | ⊎-id⁻ʳ x₁₂
  ... | refl | refl | refl | refl = refl
