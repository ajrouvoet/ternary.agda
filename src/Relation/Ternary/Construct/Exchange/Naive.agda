module Relation.Ternary.Separation.Construct.Exchange.Naive where

open import Level hiding (Lift)
open import Function
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

module _ {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {{ _ : IsSep _≡_ sep }} where

  open import Relation.Ternary.Separation.Construct.Product

  -- lifted pointwise product split
  _×⊎_≣_ : (l r t : Balance A) → Set ℓ
  (u₁ ↕ d₁) ×⊎ (u₂ ↕ d₂) ≣ (u ↕ d) = (u₁ , d₁) ⊎ (u₂ , d₂) ≣ (u , d)

  Exchange : A → Balance A → Balance A → Set ℓ
  Exchange e ud₁ ud₂ = (e ↕ e) ×⊎ ud₁ ≣ ud₂

  data Split : Balance A → Balance A → Balance A → Set ℓ where
    -- either just add up both the supply (up) and demand (down)
    -- (lifting of split on A lifted pointwise over the pair)
    sum       : ∀ {ud₁ ud₂ ud}       → ud₁ ×⊎ ud₂ ≣ ud  → Split ud₁ ud₂ ud
    -- or 'exchange' between supply and demand, dropping 'e' units on both sides
    -- of the balance
    exchange  : ∀ {ud₁ ud₂ ud e ud'} → Split ud₁ ud₂ ud → Exchange e ud ud' → Split ud₁ ud₂ ud'

  exchange-raw : RawSep (Balance A)
  exchange-raw = record { _⊎_≣_ = Split }

  mutual
    assoc-lemma : ∀ {a b e ud ab c abc} → Split a b ud → e ×⊎ ud ≣ ab → ab ×⊎ c ≣ abc →
                  ∃₂ λ udc bc → e ×⊎ udc ≣ abc × a ×⊎ bc ≣ udc × Split b c bc
    assoc-lemma (sum σ₁) x σ₂ with ⊎-assoc x σ₂
    ... | udc , σ₃ , σ₄ with ⊎-assoc σ₁ σ₄
    ... | _   , σ₅ , σ₆ =  -, -, σ₃ , σ₅ , (sum σ₆)

    assoc-lemma (exchange σ₁ x₁) x₂ σ₂ with ⊎-unassoc x₂ x₁
    ... | _ , x₃ , x₄ with assoc-lemma σ₁ x₄ σ₂
    ... | udc , bc , x₅ , σ₃ , σ₄ with ⊎-assoc x₃ x₅
    ... | _ , x₆ , x₇ with ⊎-assoc σ₃ (⊎-comm x₇)
    ... | _ , τ₁ , τ₂ = _ , _ , x₆ , τ₁ , exchange σ₄ (⊎-comm τ₂)

    instance exchange-is-sep : IsSep _≡_ exchange-raw

    IsSep.≈-equivalence exchange-is-sep = isEquivalence
    IsSep.⊎-respects-≈ exchange-is-sep refl = id
    IsSep.⊎-respects-≈ˡ exchange-is-sep refl = id

    IsSep.⊎-comm exchange-is-sep (sum x) = sum (⊎-comm x)
    IsSep.⊎-comm exchange-is-sep (exchange σ e) = exchange (⊎-comm σ) e

    IsSep.⊎-assoc exchange-is-sep σ₁              (exchange σ₂ x₁) =
      let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂  in -, exchange σ₃ x₁ , σ₄
    IsSep.⊎-assoc exchange-is-sep (sum x)         (sum y) =
      let _ , σ₁ , σ₂ = ⊎-assoc x y in -, sum σ₁ , sum σ₂
    IsSep.⊎-assoc exchange-is-sep (exchange σ₁ x) (sum σ₃) =
      let _ , bc , x' , σ₄ , σ₅ = assoc-lemma σ₁ x σ₃
      in bc , exchange (sum σ₄) x' , σ₅

module _ {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {u} {{ _ : HasUnit _≡_ sep u }} where

    open import Relation.Ternary.Separation.Construct.Product as PR

    instance exchange-has-unit : HasUnit _≡_ exchange-raw (u ↕ u)
    HasUnit.⊎-idˡ exchange-has-unit         = sum ⊎-idˡ
    HasUnit.ε-unique exchange-has-unit refl = refl
    HasUnit.⊎-id⁻ˡ exchange-has-unit (sum x) with ⊎-id⁻ˡ x
    ... | (P.refl , P.refl) = P.refl
    HasUnit.⊎-id⁻ˡ exchange-has-unit (exchange σ (x₁ , x₂)) with ⊎-id⁻ˡ σ
    ... | P.refl = {!!}

    
