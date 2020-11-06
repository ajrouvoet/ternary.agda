{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Weakening {a e} {A : Set a} {_≈_ : A → A → Set e} {u}
  {{rel : Rel₃ A}}
  {{c : IsCommutative rel}}
  {{m : IsPartialMonoid _≈_ rel u}} where

open import Level
open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

module _ where
  infixr 10 _⇑
  _⇑ : PT A A a a
  P ⇑ = P ✴ U

  -- _⇈_ : ∀ {ℓ} {P : Pred A ℓ} {Φ₁ Φ₂ Φ} → P Φ₁ → Φ₁ ∙ Φ₂ ≣ Φ → (P ⇑) Φ
  pattern _⇈_ px σ = px ∙⟨ σ ⟩ tt

  instance
    ⇑-functor : Functor _⇑
    Functor.fmap ⇑-functor f (px ⇈ wk) = (f px) ⇈ wk

    ⇑-monad : Monad ⊤ (λ _ _ → _⇑)
    Monad.return ⇑-monad px = px ⇈ ∙-idʳ
    Monad._=<<_ ⇑-monad f (px ⇈ wk) with qx ⇈ wk' ← f px =
      let _ , wk₃ , wk₄ = ∙-assocᵣ wk' wk in qx ⇈ wk₃

    ⇑-strong : Strong ⊤ (λ _ _ → _⇑)
    Strong.str ⇑-strong qx ⟨ σ ⟩ px ⇈ wk with _ , σ₃ , σ₄ ← ∙-assocₗ σ wk = (qx ∙⟨ σ₃ ⟩ px) ⇈ σ₄

  module _ {P Q : Pred A a} where
    π₁ : ∀[ P ✴ Q ⇒ P ⇑ ]
    π₁ (px ∙⟨ σ ⟩ qx) = px ⇈ σ

    π₂ : ∀[ P ✴ Q ⇒ Q ⇑ ]
    π₂ (px ∙⟨ σ ⟩ qx) = qx ⇈ (∙-comm σ)

  module _ {P Q : Pred A a} where
    unstar : ∀[ (P ✴ Q) ⇑ ⇒ ((P ⇑) ∩ (Q ⇑)) ]
    unstar p✴q = (p✴q >>= π₁) , (p✴q >>= π₂)

  th : {P : Pred A a} → Φ₁ ∙ Φ₂ ≣ Φ → (P ⇑) Φ₁ →  (P ⇑) Φ
  th σ (px ∙⟨ wk ⟩ tt) with ∙-assocᵣ wk σ
  ... | _ , σ₃ , σ₄ = px ⇈ σ₃
