open import Relation.Ternary.Core

module Relation.Ternary.Monad.Weakening {a} {A : Set a} {{rel : Rel₃ A}} where

open import Level
open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad

module _ where
  infixr 10 _⇑
  _⇑ : ∀ {ℓ} → PT A A ℓ (a ⊔ ℓ)
  P ⇑ = P ⊙ U

  pattern _⇈_ px σ = px ∙⟨ σ ⟩ tt

  π₁ : ∀ {ℓ} {P Q : Pred A ℓ} → ∀[ P ⊙ Q ⇒ P ⇑ ]
  π₁ (px ∙⟨ σ ⟩ qx) = px ⇈ σ

  π₂ : ∀ {ℓ} {{_ : IsCommutative rel}} {P Q : Pred A ℓ} → ∀[ P ⊙ Q ⇒ Q ⇑ ]
  π₂ (px ∙⟨ σ ⟩ qx) = qx ⇈ (∙-comm σ)

module _ 
  {e} {_≈_ : A → A → Set e}
  {{_ : IsPartialSemigroup _≈_ rel}} where

  th : ∀ {ℓ} {P : Pred A ℓ} → Φ₁ ∙ Φ₂ ≣ Φ → (P ⇑) Φ₁ →  (P ⇑) Φ
  th σ (px ⇈ wk) with ∙-assocᵣ wk σ
  ... | _ , σ₃ , σ₄ = px ⇈ σ₃

module _
  {e} {_≈_ : A → A → Set e} {u}
  {{_ : IsPartialMonoid _≈_ rel u}} where

  instance ⇑-monad : ∀ {ℓ} → Monad ⊤ (λ _ _ → _⇑ {ℓ})
  Monad.return ⇑-monad px = px ⇈ ∙-idʳ
  Monad.bind ⇑-monad f ⟨ σ₁ ⟩ (px ⇈ σ₂) with ∙-assocₗ σ₁ σ₂
  ... | _ , σ₃ , σ₄ with f ⟨ σ₃ ⟩ px
  ... | qx ⇈ σ₅ with ∙-assocᵣ σ₅ σ₄
  ... | _ , σ₆ , σ₇ = qx ⇈ σ₆
