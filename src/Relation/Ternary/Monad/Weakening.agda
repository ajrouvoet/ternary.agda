open import Relation.Ternary.Core

module Relation.Ternary.Monad.Weakening {a} {A : Set a} {{rel : Rel₃ A}} where

open import Level
open import Data.Unit
open import Data.Product

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad

_⇑ : ∀ {ℓ} → PT A A ℓ (a ⊔ ℓ)
P ⇑ = P ⊙ U

module _ {e} {_≈_ : A → A → Set e} {u} {{_ : IsPartialMonoid _≈_ rel u}} where

  ⇑-monad : ∀ {ℓ} → Monad ⊤ (λ _ _ → _⇑ {ℓ})
  Monad.return ⇑-monad px = px ∙⟨ ∙-idʳ ⟩ tt
  Monad.bind ⇑-monad f ⟨ σ₁ ⟩ (px ∙⟨ σ₂ ⟩ tt) with ∙-assocₗ σ₁ σ₂
  ... | _ , σ₃ , σ₄ with f ⟨ σ₃ ⟩ px
  ... | qx ∙⟨ σ₅ ⟩ tt with ∙-assocᵣ σ₅ σ₄
  ... | _ , σ₆ , σ₇ = qx ∙⟨ σ₆ ⟩ tt
