{-# OPTIONS --safe --overlapping-instances #-}
module Relation.Ternary.Monad.Update {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures _≈_
open import Relation.Ternary.Monad _≈_

open import Data.Unit
open import Data.Product

-- | The update modality
module _ {{_ : Rel₃ A}} where

  -- the naked version, which doesn't coop well with inference:
  ⤇' : ∀ {p} (P : Pred A p) → Pred A (a ⊔ p)
  ⤇' P Φᵢ = ∀ {Φⱼ Φₖ} → Φᵢ ∙ Φⱼ ≣ Φₖ → ∃₂ λ Φₗ Φ → Φₗ ∙ Φⱼ ≣ Φ × P Φₗ
  -- Φᵢ is what we own, Φⱼ is an arbitrary frame.
  -- We may update Φᵢ as long as we do not disturb the framing

  -- wrapped
  record ⤇ {p} (P : Pred A p) Φᵢ : Set (a ⊔ p) where
    constructor local
    field
      update : ⤇' P Φᵢ

  open ⤇ public

  infixr 8 _==⊙_
  _==⊙_ : ∀ {p q} → (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
  P ==⊙ Q = P ─⊙ (⤇ Q)

module _
  {u} {{r  : Rel₃ A}}
  {{us : IsPartialMonoid r u}}
  where

  instance
    ⤇-monad : Monad ⊤ _ (λ _ _ → ⤇ {p = a})
    Monad.return ⤇-monad px       = local λ σ → -, -, σ , px
    Monad.bind ⤇-monad f ⟨ σₚ ⟩ p = local λ fr →
      let
        _ , σ₁ , σ₂     = ∙-assocᵣ σₚ fr
        Δ , Σ , σ₃ , px = update p σ₁
        _ , σ₄ , σ₅     = ∙-assocₗ σ₃ σ₂
      in update (f ⟨ σ₄ ⟩ px) σ₅
