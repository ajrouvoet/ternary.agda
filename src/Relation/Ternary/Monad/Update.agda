{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Monad.Update {a} {A : Set a} where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; isEquivalence)
open import Relation.Unary
open import Relation.Binary using (IsPreorder)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import Data.Unit
open import Data.Product

-- | The update modality
module _ {{_ : Rel₃ A}} where

  -- the naked version, which doesn't coop well with inference:
  ⤇' : ∀ {p} (P : Pred A p) → Pred A (a ⊔ p)
  ⤇' P Φᵢ = ∀ {Φⱼ} → Φⱼ ◆ Φᵢ → ∃ λ Φₗ → Φⱼ ◆ Φₗ × P Φₗ
  -- Φᵢ is what we own, Φⱼ is an arbitrary frame.
  -- We may update Φᵢ as long as we do not disturb the framing

  -- wrapped
  record ⤇ {p} (P : Pred A p) Φᵢ : Set (a ⊔ p) where
    constructor local
    field
      update : ⤇' P Φᵢ

  open ⤇ public

  infixr 8 _⟾_
  _⟾_ : ∀ {p q} → (P : Pred A p) (Q : Pred A q) → Pred A (p ⊔ q ⊔ a)
  P ⟾ Q = P ─⊙ (⤇ Q)

module _
  {{r  : Rel₃ A}}
  {e} {_≈_ : A → A → Set e}
  {u} {{us : IsPartialMonoid _≈_ r u}}
  where

  instance
    ⤇-monad : Monad ⊤ (λ _ _ → ⤇ {p = a})
    Monad.return ⤇-monad px       = local λ σ → -, σ , px
    Monad.bind ⤇-monad f ⟨ σₚ ⟩ p = local λ fr →
      let
        _ , σ₁ , σ₂     = ∙-assocₗ (proj₂ fr) σₚ
        Δ , σ₃ , px = update p (-, σ₂)
        _ , σ₄ , σ₅     = ∙-assocᵣ σ₁ (proj₂ σ₃)
      in update (f ⟨ σ₅ ⟩ px) (-, σ₄) 
