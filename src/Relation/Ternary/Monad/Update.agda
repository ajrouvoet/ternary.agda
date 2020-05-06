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
open import Relation.Ternary.Functor
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
  P ⟾ Q = P ─✴ (⤇ Q)

module _
  {{r  : Rel₃ A}}
  {e} {_≈_ : A → A → Set e}
  {u} {{us : IsPartialMonoid _≈_ r u}}
  where

  instance
    ⤇-functor : Functor ⤇
    update (Functor.fmap ⤇-functor f x) fr with _ , σ , px ← update x fr = -, σ , f px

    ⤇-monad : Monad ⊤ (λ _ _ → ⤇)
    Monad.return ⤇-monad px  = local λ σ → -, σ , px
    Monad._=<<_  ⤇-monad f ⤇p = local λ σ →
      let
        _ , τ₁ , px = update ⤇p σ
        _ , τ₂ , qx = update (f px) τ₁
      in _ , τ₂ , qx

    ⤇-strong : Strong ⊤ (λ _ _ → ⤇)
    Strong.str ⤇-strong qx ⟨ σ₁ ⟩ ⤇px = local λ (_ , σ₂) →
      let
        _ , σ₃ , σ₄      = ∙-assocₗ σ₂ σ₁
        _ , (_ , τ) , px = update ⤇px (-, σ₄)
        _ , σ₅ , σ₆      = ∙-assocᵣ σ₃ τ
      in -, ((-, σ₅) , qx  ∙⟨ σ₆ ⟩ px)
