{-# OPTIONS --safe --no-qualified-instances #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Error {ℓ} {A : Set ℓ}
  {{r : Rel₃ A}}
  {e u} {_≈_ : A → A → Set e} {{_ : IsPartialMonoid _≈_ r u}}
  where

open import Level
open import Function using (_∘_)
open import Data.Unit
open import Data.Sum
open import Relation.Unary renaming (U to True)
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Morphisms
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Identity using (Id)
open import Relation.Ternary.Structures.Syntax
open import Relation.Binary.PropositionalEquality

module _ where
  record ExceptT (M : Pt A ℓ) (E : Set ℓ) (P : Pred A ℓ) (Φ : A) : Set ℓ where
    constructor partial
    field
      runErr : M ((λ _ → E) ∪ P) Φ

  open ExceptT public

  Except : ∀ E → Pt A ℓ
  Except E = ExceptT Id E

  pattern error e = partial (inj₁ e)
  pattern ✓ x     = partial (inj₂ x)

  data Err : Set ℓ where
    err : Err

  ErrorT : (M : Pt A ℓ) → Pt A ℓ
  ErrorT M = ExceptT M Err

  Error : Pt A ℓ
  Error = ErrorT Id

module ExceptTrans (M : Pt A ℓ) (Exc : Set ℓ) where

  module _ {{monad : Functor M }} where
    instance
      except-functor : Functor (ExceptT M Exc)
      Functor.fmap except-functor f (partial m) = partial ([ inj₁ , inj₂ ∘ f ] ⟨$⟩ m)

    mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ ExceptT M E₁ P ⇒ ExceptT M E₂ P ]
    mapExc f (partial mc) = partial ((λ where (inj₁ e) → inj₁ (f e); (inj₂ px) → inj₂ px) ⟨$⟩ mc)

  module _ {{monad : Monad ⊤ (λ _ _ → M) }} where
    instance 
      except-monad : Monad ⊤ (λ _ _ → ExceptT M Exc)
      Monad.return except-monad px = partial (return (inj₂ px))
      (except-monad Monad.=<< f) (partial m) = partial do
        inj₂ px ← m where (inj₁ e) → return (inj₁ e)
        runErr (f px)
        
  module _ {{strong : Strong ⊤ (λ _ _ → M) }} where
    instance 
      except-strong : Strong ⊤ (λ _ _ → ExceptT M Exc)
      Strong.str except-strong {Q = Q} q ⟨ σ ⟩ (partial m) = partial do
        qx ∙⟨ σ ⟩ px? ← str {Q = Q} q ⟨ σ ⟩ m
        return ([ inj₁ , (λ px → inj₂ (qx ∙⟨ σ ⟩ px)) ] px?)

-- module ErrorTrans (M : Pt A ℓ) {{monad : Monads.Monad ⊤ ℓ (λ _ _ → M) }} where
--   open import Relation.Ternary.Separation.Monad.Identity
--   open ExceptTrans M {{ monad }} Err public
--     renaming (except-monad to error-monad)

-- module ErrorMonad where
--   open import Relation.Ternary.Separation.Monad.Identity
--   open ExceptTrans Identity.Id {{ Identity.id-monad }} Err public
--     renaming (except-monad to error-monad)
