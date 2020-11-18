{-# OPTIONS --safe --no-qualified-instances #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Error where

open import Level
open import Function using (_∘_; const)
open import Data.Unit
open import Data.Sum
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Morphisms
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Identity using (module Wrapped)
open import Relation.Ternary.Structures.Syntax
open import Relation.Binary.PropositionalEquality
open Wrapped

module _ {ℓ} (Exc : Set ℓ) {A : Set ℓ} where

  record ExceptT (M : Pt A ℓ) (P : Pred A ℓ) (Φ : A) : Set ℓ where
    constructor exceptT
    field
      runExcT : M ((const Exc) ∪ P) Φ

  open ExceptT public

  Except : Pt A ℓ
  Except = ExceptT Id

  pattern except p = exceptT (mkId p)

  data Err : Set ℓ where
    err : Err

module _ {ℓ} {A : Set ℓ} where

  ErrorT : (M : Pt A ℓ) → Pt A ℓ
  ErrorT M = ExceptT Unit.⊤ M
    where open import Data.Unit.Polymorphic as Unit

  Error : Pt A ℓ
  Error = ErrorT Id

  pattern error e = exceptT (inj₁ e)

module _ {ℓ} {Exc : Set ℓ} {A : Set ℓ} {P : Pred A ℓ} where

  runExc : ∀[ Except Exc P ⇒ ((const Exc) ∪ P) ]
  runExc = runId ∘ runExcT
  
  runErrT : ∀ {M} → ∀[ ErrorT M P ⇒ M (True ∪ P) ]
  runErrT = runExcT
  
  runErr : ∀[ Error P ⇒ (True ∪ P) ]
  runErr = runId ∘ runErrT

module _ {ℓ e} {A : Set ℓ} {_≈_ : A → A → Set e} {Exc} {M : Pt A ℓ} {{r : Rel₃ A}} where

  expect-respect : ∀ {P} {{_ : ∀ {Q} → Respect _≈_ (M Q) }} → Respect _≈_ (ExceptT Exc M P)
  Respect.coe expect-respect eq (exceptT e) = exceptT (coe eq e)

module ExceptTrans {ℓ} (Exc : Set ℓ) {A : Set ℓ} (M : Pt A ℓ) where

  module _ {{functor : Functor M }} where
    instance
      except-functor : Functor (ExceptT Exc M)
      Functor.fmap except-functor f (exceptT m) = exceptT ([ inj₁ , inj₂ ∘ f ] ⟨$⟩ m)

    mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ ExceptT E₁ M P ⇒ ExceptT E₂ M P ]
    mapExc f (exceptT mc) = exceptT ((λ where (inj₁ e) → inj₁ (f e); (inj₂ px) → inj₂ px) ⟨$⟩ mc)

  module _ {{r : Rel₃ A}} {{monad : Monad ⊤ (λ _ _ → M) }} where
    instance 
      except-monad : Monad ⊤ (λ _ _ → ExceptT Exc M)
      Monad.return except-monad px = exceptT (return (inj₂ px))
      (except-monad Monad.=<< f) (exceptT m) = exceptT do
        inj₂ px ← m where (inj₁ e) → return (inj₁ e)
        runExcT (f px)

    raise : ∀ {P} → Exc → ∀[ ExceptT Exc M P ]
    runExcT (raise exc) = return (inj₁ exc)
        
  module _ {{r : Rel₃ A}} {{strong : Strong ⊤ (λ _ _ → M) }} where
    instance 
      except-strong : Strong ⊤ (λ _ _ → ExceptT Exc M)
      Strong.str except-strong {Q = Q} q ⟨ σ ⟩ (exceptT m) = exceptT do
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
