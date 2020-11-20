{-# OPTIONS --safe --no-qualified-instances #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Error {ℓ} {A : Set ℓ} where

open import Level
open import Function using (_∘_; const)
open import Data.Unit
open import Data.Sum
open import Relation.Unary hiding (Empty)
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Ternary.Monad
open import Relation.Ternary.Monad.Identity using (module Wrapped)
open import Relation.Ternary.Structures.Syntax
open Wrapped

{- The interface -}
module _ {{_ : Rel₃ A}} where

  record MonadError (E : Set ℓ) (M : Pt A ℓ) : Set (suc ℓ) where
    field
      overlap {{monad}} : Monad ⊤ (λ _ _ → M)
      raise             : ∀ {P} → E → ∀[ M P ]

  -- no idea what the catch signature should be
  -- catch     : ∀ {P} → ∀[ M P ⇒ (⋂[ _ ∶ E ] M P) ⇒ M P ]
      
{- We define a variety of instance constructors -}
module _ (Exc : Set ℓ) where

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

module _ where

  ErrorT : (M : Pt A ℓ) → Pt A ℓ
  ErrorT M = ExceptT Unit.⊤ M
    where open import Data.Unit.Polymorphic as Unit

  Error : Pt A ℓ
  Error = ErrorT Id

  pattern error e = exceptT (inj₁ e)

{- The eliminators for the instances -}
module _ {Exc : Set ℓ} {P : Pred A ℓ} where

  runExc : ∀[ Except Exc P ⇒ ((const Exc) ∪ P) ]
  runExc = runId ∘ runExcT
  
  runErrT : ∀ {M} → ∀[ ErrorT M P ⇒ M (True ∪ P) ]
  runErrT = runExcT
  
  runErr : ∀[ Error P ⇒ (True ∪ P) ]
  runErr = runId ∘ runErrT

{- These instances are respectful when the underlying monad is repectful -}
module _ {e} {_≈_ : A → A → Set e} {Exc} {M : Pt A ℓ} {{r : Rel₃ A}} where

  expect-respect : ∀ {P} {{_ : ∀ {Q} → Respect _≈_ (M Q) }} → Respect _≈_ (ExceptT Exc M P)
  Respect.coe expect-respect eq (exceptT e) = exceptT (coe eq e)

{- These transformer indeed implements the interface -}
module ExceptTrans (Exc : Set ℓ) (M : Pt A ℓ) where

  module _ {{functor : Functor M }} where
    instance
      exceptT-functor : Functor (ExceptT Exc M)
      Functor.fmap exceptT-functor f (exceptT m) = exceptT ([ inj₁ , inj₂ ∘ f ] ⟨$⟩ m)

    mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ ExceptT E₁ M P ⇒ ExceptT E₂ M P ]
    mapExc f (exceptT mc) = exceptT ((λ where (inj₁ e) → inj₁ (f e); (inj₂ px) → inj₂ px) ⟨$⟩ mc)

  module _ {{r : Rel₃ A}} {{monad : Monad ⊤ (λ _ _ → M) }} where
    instance 
      exceptT-monad : Monad ⊤ (λ _ _ → ExceptT Exc M)
      Monad.return exceptT-monad px = exceptT (return (inj₂ px))
      (exceptT-monad Monad.=<< f) (exceptT m) = exceptT do
        inj₂ px ← m where (inj₁ e) → return (inj₁ e)
        runExcT (f px)

      monad-exceptT : MonadError Exc (ExceptT Exc M)
      MonadError.raise monad-exceptT e = exceptT (return (inj₁ e))
        
  module _ {{r : Rel₃ A}} {{strong : Strong ⊤ (λ _ _ → M) }} where
    instance 
      exceptT-strong : Strong ⊤ (λ _ _ → ExceptT Exc M)
      Strong.str exceptT-strong {Q = Q} q ⟨ σ ⟩ (exceptT m) = exceptT do
        qx ∙⟨ σ ⟩ px? ← str {Q = Q} q ⟨ σ ⟩ m
        return ([ inj₁ , (λ px → inj₂ (qx ∙⟨ σ ⟩ px)) ] px?)

module _ {Exc : Set ℓ} where
  -- We specialize the above to avoid the extra instance arguments
  -- at the use-site

  open ExceptTrans Exc Id renaming (mapExc to mapExc')

  instance
    except-functor : Functor (Except Exc)
    except-functor = exceptT-functor {{id-functor}}

  mapExc : ∀ {E₁ E₂ P} → (E₁ → E₂) → ∀[ Except E₁ P ⇒ Except E₂ P ]
  mapExc = mapExc' {{id-functor}}

  module _ {{r : Rel₃ A}} where
    instance 
      except-monad : Monad ⊤ (λ _ _ → Except Exc)
      except-monad = exceptT-monad {{monad = id-monad}}

      monad-except : MonadError Exc (Except Exc)
      monad-except = monad-exceptT {{monad = id-monad}}
        
      except-strong : Strong ⊤ (λ _ _ → Except Exc)
      except-strong = exceptT-strong {{strong = id-strong}}

open MonadError {{...}} public
