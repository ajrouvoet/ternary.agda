{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Identity {a} {A : Set a} where

open import Level
open import Function using (_∘_; case_of_; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import Data.Unit

module Unwrapped where

  Id : ∀ {ℓ} → Pt A ℓ
  Id P = P

  module _ {{rel : Rel₃ A}} where
    instance
      id-functor : Functor Id
      Functor.fmap id-functor f px = f px

      id-monad : Monad ⊤ (λ _ _ → Id)
      Monad.return id-monad = id
      Monad._=<<_ id-monad f px = f px

      id-strong : Strong ⊤ (λ _ _ → Id)
      Strong.str id-strong qx ⟨ σ ⟩ px = qx ∙⟨ σ ⟩ px

module Wrapped where

  record Id {ℓ} (P : Pred A ℓ) (Φ : A) : Set ℓ where
    constructor mkId
    field
      runId : P Φ

  open Id public

  instance
    id-functor : Functor Id
    Functor.fmap id-functor f (mkId px) = mkId (f px)

    id-resp : ∀ {p e} {_≈_ : A → A → Set e} {P : Pred A p} {{_ : Respect _≈_ P}} → Respect _≈_ (Id P)
    Respect.coe id-resp eq (mkId px) = mkId (coe eq px)

  module _ {{rel : Rel₃ A}} where
    instance
      id-monad : Monad ⊤ (λ _ _ → Id)
      Monad.return id-monad = mkId
      Monad._=<<_ id-monad f px = f (runId px)

      id-strong : Strong ⊤ (λ _ _ → Id)
      Strong.str id-strong qx ⟨ σ ⟩ px = mkId (qx ∙⟨ σ ⟩ runId px)

open Unwrapped public
