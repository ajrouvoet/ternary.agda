open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Identity
  {a e} {A : Set a} {_≈_ : A → A → Set e}
  {{rel : Rel₃ A}}
  {unit} {{_ : IsPartialMonoid _≈_ rel unit}} where

open import Level
open import Function using (_∘_; case_of_; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

open import Data.Unit

Id : ∀ {ℓ} → Pt A ℓ
Id P = P

instance
  id-monad : Monad ⊤ (λ _ _ → Id)
  Monad.return id-monad = id
  Monad._=<<_ id-monad f px = f px

  id-strong : Strong ⊤ (λ _ _ → Id)
  Strong.str id-strong qx ⟨ σ ⟩ px = qx ∙⟨ σ ⟩ px
