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
open import Relation.Ternary.Monad

open import Data.Unit

Id : ∀ {ℓ} → Pt A ℓ
Id P = P

instance
  id-monad : ∀ {ℓ} → Monad {ℓ₁ = ℓ} ⊤ (λ _ _ → Id)
  Monad.return id-monad = id
  Monad.bind id-monad f ⟨ σ ⟩ px = f ⟨ σ ⟩ px

