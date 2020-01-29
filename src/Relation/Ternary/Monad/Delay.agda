module Relation.Ternary.Monad.Delay {a e} {A : Set a} {_≈_ : A → A → Set e} where

open import Level
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad {_≈_ = _≈_}

open import Codata.Delay as D using (now; later) public
open import Data.Unit

module _
  {{rel : Rel₃ A}}
  {u} {{us : IsPartialMonoid _≈_ rel u}}
 where

  Delay : ∀ {ℓ} i → Pt A ℓ
  Delay i P c = D.Delay (P c) i

  instance
    delay-monad : ∀ {i p} → Monad {ℓ₁ = p} ⊤ (λ _ _ → Delay i)
    Monad.return delay-monad px = D.now px
    Monad.bind delay-monad f ⟨ σ ⟩ ►px = D.bind ►px λ px → f ⟨ σ ⟩ px
