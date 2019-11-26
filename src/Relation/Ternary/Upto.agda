{-# OPTIONS --safe #-}
open import Relation.Binary.Structures

module Relation.Ternary.Upto {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open IsEquivalence {{...}}
open import Data.Unit

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad {_≈_ = _≈_}

module _ {{r : Rel₃ A}} {u} {{_ : IsPartialMonoid {_≈_ = _≈_} r u }} where
  open import Data.Unit

  record Program p : Set (e ⊔ suc p ⊔ a) where
    field
      ⌈_⌉                    : Pt A p
      overlap {{respectful}} : ∀ {P : Pred A p} → Respect _≈_ ⌈ P ⌉
      overlap {{monad}}      : Monad ⊤ (λ _ _ → ⌈_⌉) 

    _over_ : ∀ {P : Pred A p} {a b} → P a → a ≈ b → ⌈ P ⌉ b
    px over eq = coe {{respectful}} eq (return px)

    infixl 8 _∼>_
    _∼>_ : ∀ {q} (P : Pred A q) (Q : Pred A p) → Pred A (p ⊔ q)
    (P ∼> Q) Φ = P Φ → ⌈ Q ⌉ Φ

    infixl 8 _∼⊙_
    _∼⊙_ : ∀ {q} (P : Pred A q) (Q : Pred A p) → Pred A (a ⊔ p ⊔ q)
    P ∼⊙ Q = P ─⊙ ⌈ Q ⌉

  open Program {{...}} public
