{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.Structures

module Relation.Ternary.Upto {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Data.Unit

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

module _ {{r : Rel₃ A}} {u} {{_ : IsPartialMonoid _≈_ r u }} where
  open import Data.Unit

  record Upto : Set (e ⊔ suc a) where
    field
      ⌈_⌉                    : Pt A a
      overlap {{respectful}} : ∀ {P : Pred A a} → Respect _≈_ ⌈ P ⌉
      overlap {{monad}}      : Monad ⊤ (λ _ _ → ⌈_⌉) 

    _over_ : ∀ {P : Pred A a} {a b} → P a → a ≈ b → ⌈ P ⌉ b
    px over eq = coe {{respectful}} eq (return px)

    infixl 8 _∼>_
    _∼>_ : ∀ {q} (P : Pred A q) (Q : Pred A a) → Pred A (a ⊔ q)
    (P ∼> Q) Φ = P Φ → ⌈ Q ⌉ Φ

    infixl 8 _∼✴_
    _∼✴_ : ∀ {q} (P : Pred A q) (Q : Pred A a) → Pred A (a ⊔ q)
    P ∼✴ Q = P ─✴ ⌈ Q ⌉

  open Upto {{...}} public
