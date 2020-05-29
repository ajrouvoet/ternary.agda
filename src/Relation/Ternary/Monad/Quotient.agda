{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.Structures

module Relation.Ternary.Monad.Quotient {a} {A : Set a} (_≈_ : A → A → Set a) where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open IsEquivalence {{...}}
open import Data.Unit

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

{- Quotients over a given equivalence relation -}
record 𝑸 (P : Pred A a)  (aₒ : A) : Set a where
  constructor _/_
  field
    {aᵢ} : A
    px : P aᵢ
    eq : aᵢ ≈ aₒ

module _ {{eq : IsEquivalence _≈_ }} where

  instance /≈-respect-≈ : ∀ {P : Pred A a} → Respect _≈_ (𝑸 P)
  Respect.coe /≈-respect-≈ eq₁ (px / eq₂) = px / (trans eq₂ eq₁)

module _ {{r : Rel₃ A}} where

  {- Arrows module equivalence -}
  infix 4 _≈>_
  _≈>_ : ∀ {p} → Pred A p → Pred A a → Pred A (p ⊔ a)
  P ≈> Q = P ⇒ (𝑸 Q)

  infix 4 _~✴_
  _~✴_ : ∀ {p} → Pred A p → Pred A a → Pred A (p ⊔ a)
  P ~✴ Q = P ─✴ (𝑸 Q)

module _ {{r : Rel₃ A}} {u} {{_ : IsPartialMonoid _≈_ r u }} where
  open import Data.Unit

  instance /-monad : Monad ⊤ (λ _ _ P → 𝑸 P)
  Monad.return /-monad px = px / refl
  Monad._=<<_  /-monad f (px / eq) with qx / eq' ← f px = qx / (trans eq' eq)
