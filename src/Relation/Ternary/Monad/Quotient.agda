{-# OPTIONS --safe --overlapping-instances #-}
open import Relation.Binary.Structures

module Relation.Ternary.Monad.Quotient {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open IsEquivalence {{...}}

open import Relation.Ternary.Core
open import Relation.Ternary.Structures _≈_

{- Quotients over a given equivalence relation -}
record 𝑸 {p} (P : Pred A p)  (aₒ : A) : Set (e ⊔ p ⊔ a) where
  constructor _div_
  field
    {aᵢ} : A
    px : P aᵢ
    eq : aᵢ ≈ aₒ

module _ {{eq : IsEquivalence _≈_ }} where

  instance /≈-respect-≈ : ∀ {p} {P : Pred A p} → Respect _≈_ (𝑸 P) 
  Respect.coe /≈-respect-≈ eq₁ (px div eq₂) = px div (trans eq₂ eq₁)

module Quotiented {{r : Rel₃ A}} where

  {- Arrows module equivalence -}
  _≈>_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ≈> Q = P ⇒ (𝑸 Q)

  _~✴_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ~✴ Q = P ─⊙ (𝑸 Q)

module _ {{r : Rel₃ A}} {u} {{_ : IsPartialMonoid r u }} where
  open import Relation.Ternary.Monad _≈_
  open import Data.Unit

  instance /-monad : Monad ⊤ (e ⊔ a) (λ _ _ P → 𝑸 P)
  Monad.return /-monad px = px div refl
  Monad.bind /-monad f ⟨ σ ⟩ (px div eq) = f ⟨ ∙-respects-≈ˡ (sym eq) σ ⟩ px
