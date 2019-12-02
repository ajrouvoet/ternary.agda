{-# OPTIONS --safe #-}
open import Relation.Binary.Structures

module Relation.Ternary.Monad.Quotient {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open IsEquivalence {{...}}
open import Data.Unit

open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad {_≈_ = _≈_}

{- Quotients over a given equivalence relation -}
record 𝑸 {p} (P : Pred A p)  (aₒ : A) : Set (e ⊔ p ⊔ a) where
  constructor _/_
  field
    {aᵢ} : A
    px : P aᵢ
    eq : aᵢ ≈ aₒ

module _ {{eq : IsEquivalence _≈_ }} where

  instance /≈-respect-≈ : ∀ {p} {P : Pred A p} → Respect _≈_ (𝑸 P) 
  Respect.coe /≈-respect-≈ eq₁ (px / eq₂) = px / (trans eq₂ eq₁)

module _ {{r : Rel₃ A}} where

  {- Arrows module equivalence -}
  infix 4 _≈>_
  _≈>_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ≈> Q = P ⇒ (𝑸 Q)

  infix 4 _~⊙_
  _~⊙_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ~⊙ Q = P ─⊙ (𝑸 Q)

module _ {{r : Rel₃ A}} {u} {{_ : IsPartialMonoid _≈_ r u }} where
  open import Data.Unit

  instance /-monad : ∀ {ℓ} → Monad {ℓ₁ = ℓ} ⊤ (λ _ _ P → 𝑸 P)
  Monad.return /-monad px = px / refl
  Monad.bind /-monad f ⟨ σ ⟩ (px / eq) = f ⟨ coe (sym eq) σ ⟩ px

  record Respectful p : Set (e ⊔ suc p ⊔ a) where
    field
      ⌈_⌉                    : Pt A p
      overlap {{respectful}} : ∀ {P : Pred A p} → Respect _≈_ ⌈ P ⌉
      overlap {{monad}}      : Monad ⊤ (λ _ _ → ⌈_⌉) 

  open Respectful {{...}} public

