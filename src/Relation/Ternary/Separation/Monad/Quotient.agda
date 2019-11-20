open import Relation.Binary.Structures

module Relation.Ternary.Separation.Monad.Quotient {a} {A : Set a} where

open import Level
open import Relation.Unary
open IsEquivalence {{...}}

open import Relation.Ternary.Separation.Core

{- Quotients over a given equivalence relation -}
record _/_ {e p} (P : Pred A p) (_≈_ : A → A → Set e) (aₒ : A) : Set (e ⊔ p ⊔ a) where
  constructor _div_
  field
    {aᵢ} : A
    px : P aᵢ
    eq : aᵢ ≈ aₒ

module _ {e} {_≈_ : A → A → Set e} {{eq : IsEquivalence _≈_ }} where

  instance /≈-respect-≈ : ∀ {p} {P : Pred A p} → Respect _≈_ (P / _≈_) 
  Respect.coe /≈-respect-≈ eq₁ (px div eq₂) = px div (trans eq₂ eq₁)

module _ {e} {_≈_ : A → A → Set e} {{r : RawSep A}} where

  {- Arrows module equivalence -}
  _≈>_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ≈> Q = P ⇒ (Q / _≈_)

  _~✴_ : ∀ {p q} → Pred A p → Pred A q → Pred A (p ⊔ q ⊔ a ⊔ e)
  P ~✴ Q = P ─✴ (Q / _≈_)

module _ {e} {_≈_ : A → A → Set e} {{r : RawSep A}} {u} {{_ : HasUnit _≈_ r u }} where
  open import Relation.Ternary.Separation.Monad (record { isEquivalence = ≈-equivalence })
  open import Data.Unit

  instance /-monad : ∀ {p} → Monad ⊤ (e ⊔ p ⊔ a) (λ _ _ P → P / _≈_)
  Monad.return /-monad px = px div refl
  Monad.bind /-monad f ⟨ σ ⟩ (px div eq) = f ⟨ ⊎-respects-≈ʳ (sym eq) σ ⟩ px
