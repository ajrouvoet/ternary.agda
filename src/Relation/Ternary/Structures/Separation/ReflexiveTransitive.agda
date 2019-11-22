{-# OPTIONS --safe #-}
open import Relation.Ternary.Separation

module Relation.Ternary.Separation.ReflexiveTransitive
  {c} {C : Set c} {{rc : RawSep C}}
  where

open import Level
open import Data.Product
open import Relation.Unary

module _
  {_≈_ : C → C → Set c} {u} {{_ : HasUnit _≈_ rc u}}
  {A : Set c} (R : A → A → Pred C c) where

  open import Relation.Ternary.Separation.Monad _≈_
  open import Relation.Ternary.Separation.Monad.Quotient
  open Quotiented _≈_

  data Star : (a₁ a₂ : A) → Pred C c where
    nil   : ∀ {a}        → ε[ Star a a ]
    cons  : ∀ {a₁ a₂ a₃} → ∀[ R a₁ a₂ ✴ Star a₂ a₃ ⇒ Star a₁ a₃ ]

  pattern _▹⟨_⟩_ r σ rs = cons (r ×⟨ σ ⟩ rs)

  append : ∀ {a₁ a₂ a₃} → ∀[ Star a₁ a₂ ⇒ Star a₂ a₃ ~✴ Star a₁ a₃ ]
  append nil ⟨ σ ⟩ y = do
    y div ⊎-id⁻ˡ σ
  append (cons (r ×⟨ σ₁ ⟩ rs)) ⟨ σ₂ ⟩ y = do
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂
    rs ×⟨ σ₅ ⟩ r ← append rs ⟨ σ₄ ⟩ y &⟨ ⊎-comm σ₃ ⟩ r
    return (r ▹⟨ ⊎-comm σ₅ ⟩ rs)
