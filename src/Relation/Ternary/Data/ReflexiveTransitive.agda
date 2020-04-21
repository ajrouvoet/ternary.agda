{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.ReflexiveTransitive
  {c} {C : Set c} {{rc : Rel₃ C}}
  where

open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.IndexedMonoid

module _
  {A : Set c} (R : A → A → Pred C c) {u}
  {{_ : Emptiness {A = C} u}} where

  data Star : (a₁ a₂ : A) → Pred C c where
    nil   : ∀ {a}        → ε[ Star a a ]
    cons  : ∀ {a₁ a₂ a₃} → ∀[ R a₁ a₂ ✴ Star a₂ a₃ ⇒ Star a₁ a₃ ]

  pattern _▹⟨_⟩_ r σ rs = cons (r ∙⟨ σ ⟩ rs)

  data Plus : (a₁ a₂ : A) → Pred C c where
    cons  : ∀ {a₁ a₂ a₃} → ∀[ R a₁ a₂ ✴ Star a₂ a₃ ⇒ Plus a₁ a₃ ]
  
module _
  {A : Set c} {R : A → A → Pred C c}
  {e u} {_≈_ : C → C → Set e}
  {{monoid : IsPartialMonoid _≈_ rc u}}
  where

  [_] : ∀ {a₁ a₂ : A} → ∀[ R a₁ a₂ ⇒ Star R a₁ a₂ ]
  [ rx ] = rx ▹⟨ ∙-idʳ ⟩ nil

  instance star-respects : ∀ {a₁ a₂ : A} → Respect _≈_ (Star R a₁ a₂)
  Respect.coe star-respects eq nil with ε-unique eq
  ... | refl = nil
  Respect.coe star-respects eq (cons x) = cons (coe eq x)

  private
    append : ∀ {a₁ a₂ a₃} → ∀[ Star R a₁ a₂ ⇒ Star R a₂ a₃ ─✴ Star R a₁ a₃ ]
    append nil ⟨ σ ⟩ y = coe (∙-id⁻ˡ σ) y
    append (cons (r ∙⟨ σ₁ ⟩ rs)) ⟨ σ₂ ⟩ y = 
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in
      r ▹⟨ σ₃ ⟩ (append rs ⟨ σ₄ ⟩ y)

  instance starMonoid : IsIndexedMonoid (Star R)
  IsIndexedMonoid.mempty starMonoid  = nil
  IsIndexedMonoid.mappend starMonoid = append
