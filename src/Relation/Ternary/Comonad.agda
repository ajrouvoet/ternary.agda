{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Comonad {a}
  {A : Set a} {{ra : Rel₃ A}}
  where

open import Level
open import Data.Product
open import Function using (_∘_; id)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Functor public
open import Category.Monad.Predicate

RawComonad : ∀ (ℓ : Level) → Set _
RawComonad ℓ = Pt A ℓ

RawIComonad : ∀ {i} (I : Set i) → (ℓ : Level) → Set _
RawIComonad I ℓ = I → I → Pt A ℓ

-- regular indexed monad on indexed sets
record Comonad (M : RawComonad a) : Set (suc a) where
  field
    {{functor}} : Functor M
    co-return : ∀ {P}   → ∀[ M P ⇒ P ]
    _<<=_     : ∀ {P Q} → ∀[ M P ⇒ Q ] → ∀[ M P ⇒ M Q ]

  infixl 1 _<<=_
  _=>>_ : ∀ {Φ} {P Q} → M P Φ → ∀[ M P ⇒ Q ] → M Q Φ
  mp =>> f = f <<= mp

open Comonad {{...}} public

record StrongComonad (M : RawComonad a) : Set (suc a) where
  field
    {{comonad}} : Comonad M
    co-str : Strength M

  co-mzip : ∀ {P Q} → ∀[ M P ⇒ M Q ─✴ M (P ✴ Q) ]
  co-mzip {P} {Q} mpx ⟨ σ ⟩ mqx =
    (λ (mpx ∙⟨ τ ⟩ qx) → co-return mpx ∙⟨ τ ⟩ qx) ⟨$⟩ (co-str {Q = M P} mpx ⟨ σ ⟩ mqx)

open StrongComonad {{...}} public

module _ {g} {G : Set g} {{gr : Rel₃ G}}
  {e} {_≈_ : G → G → Set e} {ug} {{gm : IsPartialMonoid _≈_ gr ug}}
  where

  private
    variable
      Δ₁ Δ₂ Δ₃ Δ : G

  record GradedComonad (M[_] : G → RawComonad a) : Set (suc (a ⊔ g)) where
    field
      {{functor}} : Functor M[ Δ ]
      co-unit     : ∀ {P} → ∀[ M[ ε ] P ⇒ P ]
      co-multiply : ∀ {P} → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ M[ Δ ] P ⇒ M[ Δ₁ ] (M[ Δ₂ ] P) ]
      gstr        : ∀ {Δ} → Strength M[ Δ ]

    co-gbind   : ∀ {P Q} → Δ₁ ∙ Δ₂ ≣ Δ
               → ∀[ M[ Δ₂ ] P ⇒ Q         ]
               → ∀[ M[ Δ  ] P ⇒ M[ Δ₁ ] Q ]
    co-gbind δ f □px = f ⟨$⟩ (co-multiply δ □px)

    co-bind-syntax : ∀ {P Q} → M[ Δ ] P Φ → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ M[ Δ₂ ] P ⇒ Q ] → M[ Δ₁ ] Q Φ
    co-bind-syntax px σ f = co-gbind σ f px
    syntax co-bind-syntax px σ f = px =>>⟨ σ ⟩ f

  open GradedComonad {{...}} public
