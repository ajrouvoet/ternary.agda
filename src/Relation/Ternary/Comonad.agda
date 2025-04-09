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
open import Effect.Monad.Predicate

RawComonad : ∀ (ℓ : Level) → Set _
RawComonad ℓ = Pt A ℓ

RawIComonad : ∀ {i} (I : Set i) → (ℓ : Level) → Set _
RawIComonad I ℓ = I → I → Pt A ℓ

-- regular indexed monad on indexed sets
record Comonad (M : RawComonad a) : Set (suc a) where
  field
    {{functor}} : Functor M
    extract     : ∀ {P}   → ∀[ M P ⇒ P ]
    extend      : ∀ {P Q} → ∀[ M P ⇒ Q ] → ∀[ M P ⇒ M Q ]

  infixl 1 _<<=_
  _<<=_ = extend

  infixl 1 _=>>_
  _=>>_ : ∀ {Φ} {P Q} → M P Φ → ∀[ M P ⇒ Q ] → M Q Φ
  mp =>> f = f <<= mp

  -- you can a join
  co-join : ∀ {P} → ∀[ M (M P) ⇒ M P ]
  co-join = extract ⟨$⟩_

  -- ...and a bind
  co-bind : ∀ {P Q} → ∀[ P ⇒ M Q ] → ∀[ M P ⇒ M Q ]
  co-bind f = co-join ∘ fmap f

open Comonad {{...}} public

record StrongComonad (M : RawComonad a) : Set (suc a) where
  field
    {{comonad}} : Comonad M
    co-str : Strength M

  mzip : ∀ {P Q} → ∀[ M P ⇒ M Q ─✴ M (P ✴ Q) ]
  mzip {P} {Q} mpx ⟨ σ ⟩ mqx =
    (λ (mpx ∙⟨ τ ⟩ qx) → extract mpx ∙⟨ τ ⟩ qx) ⟨$⟩ (co-str {Q = M P} mpx ⟨ σ ⟩ mqx)

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
      g-extract   : ∀ {P} → ∀[ M[ ε ] P ⇒ P ]
      g-duplicate : ∀ {P} → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ M[ Δ ] P ⇒ M[ Δ₁ ] (M[ Δ₂ ] P) ]
      g-str       : ∀ {Δ} → Strength M[ Δ ]

    g-extend   : ∀ {P Q} → Δ₁ ∙ Δ₂ ≣ Δ
               → ∀[ M[ Δ₂ ] P ⇒ Q         ]
               → ∀[ M[ Δ  ] P ⇒ M[ Δ₁ ] Q ]
    g-extend δ f □px = f ⟨$⟩ (g-duplicate δ □px)

    g-extend-syntax : ∀ {P Q} → M[ Δ ] P Φ → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ M[ Δ₂ ] P ⇒ Q ] → M[ Δ₁ ] Q Φ
    g-extend-syntax px σ f = g-extend σ f px
    syntax g-extend-syntax px σ f = px =>>⟨ σ ⟩ f

  open GradedComonad {{...}} public
