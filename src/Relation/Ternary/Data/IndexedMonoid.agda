{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Data.IndexedMonoid {ℓ} {C : Set ℓ} {r : Rel₃ C}
  {e u} {_≈_ : C → C → Set e}
  {{m : IsPartialMonoid _≈_ r u}}
  where

open import Level
open import Relation.Unary

private instance _ = r
open import Relation.Ternary.Structures.Syntax

record IsIndexedMonoid {i w} {I : Set i} (W : I → I → Pred C w) : Set (i ⊔ w ⊔ suc ℓ) where
  field
    mempty  : ∀ {i} → W i i ε
    mappend : ∀ {i₁ i₂ i₃} → ∀[ W i₁ i₂ ⇒ W i₂ i₃ ─✴ W i₁ i₃ ]

open IsIndexedMonoid {{...}} public
