{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Functor {a} {A : Set a} where

open import Level
open import Function using (_∘_; id)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax

RawFunctor : (ℓ : Level) → Set _
RawFunctor ℓ = Pt A ℓ

record Functor (F : RawFunctor a) : Set (suc a) where
  field
    fmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ F P ⇒ F Q ]

  _⟨$⟩_ : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ F P ⇒ F Q ]
  f ⟨$⟩ mp = fmap f mp

open Functor {{...}} public

module _ {{ra : Rel₃ A}} where

  Strength : (F : RawFunctor a) → Set _
  Strength F = {P Q : Pred A a} → ∀[ Q ⇒ F P ─✴ F (Q ✴ P) ]
