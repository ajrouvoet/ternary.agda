{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Functor where

open import Level
open import Function using (_∘_; id)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT; Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax

module _ {a} {A B : Set a} where

  RawFunctor : (ℓ : Level) → Set _
  RawFunctor ℓ = PT A B ℓ ℓ

  record Functor (F : RawFunctor a) : Set (suc a) where
    field
      fmap : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ F P ⇒ F Q ]

    _⟨$⟩_ : ∀ {P Q} → ∀[ P ⇒ Q ] → ∀[ F P ⇒ F Q ]
    f ⟨$⟩ mp = fmap f mp

  open Functor {{...}} public
  
module _ {a} {A : Set a} {{ra : Rel₃ A}} where

  record Applicative (F : RawFunctor {A = A} {A} a) : Set (suc a) where
    field
      pure  : ∀ {P}   → ∀[ P ⇒ F P ]
      _⟨*⟩_ : ∀ {P Q} → ∀[ F (P ─✴ Q) ⇒ F P ─✴ F Q ]

-- when A and B coincide we can write the usual type for monadic strength,
-- but over the ✴
module _ {a} {A : Set a} {{ra : Rel₃ A}} where

  Strength : (F : RawFunctor a) → Set _
  Strength F = {P Q : Pred A a} → ∀[ Q ⇒ F P ─✴ F (Q ✴ P) ]
