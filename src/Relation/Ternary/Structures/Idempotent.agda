{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Idempotent {a} {A : Set a} where

open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

record IsIdempotent {c} (Condition : Pred A c) (rel : Rel₃ A) : Set (a ⊔ suc c) where
  open Rel₃ rel
  field
    ∙-idem    : ∀ {xs : A} → Condition xs → xs ∙ xs ≣ xs

module _ {{rel : Rel₃ A}} where
  open Rel₃ rel
  open IsIdempotent {{...}}

  idem : ∀ {p} {P : Pred A p} {{_ : IsIdempotent P rel}} → ∀[ P ⇒ P ✴ P ]
  idem px = px ∙⟨ ∙-idem px ⟩ px

module _ {e} {u} {_≈_ : A → A → Set e} {rel : Rel₃ A} {{m : IsPartialMonoid _≈_ rel u}} where

  open Rel₃ rel
  open IsPartialMonoid m
  open Emptiness emptiness

  Emp-idempotent : IsIdempotent Emp rel
  IsIdempotent.∙-idem Emp-idempotent refl = ∙-idˡ
