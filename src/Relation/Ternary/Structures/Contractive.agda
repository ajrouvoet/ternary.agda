{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Contractive {a} {A : Set a} where

open import Level
open import Data.Product
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid

record IsContractive {c} (Condition : Pred A c) (rel : Rel₃ A) : Set (a ⊔ suc c) where
  open Rel₃ rel
  field
    ∙-copy    : ∀ {xs : A} → Condition xs → xs ∙ xs ≣ xs

module _ {{rel : Rel₃ A}} where
  open Rel₃ rel
  open IsContractive {{...}}

  copy : ∀ {p} {P : Pred A p} {{_ : IsContractive P rel}} → ∀[ P ⇒ P ✴ P ]
  copy px = px ∙⟨ ∙-copy px ⟩ px

module _ {e} {u} {_≈_ : A → A → Set e} {rel : Rel₃ A} {{m : IsPartialMonoid _≈_ rel u}} where

  open Rel₃ rel
  open IsPartialMonoid m
  open Emptiness emptiness

  Emp-intuitionistic : IsContractive Emp rel
  IsContractive.∙-copy Emp-intuitionistic refl = ∙-idˡ
