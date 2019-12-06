{-# OPTIONS --safe #-}
module Relation.Ternary.Structures.Functional
  {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Relation.Ternary.Core using (Rel₃; Functional)
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open IsEquivalence {{...}}

record IsFunctional {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    functional : Functional _≈_ rel

open IsFunctional {{...}} public
