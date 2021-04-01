{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.PartialBand {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary.Structures

open import Function using (_∘_)
open import Data.Product
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Relation.Ternary.Core using (Rel₃; Idempotent)
open import Relation.Ternary.Structures.Idempotent
open import Relation.Ternary.Structures.PartialSemigroup
open IsEquivalence {{...}}

record IsBand {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (suc zero ⊔ a ⊔ e) where
  open Rel₃ rel

  field
    {{isSemigroup}}  : IsPartialSemigroup _≈_ rel
    {{isIdempotent}} : IsIdempotent U rel
