{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Functional {a} {A : Set a} where

open import Level
open import Relation.Ternary.Core using (Rel₃; Functional)

record IsFunctional {e} (_≈_ : A → A → Set e) (rel : Rel₃ A) : Set (a ⊔ e) where
  open Rel₃ rel

  field
    functional : Functional _≈_ rel
