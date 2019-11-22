{-# OPTIONS --safe #-}
module Relation.Ternary.Structures 
  {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Relation.Ternary.Structures.PartialSemigroup _≈_ public
open import Relation.Ternary.Structures.PartialCommutativeSemigroup _≈_ public
open import Relation.Ternary.Structures.PartialMonoid _≈_ public
open import Relation.Ternary.Structures.Total _≈_ public
