{-# OPTIONS --safe #-}
module Relation.Ternary.Structures {a e} {A : Set a} (_≈_ : A → A → Set e) where

open import Relation.Binary.Structures _≈_
open IsEquivalence {{...}}
  using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

module _ where
  open import Relation.Ternary.Structures.PartialSemigroup _≈_ public
  open import Relation.Ternary.Structures.PartialMonoid _≈_ public
  open import Relation.Ternary.Structures.Commutative _≈_ public
  open import Relation.Ternary.Structures.Total _≈_ public
