{-# OPTIONS --safe #-}
module Relation.Ternary.Structures where

open import Relation.Binary.Structures
open IsEquivalence {{...}}
  using ()
  renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

open import Relation.Ternary.Structures.PartialSemigroup public
open import Relation.Ternary.Structures.PartialMonoid public
open import Relation.Ternary.Structures.PartialJoinoid public
open import Relation.Ternary.Structures.PartialBand public
open import Relation.Ternary.Structures.Commutative public
open import Relation.Ternary.Structures.Total public
open import Relation.Ternary.Structures.Positive public
open import Relation.Ternary.Structures.Functional public
open import Relation.Ternary.Structures.Crosssplit public
