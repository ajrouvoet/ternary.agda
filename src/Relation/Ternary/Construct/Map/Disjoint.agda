{-# OPTIONS --without-K #-}
module Relation.Ternary.Construct.Map.Disjoint {k v} (K : Set k) (V : K → Set v) where

open import Data.Maybe
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  module _ {k} where
    open import Relation.Ternary.Construct.Empty (V k) public
    open import Relation.Ternary.Construct.Add.Unit empty-rel public

open import Relation.Ternary.Construct.Map K V

disjoint-isSemigroup : IsPartialSemigroup _ (maps {{maybes}})
disjoint-isSemigroup = map-isSemigroup

disjoint-isMonoid : IsPartialMonoid _ (maps {{maybes}}) _
disjoint-isMonoid = map-isMonoid
