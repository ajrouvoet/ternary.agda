module Relation.Ternary.Construct.Map.Overlapping {k v} (K : Set k) (V : K → Set v) where

open import Data.Maybe
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  module _ {k} where
    open import Relation.Ternary.Construct.Duplicate (V k) public

open import Relation.Ternary.Construct.Map K V

overmap-isSemigroup : IsPartialSemigroup _ (maps {{duplicate}})
overmap-isSemigroup = map-isSemigroup

overmap-isMonoid : IsPartialMonoid _ (maps {{duplicate}}) _
overmap-isMonoid = {!map-isMonoid!}
