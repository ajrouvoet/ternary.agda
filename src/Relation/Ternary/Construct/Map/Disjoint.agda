module Relation.Ternary.Construct.Map.Disjoint {k v} (K : Set k) (V : K → Set v) where

open import Data.Maybe

module _ {k} where
  open import Relation.Ternary.Construct.Empty (Maybe (V k)) public

open import Relation.Ternary.Construct.Map K V empty-rel public
