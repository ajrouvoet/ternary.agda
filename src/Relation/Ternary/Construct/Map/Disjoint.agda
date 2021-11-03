open import Relation.Ternary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_)

module Relation.Ternary.Construct.Map.Disjoint {k v}
  (K : Set k)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  where

open import Data.Maybe
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  module _ {k : K} where
    open import Relation.Ternary.Construct.Empty (V k) public

open import Relation.Ternary.Construct.Map.Map K V _≡ₖ?_ public
module M where
  open import Relation.Ternary.Construct.Map K V _≡ₖ?_ empty-rel public
  
open M public
  using (maps; _↦_; map-emptiness; _[_]; _at_; union)
module _ {k} where
  open import Relation.Ternary.Construct.Add.Unit (empty-rel {k = k}) public

instance disjoint-isSemigroup : IsPartialSemigroup _ maps
disjoint-isSemigroup = M.map-isSemigroup

instance disjoint-isMonoid : IsPartialMonoid _ maps ∅
disjoint-isMonoid = M.map-isMonoid

instance disjoint-isCommutative : IsCommutative maps
disjoint-isCommutative = M.map-isCommutative

module _ where
  open import Relation.Ternary.Construct.Map.Properties K V _≡ₖ?_
  module CrossSplit = CrossSplittable {{empty-rel}} {{empty-rel}}
  
  xsplit : CrossSplit maps maps
  xsplit = CrossSplit.xsplit λ ()

