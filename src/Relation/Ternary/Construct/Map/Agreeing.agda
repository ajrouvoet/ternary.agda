{-# OPTIONS --no-qualified-instances #-}
open import Relation.Ternary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_; trans; sym)

module Relation.Ternary.Construct.Map.Agreeing {k v}
  (K : Set k)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  where

open import Data.Maybe
open import Relation.Unary using (U)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  module _ {k : K} where
    open import Relation.Ternary.Construct.Agree (V k) public
    open import Relation.Ternary.Construct.Add.Unit agrees public

open import Relation.Ternary.Construct.Map.Map K V _≡ₖ?_ public
module M where
  open import Relation.Ternary.Construct.Map K V _≡ₖ?_ agrees public
  
open M public using (maps; _↦_; map-emptiness; _[_])
open M.Membership {{agreed-isSemigroup}} public

private variable
  m₁ m₂ m : Map

instance agreeing-isSemigroup : IsPartialSemigroup _ maps
agreeing-isSemigroup = M.map-isSemigroup

instance agreeing-isMonoid : IsPartialMonoid _ maps ∅
agreeing-isMonoid = M.map-isMonoid

instance agreeing-isCommutative : IsCommutative maps
agreeing-isCommutative = M.map-isCommutative

instance split-idempotent : ∀ {k} → IsIdempotent U (maybes {k})
IsIdempotent.∙-idem split-idempotent {just x} _  = split agreed
IsIdempotent.∙-idem split-idempotent {nothing} _ = nothing

instance agreeing-idempotent : IsIdempotent U maps
(IsIdempotent.∙-idem agreeing-idempotent _) [ k ] = ∙-idem _
