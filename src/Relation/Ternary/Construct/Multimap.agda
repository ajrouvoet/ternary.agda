{-# OPTIONS --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_; subst)

module Relation.Ternary.Construct.Multimap {ℓk v}
  (K : Set ℓk)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  where

open import Data.Unit using (⊤; tt)
open import Data.Maybe as Maybe
open import Data.Product
open import Data.List as L hiding ([_])

open import Relation.Ternary.Structures.Syntax

module _ {k} where
  open import Relation.Ternary.Construct.List.Disjoint (V k) public
  
Bucket = λ k → List (V k)

open import Relation.Ternary.Construct.Map.Map K Bucket _≡ₖ?_ as Map public
  hiding (_[_≔_]; insert; inserts)
  renaming (Map to Multimap)

open import Relation.Ternary.Construct.Map     K Bucket _≡ₖ?_ disjoint-split
  as M using ()
  renaming (maps to multimaps)

open M public using (maps; _↦_; map-emptiness; _[_])
open M.Membership {{disjoint-semigroup}} public

instance multimaps-isSemigroup : IsPartialSemigroup _ multimaps
multimaps-isSemigroup = M.map-isSemigroup

instance multimaps-isMonoid : IsPartialMonoid _ multimaps ∅
multimaps-isMonoid = M.map-isMonoid

instance multimaps-isCommutative : IsCommutative multimaps
multimaps-isCommutative = M.map-isCommutative

variable
  k : K

insert : ∀ k → V k → Multimap → Multimap
insert k v m = m [ k %= (λ where 
  (just vs) → just (v ∷ vs)
  nothing   → just L.[ v ] )]

inserts : List (Σ K V) → Multimap → Multimap
inserts bs m = foldl (λ where acc (k , v) → insert k v acc) m bs

fromList : List (Σ K V) → Multimap
fromList bs = inserts bs ∅

module _ where
  open import Relation.Ternary.Construct.Map.Map K V _≡ₖ?_

  fromMap : Map → Multimap
  fromMap m [ k ] = Maybe.map L.[_] (m [ k ])
