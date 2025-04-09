{-# OPTIONS --without-K #-}
open import Relation.Binary.Structures

open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_)

module Relation.Ternary.Construct.Map.Map {k v}
  (K : Set k)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  where

open import Function using (const; flip)
open import Level
open import Data.Unit
open import Data.Product
open import Data.Maybe
open import Data.Bool using (if_then_else_)
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Binary.Pointwise hiding (refl)
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary  as Unary using (U)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

Entry = λ k → Maybe (V k)

record Map : Set (k ⊔ v) where
  infixl 100 _[_]
  field
    _[_] : (k : K) → Entry k

open Map public
    
lookup = Function.flip _[_]

_∉_ : K → Map → Set v
k ∉ m = m [ k ] ≡ nothing

∅ : Map
∅ [ k ] = nothing

_[_%=_] : Map → (k : K) → (Maybe (V k) → Maybe (V k)) → Map
(m [ k %= f ]) [ k' ] with k' ≡ₖ? k
... | yes refl = f (m [ k ])
... | no neq   = m [ k' ]

_[_≔_] : Map → (k : K) → V k → Map
(m [ k ≔ v ]) = m [ k %= const (just v) ]

insert = λ k v m → m [ k ≔ v ]

module _ where
  open import Data.List

  inserts : List (Σ K V) → Map → Map
  inserts []             m = m
  inserts ((k , v) ∷ bs) m = inserts bs (m [ k ≔ v ])

infix 1000 [_↦_]
[_↦_] : (k : K) → V k → Map
[ k ↦ v ] = ∅ [ k ≔ v ]

remove : (k : K) → Map → Map
remove k m = m [ k %= const nothing ]

module _ where
  _≗_ : Map → Map → Set _
  m₁ ≗ m₂ = ∀ k → (m₁ [ k ]) ≡ (m₂ [ k ])

  instance ≗-isEquivalence : IsEquivalence _≗_
  IsEquivalence.refl ≗-isEquivalence k = refl
  IsEquivalence.sym ≗-isEquivalence eq k = ≡.sym (eq k)
  IsEquivalence.trans ≗-isEquivalence eq₁ eq₂ k = ≡.trans (eq₁ k) (eq₂ k)
