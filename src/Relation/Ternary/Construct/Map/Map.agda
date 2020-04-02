open import Relation.Binary.Structures

module Relation.Ternary.Construct.Map.Map {k v} (K : Set k) (V : K → Set v)
  where

open import Level
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Binary.Pointwise hiding (refl)
open import Data.Empty
open import Relation.Nullary
open import Relation.Unary  as Unary using (U)
open import Relation.Binary.Definitions
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_)
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

Entry  = λ k → Maybe (V k)
Map = (k : K) → Entry k

_∉_ : K → Map → Set v
k ∉ m = m k ≡ nothing

∅ : Map
∅ = λ k → nothing

module _ where
  _≈_ : Map → Map → Set _
  m₁ ≈ m₂ = ∀ k → (m₁ k) ≡ (m₂ k)

  instance ≈-isEquivalence : IsEquivalence _≈_
  IsEquivalence.refl ≈-isEquivalence k = refl
  IsEquivalence.sym ≈-isEquivalence eq k = ≡.sym (eq k)
  IsEquivalence.trans ≈-isEquivalence eq₁ eq₂ k = ≡.trans (eq₁ k) (eq₂ k)
