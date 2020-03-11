{-# OPTIONS --safe --without-K #-}
open import Data.Nat
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality

module Data.Nat.SizeOf {a} {A : Set a} (size : A → ℕ) where

open import Data.Nat.Properties

_≤ₐ_ = λ xs ys → size xs ≤ size ys

module _ {e}
  {_≈_ : A → A → Set e}
  (isEquivalence    : IsEquivalence _≈_)
  (≈-size : ∀ {x y} → x ≈ y → size x ≡ size y) where

  size-pre : IsPreorder _≈_ _≤ₐ_
  IsPreorder.isEquivalence size-pre = isEquivalence
  IsPreorder.reflexive size-pre eq = ≤-reflexive (≈-size eq)
  IsPreorder.trans size-pre = ≤-trans
