{-# OPTIONS --safe --without-K #-}
module Data.List.Extra where

open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary

module _ {a} {A : Set a} where

  open import Data.List.Relation.Binary.Permutation.Propositional

  ↭-[] : ∀ {xs : List A} → xs ↭ [] → xs ≡ []
  ↭-[] refl = refl
  ↭-[] (trans p q) with ↭-[] q
  ... | refl with ↭-[] p
  ... | refl = refl

  ¬∷↭[] : ∀ {x xs} → ¬ ((x ∷ xs) ↭ [])
  ¬∷↭[] (trans s₁ s₂) with ↭-[] s₂
  ... | refl = ¬∷↭[] s₁

  ↭-length : ∀ {xs ys : List A} → xs ↭ ys → length xs ≡ length ys 
  ↭-length refl = refl
  ↭-length (prep x lr) = cong suc (↭-length lr)
  ↭-length (swap x y lr) = cong (λ n → suc (suc n)) (↭-length lr)
  ↭-length (trans lr₁ lr₂) = PropEq.trans (↭-length lr₁) (↭-length lr₂)

