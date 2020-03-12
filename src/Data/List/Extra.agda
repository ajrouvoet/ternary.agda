{-# OPTIONS --safe --without-K #-}
module Data.List.Extra where

open import Data.Nat
open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary

module _ {a} {A : Set a} where

  open import Data.List.Relation.Binary.Permutation.Propositional

  private
    variable
      xs ys zs : List A

  ↭-[] : xs ↭ [] → xs ≡ []
  ↭-[] refl = refl
  ↭-[] (trans p q) with ↭-[] q
  ... | refl with ↭-[] p
  ... | refl = refl

  ¬∷↭[] : ∀ {x} → ¬ ((x ∷ xs) ↭ [])
  ¬∷↭[] (trans s₁ s₂) with ↭-[] s₂
  ... | refl = ¬∷↭[] s₁

  ↭-length : xs ↭ ys → length xs ≡ length ys 
  ↭-length refl = refl
  ↭-length (prep x lr) = cong suc (↭-length lr)
  ↭-length (swap x y lr) = cong (λ n → suc (suc n)) (↭-length lr)
  ↭-length (trans lr₁ lr₂) = PropEq.trans (↭-length lr₁) (↭-length lr₂)

  smart-trans : xs ↭ ys → ys ↭ zs → xs ↭ zs
  smart-trans refl ρ₂ = ρ₂
  smart-trans ρ₁ refl = ρ₁
  smart-trans ρ₁ ρ₂ = ↭-trans ρ₁ ρ₂

  normalize : xs ↭ ys → xs ↭ ys
  normalize refl         = refl
  normalize (prep x ρ)   = prep x (normalize ρ) 
  normalize (swap x y ρ) = swap x y (normalize ρ)
  normalize (trans ρ ρ₁) = smart-trans ρ ρ₁

  ↭-smart-equivalence : IsEquivalence _↭_
  ↭-smart-equivalence = record { refl = ↭-refl ; sym = ↭-sym ; trans = smart-trans }
