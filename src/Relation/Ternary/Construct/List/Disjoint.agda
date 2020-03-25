{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.List.Disjoint {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  Ctx = List T
  variable
    xsˡ xsʳ xs ysˡ ysʳ ys : Ctx

open import Relation.Ternary.Construct.Empty T public
open import Relation.Ternary.Construct.List empty-rel as Disjoint
open Disjoint public using ([]; consˡ; consʳ; list-monoid) renaming
  (splits           to disjoint-split
  ;list-emptiness   to disjoint-empty
  ;list-positive    to disjoint-positive
  ;list-isComm      to disjoint-commutative
  ;list-isSemigroup to disjoint-semigroup
  ;list-isMonoid    to disjoint-monoid
  ;list-isTotal     to disjoint-total)

open Rel₃ Disjoint.splits using ()
  renaming (_∙_≣_ to _⊕_≣_; _⊙_ to _⊕_; _─⊙_ to _─⊕_) public

infixl 10 _⊆_
_⊆_ : Ctx → Ctx → Set t
_⊆_ = _≤_

⊆-refl : ∀ {xs : Ctx} → xs ≤ xs
⊆-refl  = ≤-refl

⊆-trans : ∀ {xs ys zs : Ctx} → xs ≤ ys → ys ≤ zs → xs ≤ zs
⊆-trans = ≤-trans

⊆-min : ∀ {xs : Ctx} → [] ≤ xs
⊆-min = -, ∙-idˡ

⊆-∷ˡ : ∀ {x xs} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
⊆-∷ˡ σ = -, consˡ (proj₂ σ)

⊆-∷ʳ : ∀ {x xs} → xs ⊆ ys → xs ⊆ (x ∷ ys)
⊆-∷ʳ σ = -, consʳ (proj₂ σ)

_∈_ : T → Ctx → Set t
x ∈ xs = [ x ] ⊆ xs

-- from the stdlib Interleaving properties
toPermutation : ∀ {l r as} → l ⊕ r ≣ as → as ↭ l ++ r
toPermutation [] = ↭-refl
toPermutation (consˡ σ) = prep _ (toPermutation σ)
toPermutation (consʳ {xs = xs} {ys} {zs} {z} σ) = begin
  z ∷ zs       ↭⟨ prep z (toPermutation σ) ⟩
  z ∷ xs ++ ys ↭⟨ ↭-sym (shift z xs ys) ⟩
  xs ++ z ∷ ys  ∎
  where 
    open PermutationReasoning

⊕-functional : ∀ {xs ys zs zs'}  → xs ⊕ ys ≣ zs → xs ⊕ ys ≣ zs' → zs ↭ zs'
⊕-functional σ₁ σ₂ = ↭-trans (toPermutation σ₁) (↭-sym (toPermutation σ₂))

{- We can pull a permutation through separation -}

threeway : ∀ {a b c ab bc : List T} → a ∙ b ≣ ab → b ∙ c ≣ bc → ∃ λ abc → ab ∙ bc ≣ abc
threeway Split.[] σ₂ = -, ∙-idˡ
threeway (consˡ σ₁) σ₂ with threeway σ₁ σ₂
... | _ , σ₃ = -, consˡ σ₃
threeway σ₁@(consʳ _) (consʳ σ₂) with threeway σ₁ σ₂
... | _ , σ₃ = -, consʳ σ₃
threeway (consʳ σ₁) (consˡ σ₂) with threeway σ₁ σ₂
... | _ , σ₃ = -, consˡ (consʳ σ₃)
