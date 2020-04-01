{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.List.Disjoint {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap; map)
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  Ctx = List T
  variable
    xsˡ xsʳ xs ysˡ ysʳ ys zs : Ctx

module Model {t} (T : Set t) where
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
    renaming (_∙_≣_ to _⊕_≣_; _✴_ to _⊕_; _─✴_ to _─⊕_) public

module _ where
  open Model T

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

  threeway : ∀ {a b c ab bc : List T} → a ∙ b ≣ ab → b ∙ c ≣ bc → ∃ λ abc → ab ∙ bc ≣ abc
  threeway [] σ₂ = -, ∙-idˡ
  threeway (consˡ σ₁) σ₂ with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consˡ σ₃
  threeway σ₁@(consʳ _) (consʳ σ₂) with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consʳ σ₃
  threeway (consʳ σ₁) (consˡ σ₂) with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consˡ (consʳ σ₃)

module _ {a} {A : Set a} (f : T → A) where

  module L = Model T
  module R = Model A

  map-inv : ∀ {xs ys : List A} {zs : List T} → xs R.⊕ ys ≣ map f zs →
            Σ[ frags ∈ List T × List T ]
              let xs' , ys' = frags in
                xs' L.⊕ ys' ≣ zs × xs ≡ map f xs' × ys ≡ map f ys'
  map-inv {[]} {[]} {[]} R.[] = -, L.[] , refl , refl
  map-inv {[]   } {_ ∷ _} {_ ∷ _} (R.consʳ σ) with _ , τ , eq , refl ← map-inv σ = -, L.consʳ τ , eq  , refl
  map-inv {_ ∷ _} {[]   } {_ ∷ _} (R.consˡ σ) with _ , τ , refl , eq ← map-inv σ = -, L.consˡ τ , refl , eq
  map-inv {_ ∷ _} {_ ∷ _} {_ ∷ _} (R.consˡ σ) with _ , τ , refl , eq ← map-inv σ  = -, L.consˡ τ , refl , eq
  map-inv {_ ∷ _} {_ ∷ _} {_ ∷ _} (R.consʳ σ) with _ , τ , eq , refl ← map-inv σ = -, L.consʳ τ , eq  , refl

open Model T public
