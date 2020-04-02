module Relation.Ternary.Construct.Map.Properties where

open import Level
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (swap)
open import Data.Maybe

open import Relation.Nullary
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Morphisms

module CrossSplittable {k v} {K : Set k} {V : K → Set v}
  {{div₁ : ∀ {k} → Rel₃ (V k)}} {{div₂ : ∀ {k} → Rel₃ (V k)}}
  {e} {_≈₁_ : ∀ {k} → V k → V k → Set e} {_≈₂_ : ∀ {k} → V k → V k → Set e}
  {{_ : ∀ {k} → IsCommutative (div₁ {k})}} {{_ : ∀ {k} → IsPartialSemigroup _≈₁_ (div₁ {k})}}
  {{_ : ∀ {k} → IsCommutative (div₂ {k})}} {{_ : ∀ {k} → IsPartialSemigroup _≈₂_ (div₂ {k})}}
  where

  module _ {k} where
    open Rel₃ (div₁ {k}) using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
    open Rel₃ (div₂ {k}) using () renaming (_∙_≣_ to _∙ₐ₂_≣_)

    open import Relation.Ternary.Construct.Map K V as L
    open import Relation.Ternary.Construct.Map K V as R

    xsplit : (∀ {k} → CrossSplit (div₁ {k}) div₂) → CrossSplit (L.maps div₁) (R.maps div₂)
    xsplit xsplitₐ {a} {b} {c} {d} (union σs₁) (union σs₂) = 
      -, R.union (λ k → case a k of λ where
                 nothing → {!R.nothing!}
                 (just x) → {!!}
        ) -- (λ k → let _ , τ , _ = xsplitₐ (σs₁ k) (σs₂ k) in τ)
       , R.union {!!} -- (λ k → let _ , _ , τ , _ = xsplitₐ (σs₁ k) (σs₂ k) in τ)
       , R.union {!!} -- (λ k → let _ , _ , _ , τ , _ = xsplitₐ (σs₁ k) (σs₂ k) in τ)
       , R.union {!!} -- (λ k → let _ , _ , _ , _ , τ = xsplitₐ (σs₁ k) (σs₂ k) in τ)

    unxcross : (∀ {k} → Uncross (div₁ {k}) (div₂ {k})) → Uncross (L.maps div₁) (R.maps div₂)
    unxcross unxcrossₐ (union σs₁) (union σs₂) (union σs₃) (union σs₄) = {!!}
      -- -, R.union (λ k → let _ , u , _ = unxcrossₐ (σs₁ k) (σs₂ k) (σs₃ k) (σs₄ k) in u)
      --  , R.union (λ k → let _ , _ , u = unxcrossₐ (σs₁ k) (σs₂ k) (σs₃ k) (σs₄ k) in u)

