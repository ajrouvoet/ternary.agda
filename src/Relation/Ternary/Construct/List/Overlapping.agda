{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.List.Overlapping {t} (T : Set t) where

open import Level
open import Function
open import Data.Unit using (⊤)
open import Data.Product hiding (map)
open import Data.List hiding (_∷ʳ_)
open import Data.Nat

open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  Ctx = List T
  variable
    xs xs′ ys ys′ zs xsˡ xsʳ : Ctx

{- Redeclare instances to severe the dependency on Duplicate instances -}
module Model {t} (T : Set t) where
  open import Relation.Ternary.Construct.Duplicate T as D
  open import Relation.Ternary.Construct.List duplicate as Overlapping
  open Overlapping using ([]; consˡ; consʳ; list-monoid; list-emptiness; from-⊆) public

  open Rel₃ splits using ()
    renaming (_∙_≣_ to _⊗_≣_; _✴_ to _⊗_; _◆_ to _◆ₓ_; _─✴_ to _─⊗_) public

  instance overlap-rel : Rel₃ (List T)
  overlap-rel = splits

  instance overlap-positive : IsPositive _ _≡_ overlap-rel []
  overlap-positive = list-positive

  instance overlap-semigroup : IsPartialSemigroup _≡_ overlap-rel
  overlap-semigroup = list-isSemigroup

  instance overlap-commutative : IsCommutative overlap-rel
  overlap-commutative = list-isComm

  instance overlap-monoid : IsPartialMonoid _≡_ overlap-rel []
  overlap-monoid = list-isMonoid {{D.dup-isSemigroup}}

  instance overlap-total : IsTotal _≡_ overlap-rel _++_
  overlap-total = list-isTotal {{D.dup-isSemigroup}}

  instance overlap-intuitive : IsIntuitionistic U overlap-rel
  overlap-intuitive = list-isIntuitionistic {{D.dup-isIntuitive}}

  pattern overlaps σ = divide dup σ

{- The relations betweens non-overlapping list sep and sublists -}
module _ where
  open Model T
  open import Data.List.Relation.Binary.Sublist.Propositional

  ⊆-⊗ : xs′ ⊆ xs → ys′ ⊆ ys → xs ⊗ ys ≣ zs → ∃ λ zs′ → xs′ ⊗ ys′ ≣ zs′ × zs′ ⊆ zs

  ⊆-⊗ (_  ∷ʳ i₁) (_  ∷ʳ i₂) (overlaps σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, σ'       , _ ∷ʳ i
  ⊆-⊗ (_  ∷ʳ i₁) (eq ∷  i₂) (overlaps σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, consʳ σ' , eq ∷ i
  ⊆-⊗ (eq ∷  i₁) (_  ∷ʳ i₂) (overlaps σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, consˡ σ' , eq ∷ i
  ⊆-⊗ (refl ∷  i₁) (refl ∷ i₂) (overlaps σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, overlaps σ' , refl ∷ i

  ⊆-⊗ (_  ∷ʳ i₁) i₂ (consˡ σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, σ'       , _ ∷ʳ i
  ⊆-⊗ (eq ∷  i₁) i₂ (consˡ σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, consˡ σ' , eq ∷ i
  ⊆-⊗ i₁ (_  ∷ʳ i₂) (consʳ σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, σ'       , _ ∷ʳ i
  ⊆-⊗ i₁ (eq ∷  i₂) (consʳ σ) with _ , σ' , i ← ⊆-⊗ i₁ i₂ σ = -, consʳ σ' , eq ∷ i

  ⊆-⊗ [] [] [] = -, [] , []

module _ where
  open Model T
  open import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any using (index; module Any); open Any
  open import Data.Fin

  member : ∀ {x} {xs ys : Ctx} → [ x ] ∙ xs ≣ ys → x ∈ ys
  member (overlaps σ)                = here refl
  member (consˡ σ)                   = here refl
  member (consʳ σ) with p ← member σ = there p

  indexOf : ∀ {x} {xs ys : Ctx} → [ x ] ∙ xs ≣ ys → ℕ
  indexOf = toℕ ∘ index ∘ member

  threeway : ∀ {a b c ab bc : List T} → a ⊗ b ≣ ab → b ⊗ c ≣ bc → ∃ λ abc → ab ⊗ bc ≣ abc
  threeway [] σ₂ = -, ∙-idˡ
  threeway (consˡ σ₁) σ₂ with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consˡ σ₃
  threeway σ₁@(consʳ _) (consʳ σ₂) with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consʳ σ₃
  threeway σ₁@(overlaps _) (consʳ σ₂) with threeway σ₁ σ₂
  ... | _ , σ₃ = -, consʳ σ₃
  threeway (overlaps σ₁) (overlaps σ₂) = -, overlaps (proj₂ (threeway σ₁ σ₂))
  threeway (overlaps σ₁) (consˡ σ₂)    = -, overlaps (proj₂ (threeway σ₁ σ₂))
  threeway (consʳ σ₁) (overlaps σ₂) = -, overlaps (proj₂ (threeway σ₁ σ₂))
  threeway (consʳ σ₁) (consˡ σ₂)    = -, overlaps (proj₂ (threeway σ₁ σ₂))

module _ {a} {A : Set a} (f : T → A) where

  module L = Model T
  module R = Model A

  map-inv : ∀ {xs ys : List A} {zs : List T} → xs R.⊗ ys ≣ map f zs →
            Σ[ frags ∈ List T × List T ]
              let xs' , ys' = frags in xs' L.⊗ ys' ≣ zs × xs ≡ map f xs' × ys ≡ map f ys'
  map-inv {[]} {[]} {[]} R.[] = -, L.[] , refl , refl
  map-inv {[]   } {_ ∷ _} {_ ∷ _} (R.consʳ σ) with _ , τ , eq , refl ← map-inv σ = -, L.consʳ τ , eq  , refl
  map-inv {_ ∷ _} {[]   } {_ ∷ _} (R.consˡ σ) with _ , τ , refl , eq ← map-inv σ = -, L.consˡ τ , refl , eq
  map-inv {_ ∷ _} {_ ∷ _} {_ ∷ _} (R.consˡ σ) with _ , τ , refl , eq ← map-inv σ  = -, L.consˡ τ , refl , eq
  map-inv {_ ∷ _} {_ ∷ _} {_ ∷ _} (R.consʳ σ) with _ , τ , eq , refl ← map-inv σ = -, L.consʳ τ , eq  , refl
  map-inv {_ ∷ _} {_ ∷ _} {_ ∷ _} (R.overlaps σ) with _ , τ , eq , refl ← map-inv σ = -, L.overlaps τ , cong (_ ∷_) eq , refl

open Model T public
