{-# OPTIONS --safe #-}
module Relation.Ternary.Construct.List.Overlapping {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤)
open import Data.Product
open import Data.List

open import Relation.Unary hiding (_⊢_; _⊆_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  Ctx = List T
  variable
    xs xs′ ys ys′ zs xsˡ xsʳ : Ctx

{- Redeclare instances to severe the dependency on Duplicate instances -}
module _ where 
  open import Relation.Ternary.Construct.Duplicate T as D
  open import Relation.Ternary.Construct.List duplicate as Overlapping
  open Overlapping using ([]; consˡ; consʳ; list-monoid; list-emptiness) public

  open Rel₃ splits using ()
    renaming (_∙_≣_ to _⊗_≣_; _⊙_ to _⊗_; _◆_ to _◆ₓ_; _─⊙_ to _─⊗_) public

  instance overlap-rel : Rel₃ Ctx
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

  instance overlap-intuitive : IsIntuitionistic overlap-rel
  IsIntuitionistic.Condition overlap-intuitive _ = ⊤
  IsIntuitionistic.∙-copy overlap-intuitive {[]} = ∙-idˡ {{overlap-monoid}}
  IsIntuitionistic.∙-copy overlap-intuitive {x ∷ xs} = divide dup ∙-copy

  pattern overlaps σ = divide dup σ

{- The relations betweens non-overlapping and overlapping list sep -}
module _ where
  import Relation.Ternary.Construct.List.Disjoint T as D

  ⊆-⊗ : xs′ D.⊆ xs → ys′ D.⊆ ys → xs ⊗ ys ≣ zs → ∃ λ zs′ → xs′ ⊗ ys′ ≣ zs′ × zs′ D.⊆ zs

  ⊆-⊗ (_ , consˡ i₁) i₂ (consˡ σ) with ⊆-⊗ (-, i₁) i₂ σ
  ... | _ , σ′ , i′ = -, consˡ σ′ , D.⊆-∷ˡ i′
  ⊆-⊗ (_ , consʳ i₁) i₂ (consˡ σ) with ⊆-⊗ (-, i₁) i₂ σ
  ... | _ , σ′ , i′  = -, σ′ , D.⊆-∷ʳ i′

  ⊆-⊗ (_ , consˡ i₁) (_ , consˡ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, overlaps σ′ , D.⊆-∷ˡ i′
  ⊆-⊗ (_ , consˡ i₁) (_ , consʳ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, consˡ σ′ , D.⊆-∷ˡ i′

  ⊆-⊗ (_ , consʳ i₁) (_ , consˡ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, consʳ σ′ , D.⊆-∷ˡ i′
  ⊆-⊗ (_ , consʳ i₁) (_ , consʳ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, σ′ , D.⊆-∷ʳ i′

  ⊆-⊗ (.[] , []) (.[] , []) [] = -, ∙-idˡ , D.⊆-refl 

  ⊆-⊗ i₁ (_ , consˡ i₂) (consʳ σ) with ⊆-⊗ i₁ (-, i₂) σ
  ... | _ , σ′ , i′ = -, consʳ σ′ , D.⊆-∷ˡ i′
  ⊆-⊗ i₁ (_ , consʳ i₂) (consʳ σ) with ⊆-⊗ i₁ (-, i₂) σ
  ... | _ , σ′ , i′ = -, σ′ , D.⊆-∷ʳ i′

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
