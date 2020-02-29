module Relation.Ternary.Construct.List.Overlapping {t} (T : Set t) where

open import Level
open import Data.Unit using (⊤)
open import Data.Product
open import Data.List

open import Relation.Unary hiding (_⊢_; _⊆_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

private
  Ctx = List T
  variable
    xs xs′ ys ys′ zs : Ctx

open import Relation.Ternary.Construct.Duplicate T public
open import Relation.Ternary.Construct.List.Interdivide duplicate as Overlapping
open Overlapping public renaming
  (splits to overlap-rel
  ;split-positive to overlap-positive
  ;split-isSemigroup to overlap-semigroup
  ;split-isComm to overlap-commutative
  ;split-isMonoid to overlap-monoid)

open Rel₃ overlap-rel using ()
  renaming (_∙_≣_ to _⊗_≣_; _⊙_ to _⊗_; _◆_ to _◆ₓ_; _─⊙_ to _─⊗_) public

instance overlap-intuitive : Intuitionistic overlap-rel
Intuitionistic.Condition overlap-intuitive _ = ⊤
Intuitionistic.∙-copy overlap-intuitive {[]} = ∙-idˡ
Intuitionistic.∙-copy overlap-intuitive {x ∷ xs} = Overlapping.divide dup ∙-copy

pattern overlaps σ = divide dup σ

{- The relations betweens non-overlapping and overlapping list sep -}
module _ where
  open import Relation.Ternary.Construct.List.Disjoint T as D

  ⊆-⊗ : xs′ ⊆ xs → ys′ ⊆ ys → xs ⊗ ys ≣ zs → ∃ λ zs′ → xs′ ⊗ ys′ ≣ zs′ × zs′ ⊆ zs

  ⊆-⊗ (_ , consˡ i₁) i₂ (consˡ σ) with ⊆-⊗ (-, i₁) i₂ σ
  ... | _ , σ′ , i′ = -, Overlapping.consˡ σ′ , ⊆-∷ˡ i′
  ⊆-⊗ (_ , consʳ i₁) i₂ (consˡ σ) with ⊆-⊗ (-, i₁) i₂ σ
  ... | _ , σ′ , i′  = -, σ′ , ⊆-∷ʳ i′

  ⊆-⊗ (_ , consˡ i₁) (_ , consˡ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, overlaps σ′ , ⊆-∷ˡ i′
  ⊆-⊗ (_ , consˡ i₁) (_ , consʳ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, Overlapping.consˡ σ′ , ⊆-∷ˡ i′

  ⊆-⊗ (_ , consʳ i₁) (_ , consˡ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, Overlapping.consʳ σ′ , ⊆-∷ˡ i′
  ⊆-⊗ (_ , consʳ i₁) (_ , consʳ i₂) (overlaps σ) with ⊆-⊗ (-, i₁) (-, i₂) σ
  ... | _ , σ′ , i′ = -, σ′ , ⊆-∷ʳ i′

  ⊆-⊗ (.[] , []) (.[] , []) [] = -, ∙-idˡ , ⊆-refl 

  ⊆-⊗ i₁ (_ , consˡ i₂) (consʳ σ) with ⊆-⊗ i₁ (-, i₂) σ
  ... | _ , σ′ , i′ = -, Overlapping.consʳ σ′ , ⊆-∷ˡ i′
  ⊆-⊗ i₁ (_ , consʳ i₂) (consʳ σ) with ⊆-⊗ i₁ (-, i₂) σ
  ... | _ , σ′ , i′ = -, σ′ , ⊆-∷ʳ i′

threeway : ∀ {a b c ab bc : List T} → a ∙ b ≣ ab → b ∙ c ≣ bc → ∃ λ abc → ab ∙ bc ≣ abc
threeway Split.[] σ₂ = -, ∙-idˡ
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
