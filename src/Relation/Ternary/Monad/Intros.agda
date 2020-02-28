module Relation.Ternary.Monad.Intros {t} (T : Set t) where

open import Function
open import Data.Product as P
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Properties as LP

open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad.Possibly

open import Relation.Ternary.Construct.List.Disjoint T as D hiding (_∈_)
open import Relation.Ternary.Construct.List.Overlapping T --using (_⊗_≣_; ⊆-⊗)

private
  Ctx = List T

module _ where

  _∼[_]_ : Ctx → Ctx → Ctx → Set t
  Γₙ ∼[ Δ ] Γₙ₊₁ = ∃ λ Δ′ → (Δ′ ⊆ Δ) × Γₙ ++ Δ′ ≡ Γₙ₊₁

  -- McBride's introduction turnstile
  open Possibly _∼[_]_
    public
    using (◇; module ◇-Zip; module ◇-Monad; _∼_; pack)
    renaming
      ( ◇[_] to _⊢_)

  ∼-refl : ∀ {a : Ctx} → a ∼[ ε ] a
  ∼-refl = -, (-, ∙-idˡ) , LP.++-identityʳ _

  ∼-all : ∀ {a : Ctx} → ε ∼[ a ] a
  ∼-all {a} = a , ≤-refl , refl

  ∼-none : ∀ {a : Ctx} → ε ∼[ a ] ε
  ∼-none = [] , (-, ∙-idˡ) , refl

  ∼-trans : ∀ {a b c} → a ∼ b → b ∼ c → a ∼ c
  ∼-trans (_ , Δ₁′ , Δ₁′⊆Δ₁ , refl) (_ , Δ₂′ , Δ₂′⊆Δ₂ , refl) =
    -, (-, (-, ∙-idʳ) , sym (LP.++-assoc _ Δ₁′ Δ₂′))

  ∼-isPreorder : IsPreorder _≡_ _∼_
  IsPreorder.isEquivalence ∼-isPreorder = isEquivalence
  IsPreorder.reflexive ∼-isPreorder refl = -, ∼-refl
  IsPreorder.trans ∼-isPreorder = ∼-trans
  
  -- frame preserving
  ∼-fp : ∀ {fr Φ₁ Φ₂} → Φ₁ ∼ Φ₂ → (di₁ : fr ◆ₓ Φ₁) → ∃ λ (di₂ : fr ◆ₓ Φ₂) → whole di₁ ∼ whole di₂
  ∼-fp (Δ′ , i , τ , refl) (fst , σ₁) = (-, ∙-∙ᵣᵣ σ₁) , _ , (i , τ , refl)

  open ◇-Monad ∼-isPreorder ∼-fp public
    renaming (◇-⤇ to ⊢-⤇)

  ∼-pull : ∀ {Δ₁ Δ₂ Δ a b c a' b'} →
      Δ₁ ⊗ Δ₂ ≣ Δ  → a ⊗ b ≣ c    →
      a ∼[ Δ₁ ] a' → b ∼[ Δ₂ ] b' →
      ∃ λ c' → a' ⊗ b' ≣ c' × c ∼[ Δ ] c'
  ∼-pull δ σ (_ , i₁ , refl) (_ , i₂ , refl) with ⊆-⊗ i₁ i₂ δ
  ... | Δ′ , δ′ , i₃ = -, ∙-parallel σ δ′ , -, i₃ , refl

  open ◇-Zip ∼-pull public renaming
    (◇-zip to ⊢-zip)

  binders : ∀ {Γ} → ε[ Γ ⊢ Exactly Γ ]
  binders = Possibly.possibly (_ , ≤-refl , refl) refl
