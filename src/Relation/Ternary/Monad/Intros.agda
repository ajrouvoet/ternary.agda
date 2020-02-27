module Relation.Ternary.Monad.Intros {t} (T : Set t) where

open import Function
open import Data.Product as P
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Properties as LP

open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad.Possibly

open import Relation.Ternary.Construct.List.Disjoint T  as D hiding (_∈_)
open import Relation.Ternary.Construct.List.Overlapping T --using (_⊗_≣_; ⊆-⊗)

private
  Ctx = List T

module _ where

  _∼[_]_ : Ctx → Ctx → Ctx → Set t
  Γₙ ∼[ Δ ] Γₙ₊₁ = ∃ λ Δ′ → -- Σ[ ctxs ∈ (Ctx × Ctx) ]
    (Δ′ ⊆ Δ) × Γₙ ++ Δ′ ≡ Γₙ₊₁

  -- McBride's introduction turnstile
  open Possibly _∼[_]_ renaming (◇[_] to _⊢_) public

  ∼-refl  : ∀ {a : Ctx} → a ∼[ ε ] a
  ∼-refl = -, (-, ∙-idˡ) , LP.++-identityʳ _

  -- ∼-trans : ∀ {Δ₁ Δ₂ Δ : Ctx} {a b c} → a ∼[ Δ₁ ] b → b ∼[ Δ₂ ] c → ∃ λ Δ → a ∼[ Δ ] c
  -- ∼-trans (Δ₁′ , Δ₁′⊆Δ₁ , τ₂) (Δ₂′ , Δ₂′⊆Δ₂ , τ₃) with ∙-assocᵣ τ₂ τ₃
  -- ... | _ , τ₄ , τ₅ = -, (-, (-, ∙-idʳ) , τ₄)

  -- -- frame preserving
  -- ∼-fp : ∀ {Δ fr Φ₁ Φ₂} → Φ₁ ∼[ Δ ] Φ₂ → (di₁ : fr ◆ₓ Φ₁) → ∃ λ (di₂ : fr ◆ₓ Φ₂) → whole di₁ ∼[ Δ ] whole di₂
  -- ∼-fp (Δ′ , i , τ) (fst , σ₁) = ({!!} , {!!}) , _ , (i , {!!})

  -- open ◇-Monad {{r = overlap-rel}} ∼-refl ∼-trans ∼-fp public

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
