module Relation.Ternary.Monad.Intros {t} (T : Set t) where

open import Function
open import Data.Product as P
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.List.Properties

open import Relation.Unary hiding (_⊢_; _⊆_; _∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad.Possibly

open import Relation.Ternary.Construct.List.Disjoint T hiding (_∈_)

private
  Ctx = List T

module _ {{r : Rel₃ Ctx}} where

  _∼[_]_ : Ctx → Ctx → Ctx → Set t
  Γₙ ∼[ Δ ] Γₙ₊₁ = Σ[ ctxs ∈ (Ctx × Ctx) ]
    let (Δ′ , Δ′′ ) = ctxs in (Δ′ ⊆ Δ) × (Δ′ ↭ Δ′′) × Γₙ ⊕ Δ′′ ≣ Γₙ₊₁

  -- McBride's introduction turnstile
  open Possibly _∼[_]_ renaming (◇[_] to _⊢_)

  ∼-refl  : ∀ {a : Ctx} → a ∼[ ε ] a
  ∼-refl = -, (-, ∙-idˡ) , ↭-refl , ∙-idʳ

  ∼-trans : ∀ {Δ₁ Δ₂ Δ : Ctx} {a b c} → (σ : Δ₁ ⊕ Δ₂ ≣ Δ) → a ∼[ Δ₁ ] b → b ∼[ Δ₂ ] c → a ∼[ Δ ] c
  ∼-trans σ (Δ₁′ , (_ , Δ₁′⊆Δ₁) , p₁ , z) (Δ₂′ , (_ , Δ₂′⊆Δ₂) , p₂ , z') with resplit Δ₁′⊆Δ₁ Δ₂′⊆Δ₂ σ
  ... | _ , _ , σ₂ , σ₃ , σ₄ with ∙-assocᵣ z z'
  ... | _ , σ₅ , σ₆ =
    let
      prf₁ = toPermutation σ₂
      prf₂ = toPermutation σ₆
      prf₃  = ++⁺ p₁ p₂
    in -, (-, σ₄) , ↭-trans (↭-trans prf₁ prf₃) (↭-sym prf₂) , σ₅

  -- frame preserving
  ∼-fp : ∀ {Δ fr Φ₁ Φ₂} → Φ₁ ∼[ Δ ] Φ₂ → (di₁ : fr ◆ Φ₁) → ∃ λ (di₂ : fr ◆ Φ₂) → whole di₁ ∼[ Δ ] whole di₂
  ∼-fp = {!!}
  

-- module _ {{r : Rel₃ Ctx}} {P : Pred Ctx t}
--   {e} {_≈_ : Ctx → Ctx → Set e}
--   {{_ : IsPartialMonoid _≈_ r []}} where

--   pure : ∀[ P ⇒ ε ⊢ P ]
--   pure px = intros ⊆-refl ↭-refl px

--   graded-zip : ∀ {Δ₁ Δ₂ Δ} {Q} → Δ₁ ∙ Δ₂ ≣ Δ → ∀[ (Δ₁ ⊢ P) ⊙ (Δ₂ ⊢ Q) ⇒ Δ ⊢ (P ⊙ Q) ]
--   graded-zip {Δ₁} {Δ₂} {Δ} σ₁ {Γ} (intros {Δₗ} {Γₗ} th mk px ∙⟨ σ₂ ⟩ intros {Δᵣ} {Γᵣ} th₁ mk₁ qx) = intros  {!!} {!!} (px Rel₃.∙⟨ {!!} ⟩ qx)

--   -- There is *NO* graded join:
--   -- goin : ∀ {Δ₁ Δ₂ Δ} → Δ₂ ∙ Δ₁ ≣ Δ → ∀[ Δ₁ ⊢ (Δ₂ ⊢ P) ⇒ Δ ⊢ P ]
--   --
--   -- Because you aren't allowed to identify consecutive introductions,
--   -- whereas you are (potentially) allowed to do that in (Δ₂ ∙ Δ₁ ≣ Δ)
