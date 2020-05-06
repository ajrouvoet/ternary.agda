{-# OPTIONS --safe --without-K #-}

{- A graded possibility modality -}
module Relation.Ternary.Monad.Possibly {ℓa} {A : Set ℓa} where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)
open import Relation.Binary using (Rel)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Functor
open import Relation.Ternary.Monad.Update
open import Algebra.Structures

open import Data.Unit
open import Data.Product

private
  variable
    p   : Level
    P Q : Pred A p

GradedRel : ∀ {a g} → Set a → Set g → ∀ ℓ → Set (a ⊔ g ⊔ suc ℓ)
GradedRel A G ℓ = A → G → A → Set ℓ

module Possibly {r g} {G : Set g} (_∼[_]_  : GradedRel A G r) where

  private
    variable
      Δ₁ Δ₂ Δ : G

  record ◇[_] {ℓ} (gr : G) (P : Pred A ℓ) (Φ : A) : Set (r ⊔ ℓa ⊔ ℓ) where
    constructor possibly
    field
      {Φ′} : A
      rel  : Φ ∼[ gr ] Φ′
      px   : P Φ′

  ◇ : ∀ {ℓ} → PT A A ℓ _
  ◇ P = ⋃[ Δ ∶ _ ] ◇[ Δ ] P

  _∼_ : A → A → Set _
  a ∼ b = ∃ λ Δ → a ∼[ Δ ] b

  pack : ∀[ ◇[ Δ ] P ⇒ ◇ P ]
  pack px = -, px

  module IsMonotone {{r  : Rel₃ A}}
    (mono : ∀ {cₙ cₙ₊₁ a b} → cₙ ∼ cₙ₊₁ → a ∙ b ≣ cₙ₊₁ → cₙ ∼ a)
    where

    π₁ : ∀[ ◇ (P ✴ Q) ⇒ ◇ P ]
    π₁ (_ , possibly r (px ∙⟨ σ ⟩ qx)) with _ , r' ← mono (-, r) σ          = -, (possibly r' px)

    π₂ : {{_ : IsCommutative r}} → ∀[ ◇ (P ✴ Q) ⇒ ◇ Q ]
    π₂ (_ , possibly r (px ∙⟨ σ ⟩ qx)) with _ , r' ← mono (-, r) (∙-comm σ) = -, (possibly r' qx)

  module _ {{r  : Rel₃ A}} {e}  {_≈_ : A → A → Set e}
    {{∼-respects-≈ˡ : ∀ {g a} → Respect _≈_ (_∼[ g ] a)}} where

    instance ◇[]-respect-≈ : ∀ {p} {P : Pred A p} {g} → Respect _≈_ (◇[ g ] P)
    Respect.coe ◇[]-respect-≈ eq (possibly rel px) = possibly (coe eq rel) px

    instance ◇-respect-≈ : ∀ {p} {P : Pred A p} → Respect _≈_ (◇ P)
    Respect.coe ◇-respect-≈ eq (g , px) = g , coe eq px

  module ◇-GradedMonad
    {{r  : Rel₃ A}} {{g : Rel₃ G}}
    {e}  {_≈_ : G → G → Set e} {ug} {{gm : IsPartialMonoid _≈_ g ug}}

    -- graded preorder
    (∼-refl  : ∀ {a} → a ∼[ ε ] a)
    (∼-trans : ∀ {Δ₁ Δ₂ Δ : G} {a b c} → (σ : Δ₁ ∙ Δ₂ ≣ Δ) → a ∼[ Δ₁ ] b → b ∼[ Δ₂ ] c → a ∼[ Δ ] c)

    -- frame preserving
    (∼-fp : ∀ {Δ fr Φ₁ Φ₂} → Φ₁ ∼[ Δ ] Φ₂ → (di₁ : fr ◆ Φ₁) → ∃ λ (di₂ : fr ◆ Φ₂) → whole di₁ ∼[ Δ ] whole di₂)
    where

    -- greturn : ∀[ P ⇒ ◇[ ε ] P ]
    -- greturn px = possibly ∼-refl px

    -- goin : Δ₁ ∙ Δ₂ ≣ Δ → ∀[ ◇[ Δ₁ ] (◇[ Δ₂ ] P) ⇒ ◇[ Δ ] P ]
    -- goin σ (possibly x∼y (possibly y∼z px)) = possibly (∼-trans σ x∼y y∼z) px

    -- gstr : ∀ {Δ} → ∀[ P ✴ (◇[ Δ ] Q) ⇒ ◇[ Δ ] (P ✴ Q) ]
    -- gstr (px ∙⟨ σ ⟩ possibly rel qx) with ∼-fp rel (-, σ)
    -- ... | di , rel' = possibly rel' (px ∙⟨ proj₂ di ⟩ qx)

  module ◇-Zip
    {{r  : Rel₃ A}} {{g : Rel₃ G}}
    (∼-pull : ∀ {a b c a' b' Δ₁ Δ₂ Δ}
            → Δ₁ ∙ Δ₂ ≣ Δ
            → a ∙ b ≣ c
            → a ∼[ Δ₁ ] a'
            → b ∼[ Δ₂ ] b'
            → ∃ λ c' → a' ∙ b' ≣ c' × c ∼[ Δ ] c') where

      ◇-zip : Δ₁ ∙ Δ₂ ≣ Δ → ∀[ ◇[ Δ₁ ] P ✴ ◇[ Δ₂ ] Q ⇒ ◇[ Δ ] (P ✴ Q) ]
      ◇-zip δ (possibly r₁ px ∙⟨ σ ⟩ possibly r₂ qx) with ∼-pull δ σ r₁ r₂ 
      ... | _ , σ′ , r′ = possibly r′ (px ∙⟨ σ′ ⟩ qx)

  module ◇-Unzip
    {{r  : Rel₃ A}}
    (∼-push : ∀ {a b c c' Δ}
            → c' ∼[ Δ ] c
            → a ∙ b ≣ c
            → ∃₂ λ a' b'
            → a' ∼[ Δ ] a × b' ∼[ Δ ] b × a' ∙ b' ≣ c') where

      ◇-unzip : ∀[ ◇[ Δ ] (P ✴ Q) ⇒ ◇[ Δ ] P ✴ ◇[ Δ ] Q ]
      ◇-unzip (possibly rel (px ∙⟨ σ ⟩ qx)) with _ , _ , r₂ , r₃ , τ ← ∼-push rel σ =
        possibly r₂ px ∙⟨ τ ⟩ possibly r₃ qx

module ◇-Monad
  {G : Set ℓa} (_∼[_]_  : GradedRel A G ℓa)
  {{r  : Rel₃ A}}
  (open Possibly _∼[_]_)
  {e} {_≈_ : A → A → Set e} (∼-isPreorder : IsPreorder _≈_ _∼_)
  (∼-fp : ∀ {fr Φ₁ Φ₂} → Φ₁ ∼ Φ₂ → (di₁ : fr ◆ Φ₁) → ∃ λ (di₂ : fr ◆ Φ₂) → whole di₁ ∼ whole di₂)
  where

  open IsPreorder ∼-isPreorder

  instance
    ◇-functor : Functor ◇
    Functor.fmap ◇-functor f (g , possibly rel px) = -, possibly rel (f px)

    ◇-monad : Monad ⊤ (λ _ _ → ◇)
    Monad.return ◇-monad px =
      -, possibly (proj₂ refl) px
    Monad._=<<_ ◇-monad f (_ , possibly r px) with (_ , possibly r' qx) ← f px =
      -, possibly (proj₂ (trans (-, r) (-, r'))) qx

    ◇-strong : Strong ⊤ (λ _ _ → ◇)
    Strong.str ◇-strong qx ⟨ σ ⟩ (_ , possibly rel px) with fr , rel' ← ∼-fp (-, rel) (-, σ) =
      -, Possibly.possibly (proj₂ rel') (qx ∙⟨ proj₂ fr ⟩ px)

  ◇-⤇ : ∀[ ◇ P ⇒ ⤇ P ]
  ◇-⤇ (_ , possibly r px) = local (λ fr → _ , proj₁ (∼-fp (-, r) fr) , px)
