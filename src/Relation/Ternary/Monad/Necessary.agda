{-# OPTIONS --without-K #-} -- --safe 

{- A graded necessity modality -}
module Relation.Ternary.Monad.Necessary {ℓa} {A : Set ℓa} where

open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary using (Rel)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Comonad
open import Relation.Ternary.Monad.Update
open import Algebra.Structures

open import Data.Unit
open import Data.Product

private
  variable
    p   : Level
    P Q : Pred A p

open import Relation.Ternary.Monad.Possibly {A = A} using (GradedRel)

module Necessary {G : Set ℓa} (_∼[_]_  : GradedRel A G ℓa) where

  private
    variable
      Δ₁ Δ₂ Δ : G

  record □[_] (gr : G) (P : Pred A ℓa) (Φ : A) : Set ℓa where
    constructor necessary
    field
      future : ∀ {Φ′} → Φ ∼[ gr ] Φ′ → P Φ′

  open □[_] public

  □ : Pt A _
  □ P = ⋂[ Δ ∶ _ ] □[ Δ ] P

  _∼_ : A → A → Set _
  a ∼ b = ∃ λ Δ → a ∼[ Δ ] b

  instance □-functor : Functor □[ Δ ]
  future (Functor.fmap □-functor f □px) r = f (future □px r)

  module _ {e}  {_≈_ : A → A → Set e} {{_ : IsEquivalence _≈_}}
    {{∼-respects-≈ˡ : ∀ {g a} → Respect _≈_ (_∼[ g ] a)}} where

    instance □[]-respect-≈ : ∀ {P} {g} → Respect _≈_ (□[ g ] P)
    Respect.coe □[]-respect-≈ eq (necessary f) = necessary λ x∼y → f (coe (≈-sym eq) x∼y)

    instance □-respect-≈ : ∀ {P} → Respect _≈_ (□ P)
    Respect.coe □-respect-≈ eq f x~y = coe eq (f x~y)

  -- module □-GradedMonad
  --   {{r  : Rel₃ A}} {{g : Rel₃ G}}
  --   {e}  {_≈_ : G → G → Set e} {ug} {{gm : IsPartialMonoid _≈_ g ug}}
  --   {_≈ₐ_ : A → A → Set e}

  --   (∼-unrefl    : ∀ {a b} → a ∼[ ε ] b → a ≈ₐ b)
  --   (∼-untrans   : ∀ {Δ₁ Δ₂ Δ : G} {a c : A} → (σ : Δ₁ ∙ Δ₂ ≣ Δ) → a ∼[ Δ ] c
  --                → ∃ λ b → a ∼[ Δ₁ ] b × b ∼[ Δ₂ ] c)

  --   (∼-cofp : ∀ {Δ Φ₁ Φ₂ Φ₁₁ Φ₁₂} → Φ₁ ∼[ Δ ] Φ₂ → Φ₁₁ ∙ Φ₁₂ ≣ Φ₁
  --           → ∃ λ Φ → Φ₁₂ ∼[ Δ ] Φ × Φ₁₁ ∙ Φ ≣ Φ₂)
  --   where

  --   -- greturn : {{_ : Respect _≈ₐ_ P}} → ∀[ P ⇒ □[ ε ] P ]
  --   -- greturn px = necessary (λ r → coe (∼-unrefl r) px)

  --   -- goin : Δ₁ ∙ Δ₂ ≣ Δ → ∀[ □[ Δ₁ ] (□[ Δ₂ ] P) ⇒ □[ Δ ] P ]
  --   -- future (goin δ □□px) r = let _ , r₁ , r₂ = ∼-untrans δ r in future (future □□px r₁) r₂ 

  --   -- gstr : ∀ {Δ} → ∀[ P ✴ (□[ Δ ] Q) ⇒ □[ Δ ] (P ✴ Q) ]
  --   -- future (gstr (px ∙⟨ σ ⟩ mqx)) r with ∼-cofp r σ
  --   -- ... | _ , δ₁ , τ = px ∙⟨ τ ⟩ future mqx δ₁

  --   □-gmonad : GradedMonad □[_]
  --   future (unit □-gmonad px) r = {!!}
  --   multiply □-gmonad = {!!}
  --   gstr □-gmonad = {!!}

  module □-GradedComonad
    {{r  : Rel₃ A}} {{g : Rel₃ G}}
    {e}  {_≈_ : G → G → Set e} {ug} {{gm : IsPartialMonoid _≈_ g ug}}

    -- graded preorder
    (∼-refl    : ∀ {a} → a ∼[ ε ] a)
    (∼-trans   : ∀ {Δ₁ Δ₂ Δ : G} {a b c : A} → (σ : Δ₁ ∙ Δ₂ ≣ Δ) → a ∼[ Δ₁ ] b → b ∼[ Δ₂ ] c
               → a ∼[ Δ ] c)

    (∼-cofp : ∀ {Δ Φ₁ Φ₂ Φ₁₁ Φ₁₂} → Φ₁ ∼[ Δ ] Φ₂ → Φ₁₁ ∙ Φ₁₂ ≣ Φ₁
            → ∃ λ Φ → Φ₁₂ ∼[ Δ ] Φ × Φ₁₁ ∙ Φ ≣ Φ₂)
    where

    instance □-comonad : GradedComonad □[_]
    GradedComonad.co-unit □-comonad mpx = future mpx ∼-refl
    future (future (GradedComonad.co-multiply □-comonad δ mpx) r) s = future mpx (∼-trans δ r s)
    future (GradedComonad.gstr □-comonad qx ⟨ σ ⟩ mpx) r with ∼-cofp r σ
    ... | _ , δ , τ = qx ∙⟨ τ ⟩ future mpx δ

