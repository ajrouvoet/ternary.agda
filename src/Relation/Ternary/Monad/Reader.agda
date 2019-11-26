{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Reader
  {a} {A : Set a}
  {C : Set a} {{rel : Rel₃ C}}
  {_≈_ : C → C → Set a}
  {u} {{_ : IsPartialMonoid {_≈_ = _≈_} rel u}} 
  where

open import Level
open import Function using (_∘_; case_of_)

open import Data.Product
open import Data.List hiding (concat; lookup)
open import Data.Unit

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relation.Ternary.Monad {_≈_ = _≈_}
open import Relation.Ternary.Data.Allstar A _≈_
open import Relation.Ternary.Upto.Quotient

private
  variable
    ℓv : Level
    Γ Γ₁ Γ₂ Γ₃ : List A

module ReaderTransformer
  (V : A → Pred C a)
  (M : Pt C a) {{monad : Monad ⊤ (λ _ _ → M)}}
  where

  open import Relation.Ternary.Construct.List.Interleave A

  variable
    P Q R : Pred C a

  module _ where

    Reader : ∀ (Γ₁ Γ₂ : List A) → Pt C a
    Reader Γ₁ Γ₂ P = (Allstar V Γ₁) ─⊙ M (Allstar V Γ₂ ⊙ P)

    instance
      reader-monad : Monad (List A) Reader
      Monad.return reader-monad px ⟨ σ ⟩ env =
        Monad.return monad env &⟨ σ ⟩ px
      Monad.bind reader-monad f ⟨ σ₁ ⟩ mp ⟨ σ₂ ⟩ env =
        let _ , σ₃ , σ₄ = ∙-assocₗ σ₂ σ₁ in
        bind
          (arr λ where
            σ₅ (env' ∙⟨ σ₆ ⟩ px) → let _ , σ₇ , σ₈ = ∙-assocᵣ σ₆ σ₅ in f ⟨ σ₈ ⟩ px ⟨ σ₇ ⟩ env')
          ⟨ σ₄ ⟩
          (mp ⟨ σ₃ ⟩ env)

  module _ where

    ask : ε[ Reader Γ [] (Allstar V Γ) ]
    ask ⟨ σ ⟩ env = return (nil ∙⟨ ∙-id⁺ˡ (∙-id⁻ʳ σ) ⟩ env)

  module _
    {{_ : ∀ {P} → Respect _≈_ (M P) }}
    {{_ : IsCommutative {_≈_ = _≈_} rel}} where

    frame : Γ₁ ∙ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ [] P ⇒ Reader Γ₂ Γ₃ P ]
    frame sep c ⟨ σ ⟩ env = do
      let E₁ ∙⟨ σ₁ ⟩ E₂ = repartition sep env
      let _ , σ₂ , σ₃   = ∙-assocᵣ (∙-comm σ₁) σ 
      (nil ∙⟨ σ₆ ⟩ px) ∙⟨ σ₅ ⟩ E₂ ← (c ⟨ σ₃ ⟩ E₁) &⟨ Allstar _ _ ∥ ∙-comm σ₂ ⟩ E₂
      return (E₂ ∙⟨ coe {{ ∙-respects-≈ʳ }} (≈-sym (∙-id⁻ˡ σ₆)) (∙-comm σ₅) ⟩ px)

    liftM : ∀[ M P ⇒ Reader Γ Γ P ]
    liftM mp ⟨ σ ⟩ env =
      mapM (mp &⟨ ∙-comm σ ⟩ env) ⊙-swap

    lookup : ∀ {a} → ε[ Reader [ a ] [] (V a) ]
    lookup =
      do
      v :⟨ σ ⟩: nil ←  ask
      coe (∙-id⁻ʳ σ) (return v)

    prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ++ Γ₂) Emp ]
    prepend env₁ ⟨ σ ⟩ env₂ =
      return (concat (env₁ ∙⟨ ∙-comm σ ⟩ env₂) ∙⟨ ∙-idʳ ⟩ refl)

    append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ++ Γ₁) Emp ]
    append env₁ ⟨ σ ⟩ env₂ =
      return (concat (env₂ ∙⟨ σ ⟩ env₁) ∙⟨ ∙-idʳ ⟩ refl)

--     runReader : ∀[ Allstar V Γ ⇒ⱼ Reader Γ ε P ─✴ M P ]
--     app (runReader env) mp σ = do
--       px ×⟨ σ ⟩ nil ← app mp (inj env) (⊎-comm σ)
--       case ⊎-id⁻ʳ σ of λ where
--         refl → return px 

--   module _ where
--     open Monad reader-monad

-- module ReaderMonad {ℓ}
--   -- types
--   {T : Set ℓ}
--   -- runtime resourele
--   {C : Set ℓ} {{rel : Rel₃ C}} {u} {{sc : IsUnitalSep rel u}} {{cc : HasConcat rel}}
--   -- values
--   (V : T → Pred C ℓ)
--   where

--   open import Relation.Ternary.Separation.Monad.Identity
--   open ReaderTransformer id-morph V Identity.Id {{ monad = Identity.id-monad }} public
