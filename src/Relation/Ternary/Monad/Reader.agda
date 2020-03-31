{-# OPTIONS --safe #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Reader
  {a} {A : Set a}
  {C : Set a} {{rel : Rel₃ C}}
  {_≈_ : C → C → Set a}
  {u} {{csg : IsPartialMonoid _≈_ rel u}} 
  where

open import Level
open import Function using (_∘_; case_of_)

open import Data.Product
open import Data.List hiding (concat; lookup)
open import Data.Unit
open import Algebra.Structures using (IsMonoid)

open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Data.Allstar A
open import Relation.Ternary.Upto.Quotient
open import Relation.Ternary.Monad

private
  variable
    ℓv : Level
    Γ Γ₁ Γ₂ Γ₃ : List A

module ReaderTransformer
  (V : A → Pred C a)
  (M : Pt C a)
  where

  open import Relation.Ternary.Construct.List.Disjoint A

  variable
    P Q R : Pred C a

  module _ where

    Reader : ∀ (Γ₁ Γ₂ : List A) → Pt C a
    Reader Γ₁ Γ₂ P = (Allstar V Γ₁) ─✴ M (P ✴ Allstar V Γ₂)

    instance
      reader-monad : {{monad : Monad ⊤ (λ _ _ → M)}} → Monad (List A) Reader
      Monad.return reader-monad px ⟨ σ ⟩ env   = return (px ∙⟨ σ ⟩ env)
      Monad._=<<_ reader-monad f mp ⟨ σ₁ ⟩ env = do
        px ∙⟨ σ₂ ⟩ env' ← mp ⟨ σ₁ ⟩ env
        f px ⟨ σ₂ ⟩ env'

      reader-strong : {{monad : Strong ⊤ (λ _ _ → M)}} → Strong (List A) Reader
      Strong.str reader-strong {Q = Q} qx ⟨ σ₁ ⟩ mp ⟨ σ₂ ⟩ env = do
        let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂
        ✴-assocₗ ⟨$⟩ (mp ⟨ σ₄ ⟩ env &⟨ Q # σ₃ ⟩ qx)

  module _ {{monad : Monad ⊤ (λ _ _ → M)}} where

    ask : ε[ Reader Γ [] (Allstar V Γ) ]
    ask ⟨ σ ⟩ env = return (env ∙⟨ ∙-id⁺ʳ (∙-id⁻ˡ σ) ⟩ nil)

  module _
    {{monad : Strong ⊤ (λ _ _ → M)}}
    {{_ : IsCommutative rel}} where

    frame : Γ₁ ∙ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ [] P ⇒ Reader Γ₂ Γ₃ P ]
    frame sep c ⟨ σ ⟩ env = do
      let E₁ ∙⟨ σ₁ ⟩ E₂ = repartition sep env
      let _ , σ₂ , σ₃   = ∙-assocₗ σ σ₁  
      E₂ ∙⟨ σ₅ ⟩ (px ∙⟨ σ₆ ⟩ nil) ← (c ⟨ σ₂ ⟩ E₁) &⟨ Allstar _ _ # ∙-comm σ₃ ⟩ E₂
      return (px ∙⟨ ∙-comm (coe {{∙-respects-≈ʳ}} (≈-sym (∙-id⁻ʳ σ₆)) σ₅) ⟩ E₂ )

    liftM : ∀[ M P ⇒ Reader Γ Γ P ]
    liftM mp ⟨ σ ⟩ env = ✴-swap ⟨$⟩ (mp &⟨ ∙-comm σ ⟩ env)

    lookup : ∀ {a} → ε[ Reader [ a ] [] (V a) ]
    lookup =
      do
      v :⟨ σ ⟩: nil ←  ask
      coe (∙-id⁻ʳ σ) (return v)

    prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ++ Γ₂) Emp ]
    prepend env₁ ⟨ σ ⟩ env₂ =
      return (refl ∙⟨ ∙-idˡ ⟩ concat (env₁ ∙⟨ σ ⟩ env₂))

    append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ++ Γ₁) Emp ]
    append env₁ ⟨ σ ⟩ env₂ =
      return (refl ∙⟨ ∙-idˡ ⟩ concat (env₂ ∙⟨ ∙-comm σ ⟩ env₁))

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
