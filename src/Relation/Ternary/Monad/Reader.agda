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

    record Reader (Γ₁ Γ₂ : List A) (P : Pred C a) (c : C) : Set a where
      constructor reader
      field
        runReader : ((Allstar V Γ₁) ─✴ M (P ✴ Allstar V Γ₂)) c
        
    open Reader public

    instance
      reader-respect : Respect _≈_ (Reader Γ₁ Γ₂ P)
      Respect.coe reader-respect x (reader m) = reader (coe x m)

      reader-functor : {{functor : Functor M}} → Functor (Reader Γ₁ Γ₂)
      runReader (Functor.fmap reader-functor f (reader m)) ⟨ σ ⟩ env =
        (λ where (px ∙⟨ σ ⟩ env) → f px ∙⟨ σ ⟩ env) ⟨$⟩ (m ⟨ σ ⟩ env)

      reader-monad : {{monad : Monad ⊤ (λ _ _ → M)}} → Monad (List A) Reader
      runReader (Monad.return reader-monad px) ⟨ σ ⟩ env   = return (px ∙⟨ σ ⟩ env)
      runReader (Monad._=<<_ reader-monad f (reader m)) ⟨ σ₁ ⟩ env = do
        px ∙⟨ σ₂ ⟩ env' ← m ⟨ σ₁ ⟩ env
        runReader (f px) ⟨ σ₂ ⟩ env'

      reader-strong : {{monad : Strong ⊤ (λ _ _ → M)}} → Strong (List A) Reader
      runReader ((Strong.str reader-strong {Q = Q} qx) ⟨ σ₁ ⟩ (reader m)) ⟨ σ₂ ⟩ env = do
        let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂
        ✴-assocₗ ⟨$⟩ (m ⟨ σ₄ ⟩ env &⟨ Q # σ₃ ⟩ qx)

  module _ {{monad : Monad ⊤ (λ _ _ → M)}} where

    ask : ε[ Reader Γ [] (Allstar V Γ) ]
    runReader ask ⟨ σ ⟩ env = return (env ∙⟨ ∙-id⁺ʳ (∙-id⁻ˡ σ) ⟩ nil)

    lookup : ∀ {a} → ε[ Reader [ a ] [] (V a) ]
    lookup = do
      v :⟨ σ ⟩: nil ← ask
      coe (∙-id⁻ʳ σ) (return v)

  module _
    {{monad : Strong ⊤ (λ _ _ → M)}}
    {{_ : IsCommutative rel}} where

    frame : Γ₁ ∙ Γ₃ ≣ Γ₂ → ∀[ Reader Γ₁ [] P ⇒ Reader Γ₂ Γ₃ P ]
    runReader (frame sep (reader c)) ⟨ σ ⟩ env = do
      let E₁ ∙⟨ σ₁ ⟩ E₂ = repartition sep env
      let _ , σ₂ , σ₃   = ∙-assocₗ σ σ₁
      E₂ ∙⟨ σ₅ ⟩ (px ∙⟨ σ₆ ⟩ nil) ← (c ⟨ σ₂ ⟩ E₁) &⟨ Allstar _ _ # ∙-comm σ₃ ⟩ E₂
      return (px ∙⟨ ∙-comm (coe {{∙-respects-≈ʳ}} (≈-sym (∙-id⁻ʳ σ₆)) σ₅) ⟩ E₂ )

    liftM : ∀[ M P ⇒ Reader Γ Γ P ]
    runReader (liftM mp) ⟨ σ ⟩ env = ✴-swap ⟨$⟩ (mp &⟨ ∙-comm σ ⟩ env)

    module _ {{_ : IsUnique _≈_ u}} where
      append : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₂ ++ Γ₁) Emp ]
      runReader (append env₁) ⟨ σ ⟩ env₂ =
        return (refl ∙⟨ ∙-idˡ ⟩ concat (env₂ ∙⟨ ∙-comm σ ⟩ env₁))

      prepend : ∀[ Allstar V Γ₁ ⇒ Reader Γ₂ (Γ₁ ++ Γ₂) Emp ]
      runReader (prepend env₁) ⟨ σ ⟩ env₂ =
        return (refl ∙⟨ ∙-idˡ ⟩ concat (env₁ ∙⟨ σ ⟩ env₂))

-- -- module ReaderMonad {ℓ}
-- --   -- types
-- --   {T : Set ℓ}
-- --   -- runtime resourele
-- --   {C : Set ℓ} {{rel : Rel₃ C}} {u} {{sc : IsUnitalSep rel u}} {{cc : HasConcat rel}}
-- --   -- values
-- --   (V : T → Pred C ℓ)
-- --   where

-- --   open import Relation.Ternary.Separation.Monad.Identity
-- --   open ReaderTransformer id-morph V Identity.Id {{ monad = Identity.id-monad }} public
