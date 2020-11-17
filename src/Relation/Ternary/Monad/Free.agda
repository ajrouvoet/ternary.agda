{-# OPTIONS --safe --overlapping-instances #-}

open import Level
open import Function using (case_of_)
open import Data.Unit
open import Data.Product
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Monad
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

module Relation.Ternary.Monad.Free
  {ℓ e} {A : Set ℓ} {{r : Rel₃ A}}
  (_≈_ : A → A → Set e)
  (Cmd : Pred A ℓ)
  (δ   : ∀ {Φ} → Cmd Φ → Pred A ℓ) 
  where

mutual
  Cont : ∀ {Δ} → Cmd Δ → Pred A ℓ → Pred A ℓ
  Cont c P = δ c ─✴ Free P

  data Free : Pt A ℓ where
    pure   : ∀ {P}   → ∀[ P ⇒ Free P ]
    impure : ∀ {P}   → ∀[ Σ[ c ∈ Cmd ]✴ (Cont c P) ⇒ Free P ]

module _ {u} {{_ : IsPartialMonoid _≈_ r u}} where
  instance
    free-respect : ∀ {P} {{_ : Respect _≈_ P}} → Respect _≈_ (Free P)
    Respect.coe free-respect eq (pure x) = pure (coe eq x)
    Respect.coe free-respect eq (impure c∙κ) = impure (coe eq c∙κ)

    free-functor : Functor Free
    Functor.fmap free-functor f (pure x) = pure (f x)
    Functor.fmap free-functor f (impure (c ∙⟨ σ ⟩ κ)) = 
      impure (c ∙⟨ σ ⟩ arr λ τ r → fmap f (κ ⟨ τ ⟩ r))

    free-monad : Monad ⊤ (λ _ _ → Free)
    Monad.return free-monad = pure
    (free-monad Monad.=<< f) (pure x)   = f x
    (free-monad Monad.=<< f) (impure (c ∙⟨ σ₁ ⟩ κ)) = 
      impure (c ∙⟨ σ₁ ⟩ arr (λ σ₂ r → f =<< (κ ⟨ σ₂ ⟩ r)))

  ⟪_⟫ : ∀ {Φ} (c : Cmd Φ) → {{δ-≈ : Respect _≈_ (δ c)}} → Free (δ c) Φ
  ⟪_⟫ c =
    impure (c ∙⟨ ∙-idʳ ⟩
      arr λ σ r → return (coe (∙-id⁻ˡ σ) r))

module _
  {u} {{pm : IsPartialMonoid _≈_ r u}}
  {M : Pt A ℓ}
  {{_ : Strong ⊤ (λ _ _ → M)}} {{_ : IsCommutative r}}
  where

  open import Data.Nat

  -- Unfolding a command tree one step
  step : ∀ {P : Pred A ℓ} → ∀[ Π[ c ∈ Cmd ]⇒ M (δ c) ] → ∀[ Free P ⇒ M (Free P) ]
  step cmd (pure px) = return (pure px)
  step cmd (impure (c ∙⟨ σ ⟩ κ)) = do
    r ∙⟨ σ ⟩ κ ← cmd c ⟨ Cont c _ # σ ⟩& κ
    return (κ ⟨ ∙-comm σ ⟩ r)

  -- A fueled generic interpreter for command trees in Free
  interpret : ∀ {P : Pred A ℓ} (n : ℕ) → ∀[ M P ] → ∀[ Π[ c ∈ Cmd ]⇒ M (δ c) ] → ∀[ Free P ⇒ M P ]
  interpret zero    def cmd f = def
  interpret (suc n) def cmd f = do
    impure f ← step cmd f
      where
        (pure v) → return v
    interpret n def cmd (impure f)
