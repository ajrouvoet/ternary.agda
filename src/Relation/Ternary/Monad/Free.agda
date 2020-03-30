{-# OPTIONS --safe --overlapping-instances #-}
open import Relation.Unary
open import Relation.Ternary.Core

module Relation.Ternary.Monad.Free
  {ℓ e} {A : Set ℓ} {{r : Rel₃ A}}
  (_≈_ : A → A → Set e)
  (Cmd : Pred A ℓ)
  (δ   : ∀ {Φ} → Cmd Φ → Pred A ℓ) {{δ-≈ : ∀ {Φ} {c : Cmd Φ} → Respect _≈_ (δ c)}}
  where

open import Level
open import Function using (case_of_)
open import Data.Unit
open import Data.Product
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Monad _≈_
open import Relation.Ternary.Structures _≈_

mutual
  Cont : ∀ {Δ} → Cmd Δ → Pred A ℓ → Pred A ℓ
  Cont c P = δ c ─✴ Free P

  data Free : Pt A ℓ where
    pure   : ∀ {P}   → ∀[ P ⇒ Free P ]
    impure : ∀ {P}   → ∀[ ∃[ Cmd ]✴ (λ c → Cont c P) ⇒ Free P ]

module _ {u} {{_ : IsPartialMonoid r u}} where
  instance
    free-monad : Monad ⊤ ℓ (λ _ _ → Free)

    Monad.return free-monad = pure

    (Monad.bind free-monad f) ⟨ σ ⟩  (pure x) =
      f ⟨ σ ⟩ x
    (Monad.bind free-monad f) ⟨ σ₁ ⟩ (impure (cmd ∙⟨ σ₂ ⟩ κ)) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₂ σ₁ in
      impure (cmd ∙⟨ σ₃ ⟩
        arr λ σ₅ resp →
          let _ , σ₆ , σ₇ = ∙-assocₗ σ₅ σ₄ in
          bind f ⟨ σ₇ ⟩ (κ ⟨ σ₆ ⟩ resp))

  ⟪_⟫ : ∀ {Φ} → (c : Cmd Φ) → Free (δ c) Φ
  ⟪_⟫ c = 
    impure (c ∙⟨ ∙-idʳ ⟩ 
      arr λ σ r → return (coe (∙-id⁻ʳ σ) r))

module _
  {u} {{pm : IsPartialMonoid r u}}
  {M : Pt A ℓ}
  {{ monad : Monad ⊤ ℓ (λ _ _ → M) }}
  where

  open import Data.Nat

  -- Unfolding a command tree one step
  step : ∀ {P : Pred A ℓ} (cmd : ∀ {Φ} → (c : Cmd Φ) → M (δ c) Φ) → ∀[ Free P ⇒ M (Free P) ]
  step cmd (pure px) = return (pure px)
  step cmd (impure (c ∙⟨ σ ⟩ κ)) = do
    r ∙⟨ σ ⟩ κ ← str {{ monad = monad }} (cmd c) κ -- &⟨ Cont c _ ∥ σ ⟩ κ
    return (κ ⟨ σ ⟩ r)

  -- -- A fueled generic interpreter for command trees in Free
  -- interpret : ℕ → ∀[ M P ] → (cmd : ∀ {Φ} → (c : Cmd Φ) → M (δ c) (j Φ)) → ∀[ Free P ⇒ⱼ M P ]
  -- interpret zero    def cmd f = def
  -- interpret (suc n) def cmd f = do
  --   impure f ← step cmd f
  --     where
  --       (pure v) → return v
  --   interpret n def cmd (impure f)
