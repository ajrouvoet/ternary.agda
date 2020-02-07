module Relation.Ternary.Monad.Possibly {a} {A : Set a} where

open import Level
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Monad

open import Data.Unit
open import Data.Product

module Possibly {r ℓ} (_∼_ : Rel A r) where

  record ◇ (P : Pred A ℓ) (Φ : A) : Set (r ⊔ a ⊔ ℓ) where
    constructor possibly
    field
      {Φ′} : A
      rel  : Φ ∼ Φ′
      px   : P Φ′

  module ◇-Monad 
    {{r  : Rel₃ A}}
    {e} {_≈_ : A → A → Set e}
    {u} {{us : IsPartialMonoid _≈_ r u}}
    (pre : IsPreorder _≈_ _∼_)
    (fp : ∀ {Φ Φ′ Δ Ψ : A} → Φ ∼ Φ′ → Δ ∙ Φ ≣ Ψ → ∃ λ (Ψ′ : A) → Δ ∙ Φ′ ≣ Ψ′ × Ψ ∼ Ψ′)
    where

    instance ◇-monad : Monad ⊤ (λ _ _ → ◇)
    Monad.return ◇-monad px = possibly (IsPreorder.refl pre) px
    Monad.bind ◇-monad f ⟨ σ ⟩ (possibly r px) with fp r σ
    ... | Φ′ , σ′ , r′′ with f ⟨ σ′ ⟩ px
    ... | possibly r′ qx = possibly (IsPreorder.trans pre r′′ r′) qx
