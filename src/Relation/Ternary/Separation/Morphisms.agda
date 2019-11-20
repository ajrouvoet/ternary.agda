module Relation.Ternary.Separation.Morphisms where

open import Level
open import Relation.Unary
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality as P
open import Data.Product
open import Function using (_∘_)

open import Relation.Ternary.Separation.Core
import Function.Definitions as Functions

module _ {a b e₁ e₂} (Aₛ : Setoid a e₁) (Bₛ : Setoid b e₂) where

  open Setoid Aₛ renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid Bₛ renaming (Carrier to B; _≈_ to _≈₂_)

  record Morphism 
    {{r : RawSep A}} {u} {{s₁ : HasUnit _≈₁_ r u}}
    {{rb : RawSep B}} : Set (a ⊔ b ⊔ e₁ ⊔ e₂) where

    open Functions _≈₁_ _≈₂_
    field
      j      : A → B
      j-cong : Congruent j

      -- j "commutes" with _⊎_
      j-⊎  : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ⊎ Φ₂ ≣ Φ → j Φ₁ ⊎ j Φ₂ ≣ j Φ
      j-⊎⁻ : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ⊎ j Φ₂ ≣ Φ → ∃ λ Φ' → Φ ≡ j Φ' × Φ₁ ⊎ Φ₂ ≣ Φ'

    instance _ = s₁

    infixr 8 _⇒ⱼ_
    _⇒ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _ 
    P ⇒ⱼ Q = P ⇒ (Q ∘ j)

    infixr 8 _─✴ⱼ_
    _─✴ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred B _ 
    P ─✴ⱼ Q = P ─✴[ j ] Q

    {- Such a morphism on SAs induces a functor on SA-predicates -}
    module _ where

      data J {p} (P : Pred A p) : Pred B (a ⊔ p) where
        inj : ∀ {Φ} → P Φ → J P (j Φ)

      jstar : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J (P ✴ Q) ⇒ J P ✴ J Q ]
      jstar (inj (p ×⟨ σ ⟩ q)) = inj p ×⟨ j-⊎ σ ⟩ inj q

      jmap : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ (P ─✴ Q) ⇒ⱼ (J P ─✴ J Q) ]
      jmap f ⟨ σ ⟩ (inj px) with j-⊎⁻ σ
      ... | _ , refl , σ' = inj (f ⟨ σ' ⟩ px)

    -- wanditⱼ : ∀ {p q} {P : Pred A p} {Q : Pred B q} → ∀[ P ⇒ⱼ Q ] → (P ─✴ⱼ Q) (j u)
    -- wanditⱼ f ⟨ σ ⟩ px with j-⊎⁻ σ
    -- ... | _ , refl , σ' with ⊎-id⁻ˡ σ'
    -- ... | refl = f px

{- identity morphism -}
module _ {a} {A : Set a} {{r : RawSep A}} {u} {{s₁ : HasUnit _≡_ r u}} where

  open import Function

  instance id-morph : Morphism (setoid A) (setoid A)
  id-morph = record 
    { j      = id
    ; j-cong = cong id
    ; j-⊎    = id 
    ; j-⊎⁻   = λ x → -, P.refl , x
    }
