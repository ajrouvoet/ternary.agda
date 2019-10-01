-- | An implementation of the Marketoritative PCM
module Relation.Unary.Separation.Construct.Market where

open import Level hiding (Lift)
open import Data.Product
open import Data.Maybe

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality as P

open import Relation.Unary.Separation
open import Relation.Unary.Separation.Morphisms

module _ {ℓ} (A : Set ℓ) where

  data Market : Set ℓ where
    offer  : (l : A) → Market
    demand : (r : A) → Market

module _ {ℓ} {A : Set ℓ} {{ sep : RawSep A }} {{ _ : IsSep sep }} where

  data Split : Market A → Market A → Market A → Set ℓ where

    offerₗ : {r l₁ l₂ : A} (σ : l₂ ⊎ r ≣ l₁) → Split (offer l₁) (demand r) (offer l₂)
    offerᵣ : {r l₁ l₂ : A} (σ : r ⊎ l₂ ≣ l₁) → Split (demand r) (offer l₁) (offer l₂)
    demand : {r₁ r₂ r : A} (σ : r₁ ⊎ r₂ ≣ r) → Split (demand r₁) (demand r₂) (demand r)

  comm : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Split Φ₂ Φ₁ Φ
  comm (demand p) = demand (⊎-comm p)
  comm (offerₗ σ) = offerᵣ (⊎-comm σ)
  comm (offerᵣ σ) = offerₗ (⊎-comm σ)

  assoc : ∀ {a b ab c abc} → Split a b ab → Split ab c abc → ∃ λ bc → (Split a bc abc) × (Split b c bc)
  assoc (offerₗ σ₁) (offerₗ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₂ σ₁ in -, offerₗ σ₃ , demand (⊎-comm σ₄)
  assoc (offerᵣ σ₁) (offerₗ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-unassoc σ₁ σ₂ in -, offerᵣ σ₃ , offerₗ σ₄
  assoc (demand σ₁) (offerᵣ σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc (⊎-comm σ₁) σ₂ in -, offerᵣ σ₄ , offerᵣ σ₃
  assoc (demand σ₁) (demand σ₂) =
    let _ , σ₃ , σ₄ = ⊎-assoc σ₁ σ₂ in -, demand σ₃ , demand σ₄
  instance market-raw-sep : RawSep (Market A)
  RawSep._⊎_≣_ market-raw-sep = Split

  instance market-has-sep : IsSep market-raw-sep
  market-has-sep = record
    { ⊎-comm  = comm
    ; ⊎-assoc = assoc
    }

  instance market-sep : Separation _
  market-sep = record
    { isSep = market-has-sep }

module _ {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }} where

  module U = IsUnitalSep
  instance market-is-unital : IsUnitalSep market-raw-sep (demand ε)
  U.isSep market-is-unital  = market-has-sep
  U.⊎-idˡ market-is-unital {offer l} = offerᵣ ⊎-idˡ
  U.⊎-idˡ market-is-unital {demand r} = demand ⊎-idˡ
  U.⊎-id⁻ˡ market-is-unital (offerᵣ σ) = cong offer (sym (⊎-id⁻ˡ σ))
  U.⊎-id⁻ˡ market-is-unital (demand σ) = cong demand (⊎-id⁻ˡ σ)


module _ {a} {{ s : MonoidalSep a }} where

  open MonoidalSep s using () renaming (Carrier to A)

  matching : ∀ {a b : A} {c d} → (demand a) ⊎ (offer b) ≣ c → (demand (d ∙ a)) ⊎ (offer (d ∙ b)) ≣ c
  matching (offerᵣ σ) = offerᵣ (⊎-∙ₗ σ)

module _ {ℓ} {A : Set ℓ} {{_ : RawSep A}} where

  private
    variable
      ℓv : Level
      P Q : Pred (A × A) ℓv
        
  Completion : A → (A × A) → Set ℓ
  Completion x (y , z) = x ⊎ z ≣ y

  data ● {p} (P : Pred (A × A) p) : Pred (Market A) (ℓ ⊔ p) where
    lift : ∀ {xs l₂} → P xs → Completion l₂ xs → ● P (offer l₂)

  ●-map : ∀[ P ⇒ Q ] → ∀[ ● P ⇒ ● Q ]
  ●-map f (lift px le) = lift (f px) le

module _ {a} {A : Set a} {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  data ○ {p} (P : Pred (A × A) p) : Pred (Market A) (p) where
    lift : ∀ {xs} → P (ε , xs) → ○ P (demand xs)

module _ {a} (A : Set a) {{r : RawSep A}} {u} {{s₁ : IsUnitalSep r u}} where

  open Morphism

  market : Morphism s₁ market-sep
  j market                 = demand
  j-map market s           = demand s
  j-⊎ market (demand σ)    = -, refl
  j-map⁻ market (demand σ) = σ

{- Completion preserving updates -}
module _ {a} {A : Set a} {{r : RawSep A}} {u} {{ s : IsUnitalSep r u }} where

  open import Relation.Unary.Separation.Construct.Product
  open Morphism (market A)

  record ⇥_ {p} (P : Pred (A × A) p) (Φᵢ : A × A) : Set (a ⊔ p) where
    field
      updater : ∀ {Φⱼ Φₖ as} →
                Φᵢ ⊎ Φⱼ ≣ Φₖ → Completion as Φₖ →
                ∃₂ λ Φₗ Φ → Φₗ ⊎ Φⱼ ≣ Φ × Completion as Φ × P Φₗ
  open ⇥_

  ●-update : ∀ {p q} {P : Pred (A × A) p} {Q : Pred (A × A) q} →
           ∀[ ○ (P ─✴ ⇥ Q) ⇒ ● P ─✴ ● Q ]
  app (●-update (lift f)) (lift px σ₁) (offerᵣ σ₂) with ⊎-assoc (⊎-comm σ₂) σ₁
  ... | _ , σ₃ , σ₄ with updater (app f px (⊎-idˡ , σ₄)) ⊎-idʳ σ₃
  ... | _ , _ , σ₅ , σ₆ , qx rewrite ⊎-id⁻ʳ σ₅ = lift qx σ₆
