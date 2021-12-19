{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Morphisms where

open import Level
open import Relation.Unary
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality as P hiding (J)
open import Data.Product
open import Function using (_∘_)

open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Function.Definitions

module _
  {a b e₁ e₂}
  {A : Set a} {B : Set b}
  {_≈a_ : A → A → Set e₁}
  {_≈b_ : B → B → Set e₂}
  {ra : Rel₃ A} {rb : Rel₃ B}
  where

  private instance _ = ra
  private instance _ = rb

  record SemigroupMorphism
    (m₁ : IsPartialSemigroup _≈a_ ra)
    (m₂ : IsPartialSemigroup _≈b_ rb): Set (a ⊔ b ⊔ suc (e₁ ⊔ e₂)) where

    field
      j       : A → B
      jcong   : Congruent _≈a_ _≈b_ j
      j-∙     : ∀ {Φ₁ Φ₂ Φ} → Φ₁ ∙ Φ₂ ≣ Φ     → j Φ₁ ∙ j Φ₂ ≣ j Φ
      j-∙⁻    : ∀ {Φ₁ Φ₂ Φ} → j Φ₁ ∙ j Φ₂ ≣ Φ → ∃ λ Φ′ → Φ₁ ∙ Φ₂ ≣ Φ′ × Φ ≡ j Φ′

    infixr 8 _⇒ⱼ_
    _⇒ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred A _
    P ⇒ⱼ Q = P ⇒ (Q ∘ j)

    infixr 8 _─✴ⱼ_
    _─✴ⱼ_ : ∀ {p q} → Pred A p → Pred B q → Pred B _
    P ─✴ⱼ Q = P ─✴[ j ] Q

    module _ where

      data J {p} (P : Pred A p) : Pred B (a ⊔ p ⊔ b) where
        inj : ∀ {Φ} → P Φ → J P (j Φ)

      j-zip : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J P ⇒ J Q ─✴ J (P ✴ Q) ]
      j-zip (inj px) ⟨ σ ⟩ (inj qx) with j-∙⁻ σ
      ... | _ , τ , refl = inj (px ∙⟨ τ ⟩ qx)

      j-unzip : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ J (P ✴ Q) ⇒ J P ✴ J Q ]
      j-unzip (inj (p ∙⟨ σ ⟩ q)) = inj p ∙⟨ j-∙ σ ⟩ inj q

      jmap : ∀ {p q} {P : Pred A p} {Q : Pred A q} → ∀[ (P ─✴ Q) ⇒ⱼ (J P ─✴ J Q) ]
      jmap f ⟨ σ ⟩ (inj px) with _ , τ , refl ← j-∙⁻ σ = inj (f ⟨ τ ⟩ px)

      J⁻ : ∀ {p} (P : Pred B p) → Pred A p
      J⁻ P Φ = P (j Φ)

  record MonoidMorphism {εa εb}
    (m₁ : IsPartialMonoid _≈a_ ra εa)
    (m₂ : IsPartialMonoid _≈b_ rb εb): Set (a ⊔ b ⊔ suc (e₁ ⊔ e₂)) where

    private module M₁ = IsPartialMonoid m₁
    private module M₂ = IsPartialMonoid m₂

    field
      semigroupMorphism : SemigroupMorphism M₁.isSemigroup M₂.isSemigroup

    open SemigroupMorphism semigroupMorphism public

    field
      j-ε : j εa ≈b εb

{- identity morphism -}
module _ {a e} {A : Set a} {{r : Rel₃ A}}
  {_≈_ : A → A → Set e} {u} {{m : IsPartialMonoid _≈_ r u}} where

  open import Function

  instance id-morph : MonoidMorphism m m
  id-morph = record
    { semigroupMorphism = record
      { j      = id
      ; jcong  = id
      ; j-∙    = id
      ; j-∙⁻   = λ x → -, x , P.refl }
      ; j-ε    = ≈-refl
    }
