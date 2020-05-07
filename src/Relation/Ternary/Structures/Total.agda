{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Structures.Total {ℓ} {A : Set ℓ} where

open import Level
open import Function using (_∘_)
open import Algebra

open import Relation.Unary hiding (Empty)
open import Relation.Binary.Structures
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Relation.Ternary.Core
open import Relation.Ternary.Structures.PartialSemigroup
open import Relation.Ternary.Structures.PartialMonoid
open import Relation.Ternary.Structures.Intuitionistic

open IsPartialMonoid    {{...}}
open IsPartialSemigroup {{...}}
open IsIntuitionistic   {{...}}
open Emptiness          {{...}}

-- Being a total proof-relevant relation means that there is always at least one way
-- to put two arbitrary elements together.
record IsTotal {ℓe} (_≈_ : A → A → Set ℓe) (rel : Rel₃ A) (_++_ : A → A → A) : Set (suc ℓ ⊔ ℓe) where
  open Rel₃ rel

  field
    ∙-parallel  : ∀ {a b c d ab cd}
                → a ∙ b ≣ ab
                → c ∙ d ≣ cd
                → (a ++ c) ∙ (b ++ d) ≣ (ab ++ cd)

  -- If the relation is monoidal, we get some useful biased variations.
  module _ {unit} {{m : IsMonoid _≈_ _++_ unit}} {{p : IsPartialMonoid _≈_ rel unit}} where

    private
      variable
        a b c d e : A

    open IsMonoid {{...}} 

    ∙-disjointₗₗ : a ∙ b ≣ Φ → (e ++ a) ∙ b ≣ (e ++ Φ)
    ∙-disjointₗₗ σ with z ← ∙-parallel ∙-idʳ σ = coe (identityˡ _) z

    ∙-disjointₗᵣ : a ∙ b ≣ Φ → (a ++ e) ∙ b ≣ (Φ ++ e)
    ∙-disjointₗᵣ σ with z ← ∙-parallel σ ∙-idʳ = coe (identityʳ _) z 

    ∙-disjointᵣₗ : a ∙ b ≣ c → a ∙ (e ++ b) ≣ (e ++ c)
    ∙-disjointᵣₗ σ with z ← ∙-parallel ∙-idˡ σ = coe (identityˡ _) z

    ∙-disjointᵣᵣ : a ∙ b ≣ c → a ∙ (b ++ e) ≣ (c ++ e)
    ∙-disjointᵣᵣ σ with z ← ∙-parallel σ ∙-idˡ = coe (identityʳ _) z

    ∙-disjoint : a ∙ b ≣ (a ++ b)
    ∙-disjoint with z ← ∙-parallel ∙-idʳ ∙-idˡ =
      coe (identityʳ _) (coe {{∙-respects-≈ʳ}} (identityˡ _) z)

    pair : ∀ {p q} {P : Pred A p} {Q : Pred A q} {a b} → P a → Q b → (P ✴ Q) (a ++ b)
    pair px qx = px ∙⟨ ∙-disjoint ⟩ qx


    -- If in addition (!) the relation is contractible,
    -- we can add a part with a whole and get the whole again.
    module _ {c} {C : Pred A c} {{i : IsIntuitionistic C rel}} where

      subₗ : (_ : C a) → a ∙ (a ++ b) ≣ (a ++ b)
      subₗ c = ∙-disjointᵣᵣ (∙-copy c)

      subᵣ : (_ : C b) → b ∙ (a ++ b) ≣ (a ++ b)
      subᵣ c with z ← ∙-parallel ∙-idˡ (∙-copy c) = coe (identityˡ _) z

open IsTotal {{...}} public
