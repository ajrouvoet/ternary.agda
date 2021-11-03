open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Construct.Associationlist
  (K : Set)
  (V : K → Set)
  (div : ∀ {k} → Rel₃ (V k))
  where

open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All

open import Relation.Binary.Structures
open import Relation.Ternary.Structures.Syntax

open Σ renaming (proj₁ to key; proj₂ to val)

private
  instance _ = div

  Assoc   = Σ K V

  variable
    k₁ k₂ k : K
    v₁ v₂ v : V k
    e₁ e₂ e₃ e : Assoc

Assoclist = List Assoc

data AssocUnion : (e₁ e₂ e : Assoc) → Set where
  assocUnion : v₁ ∙ v₂ ≣ v → AssocUnion (k , v₁) (k , v₂) (k , v)

instance entries : Rel₃ Assoc
Rel₃._∙_≣_ entries  = AssocUnion

module _
  {e} {_≈_ : ∀ {k} → V k → V k → Set e}
  {{_ : ∀ {k} → IsEquivalence (_≈_ {k})}} where
  data _≈ₑ_ : Assoc → Assoc → Set e where
    eqe : v₁ ≈ v₂ → (k , v₁) ≈ₑ (k , v₂)

  instance
    ≈ₑ-isEquivalence : IsEquivalence _≈ₑ_
    IsEquivalence.refl ≈ₑ-isEquivalence                  = eqe ≈-refl
    IsEquivalence.sym ≈ₑ-isEquivalence (eqe x)           = eqe (≈-sym x)
    IsEquivalence.trans ≈ₑ-isEquivalence (eqe x) (eqe y) = eqe (≈-trans x y)

module _ {e} {_≈_ : ∀ {k} → V k → V k → Set e}
  {{_ : ∀ {k} → IsEquivalence (_≈_ {k})}}
  {{_ : ∀ {k} → IsPartialSemigroup _≈_ (div {k})}} where
  instance
    assocUnion-respect : Respect _≈ₑ_ (e₁ ∙ e₂)
    Respect.coe assocUnion-respect (eqe eq) (assocUnion x) = assocUnion (coe {{∙-respects-≈}} eq x)

    assocUnion-respectˡ : Respect _≈ₑ_ (_∙ e₂ ≣ e₃)
    Respect.coe assocUnion-respectˡ (eqe eq) (assocUnion x) = assocUnion (coe {{∙-respects-≈ˡ}} eq x)

    assocUnion-respectʳ : Respect _≈ₑ_ (e₁ ∙_≣ e₃)
    Respect.coe assocUnion-respectʳ (eqe eq) (assocUnion x) = assocUnion (coe {{∙-respects-≈ʳ}} eq x)

    entries-isSemigroup : IsPartialSemigroup _≈ₑ_ entries
    IsPartialSemigroup.∙-assocᵣ entries-isSemigroup (assocUnion σ₁) (assocUnion σ₂) 
      with _ , σ₃ , σ₄ ← ∙-assocᵣ σ₁ σ₂ = _ , assocUnion σ₃ , assocUnion σ₄
    IsPartialSemigroup.∙-assocₗ entries-isSemigroup (assocUnion σ₁) (assocUnion σ₂) 
      with _ , σ₃ , σ₄ ← ∙-assocₗ σ₁ σ₂ = _ , assocUnion σ₃ , assocUnion σ₄

module _ {{_ : ∀ {k} → IsCommutative (div {k})}} where
  instance
    entries-isCommutative : IsCommutative entries
    IsCommutative.∙-comm entries-isCommutative (assocUnion x) = assocUnion (∙-comm x)

{- Multimaps are bags of entries -}
module _
  {e} {_≈_ : ∀ {k} → V k → V k → Set e}
  {{_ : ∀ {k} → IsEquivalence (_≈_ {k})}}
  {{_ : ∀ {k} → IsPartialSemigroup _≈_ (div {k})}}
  {{_ : ∀ {k} → IsCommutative (div {k})}}
  where
  open import Relation.Ternary.Construct.Bag entries _ as L
