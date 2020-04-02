{-# OPTIONS --without-K #-}
module Relation.Ternary.Construct.Map {k v} (K : Set k) (V : K → Set v) where

open import Axiom.Extensionality.Propositional
open import Level
open import Function
open import Data.Maybe
open import Data.Maybe.Relation.Binary.Pointwise as M using (Pointwise; isEquivalence)
open import Data.Product

open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_)
open import Relation.Ternary.Structures.Syntax
open import Data.Empty using (⊥-elim)
open Pointwise

postulate funext : Extensionality k v

Entry  = λ k → Maybe (V k)
Map = (k : K) → Entry k

_∉_ : K → Map → Set v
k ∉ m = m k ≡ nothing

module _ {e} (_≈v_ : ∀ {k} → Entry k → Entry k → Set e) where

  _≈_ : Map → Map → Set (e ⊔ k)
  m₁ ≈ m₂ = ∀ k → (m₁ k ) ≈v (m₂ k)

module _
  {e} {_≈v_ : ∀ {k} → Entry k → Entry k → Set e}
  {{eq : ∀ {k} → IsEquivalence (_≈v_ {k})}} where
  module Eq {k} = IsEquivalence (eq {k})

  instance ≈-isEquivalence : IsEquivalence (_≈_ _≈v_)
  IsEquivalence.refl ≈-isEquivalence k          = Eq.refl
  IsEquivalence.sym ≈-isEquivalence  eq k       = Eq.sym (eq k)
  IsEquivalence.trans ≈-isEquivalence eq₁ eq₂ k = Eq.trans (eq₁ k) (eq₂ k)

variable
  m₁ m₂ m₃ m : Map

empty-map : Map
empty-map = λ k → nothing

module _ {{div : ∀ {k} → Rel₃ (Entry k)}} where
  record Union (l r : Map) (m : Map) : Set (k ⊔ v) where
    constructor union
    field
      unions : ∀ k → (l k) ∙ (r k) ≣ (m k)

  maps : Rel₃ Map
  maps = record { _∙_≣_ = Union }

instance
  map-emptiness : Emptiness {A = Map} empty-map
  map-emptiness = record {}

module _
  {{div : ∀ {k} → Rel₃ (Entry k)}}
  {e} {_≈v_ : ∀ {k} → Entry k → Entry k → Set e}
  {{sg : ∀ {k} → IsPartialSemigroup (_≈v_ {k}) div}} where

  instance
    map-isSemigroup : IsPartialSemigroup (_≈_ _≈v_) maps
    IsPartialSemigroup.≈-equivalence map-isSemigroup = ≈-isEquivalence {{IsPartialSemigroup.≈-equivalence sg}}
    Respect.coe (IsPartialSemigroup.∙-respects-≈ map-isSemigroup) {x} {y} eq (union v) =
      union (λ k → coe {{∙-respects-≈}} (eq k) (v k))
    Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ map-isSemigroup) {x} {y} eq (union v) =
      union (λ k → coe {{∙-respects-≈ˡ}} (eq k) (v k))
    Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ map-isSemigroup) {x} {y} eq (union v) =
      union (λ k → coe {{∙-respects-≈ʳ}} (eq k) (v k))
    IsPartialSemigroup.∙-assocᵣ map-isSemigroup (union σs₁) (union σs₂) =
      -, union (λ k → let _ , σ₂ , σ₃ = ∙-assocᵣ (σs₁ k) (σs₂ k) in σ₂)
       , union (λ k → let _ , σ₂ , σ₃ = ∙-assocᵣ (σs₁ k) (σs₂ k) in σ₃)
    IsPartialSemigroup.∙-assocₗ map-isSemigroup (union σs₁) (union σs₂) =
      -, union (λ k → let _ , σ₂ , σ₃ = ∙-assocₗ (σs₁ k) (σs₂ k) in σ₂)
       , union (λ k → let _ , σ₂ , σ₃ = ∙-assocₗ (σs₁ k) (σs₂ k) in σ₃)

module _
  {{div : ∀ {k} → Rel₃ (Entry k)}}
  {e} {_≈v_ : ∀ {k} → Entry k → Entry k → Set e}
  {{sg : ∀ {k} → IsCommutative (div {k})}} where

  instance
    map-isCommutative : IsCommutative maps
    IsCommutative.∙-comm map-isCommutative (union m) = union λ k → ∙-comm (m k)

module _
  {{div : ∀ {k} → Rel₃ (Entry k)}}
  {e} {_≈v_ : ∀ {k} → Entry k → Entry k → Set e}
  {{mon : ∀ {k} → IsPartialMonoid (_≈v_ {k}) div nothing}} where

  instance
    map-isMonoid : IsPartialMonoid (_≈_ _≈v_) maps empty-map
    IsPartialMonoid.isSemigroup map-isMonoid = map-isSemigroup {{sg = IsPartialMonoid.isSemigroup mon}}
    IsPartialMonoid.ε-unique map-isMonoid e = funext λ k → ε-unique (e k)
    IsPartialMonoid.∙-idˡ map-isMonoid  = union (λ k → ∙-idˡ)
    IsPartialMonoid.∙-idʳ map-isMonoid  = union (λ k → ∙-idʳ)
    IsPartialMonoid.∙-id⁻ˡ map-isMonoid (union ev) k = ∙-id⁻ˡ (ev k)
    IsPartialMonoid.∙-id⁻ʳ map-isMonoid (union ev) k = ∙-id⁻ʳ (ev k)

module _
  {{div : ∀ {k} → Rel₃ (Entry k)}}
  {e} {_≈v_ : ∀ {k} → Entry k → Entry k → Set e}
  {_&_ : ∀ {k} → Entry k → Entry k → Entry k} {{_ : ∀ {k} → IsTotal (_≈v_ {k}) div _&_}} where

  instance
    map-isTotal : IsTotal (_≈_ _≈v_) maps λ m m' → (λ k → m k & m' k )
    IsTotal.∙-parallel map-isTotal (union m) (union n) = union (λ k → ∙-parallel (m k) (n k))
