open import Relation.Ternary.Core

open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≢_; _≡_)

module Relation.Ternary.Construct.Map {k v}
  (K : Set k)
  (V : K → Set v)
  (_≡ₖ?_ : Decidable (_≡_ {A = K}))
  (div : ∀ {k} → Rel₃ (V k)) where

open import Axiom.Extensionality.Propositional
open import Level
open import Function
open import Data.Unit hiding (_≤_)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All
open import Data.Maybe.Relation.Binary.Pointwise as M using (Pointwise; isEquivalence)
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent

open import Relation.Unary using (Pred)
open import Relation.Binary.Structures
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Structures.Syntax
open import Data.Empty using (⊥-elim)
open Pointwise

module _ {k} where
  open import Relation.Ternary.Construct.Add.Unit (div {k}) public

open import Relation.Ternary.Construct.Map.Map K V _≡ₖ?_

-- postulate funext : Extensionality k v

instance _ = ≡.isEquivalence
instance _ = div

variable
  m₁ m₂ m₃ m : Map

record Union (l r : Map) (m : Map) : Set (k ⊔ v) where
  constructor union
  field
    _[_] : ∀ k → (l [ k ]) ∙ (r [ k ]) ≣ (m [ k ])

instance
  maps : Rel₃ Map
  maps = record { _∙_≣_ = Union }

instance
  map-emptiness : Emptiness {A = Map} ∅
  map-emptiness = record {}

module _ {{sg : ∀ {k} → IsPartialSemigroup _≡_ (div {k})}} where
  instance
    map-isSemigroup : IsPartialSemigroup _≗_ maps
    IsPartialSemigroup.≈-equivalence map-isSemigroup = ≗-isEquivalence
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

    map-isMonoid : IsPartialMonoid _≗_ maps ∅
    IsPartialMonoid.isSemigroup map-isMonoid = map-isSemigroup
    IsPartialMonoid.∙-idˡ map-isMonoid  = union (λ k → ∙-idˡ)
    IsPartialMonoid.∙-idʳ map-isMonoid  = union (λ k → ∙-idʳ)
    IsPartialMonoid.∙-id⁻ˡ map-isMonoid (union ev) k = ∙-id⁻ˡ (ev k)
    IsPartialMonoid.∙-id⁻ʳ map-isMonoid (union ev) k = ∙-id⁻ʳ (ev k)

  infix 4 _≤ₘ_
  _≤ₘ_ : Map → Map → Set _
  m₁ ≤ₘ m₂ = ∀ k → m₁ [ k ] ≤ m₂ [ k ]

  ≤ₘ-min : Minimum _≤ₘ_ ∅
  ≤ₘ-min x k = -, ∙-idˡ

  instance ≤ₘ-isPreorder : IsPreorder _≗_ _≤ₘ_
  IsPreorder.isEquivalence ≤ₘ-isPreorder = ≗-isEquivalence
  IsPreorder.reflexive ≤ₘ-isPreorder eq k = ≤-reflexive (eq k)
  IsPreorder.trans ≤ₘ-isPreorder l₁ l₂ k  = ≤-trans (l₁ k) (l₂ k)

  module _ (≤-po : ∀ {k} → IsPartialOrder {A = V k} _≡_ _≤_) where

    instance ≤ₘ-isPartialOrder : IsPartialOrder _≗_ _≤ₘ_
    IsPartialOrder.isPreorder ≤ₘ-isPartialOrder = ≤ₘ-isPreorder
    IsPartialOrder.antisym ≤ₘ-isPartialOrder {i = i} {j} l₁ l₂ k with i [ k ] | j [ k ] | l₁ k | l₂ k
    ... | nothing | nothing | _ | _ = refl
    ... | just x  | just y  | l | n = IsPartialOrder.antisym (≤-isPartialOrder ≤-po) l n

  -- module _ {s} {{_ : ∀ {k} → IsNonNegative s _≡_ (div {k})}} where

  --   ε-split' : ∀ {Φ₁ Φ₂ : Map} → Union Φ₁ Φ₂ ∅ → Φ₁ ≡ ∅ × Φ₂ ≡ ∅
  --   ε-split' (union σs) = (funext λ k → ≡.cong proj₁ $ ε-split (σs k))
  --                       , (funext λ k → ≡.cong proj₂ $ ε-split (σs k))

  --   instance
  --     map-isNonNegative : IsNonNegative _ _≗_ maps
  --     IsNonNegative._≤ₐ_ map-isNonNegative = _≤ₘ_
  --     IsNonNegative.orderₐ map-isNonNegative = ≤ₘ-isPreorder

  --     IsNonNegative.nonNegativeˡ map-isNonNegative {Φ₁ = Φ₁} (union σs) k an with Φ₁ k | σs k
  --     IsNonNegative.nonNegativeˡ map-isNonNegative {Φ₁ = Φ₁} (union σs) k (just _) | just _ | σ with left-inv σ
  --     ... | _ , eq , τ = ≡.subst (Any _) (≡.sym eq) (just _)

  --     IsNonNegative.nonNegativeʳ map-isNonNegative {Φ₂ = Φ₂} (union σs) k an with Φ₂ k | σs k
  --     IsNonNegative.nonNegativeʳ map-isNonNegative {Φ₂ = Φ₂} (union σs) k (just _) | just _ | σ with right-inv σ
  --     ... | _ , eq , τ = ≡.subst (Any _) (≡.sym eq) (just _)

  --     map-isPositive : IsPositive _ _≗_ maps ∅
  --     IsPositive.isNonNegative map-isPositive = map-isNonNegative
  --     IsPositive.ε-least map-isPositive {Φ}   = ≤ₘ-min Φ
  --     IsPositive.ε-split map-isPositive σ     = ≡×≡⇒≡ (ε-split' σ)

module _
  {{_ : ∀ {k} → IsCommutative (div {k})}} where

  instance
    map-isCommutative : IsCommutative maps
    IsCommutative.∙-comm map-isCommutative (union m) = union λ k → ∙-comm (m k)

-- module _
--   {_&_ : ∀ {k} → V k → V k → V k}
--   {{_ : ∀ {k} → IsTotal _≡_ (div {k}) _&_}}
--   {{_ : ∀ {k} → IsCommutative (div {k})}}
--   {u} {{_ : ∀ {k} → IsCommutative (div {k})}} {{_ : ∀ {k} → IsPartialMonoid _≡_ (div {k}) u}}
--   where

--   instance
--     map-isTotal : IsTotal _≗_ maps λ m m' → (λ k → op (m k)  (m' k) )
--     IsTotal.∙-parallel map-isTotal (union m) (union n) = union (λ k → ∙-parallel (m k) (n k))

module _ where
  
  _↦_ : (k : K) → V k → Pred Map _
  (ℓ ↦ v) m = m ≗ [ ℓ ↦ v ]
