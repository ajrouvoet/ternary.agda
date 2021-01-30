{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.Add.Unit {a} {A : Set a} (div : Rel₃ A) where

open import Algebra
open import Data.Sum
open import Data.Maybe as Maybe
open import Data.Product
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as ≡ hiding (refl)
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Respect.Propositional

instance _ = div

module _ where

  data Split? : Maybe A → Maybe A → Maybe A → Set a where
    nothing  : Split? nothing nothing nothing
    right : ∀ {a} → Split? nothing (just a) (just a)
    left : ∀ {a} → Split? (just a) nothing (just a)
    split    : ∀ {a b ab} → a ∙ b ≣ ab → Split? (just a) (just b) (just ab)

  instance maybes : Rel₃ (Maybe A)
  Rel₃._∙_≣_ maybes = Split?

  right-inv : ∀ {a b c} → Split? a (just b) c → ∃ λ c' → c ≡ just c' × Split? a (just b) (just c')
  right-inv right     = -, ≡.refl , right
  right-inv (split x) = -, ≡.refl , split x

  left-inv : ∀ {a b c} → Split? (just b) a c → ∃ λ c' → c ≡ just c' × Split? (just b) a  (just c')
  left-inv left     = -, ≡.refl , left
  left-inv (split x) = -, ≡.refl , split x

  ≤-just-inv : ∀ {a b : A} → (just a) ≤ (just b) → a ≡ b ⊎ a ≤ b
  ≤-just-inv (.nothing , left)     = inj₁ ≡.refl
  ≤-just-inv (.(just _) , split x) = inj₂ (-, x)


module _ {{_ : IsPartialSemigroup _≡_ div}} where

  instance maybe-semigroup : IsPartialSemigroup _≡_ maybes

  IsPartialSemigroup.≈-equivalence maybe-semigroup = isEquivalence

  IsPartialSemigroup.∙-assocᵣ maybe-semigroup right left  = -, right , left
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup left left  = -, left , nothing
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup (split x) left = -, split x , left
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup right (split x) = -, right , split x
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup left (split x) = -, split x , right
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup (split x₁) (split x)
    with _ , x₂ , x₃ ← ∙-assocᵣ x₁ x                             = -, split x₂ , split x₃
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup nothing nothing    = -, nothing , nothing
  IsPartialSemigroup.∙-assocᵣ maybe-semigroup nothing right   = -, right , right

  IsPartialSemigroup.∙-assocₗ maybe-semigroup nothing nothing = -, nothing , nothing
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right right     = -, nothing , right
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right left      = -, right , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup right (split x) = -, right , split x
  IsPartialSemigroup.∙-assocₗ maybe-semigroup left nothing    = -, left , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) right = -, left , split x
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) left  = -, split x , left
  IsPartialSemigroup.∙-assocₗ maybe-semigroup (split x) (split x₁)
    with _ , x₃ , x₂ ← ∙-assocₗ x x₁                          = -, split x₃ , split x₂

  instance maybe-monoid : IsPartialMonoid _≡_ maybes nothing
  IsPartialMonoid.emptiness maybe-monoid            = record {}
  IsPartialMonoid.∙-idˡ maybe-monoid {nothing}      = nothing
  IsPartialMonoid.∙-idˡ maybe-monoid {just x}       = right
  IsPartialMonoid.∙-idʳ maybe-monoid {nothing}      = nothing
  IsPartialMonoid.∙-idʳ maybe-monoid {just x}       = left
  IsPartialMonoid.∙-id⁻ˡ maybe-monoid nothing = ≡.refl
  IsPartialMonoid.∙-id⁻ˡ maybe-monoid right   = ≡.refl
  IsPartialMonoid.∙-id⁻ʳ maybe-monoid nothing = ≡.refl
  IsPartialMonoid.∙-id⁻ʳ maybe-monoid left    = ≡.refl

  module _ (≤-po : IsPartialOrder {A = A} _≡_ _≤_) where

    open IsPartialOrder
    ≤-isPartialOrder : IsPartialOrder {A = Maybe A}  _≡_ _≤_
    IsPartialOrder.isPreorder ≤-isPartialOrder = ≤-isPreorder
    antisym ≤-isPartialOrder (._ , nothing) (._ , nothing) = ≡.refl
    antisym ≤-isPartialOrder (._ , left) _                 = ≡.refl
    antisym ≤-isPartialOrder (._ , split x) (._ , left)    = ≡.refl
    antisym ≤-isPartialOrder (._ , split x) (._ , split y) =
      ≡.cong just (IsPartialOrder.antisym ≤-po (-, x) (-, y))

module _ {{_ : IsCommutative div}} where

  instance maybe-comm : IsCommutative maybes
  IsCommutative.∙-comm maybe-comm nothing   = nothing
  IsCommutative.∙-comm maybe-comm right     = left
  IsCommutative.∙-comm maybe-comm left      = right
  IsCommutative.∙-comm maybe-comm (split x) = split (∙-comm x)

module _ {s} {{nn : IsPositive s _≡_ div}} where

  open import Relation.Binary.Construct.Add.Infimum.NonStrict _≤ₐ_
  open IsPreorder orderₐ

  -- instance maybe-nonNegative : IsPositive _ _≡_ maybes
  -- IsNonNegative._≤ₐ_ maybe-nonNegative = _≤₋_
  -- IsNonNegative.orderₐ maybe-nonNegative = ≤₋-isPreorder-≡ orderₐ

  -- IsNonNegative.nonNegativeˡ maybe-nonNegative nothing   = ⊥₋≤ _
  -- IsNonNegative.nonNegativeˡ maybe-nonNegative right     = ≤₋-minimum _
  -- IsNonNegative.nonNegativeˡ maybe-nonNegative left      = [ refl ]
  -- IsNonNegative.nonNegativeˡ maybe-nonNegative (split x) = [ nonNegativeˡ x ]
  -- IsNonNegative.nonNegativeʳ maybe-nonNegative nothing   = ⊥₋≤ _
  -- IsNonNegative.nonNegativeʳ maybe-nonNegative right     = [ refl ]
  -- IsNonNegative.nonNegativeʳ maybe-nonNegative left      = ≤₋-minimum _
  -- IsNonNegative.nonNegativeʳ maybe-nonNegative (split x) = [ nonNegativeʳ x ]

  -- instance maybe-positive : IsPositive _ _≡_ maybes nothing
  -- IsPositive.isNonNegative maybe-positive   = maybe-nonNegative
  -- IsPositive.ε-least maybe-positive {Φ}     = ≤₋-minimum Φ
  -- IsPositive.ε-split maybe-positive nothing = ≡.refl

module _ {_++_}
  {{_ : IsTotal div _++_}}
  {u} {{_ : IsCommutative div}} {{_ : IsPartialMonoid _≡_ div u}}
  {{_ : IsMonoid _≡_ _++_ u}} where

  op : Maybe A → Maybe A → Maybe A
  op nothing nothing = nothing
  op nothing (just x) = just x
  op (just x) nothing = just x
  op (just x) (just x₁) = just (x ++ x₁)

  instance maybe-total : IsTotal maybes op
  IsTotal.∙-parallel maybe-total nothing nothing = nothing
  IsTotal.∙-parallel maybe-total nothing right = right
  IsTotal.∙-parallel maybe-total nothing left = left
  IsTotal.∙-parallel maybe-total nothing (split x) = split x
  IsTotal.∙-parallel maybe-total right nothing = right
  IsTotal.∙-parallel maybe-total right right = right
  IsTotal.∙-parallel maybe-total right left = split (∙-comm ∙-disjoint)
  IsTotal.∙-parallel maybe-total right (split x) = split (∙-disjointᵣₗ x)
  IsTotal.∙-parallel maybe-total left nothing = left
  IsTotal.∙-parallel maybe-total left right = split ∙-disjoint
  IsTotal.∙-parallel maybe-total left left = left
  IsTotal.∙-parallel maybe-total left (split x) = split (∙-disjointₗₗ x)
  IsTotal.∙-parallel maybe-total (split x) nothing = split x
  IsTotal.∙-parallel maybe-total (split x) right = split (∙-disjointᵣᵣ x)
  IsTotal.∙-parallel maybe-total (split x) left = split (∙-disjointₗᵣ x)
  IsTotal.∙-parallel maybe-total (split x) (split x₁) = split (∙-parallel x x₁)
