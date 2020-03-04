{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.List.Interdivide {a} {A : Set a} (division : Rel₃ A) where

open import Level
open import Algebra.Structures using (IsMonoid)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Properties using (++-isMonoid; ++-identityʳ)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional
open import Relation.Binary.PropositionalEquality using (refl; _≡_; isEquivalence; cong)
open import Relation.Ternary.Structures hiding (≤-refl)
open import Relation.Ternary.Respect.Propositional
import Data.Nat as Nat

open import Relation.Unary hiding (_∈_; _⊢_)

private
  instance sep-instance = division
  Carrier = List A
  variable
    xˡ xʳ x y z : A
    xsˡ xsʳ xs ys zs : Carrier

module _ where

  data Split : (xs ys zs : Carrier) → Set a where
    divide   : xˡ ∙ xʳ ≣ x → Split xs ys zs → Split (xˡ ∷ xs) (xʳ ∷ ys) (x ∷ zs)
    consˡ    : Split xs ys zs → Split (z ∷ xs) ys (z ∷ zs)
    consʳ    : Split xs ys zs → Split xs (z ∷ ys) (z ∷ zs)
    []       : Split [] [] []

  -- Split yields a separation algebra
  instance splits : Rel₃ Carrier
  Rel₃._∙_≣_ splits = Split

  instance list-emptiness : Emptiness {A = List A} []
  list-emptiness = record {}

module _ {e} {_≈_ : A → A → Set e} {{_ : IsPartialSemigroup _≈_ division}} where

  private
    assocᵣ : RightAssoc splits
    assocᵣ σ₁ (consʳ σ₂) with assocᵣ σ₁ σ₂
    ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , consʳ σ₅
    assocᵣ (consˡ σ₁) (divide τ σ₂) with assocᵣ σ₁ σ₂
    ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , consʳ σ₅
    assocᵣ (consʳ σ₁) (divide τ σ₂)  with assocᵣ σ₁ σ₂
    ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , divide τ σ₅
    assocᵣ (divide τ σ₁) (consˡ σ) with assocᵣ σ₁ σ
    ... | _ , σ₄ , σ₅ = -, divide τ σ₄ , consˡ σ₅
    assocᵣ (consˡ σ₁) (consˡ σ)  with assocᵣ σ₁ σ
    ... | _ , σ₄ , σ₅ = -, consˡ σ₄ , σ₅
    assocᵣ (consʳ σ₁) (consˡ σ) with assocᵣ σ₁ σ
    ... | _ , σ₄ , σ₅ = -, consʳ σ₄ , consˡ σ₅
    assocᵣ [] [] = -, [] , []
    assocᵣ (divide lr σ₁) (divide rl σ₂) with assocᵣ σ₁ σ₂ | ∙-assocᵣ lr rl
    ... | _ , σ₃ , σ₄ | _ , τ₃ , τ₄ = -, divide τ₃ σ₃ , divide τ₄ σ₄

    assocₗ : LeftAssoc splits
    assocₗ (divide x σ₁) (divide y σ₂) with assocₗ σ₁ σ₂ | ∙-assocₗ x y
    ... | _ , σ₃ , σ₄ | _ , x' , y' = -, divide x' σ₃ , divide y' σ₄
    assocₗ (divide x σ₁) (consˡ σ₂) with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, divide x σ₃ , consˡ σ₄
    assocₗ (divide x σ₁) (consʳ σ₂) with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, consˡ σ₃ , divide x σ₄
    assocₗ (consˡ σ₁) σ₂ with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, consˡ σ₃ , consˡ σ₄
    assocₗ (consʳ σ₁) (divide x σ₂) with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, consʳ σ₃ , divide x σ₄
    assocₗ (consʳ σ₁) (consˡ σ₂) with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, consʳ σ₃ , consˡ σ₄
    assocₗ (consʳ σ₁) (consʳ σ₂) with assocₗ σ₁ σ₂
    ... | _ , σ₃ , σ₄ = -, σ₃ , consʳ σ₄
    assocₗ [] [] = -, [] , []

  instance split-isSemigroup : IsPartialSemigroup _≡_ splits

  IsPartialSemigroup.≈-equivalence split-isSemigroup = isEquivalence
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ split-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ split-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ split-isSemigroup) refl σ = σ

  -- reassociates
  IsPartialSemigroup.∙-assocᵣ split-isSemigroup = assocᵣ
  IsPartialSemigroup.∙-assocₗ split-isSemigroup = assocₗ

module _ {{_ : IsCommutative division}} where

  instance split-isComm : IsCommutative splits
  IsCommutative.∙-comm split-isComm (divide τ σ) = divide (∙-comm τ) (∙-comm σ)
  IsCommutative.∙-comm split-isComm (consˡ σ)  = consʳ (∙-comm σ)
  IsCommutative.∙-comm split-isComm (consʳ σ) = consˡ (∙-comm σ)
  IsCommutative.∙-comm split-isComm [] = []

module _ where
  open import Data.Nat.SizeOf {A = List A} length as SizeOf
  open import Data.Nat.Properties
  open import Data.List.Relation.Binary.Equality.DecPropositional
  open import Relation.Nullary

  instance split-positive : IsPositive _ _≡_ splits []
  IsPositive._≤ₐ_ split-positive = SizeOf._≤ₐ_

  IsPositive.is-empty split-positive []       = yes refl
  IsPositive.is-empty split-positive (x ∷ xs) = no (λ ())

  IsPositive.orderₐ split-positive = size-pre isEquivalence (λ where refl → refl)

  IsPositive.positiveˡ split-positive (divide x σ) = Nat.s≤s (positiveˡ σ)
  IsPositive.positiveˡ split-positive (consˡ σ)    = Nat.s≤s (positiveˡ σ)
  IsPositive.positiveˡ split-positive (consʳ σ)    = ≤-step (positiveˡ σ)
  IsPositive.positiveˡ split-positive []           = ≤-refl

  IsPositive.positiveʳ split-positive (divide x σ) = Nat.s≤s (positiveʳ σ)
  IsPositive.positiveʳ split-positive (consˡ σ)    = ≤-step (positiveʳ σ)
  IsPositive.positiveʳ split-positive (consʳ σ)    = Nat.s≤s (positiveʳ σ)
  IsPositive.positiveʳ split-positive []           = ≤-refl

  IsPositive.ε-least split-positive {[]} Nat.z≤n = refl

module _ {e} {_≈_ : A → A → Set e} {{_ : IsPartialSemigroup _≈_ division}} where

  instance split-isMonoid : IsPartialMonoid _≡_ splits []

  IsPartialMonoid.∙-idˡ split-isMonoid {[]} = []
  IsPartialMonoid.∙-idˡ split-isMonoid {x ∷ Φ} = consʳ ∙-idˡ 

  IsPartialMonoid.∙-idʳ split-isMonoid {[]} = []
  IsPartialMonoid.∙-idʳ split-isMonoid {x ∷ Φ} = consˡ ∙-idʳ

  IsPartialMonoid.ε-unique split-isMonoid refl = refl

  IsPartialMonoid.∙-id⁻ˡ split-isMonoid (consʳ σ) = cong (_ ∷_) (∙-id⁻ˡ σ)
  IsPartialMonoid.∙-id⁻ˡ split-isMonoid []        = refl

  IsPartialMonoid.∙-id⁻ʳ split-isMonoid (consˡ σ) = cong (_ ∷_) (∙-id⁻ʳ σ)
  IsPartialMonoid.∙-id⁻ʳ split-isMonoid []        = refl

  instance split-isTotal : IsTotal _≡_ splits _++_
  IsTotal.∙-parallel split-isTotal [] σ₂ = σ₂
  IsTotal.∙-parallel split-isTotal (divide x σ₁) σ₂ = divide x (∙-parallel σ₁ σ₂)
  IsTotal.∙-parallel split-isTotal (consˡ σ₁) σ₂ = consˡ (∙-parallel σ₁ σ₂)
  IsTotal.∙-parallel split-isTotal (consʳ σ₁) σ₂ = consʳ (∙-parallel σ₁ σ₂)


{- We need this instance to be around for the isTotal operations -}
instance list-monoid : ∀ {a} {A : Set a} → IsMonoid {A = List A} _≡_ _++_ []
list-monoid = ++-isMonoid

{- We can push permutation through separation. -}
module _ where

  ∙-↭ : xsˡ ∙ xsʳ ≣ xs → xs ↭ ys →
           Σ[ yss ∈ Carrier × Carrier ]
           let (ysˡ , ysʳ) = yss in
           ysˡ ↭ xsˡ × ysʳ ↭ xsʳ × ysˡ ∙ ysʳ ≣ ys
  -- refl
  ∙-↭ σ refl = _ , ↭-refl , ↭-refl , σ

  -- prep
  ∙-↭ (consˡ σ) (prep x ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep x h₁ , h₂ , consˡ σ'
  ∙-↭ (consʳ σ) (prep x ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, h₁ , prep x h₂ , consʳ σ'
  ∙-↭ (divide τ σ) (prep x ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , divide τ σ'

  -- swap
  -- todo, cleanup this proof?
  ∙-↭ (consˡ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, swap y x h₁ , h₂ , consˡ (consˡ σ')
  ∙-↭ (consˡ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , consʳ (consˡ σ')
  ∙-↭ (consˡ (divide τ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ'  = -, swap _ _ h₁ , prep _ h₂ , divide τ (consˡ σ')
  ∙-↭ (consʳ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , prep _ h₂ , consˡ (consʳ σ')
  ∙-↭ (consʳ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, h₁ , swap y x h₂ , consʳ (consʳ σ')
  ∙-↭ (consʳ (divide τ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , swap _ _ h₂ , divide τ (consʳ σ') 
  ∙-↭ (divide τ (consˡ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, swap _ _ h₁ , prep _ h₂ , consˡ (divide τ σ')
  ∙-↭ (divide τ (consʳ σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, prep _ h₁ , swap _ _ h₂ , consʳ (divide τ σ')
  ∙-↭ (divide τ (divide τ' σ)) (swap x y ρ) with ∙-↭ σ ρ
  ... | _ , h₁ , h₂ , σ' = -, swap _ _ h₁ , swap _ _ h₂ , divide τ' (divide τ σ')

  -- trans
  ∙-↭ σ (trans ρ₁ ρ₂) with ∙-↭ σ ρ₁
  ... | _ , h₁ , h₂ , σ₂ with ∙-↭ σ₂ ρ₂
  ... | _ , h₃ , h₄ , σ₃ = _ , trans h₃ h₁ , trans h₄ h₂ , σ₃
