{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Data.Unit using (⊤)

module Relation.Ternary.Construct.Bag
  {ℓ} {A : Set ℓ} (div : Rel₃ A) 
  {e} {_≈_ : A → A → Set e} {{_ : IsCommutative div}} {{_ : IsPartialSemigroup _≈_ div}}
  (force : ⊤)
  where

open import Level
import Data.Nat as Nat
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties as Pm
open import Data.Nat.Properties
open import Data.List.Relation.Binary.Equality.DecPropositional

open import Relation.Nullary
open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Syntax

open import Relation.Ternary.Construct.List div
open import Relation.Ternary.Construct.List div public using (list-emptiness)

private
  variable
    xs ys zs : List A

record BagSplit (xs ys zs : List A) : Set ℓ where
  constructor hustle
  field
    {xs' ys' zs'} : _

    -- permutations
    ρx : xs' ↭ xs
    ρy : ys' ↭ ys
    ρz : zs' ↭ zs

    -- list separation
    sep : xs' ∙ ys' ≣ zs'

-- Split yields a separation algebra
instance bags : Rel₃ (List A)
Rel₃._∙_≣_ bags = BagSplit

^_ : xs ∙ ys ≣ zs → BagSplit xs ys zs
^ σ = hustle refl refl refl σ

module _ where

  -- commutativity follows immediately from commutativity of list separation
  instance bags-isCommutative : IsCommutative bags
  IsCommutative.∙-comm bags-isCommutative (hustle ρ₁ ρ₂ ρ₃ sep) = hustle ρ₂ ρ₁ ρ₃ (∙-comm sep)

  bags-isSemigroupˡ : IsPartialSemigroupˡ _↭_ bags

  IsPartialSemigroupˡ.≈-equivalence bags-isSemigroupˡ = ↭-isEquivalence

  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ bags-isSemigroupˡ) ρs (hustle bxs bys bzs sep) =
    hustle (↭-trans bxs ρs) bys bzs sep

  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ bags-isSemigroupˡ) ρzs (hustle bxs bys bzs sep) =
    hustle bxs bys (↭-trans bzs ρzs) sep

  -- Associativity holds because we can collect the permutations on the list ab
  -- and push them through σ₁, so that we can make use of the associativity of the underlying separation of lists
  -- to finish the proof.
  IsPartialSemigroupˡ.assocᵣ bags-isSemigroupˡ (hustle ρa ρb ρab σ₁) (hustle ρab' ρc ρabc σ₂) with ∙-↭ σ₁ (↭-trans ρab (↭-sym ρab'))
  ... | _ , ρ₁ , ρ₂ , σ₅ with ∙-assocᵣ σ₅ σ₂
  ... | _ , σ₃ , σ₄ = -, hustle (↭-trans ρ₁ ρa) ↭-refl ρabc σ₃ , hustle (↭-trans ρ₂ ρb) ρc ↭-refl σ₄

  instance empty-unique : IsUnique {A = List A} _↭_ []
  IsUnique.unique empty-unique eq rewrite ↭-empty-inv (↭-sym eq) = refl

  instance singleton-unique : ∀ {a} → IsUnique {A = List A} _↭_ [ a ]
  IsUnique.unique singleton-unique eq rewrite ↭-singleton-inv (↭-sym eq) = refl

  instance bags-isSemigroup : IsPartialSemigroup _↭_ bags
  bags-isSemigroup = IsPartialSemigroupˡ.semigroupˡ bags-isSemigroupˡ

  -- The identities follow almost immediately from the identity laws of list separation
  bags-isMonoidˡ : IsPartialMonoidˡ _↭_ bags []
  IsPartialMonoidˡ.identityˡ bags-isMonoidˡ = hustle ↭-refl ↭-refl ↭-refl ∙-idˡ
  IsPartialMonoidˡ.identity⁻ˡ bags-isMonoidˡ (hustle ρx ρy ρz σ) with ↭-empty-inv ρx
  ... | refl with ∙-id⁻ˡ σ
  ... | refl = ↭-trans (↭-sym ρy) ρz

  instance bags-isMonoid : IsPartialMonoid _↭_ bags []
  bags-isMonoid = IsPartialMonoidˡ.partialMonoidˡ bags-isMonoidˡ

  open import Data.Nat.SizeOf {A = List A} length as SizeOf
  
  -- Positivity follows by the positivity of list separation together 
  -- with the fact that permutations are length preserving
  instance bags-isPositive : IsPositive _ _↭_ bags

  IsPositive._≤ₐ_ bags-isPositive = SizeOf._≤ₐ_

  IsPositive.orderₐ bags-isPositive = size-pre ↭-isEquivalence ↭-length

  IsPositive.positiveˡ bags-isPositive (hustle ρx ρy ρz sep)
    rewrite sym (↭-length ρx) | sym (↭-length ρz) = positiveˡ sep
  IsPositive.positiveʳ bags-isPositive (hustle ρx ρy ρz sep)
    rewrite sym (↭-length ρy) | sym (↭-length ρz) = positiveʳ sep

  instance bags-isPositive-w/0 : IsPositiveWithZero _ _↭_ bags []
  IsPositiveWithZero.isPositive bags-isPositive-w/0 = bags-isPositive
  IsPositiveWithZero.ε-least bags-isPositive-w/0 = Nat.z≤n
  IsPositiveWithZero.ε-split bags-isPositive-w/0 (hustle ρx ρy ρz σ) with _ , ρx' , ρy' , σ′ ← ∙-↭ σ ρz with ε-split σ′
  ... | refl with refl ← ↭-empty-inv (↭-sym (↭-trans ρx' ρx))
                | refl ← ↭-empty-inv (↭-sym (↭-trans ρy' ρy)) = refl

  instance bags-isTotal : IsTotal _↭_ bags _++_
  IsTotal.∙-parallel bags-isTotal (hustle ρ₁ ρ₂ ρ₃ l) (hustle ρ₄ ρ₅ ρ₆ r) =
    hustle (Pm.++⁺ ρ₁ ρ₄) (Pm.++⁺ ρ₂ ρ₅) (Pm.++⁺ ρ₃ ρ₆) (∙-parallel l r)

module _ {{_ : IsContractive U div}} where

  instance bags-isContractive : IsContractive U bags
  IsContractive.∙-copy bags-isContractive {xs} tt = hustle ↭-refl ↭-refl ↭-refl (∙-copy tt)
