{-# OPTIONS --safe #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.Bag {ℓ} {A : Set ℓ} (div : Rel₃ A) where

open import Level
import Data.Nat as Nat
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Nat.Properties
open import Data.List.Relation.Binary.Equality.DecPropositional

open import Relation.Nullary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

open import Relation.Ternary.Construct.List.Interdivide div

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

module _ {e} {_≈_ : A → A → Set e} {{_ : IsCommutative div}} {{_ : IsPartialSemigroup _≈_ div}} where

  -- commutativity follows immediately from commutativity of list separation
  instance comm : IsCommutative bags
  IsCommutative.∙-comm comm (hustle ρ₁ ρ₂ ρ₃ sep) = hustle ρ₂ ρ₁ ρ₃ (∙-comm sep)

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

  instance bags-isSemigroup : IsPartialSemigroup _↭_ bags
  bags-isSemigroup = IsPartialSemigroupˡ.semigroupˡ bags-isSemigroupˡ

  -- The identities follow almost immediately from the identity laws of list separation
  bags-monoidˡ : IsPartialMonoidˡ _↭_ bags []
  IsPartialMonoidˡ.ε-uniq bags-monoidˡ ρ = sym (↭-[] (↭-sym ρ))
  IsPartialMonoidˡ.identityˡ bags-monoidˡ = hustle ↭-refl ↭-refl ↭-refl ∙-idˡ
  IsPartialMonoidˡ.identity⁻ˡ bags-monoidˡ (hustle ρx ρy ρz σ) with ↭-[] ρx
  ... | refl with ∙-id⁻ˡ σ
  ... | refl = ↭-trans (↭-sym ρy) ρz

  instance bags-monoid : IsPartialMonoid _↭_ bags []
  bags-monoid = IsPartialMonoidˡ.partialMonoidˡ bags-monoidˡ

  open import Data.Nat.SizeOf {A = List A} length as SizeOf
  
  -- Positivity follows by the positivity of list separation together 
  -- with the fact that permutations are length preserving
  instance bags-positive : IsPositive _ _↭_ bags []

  IsPositive._≤ₐ_ bags-positive = SizeOf._≤ₐ_

  IsPositive.is-empty bags-positive []      = yes refl
  IsPositive.is-empty bags-positive (x ∷ σ) = no ¬∷↭[]

  IsPositive.orderₐ bags-positive = size-pre ↭-isEquivalence ↭-length

  IsPositive.positiveˡ bags-positive (hustle ρx ρy ρz sep) rewrite sym (↭-length ρx) | sym (↭-length ρz) = positiveˡ sep
  IsPositive.positiveʳ bags-positive (hustle ρx ρy ρz sep) rewrite sym (↭-length ρy) | sym (↭-length ρz) = positiveʳ sep

  IsPositive.ε-least bags-positive {[]} Nat.z≤n = ↭-refl