{-# OPTIONS --safe --overlapping-instances #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Construct.List.Interdivide
  {a e} (A : Set a) 
  {division : Rel₃ A}
  {_≈_ : A → A → Set e}
  (_ : IsCommutativeSemigroup _≈_ division)
  where

open import Level
open import Algebra.Structures using (IsMonoid)
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Inductive
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Ternary.Structures

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

  instance split-comm : IsCommutative splits
  IsCommutative.∙-comm split-comm (divide τ σ) = divide (∙-comm τ) (∙-comm σ)
  IsCommutative.∙-comm split-comm (consˡ σ)  = consʳ (∙-comm σ)
  IsCommutative.∙-comm split-comm (consʳ σ) = consˡ (∙-comm σ)
  IsCommutative.∙-comm split-comm [] = []

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

  instance split-is-semigroupˡ : IsPartialSemigroupˡ _≡_ splits

  IsPartialSemigroupˡ.≈-equivalence split-is-semigroupˡ = isEquivalence
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ split-is-semigroupˡ) refl σ = σ
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ split-is-semigroupˡ) refl σ = σ

  -- reassociates
  IsPartialSemigroupˡ.assocᵣ split-is-semigroupˡ = assocᵣ

  instance split-is-semigroup : IsPartialSemigroup _≡_ splits
  split-is-semigroup = IsPartialSemigroupˡ.semigroupˡ split-is-semigroupˡ

  split-is-monoidˡ : IsPartialMonoidˡ _≡_ splits []

  IsPartialMonoidˡ.identityˡ split-is-monoidˡ {[]} = []
  IsPartialMonoidˡ.identityˡ split-is-monoidˡ {x ∷ Φ} = consʳ (IsPartialMonoidˡ.identityˡ split-is-monoidˡ)

  IsPartialMonoidˡ.ε-uniq split-is-monoidˡ refl = refl

  IsPartialMonoidˡ.identity⁻ˡ split-is-monoidˡ (consʳ σ) = cong (_ ∷_) (IsPartialMonoidˡ.identity⁻ˡ split-is-monoidˡ σ)
  IsPartialMonoidˡ.identity⁻ˡ split-is-monoidˡ []        = refl

  instance split-is-monoid : IsPartialMonoid _≡_ splits []
  split-is-monoid = IsPartialMonoidˡ.partialMonoidˡ split-is-monoidˡ

--     split-has-concat : HasConcat _≡_ splits
--     HasConcat._∙_ split-has-concat = _++_
--     HasConcat.∙-∙ₗ split-has-concat {Φₑ = []} σ = σ
--     HasConcat.∙-∙ₗ split-has-concat {Φₑ = x ∷ Φₑ} σ = consˡ (∙-∙ₗ σ) 

--     list-positive : IsPositive _≡_ splits []
--     list-positive = record
--       { ∙-εˡ = λ where [] → refl }

--     list-monoid : ∀ {a} {A : Set a} → IsMonoid {A = List A} _≡_ _++_ []
--     list-monoid = ++-isMonoid
