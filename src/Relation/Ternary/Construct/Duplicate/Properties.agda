module Relation.Ternary.Construct.Duplicate.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Ternary.Core
open import Relation.Ternary.Morphisms
open import Function

{- Every injection induces a morphism between instances of Duplicate -}
module _ {a b} {A : Set a} {B : Set b} (𝑓 : A ↣ B) where

  import Relation.Ternary.Construct.Duplicate A as L
  import Relation.Ternary.Construct.Duplicate B as R
  open Injection 𝑓

  private
    j = λ a → f a

  f-morphism : SemigroupMorphism L.dup-isSemigroup R.dup-isSemigroup
  SemigroupMorphism.j f-morphism     = j
  SemigroupMorphism.jcong f-morphism = cong 
  SemigroupMorphism.j-∙ f-morphism L.dup = R.dup
  SemigroupMorphism.j-∙⁻ f-morphism σ = lem σ refl refl
    where
      lem : ∀ {a b c a' b'} → R.Dup a b c → a ≡ j a' → b ≡ j b' → ∃ λ c' → L.Dup a' b' c' × c ≡ j c'
      lem R.dup refl eqb =
        -, subst (λ b → L.Dup _ b _) (injective eqb) L.dup , eqb
