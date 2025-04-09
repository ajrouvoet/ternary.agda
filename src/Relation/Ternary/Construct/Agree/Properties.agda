module Relation.Ternary.Construct.Agree.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Ternary.Core
open import Relation.Ternary.Morphisms
open import Function

{- Every injection induces a morphism between instances of Agree -}
module _ {a b} {A : Set a} {B : Set b} (𝑓 : A ↣ B) where

  import Relation.Ternary.Construct.Agree A as L
  import Relation.Ternary.Construct.Agree B as R
  open Injection 𝑓

  private
    j = λ a → Injection.to 𝑓 a

  f-morphism : SemigroupMorphism L.agreed-isSemigroup R.agreed-isSemigroup
  SemigroupMorphism.j f-morphism     = j
  SemigroupMorphism.jcong f-morphism = cong
  SemigroupMorphism.j-∙ f-morphism L.agreed = R.agreed
  SemigroupMorphism.j-∙⁻ f-morphism σ = lem σ refl refl
    where
      lem : ∀ {a b c a' b'} → R.Agree a b c → a ≡ j a' → b ≡ j b' → ∃ λ c' → L.Agree a' b' c' × c ≡ j c'
      lem R.agreed refl eqb =
        -, subst (λ b → L.Agree _ b _) (injective eqb) L.agreed , eqb
