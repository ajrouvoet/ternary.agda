module Relation.Ternary.Construct.Empty.Properties where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Morphisms
open import Function

{- Every function induces a morphism between instances of Empty -}
module _ {a b} {A : Set a} {B : Set b} (f : A → B) where

  import Relation.Ternary.Construct.Empty A as L
  import Relation.Ternary.Construct.Empty B as R

  ⊥-morphism : SemigroupMorphism L.empty-semigroup R.empty-semigroup
  SemigroupMorphism.j ⊥-morphism     = f
  SemigroupMorphism.jcong ⊥-morphism = cong f
  SemigroupMorphism.j-∙ ⊥-morphism ()
  SemigroupMorphism.j-∙⁻ ⊥-morphism ()
