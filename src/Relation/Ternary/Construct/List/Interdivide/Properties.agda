module Relation.Ternary.Construct.List.Interdivide.Properties {ℓ} {A : Set ℓ} where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module ListXSplit
  (div₁ : Rel₃ A) (div₂ : Rel₃ A)
  {e} {_≈_ : A → A → Set e}
  {{_ : IsCommutative div₁}} {{_ : IsPartialSemigroup _≈_ div₁}}
  {{_ : IsCommutative div₂}} {{_ : IsPartialSemigroup _≈_ div₂}}
  (xsplitₐ : CrossSplit div₁ div₂)
  where

  open import Relation.Ternary.Construct.List.Interdivide div₁ as L
  open import Relation.Ternary.Construct.List.Interdivide div₂ as R
  open Rel₃ L.splits using () renaming (_∙_≣_ to _∙₁_≣_)
  open Rel₃ R.splits using () renaming (_∙_≣_ to _∙₂_≣_)
  
  xsplit : CrossSplit L.splits R.splits

  xsplit [] σ₂ with ε-split σ₂
  ... | refl = -, ∙-idˡ , ∙-idˡ , ∙-idˡ , ∙-idˡ

  xsplit (divide x σ₁) (divide y σ₂) with xsplit σ₁ σ₂ | xsplitₐ x y
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ | _ , xy₁₁ , xy₁₂ , xy₂₁ , xy₂₂ =
    -, R.divide xy₁₁ σ₃ , R.divide xy₁₂ σ₄ , L.divide xy₂₁ σ₅ , L.divide xy₂₂ σ₆

  xsplit (divide x σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consˡ σ₃ , R.consˡ σ₄ , L.divide x σ₅ , σ₆
  xsplit (divide x σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consʳ σ₃ , R.consʳ σ₄ , σ₅ , L.divide x σ₆

  xsplit (consˡ σ₁) (divide x σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.divide x σ₃ , σ₄ , L.consˡ σ₅ , L.consˡ σ₆
  xsplit (consˡ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consˡ σ₃ , σ₄ , L.consˡ σ₅ , σ₆
  xsplit (consˡ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consʳ σ₃ , σ₄ , σ₅ , L.consˡ σ₆
  
  xsplit (consʳ σ₁) (divide x σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.divide x σ₄ , L.consʳ σ₅ , L.consʳ σ₆
  xsplit (consʳ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.consˡ σ₄ , L.consʳ σ₅ , σ₆
  xsplit (consʳ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
  ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.consʳ σ₄ , σ₅ , L.consʳ σ₆
