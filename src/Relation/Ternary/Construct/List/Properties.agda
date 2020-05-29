{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.List.Properties {ℓ} {A : Set ℓ} where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List as List hiding (_∷ʳ_)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Nullary
open import Relation.Unary hiding (_⊆_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Morphisms

module _
  {e} {_≈_ : A → A → Set e}
  {{div : Rel₃ A}} {{_ : IsPartialSemigroup _≈_ div}} {{_ : IsCommutative div}}
  (no-div : ∀ {x y xy : A} → ¬ (x ∙ y ≣ xy)) where

  open import Relation.Ternary.Construct.List div

  ↭-∙ˡ : ∀ {xsˡ xsʳ ysˡ xs} → xsˡ ∙ xsʳ ≣ xs → xsˡ ↭ ysˡ → Σ[ ys ∈ List A ] ys ↭ xs × (ysˡ ∙ xsʳ ≣ ys)
  ↭-∙ˡ [] ρ = -, ↭-sym ρ , ∙-idʳ
  ↭-∙ˡ (consʳ σ) ρ with ↭-∙ˡ σ ρ
  ... | _ , ρ′ , σ′ = -, prep _ ρ′ , consʳ σ′

  ↭-∙ˡ (consˡ σ) refl = -, refl , consˡ σ
  ↭-∙ˡ (consˡ σ) (prep x ρ) with ↭-∙ˡ σ ρ
  ... | _ , ρ′ , σ′ = -, prep _ ρ′ , consˡ σ′
  ↭-∙ˡ (consˡ (consˡ σ)) (swap x y ρ) with ↭-∙ˡ σ ρ
  ... | _ , ρ′ , σ′ = -, swap _ _ ρ′ , consˡ (consˡ σ′)
  ↭-∙ˡ (consˡ (consʳ σ)) ρ@(swap _ _ _) with ↭-∙ˡ (consˡ σ) ρ
  ... | _ , ρ′ , σ′ = -, ↭-trans (prep _ ρ′) (swap _ _ ↭-refl) , consʳ σ′
  ↭-∙ˡ (consˡ (divide x _)) (swap _ _ _) with no-div x
  ... | ()

  ↭-∙ˡ σ@(consˡ _) (_↭_.trans ρ₁ ρ₂) with ↭-∙ˡ σ ρ₁
  ... | _ , ρ₃ , σ′ with ↭-∙ˡ σ′ ρ₂
  ... | _ , ρ₄ , σ′′ = -, ↭-trans ρ₄ ρ₃ , σ′′

  ↭-∙ˡ (divide x σ) ρ with no-div x
  ... | ()

  ↭-∙ʳ : ∀ {xsˡ xsʳ xs ysʳ} → xsˡ ∙ xsʳ ≣ xs → xsʳ ↭ ysʳ → Σ[ ys ∈ _ ] ys ↭ xs × (xsˡ ∙ ysʳ ≣ ys)
  ↭-∙ʳ σ ρ with ↭-∙ˡ (∙-comm σ) ρ
  ... | _ , ρ′ , σ′ = -, ρ′ , ∙-comm σ′

  ↭-∙ : ∀ {xsˡ xsʳ xs ysˡ ysʳ} → xsˡ ∙ xsʳ ≣ xs → xsˡ ↭ ysˡ → xsʳ ↭ ysʳ → Σ[ ys ∈ _ ] ys ↭ xs × (ysˡ ∙ ysʳ ≣ ys)
  ↭-∙ σ ρ₁ ρ₂ with ↭-∙ˡ σ ρ₁
  ... | _ , ρ₃ , σ₂ with ↭-∙ʳ σ₂ ρ₂
  ... | _ , ρ₄ , σ₃ = -, ↭-trans ρ₄ ρ₃ , σ₃

module ListXSplit
  (div₁ : Rel₃ A) (div₂ : Rel₃ A)
  {e} {_≈₁_ : A → A → Set e} {_≈₂_ : A → A → Set e}
  {{_ : IsCommutative div₁}} {{_ : IsPartialSemigroup _≈₁_ div₁}}
  {{_ : IsCommutative div₂}} {{_ : IsPartialSemigroup _≈₂_ div₂}}
  (xsplitₐ : CrossSplit div₁ div₂)
  where

  open import Relation.Ternary.Construct.List div₁ as L
  open import Relation.Ternary.Construct.List div₂ as R
  open Rel₃ div₁ using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
  open Rel₃ div₂ using () renaming (_∙_≣_ to _∙ₐ₂_≣_)
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

  module _ (no-div₂ : ∀ {x y xy} → ¬ (x ∙ₐ₂ y ≣ xy)) where
    private
      data Resplit x (xs ys zs : List A) : Set ℓ where
        left    : ∀ {zs'}
                → (x ∷ zs') ↭ zs
                → (xs ∙₂ ys ≣ zs')
                → Resplit x xs ys zs

      lemma : ∀ {x} {xs ys zs : List A} → (x ∷ xs) ∙₂ ys ≣ zs → Resplit x xs ys zs
      lemma (consˡ σ)    = left    ↭-refl σ
      lemma (consʳ σ) with lemma σ
      ... | left ρ σ' = left (↭-trans (swap _ _ ↭-refl) (prep _ ρ)) (R.consʳ σ')
      lemma (divide x σ) with no-div₂ x
      ... | ()

    {- A weaker version of uncross, that permits permutations as the leaves -}
    unxross : ∀ {a b c d ac ad bc bd}
      → ac ∙₁ ad ≣ a → bc ∙₁ bd ≣ b → ac ∙₂ bc ≣ c → ad ∙₂ bd ≣ d
      → Σ[ as ∈ List A × List A × List A × List A × List A ]
        let a' , b' , c' , d' , z = as
        in a ↭ a' × b ↭ b' × c ↭ c' × d ↭ d'
          × a' ∙₂ b' ≣ z
          × c' ∙₁ d' ≣ z

    unxross [] σ₂ σ₃ σ₄ rewrite ∙-id⁻ˡ σ₃ | ∙-id⁻ˡ σ₄ =
      -, ↭-refl , ↭-refl , ↭-refl , ↭-refl , ∙-idˡ , σ₂

    unxross (consˡ σ₁) σ₂ σ₃ σ₄ with lemma σ₃
    ... | left ρ σ₃′ with unxross σ₁ σ₂ σ₃′ σ₄
    ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
      -, prep _ ρ₁ , ρ₂  , ↭-trans (↭-sym ρ) (prep _ ρ₃) , ρ₄ , R.consˡ τ₁ , L.consˡ τ₂

    unxross (divide x σ₁) σ₂ σ₃ σ₄ with lemma σ₃ | lemma σ₄
    ... | left ρ σ₃′ | left ρ′ σ₄′ with unxross σ₁ σ₂ σ₃′ σ₄′
    ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
      -, prep _ ρ₁ , ρ₂ , ↭-trans (↭-sym ρ) (prep _ ρ₃) , ↭-trans (↭-sym ρ′) (prep _ ρ₄) , R.consˡ τ₁ , L.divide x τ₂

    unxross (consʳ σ₁) σ₂ σ₃ σ₄ with lemma σ₄
    ... | left ρ σ₄′ with unxross σ₁ σ₂ σ₃ σ₄′
    ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
      -, prep _ ρ₁ , ρ₂  , ρ₃ , ↭-trans (↭-sym ρ) (prep _ ρ₄) , R.consˡ τ₁ , L.consʳ τ₂

module _ {{div : Rel₃ A}} {p} {P : Pred A p} (divP : ∀ {a b c} → a ∙ b ≣ c → P c → P a × P b) where

  open import Relation.Ternary.Construct.List div
  open import Data.List.Relation.Unary.All

  splitAll : ∀ {xs ys zs} → xs ∙ ys ≣ zs → All P zs → All P xs × All P ys
  splitAll (divide x σ) (z ∷ zs)
    with xs , ys ← splitAll σ zs
       | z₁ , z₂ ← divP x z = z₁ ∷ xs , z₂ ∷ ys
  splitAll (consˡ σ) (z ∷ zs) with xs , ys ← splitAll σ zs = z ∷ xs , ys
  splitAll (consʳ σ) (z ∷ zs) with xs , ys ← splitAll σ zs = xs , z ∷ ys
  splitAll [] []              = [] , []

module _ {{div : Rel₃ A}} {p} {P : Pred A p} (joinP : ∀ {a b c} → a ∙ b ≣ c → P a → P b → P c) where

  open import Relation.Ternary.Construct.List div
  open import Data.List.Relation.Unary.All

  joinAll : ∀ {xs ys zs} → xs ∙ ys ≣ zs → All P xs → All P ys → All P zs
  joinAll [] _ _                             = []
  joinAll (divide x σ) (px ∷ pxs) (py ∷ pys) = joinP x px py ∷ joinAll σ pxs pys
  joinAll (consˡ σ) (px ∷ pxs) pys           = px ∷ joinAll σ pxs pys
  joinAll (consʳ σ) pxs (py ∷ pys)           = py ∷ joinAll σ pxs pys


-- Every monoid morphism between element divisions, induces a monoid morphism between
-- list divisions
module _ {b} {B : Set b}
  {div₁ : Rel₃ A} {div₂ : Rel₃ B}
  {e₁ e₂} {_≈₁_ : A → A → Set e₁} {_≈₂_ : B → B → Set e₂}
  {{ma : IsPartialSemigroup _≈₁_ div₁}} {{mb : IsPartialSemigroup _≈₂_ div₂}}
  (𝑚 : SemigroupMorphism ma mb)
  where

  import Relation.Ternary.Construct.List div₁ as L
  import Relation.Ternary.Construct.List div₂ as R
  open SemigroupMorphism 𝑚
  open L

  private
    j' = List.map j

    lem⁺ : ∀ {xs ys zs} → L.Split xs ys zs → R.Split (j' xs) (j' ys) (j' zs)
    lem⁺ (divide x σ) = R.divide (j-∙ x) (lem⁺ σ )
    lem⁺ (consˡ σ)    = R.consˡ (lem⁺ σ)
    lem⁺ (consʳ σ)    = R.consʳ (lem⁺ σ)
    lem⁺ []           = R.[]

    lem⁻ : ∀ {xs ys zs} → (R.Split (j' xs) (j' ys) zs) → ∃ λ zs' → L.Split xs ys zs' × zs ≡ j' zs'
    lem⁻ {[]} {[]} {[]} [] = -, [] , refl
    lem⁻ {[]} {x₁ ∷ ys} {._ ∷ zs} (consʳ σ)         with _ , τ , refl ← lem⁻ σ = -, consʳ τ , refl
    lem⁻ {x₁ ∷ xs} {[]} {._ ∷ zs} (consˡ σ)         with _ , τ , refl ← lem⁻ σ = -, consˡ τ , refl
    lem⁻ {x₁ ∷ xs} {x₂ ∷ ys} {x ∷ zs} (divide x₃ σ) with _ , τ , refl ← lem⁻ σ | _ , x' , refl ← j-∙⁻ x₃ =
      -, divide x' τ , refl
    lem⁻ {x₁ ∷ xs} {x₂ ∷ ys} {._ ∷ zs} (consˡ σ)    with _ , τ , refl ← lem⁻ σ = -, consˡ τ , refl
    lem⁻ {x₁ ∷ xs} {x₂ ∷ ys} {._ ∷ zs} (consʳ σ)    with _ , τ , refl ← lem⁻ σ = -, consʳ τ , refl

  open MonoidMorphism

  listMap : MonoidMorphism L.list-isMonoid R.list-isMonoid
  SemigroupMorphism.j (semigroupMorphism listMap)     = j'
  SemigroupMorphism.jcong (semigroupMorphism listMap) = cong j'
  SemigroupMorphism.j-∙ (semigroupMorphism listMap)   = lem⁺
  SemigroupMorphism.j-∙⁻ (semigroupMorphism listMap)  = lem⁻
  j-ε listMap  = refl
