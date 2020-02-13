{-# OPTIONS #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Construct.List.Intermuted
  {a} (A : Set a)
  (division : Rel₃ A)
  where

open import Level
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Properties using (++-isMonoid)
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Empty

open import Relation.Unary hiding (_∈_; _⊢_)

private 
  Carrier = List A
  variable
    xsˡ xsʳ xs ys ysˡ ysʳ zs xxs yys : Carrier

open import Relation.Ternary.Construct.List.Interdivide division
open Rel₃ splits renaming (_∙_≣_ to _∘_≣_)

module _ where
  {- An inductive definition of xs ++ ys ↭ zs -}
  data Hustle : ∀ (l r : Carrier) → Carrier → Set a where
    hustle : (h₁ : xsˡ ↭ ysˡ) → (h₂ : xsʳ ↭ ysʳ) → (σ₁ : ysˡ ∙ ysʳ ≣ ys) → Hustle xsˡ xsʳ ys

  instance hustler : Rel₃ Carrier
  hustler = record { _∙_≣_ = Hustle }

{- Permutations commute with interleavings -}
module _ where

  {- We can push permutation through separation. -}
  ∙-↭ : xsˡ ∘ xsʳ ≣ xs → xs ↭ ys →
           Σ[ yss ∈ Carrier × Carrier ]
           let (ysˡ , ysʳ) = yss in
           ysˡ ↭ xsˡ × ysʳ ↭ xsʳ × ysˡ ∘ ysʳ ≣ ys
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

{- Hustle is a separation logic -}
module _
  {e} {_≈_ : A → A → Set e}
  {{csg : IsPartialSemigroup  _≈_ division}}
  {{cc  : IsCommutative division}}
  where

  instance comm : IsCommutative hustler
  IsCommutative.∙-comm comm (hustle h₁ h₂ σ) = hustle h₂ h₁ (∙-comm σ)

  hustle-is-semigroupˡ : IsPartialSemigroupˡ _↭_ hustler
  IsPartialSemigroupˡ.≈-equivalence hustle-is-semigroupˡ = ↭-isEquivalence
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ hustle-is-semigroupˡ) eq (hustle x₁ x₂ σ) = hustle (trans (↭-sym eq) x₁) x₂ σ
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ hustle-is-semigroupˡ) eq (hustle x₁ x₂ σ) with ∙-↭ σ eq
  ... | _ , h₁ , h₂ , σ' = hustle (trans x₁ (↭-sym h₁)) (trans x₂ (↭-sym h₂)) σ'
  IsPartialSemigroupˡ.comm  hustle-is-semigroupˡ = comm
  IsPartialSemigroupˡ.assocᵣ hustle-is-semigroupˡ (hustle h₁₁ h₁₂ σ₁) (hustle h₂₁ h₂₂ σ₂) with ∙-↭ σ₁ h₂₁
  ... | _ , h₃ , h₄ , σ₃ with ∙-assocᵣ σ₃ σ₂
  ... | _ , σ₄ , σ₅ = -, hustle (trans h₁₁ (↭-sym h₃)) refl σ₄ , hustle (trans h₁₂ (↭-sym h₄)) h₂₂ σ₅

  instance hustle-is-semigroup : IsPartialSemigroup _↭_ hustler
  hustle-is-semigroup = IsPartialSemigroupˡ.semigroupˡ hustle-is-semigroupˡ
  
  hustle-is-monoidˡ : IsPartialMonoidˡ _↭_ hustler []
  IsPartialMonoidˡ.identityˡ hustle-is-monoidˡ = hustle refl refl ∙-idˡ
  IsPartialMonoidˡ.ε-uniq hustle-is-monoidˡ x = sym (↭-[] (↭-sym x))
  IsPartialMonoidˡ.identity⁻ˡ hustle-is-monoidˡ (hustle h₁ h₂ σ₁) with ↭-[] (↭-sym h₁)
  ... | refl with ∙-id⁻ˡ σ₁
  ... | refl = h₂

  instance hustle-is-monoid : IsPartialMonoid _↭_ hustler []
  hustle-is-monoid = IsPartialMonoidˡ.partialMonoidˡ hustle-is-monoidˡ

module _
  {e} {_≈_ : A → A → Set e}
  {{csg : IsPartialSemigroup  _≈_ division}}
  {{cc  : IsCommutative division}}
  where
  open import Data.List.Extra
  open import Data.Nat.SizeOf {A = List A} length ↭-isEquivalence ↭-length as SizeOf
  open import Data.Nat.Properties
  open import Relation.Binary.Structures
  open import Data.List.Relation.Binary.Equality.DecPropositional
  open import Relation.Nullary

  instance hustle-positive : IsPositive _ _↭_ hustler []
  IsPositive._≤ₐ_ hustle-positive = SizeOf._≤ₐ_

  IsPositive.is-empty hustle-positive []       = yes refl
  IsPositive.is-empty hustle-positive (x ∷ xs) = no ¬∷↭[]

  IsPositive.orderₐ hustle-positive = size-pre

  IsPositive.positiveˡ hustle-positive  {Φ = Φ} (hustle h₁ h₂ σ₁) =
    IsPreorder.∼-respˡ-≈ SizeOf.size-pre {y = Φ} (↭-sym h₁) (positiveˡ σ₁)

  IsPositive.positiveʳ hustle-positive {Φ = Φ} (hustle h₁ h₂ σ₁) =
    IsPreorder.∼-respˡ-≈ SizeOf.size-pre {y = Φ} (↭-sym h₂) (positiveʳ σ₁)

  IsPositive.ε-least hustle-positive {[]} le = refl

  postulate instance hustle-has-cross : IsCrosssplittable _↭_ hustler
  -- Cr⁺.cross hustle-has-cross⁺ (hustle σ₁ h₁) (hustle σ₂ h₂) with ∙-↭ σ₁ (trans h₁ (↭-sym h₂))
  -- ... | _ , h₃ , h₄ , σ₃ with ∙-cross σ₃ σ₂
  -- ... | _ , τ₁ , τ₂ , τ₃ , τ₄ = -, hustle τ₁ h₃ , hustle τ₂ h₄ , hustle τ₃ refl , hustle τ₄ refl

  -- Cr⁻.uncross hustle-has-cross⁻ {a} {b} {c} {d} {ac} {ad} {bc} {bd} σ₁ σ₂ σ₃ σ₄ =
  --   -, hustle ∙-∙ refl
  --    , hustle ∙-∙ (
  --      let ρ₁ = ⟦ σ₁ ⟧; ρ₂ = ⟦ σ₂ ⟧
  --          ρ₃ = ⟦ σ₃ ⟧; ρ₄ = ⟦ σ₄ ⟧ 
  --          a++b = ++⁺ ρ₁ ρ₂
  --          c++d = ++⁺ ρ₃ ρ₄
  --          q = trans a++b (↭-sym (++-assoc (ac ++ ad) bc bd)) 
  --          r = trans q (++⁺ʳ bd (trans (++-assoc ac ad bc) (++⁺ˡ ac (++-comm ad bc))) )
  --          s = trans r (++-assoc ac (bc ++ ad) bd)
  --          t = trans s (++⁺ˡ ac (++-assoc bc ad bd))
  --          u = trans t (↭-sym (++-assoc ac bc (ad ++ bd)))
  --      in trans c++d (↭-sym u)
  --    )
