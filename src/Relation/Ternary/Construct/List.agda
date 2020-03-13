{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.List {a} {A : Set a} (division : Rel₃ A) where

open import Level
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Properties using (++-isMonoid; ++-identityʳ)
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional

open import Algebra.Structures using (IsMonoid)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (refl; _≡_; isEquivalence; cong)
open import Relation.Ternary.Structures
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Structures.Syntax hiding (≤-refl; ≤-trans)

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
    assocᵣ σ₁ (consʳ σ₂) =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ₂ in -, consʳ σ₄ , consʳ σ₅
    assocᵣ (consˡ σ₁) (divide τ σ₂) =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ₂ in -, divide τ σ₄ , consʳ σ₅
    assocᵣ (consʳ σ₁) (divide τ σ₂)  =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ₂ in -, consʳ σ₄ , divide τ σ₅
    assocᵣ (divide τ σ₁) (consˡ σ) =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ in -, divide τ σ₄ , consˡ σ₅
    assocᵣ (consˡ σ₁) (consˡ σ)  =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ in -, consˡ σ₄ , σ₅
    assocᵣ (consʳ σ₁) (consˡ σ) =
      let _ , σ₄ , σ₅ = assocᵣ σ₁ σ in -, consʳ σ₄ , consˡ σ₅
    assocᵣ (divide lr σ₁) (divide rl σ₂) =
      let _ , σ₃ , σ₄ = assocᵣ σ₁ σ₂
          _ , τ₃ , τ₄ = ∙-assocᵣ lr rl in -, divide τ₃ σ₃ , divide τ₄ σ₄
    assocᵣ [] [] = -, [] , []

    assocₗ : LeftAssoc splits
    assocₗ (divide x σ₁) (divide y σ₂) =
      let _ , σ₃ , σ₄  = assocₗ σ₁ σ₂
          _ , x' , y' = ∙-assocₗ x y in -, divide x' σ₃ , divide y' σ₄
    assocₗ (divide x σ₁) (consˡ σ₂) =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, divide x σ₃ , consˡ σ₄
    assocₗ (divide x σ₁) (consʳ σ₂) =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, consˡ σ₃ , divide x σ₄
    assocₗ (consˡ σ₁) σ₂ =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, consˡ σ₃ , consˡ σ₄
    assocₗ (consʳ σ₁) (divide x σ₂) =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, consʳ σ₃ , divide x σ₄
    assocₗ (consʳ σ₁) (consˡ σ₂) =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, consʳ σ₃ , consˡ σ₄
    assocₗ (consʳ σ₁) (consʳ σ₂) =
      let _ , σ₃ , σ₄ = assocₗ σ₁ σ₂ in -, σ₃ , consʳ σ₄
    assocₗ [] [] = -, [] , []

  {- Semigroup instance -}
  instance list-isSemigroup : IsPartialSemigroup _≡_ splits
  IsPartialSemigroup.≈-equivalence list-isSemigroup = isEquivalence
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ list-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ list-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ list-isSemigroup) refl σ = σ
  IsPartialSemigroup.∙-assocᵣ list-isSemigroup = assocᵣ
  IsPartialSemigroup.∙-assocₗ list-isSemigroup = assocₗ

module _ {{_ : IsCommutative division}} where

  private
    comm : Commutative splits
    comm (divide τ σ) = divide (∙-comm τ) (comm σ)
    comm (consˡ σ)    = consʳ  (comm σ)
    comm (consʳ σ)    = consˡ  (comm σ)
    comm []           = []

  instance list-isComm : IsCommutative splits
  IsCommutative.∙-comm list-isComm = comm

module _ where
  open import Data.Nat.SizeOf {A = List A} length as SizeOf
  open import Data.Nat.Properties
  open import Data.List.Relation.Binary.Equality.DecPropositional

  instance list-positive : IsPositive _ _≡_ splits []
  IsPositive._≤ₐ_ list-positive = SizeOf._≤ₐ_

  IsPositive.is-empty list-positive []       = yes refl
  IsPositive.is-empty list-positive (x ∷ xs) = no (λ ())

  IsPositive.orderₐ list-positive = size-pre isEquivalence (λ where refl → refl)

  IsPositive.positiveˡ list-positive = posˡ
    where
      posˡ : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Φ₁ SizeOf.≤ₐ Φ
      posˡ (divide x σ) = Nat.s≤s (posˡ σ)
      posˡ (consˡ σ)    = Nat.s≤s (posˡ σ)
      posˡ (consʳ σ)    = ≤-step (posˡ σ)
      posˡ []           = ≤-refl

  IsPositive.positiveʳ list-positive = posʳ
    where
      posʳ : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Φ₂ SizeOf.≤ₐ Φ
      posʳ (divide x σ) = Nat.s≤s (posʳ σ)
      posʳ (consˡ σ)    = ≤-step (posʳ σ)
      posʳ (consʳ σ)    = Nat.s≤s (posʳ σ)
      posʳ []           = ≤-refl

  IsPositive.ε-least list-positive {[]} Nat.z≤n = refl

module _ {e} {_≈_ : A → A → Set e} {{_ : IsPartialSemigroup _≈_ division}} where

  instance list-isMonoid : IsPartialMonoid _≡_ splits []
  IsPartialMonoid.ε-unique list-isMonoid refl = refl
  IsPartialMonoid.∙-idˡ list-isMonoid {Φ}     = idˡ Φ
    where
      idˡ : ∀ Φ → Split [] Φ Φ
      idˡ []      = []
      idˡ (x ∷ Φ) = consʳ (idˡ Φ) 
  IsPartialMonoid.∙-idʳ list-isMonoid {Φ} = idʳ Φ
    where
      idʳ : ∀ Φ → Split Φ [] Φ
      idʳ []      = []
      idʳ (x ∷ Φ) = consˡ (idʳ Φ)
  IsPartialMonoid.∙-id⁻ˡ list-isMonoid = id⁻ˡ
    where
      id⁻ˡ : ∀ {Φ₁ Φ₂} → Split [] Φ₁ Φ₂ → Φ₁ ≡ Φ₂
      id⁻ˡ []        = refl
      id⁻ˡ (consʳ σ) = cong (_ ∷_) (id⁻ˡ σ)
  IsPartialMonoid.∙-id⁻ʳ list-isMonoid = id⁻ʳ
    where
      id⁻ʳ : ∀ {Φ₁ Φ₂} → Split Φ₁ [] Φ₂ → Φ₁ ≡ Φ₂
      id⁻ʳ []        = refl
      id⁻ʳ (consˡ σ) = cong (_ ∷_) (id⁻ʳ σ)

  instance list-isTotal : IsTotal _≡_ splits _++_
  IsTotal.∙-parallel list-isTotal = par
    where
      par : ∀ {a b c d ab cd} → Split a b ab → Split c d cd → Split (a ++ c) (b ++ d) (ab ++ cd)
      par [] σ₂ = σ₂
      par (divide x σ₁) σ₂ = divide x (par σ₁ σ₂)
      par (consˡ σ₁) σ₂ = consˡ (par σ₁ σ₂)
      par (consʳ σ₁) σ₂ = consʳ (par σ₁ σ₂)

module _ {{_ : IsIntuitionistic U division}} where

  instance list-isIntuitionistic : IsIntuitionistic U splits
  IsIntuitionistic.∙-copy list-isIntuitionistic {xs} = copies xs
    where
      copies : ∀ (xs : List A) → xs ∙ xs ≣ xs
      copies [] = []
      copies (x ∷ xs) = divide ∙-copy (copies xs)

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
  ... | _ , h₃ , h₄ , σ₃ = _ , smart-trans h₃ h₁ , smart-trans h₄ h₂ , σ₃
