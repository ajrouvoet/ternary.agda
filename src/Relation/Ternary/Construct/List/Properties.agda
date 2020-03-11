module Relation.Ternary.Construct.List.Properties {ℓ} {A : Set ℓ} where

open import Level
open import Data.Unit using (⊤)
open import Data.Product hiding (swap)
open import Data.List
open import Data.List.Extra
open import Data.List.Relation.Binary.Permutation.Propositional
open import Data.List.Relation.Binary.Permutation.Propositional.Properties

open import Relation.Nullary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_; isEquivalence; refl; cong)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Bundles

open import Relation.Ternary.Construct.List
open PartialSemigroup {{...}}

{- List division is positive -}
module _ where

  import Data.Nat as Nat
  open import Data.Nat.SizeOf {A = List A} length as SizeOf
  open import Data.Nat.Properties
  open import Relation.Nullary

  split-positive : IsPositive _ _≡_ (splits) []
  IsPositive._≤ₐ_ split-positive = SizeOf._≤ₐ_

  IsPositive.is-empty split-positive []       = yes refl
  IsPositive.is-empty split-positive (x ∷ xs) = no (λ ())

  IsPositive.orderₐ split-positive = size-pre isEquivalence (λ where refl → refl)

  IsPositive.positiveˡ split-positive = positiveˡ
    where
      positiveˡ : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Φ₁ SizeOf.≤ₐ Φ
      positiveˡ (divide x σ) = Nat.s≤s (positiveˡ σ)
      positiveˡ (consˡ σ)    = Nat.s≤s (positiveˡ σ)
      positiveˡ (consʳ σ)    = ≤-step (positiveˡ σ)
      positiveˡ []           = ≤-refl

  IsPositive.positiveʳ split-positive = positiveʳ
    where
      positiveʳ : ∀ {Φ₁ Φ₂ Φ} → Split Φ₁ Φ₂ Φ → Φ₂ SizeOf.≤ₐ Φ
      positiveʳ (divide x σ) = Nat.s≤s (positiveʳ σ)
      positiveʳ (consˡ σ)    = ≤-step (positiveʳ σ)
      positiveʳ (consʳ σ)    = Nat.s≤s (positiveʳ σ)
      positiveʳ []           = ≤-refl

  IsPositive.ε-least split-positive {[]} Nat.z≤n = refl

module _ {a e} {{isSemigroup : PartialSemigroup a e}} where

  private
    assocᵣ : RightAssoc (splits rel)
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

    assocₗ : LeftAssoc (splits rel)
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
  split-isSemigroup : IsPartialSemigroup _≡_ (splits rel)
  IsPartialSemigroup.≈-equivalence split-isSemigroup = isEquivalence
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ split-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ split-isSemigroup) refl σ = σ
  Respect.coe (IsPartialSemigroup.∙-respects-≈ split-isSemigroup) refl σ = σ
  IsPartialSemigroup.∙-assocᵣ split-isSemigroup = assocᵣ
  IsPartialSemigroup.∙-assocₗ split-isSemigroup = assocₗ

  instance split-semigroup : PartialSemigroup _ _
  split-semigroup = record { isSemigroup = split-isSemigroup }

  {- Monoid instance -}
  split-isMonoid : IsPartialMonoid _≡_ (splits rel) []
  IsPartialMonoid.isPartialSemigroup split-isMonoid = split-isSemigroup
  IsPartialMonoid.emptiness split-isMonoid          = list-emptiness rel
  IsPartialMonoid.ε-unique split-isMonoid refl      = refl
  IsPartialMonoid.∙-idˡ split-isMonoid {Φ}          = idˡ Φ
    where
      idˡ : ∀ Φ → Split rel [] Φ Φ
      idˡ []      = []
      idˡ (x ∷ Φ) = consʳ (idˡ Φ) 
  IsPartialMonoid.∙-idʳ split-isMonoid {Φ} = idʳ Φ
    where
      idʳ : ∀ Φ → Split rel Φ [] Φ
      idʳ []      = []
      idʳ (x ∷ Φ) = consˡ (idʳ Φ)
  IsPartialMonoid.∙-id⁻ˡ split-isMonoid = id⁻ˡ
    where
      id⁻ˡ : ∀ {Φ₁ Φ₂} → Split rel [] Φ₁ Φ₂ → Φ₁ ≡ Φ₂
      id⁻ˡ []        = refl
      id⁻ˡ (consʳ σ) = cong (_ ∷_) (id⁻ˡ σ)
  IsPartialMonoid.∙-id⁻ʳ split-isMonoid = id⁻ʳ
    where
      id⁻ʳ : ∀ {Φ₁ Φ₂} → Split rel Φ₁ [] Φ₂ → Φ₁ ≡ Φ₂
      id⁻ʳ []        = refl
      id⁻ʳ (consˡ σ) = cong (_ ∷_) (id⁻ʳ σ)

  instance split-monoid : PartialMonoid _ _
  split-monoid = record { isMonoid = split-isMonoid }

  -- {- Total instance -}
  -- split-isTotal : IsTotal _≡_ (splits rel) _++_
  -- IsTotal.∙-parallel split-isTotal = par
  --   where
  --     par : ∀ {a b c d ab cd} → Split rel a b ab → Split rel c d cd → Split rel (a ++ c) (b ++ d) (ab ++ cd)
  --     par [] σ₂ = σ₂
  --     par (divide x σ₁) σ₂ = divide x (par σ₁ σ₂)
  --     par (consˡ σ₁) σ₂ = consˡ (par σ₁ σ₂)
  --     par (consʳ σ₁) σ₂ = consʳ (par σ₁ σ₂)

-- module WithCommutative
--   {a} {A : Set a} {elementDivision : Rel₃ A}
--   (isCommutative : IsCommutative elementDivision) where

--   open IsCommutative isCommutative

--   private
--     comm : Commutative (splits rel)
--     comm (divide τ σ) = divide (∙-comm τ) (comm σ)
--     comm (consˡ σ)    = consʳ  (comm σ)
--     comm (consʳ σ)    = consˡ  (comm σ)
--     comm []           = []

--   split-isComm : IsCommutative splits
--   IsCommutative.∙-comm split-isComm = comm

  ∙-↭ : ∀ {xs : List  A} → xsˡ ∙ xsʳ ≣ xs → xs ↭ ys →
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
  ... | _ , h₃ , h₄ , σ₃ = _ , trans h₃ h₁ , trans h₄ h₂ , σ₃

-- module _
--   {e} {_≈_ : A → A → Set e}
--   {{div : Rel₃ A}} {{_ : IsPartialSemigroup _≈_ div}} {{_ : IsCommutative div}}
--   (no-div : ∀ {x y xy : A} → ¬ (x ∙ y ≣ xy)) where

--   open import Relation.Ternary.Construct.List div

--   ↭-∙ˡ : ∀ {xsˡ xsʳ ysˡ xs} → xsˡ ∙ xsʳ ≣ xs → xsˡ ↭ ysˡ → Σ[ ys ∈ List A ] ys ↭ xs × (ysˡ ∙ xsʳ ≣ ys)
--   ↭-∙ˡ [] ρ = -, ↭-sym ρ , ∙-idʳ
--   ↭-∙ˡ (consʳ σ) ρ with ↭-∙ˡ σ ρ
--   ... | _ , ρ′ , σ′ = -, prep _ ρ′ , consʳ σ′

--   ↭-∙ˡ (consˡ σ) refl = -, refl , consˡ σ
--   ↭-∙ˡ (consˡ σ) (prep x ρ) with ↭-∙ˡ σ ρ
--   ... | _ , ρ′ , σ′ = -, prep _ ρ′ , consˡ σ′
--   ↭-∙ˡ (consˡ (consˡ σ)) (swap x y ρ) with ↭-∙ˡ σ ρ
--   ... | _ , ρ′ , σ′ = -, swap _ _ ρ′ , consˡ (consˡ σ′)
--   ↭-∙ˡ (consˡ (consʳ σ)) ρ@(swap _ _ _) with ↭-∙ˡ (consˡ σ) ρ
--   ... | _ , ρ′ , σ′ = -, ↭-trans (prep _ ρ′) (swap _ _ ↭-refl) , consʳ σ′
--   ↭-∙ˡ (consˡ (divide x _)) (swap _ _ _) with no-div x 
--   ... | ()

--   ↭-∙ˡ σ@(consˡ _) (_↭_.trans ρ₁ ρ₂) with ↭-∙ˡ σ ρ₁
--   ... | _ , ρ₃ , σ′ with ↭-∙ˡ σ′ ρ₂
--   ... | _ , ρ₄ , σ′′ = -, ↭-trans ρ₄ ρ₃ , σ′′

--   ↭-∙ˡ (divide x σ) ρ with no-div x
--   ... | () 

--   ↭-∙ʳ : ∀ {xsˡ xsʳ xs ysʳ} → xsˡ ∙ xsʳ ≣ xs → xsʳ ↭ ysʳ → Σ[ ys ∈ _ ] ys ↭ xs × (xsˡ ∙ ysʳ ≣ ys)
--   ↭-∙ʳ σ ρ with ↭-∙ˡ (∙-comm σ) ρ
--   ... | _ , ρ′ , σ′ = -, ρ′ , ∙-comm σ′

--   ↭-∙ : ∀ {xsˡ xsʳ xs ysˡ ysʳ} → xsˡ ∙ xsʳ ≣ xs → xsˡ ↭ ysˡ → xsʳ ↭ ysʳ → Σ[ ys ∈ _ ] ys ↭ xs × (ysˡ ∙ ysʳ ≣ ys)
--   ↭-∙ σ ρ₁ ρ₂ with ↭-∙ˡ σ ρ₁
--   ... | _ , ρ₃ , σ₂ with ↭-∙ʳ σ₂ ρ₂
--   ... | _ , ρ₄ , σ₃ = -, ↭-trans ρ₄ ρ₃ , σ₃

-- module ListXSplit
--   (div₁ : Rel₃ A) (div₂ : Rel₃ A)
--   {e} {_≈_ : A → A → Set e}
--   {{_ : IsCommutative div₁}} {{_ : IsPartialSemigroup _≈_ div₁}}
--   {{_ : IsCommutative div₂}} {{_ : IsPartialSemigroup _≈_ div₂}}
--   (xsplitₐ : CrossSplit div₁ div₂)
--   where

--   open import Relation.Ternary.Construct.List div₁ as L
--   open import Relation.Ternary.Construct.List div₂ as R
--   open Rel₃ div₁ using () renaming (_∙_≣_ to _∙ₐ₁_≣_)
--   open Rel₃ div₂ using () renaming (_∙_≣_ to _∙ₐ₂_≣_)
--   open Rel₃ L.splits using () renaming (_∙_≣_ to _∙₁_≣_)
--   open Rel₃ R.splits using () renaming (_∙_≣_ to _∙₂_≣_)
  
--   xsplit : CrossSplit L.splits R.splits

--   xsplit [] σ₂ with ε-split σ₂
--   ... | refl = -, ∙-idˡ , ∙-idˡ , ∙-idˡ , ∙-idˡ

--   xsplit (divide x σ₁) (divide y σ₂) with xsplit σ₁ σ₂ | xsplitₐ x y
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ | _ , xy₁₁ , xy₁₂ , xy₂₁ , xy₂₂ =
--     -, R.divide xy₁₁ σ₃ , R.divide xy₁₂ σ₄ , L.divide xy₂₁ σ₅ , L.divide xy₂₂ σ₆

--   xsplit (divide x σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consˡ σ₃ , R.consˡ σ₄ , L.divide x σ₅ , σ₆
--   xsplit (divide x σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consʳ σ₃ , R.consʳ σ₄ , σ₅ , L.divide x σ₆

--   xsplit (consˡ σ₁) (divide x σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.divide x σ₃ , σ₄ , L.consˡ σ₅ , L.consˡ σ₆
--   xsplit (consˡ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consˡ σ₃ , σ₄ , L.consˡ σ₅ , σ₆
--   xsplit (consˡ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, R.consʳ σ₃ , σ₄ , σ₅ , L.consˡ σ₆
  
--   xsplit (consʳ σ₁) (divide x σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.divide x σ₄ , L.consʳ σ₅ , L.consʳ σ₆
--   xsplit (consʳ σ₁) (consˡ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.consˡ σ₄ , L.consʳ σ₅ , σ₆
--   xsplit (consʳ σ₁) (consʳ σ₂) with xsplit σ₁ σ₂
--   ... | _ , σ₃ , σ₄ , σ₅ , σ₆ = -, σ₃ , R.consʳ σ₄ , σ₅ , L.consʳ σ₆

--   module _ (no-div₂ : ∀ {x y xy} → ¬ (x ∙ₐ₂ y ≣ xy)) where
--     private
--       data Resplit x (xs ys zs : List A) : Set ℓ where
--         left    : ∀ {zs'}
--                 → (x ∷ zs') ↭ zs 
--                 → (xs ∙₂ ys ≣ zs')
--                 → Resplit x xs ys zs

--       lemma : ∀ {x} {xs ys zs : List A} → (x ∷ xs) ∙₂ ys ≣ zs → Resplit x xs ys zs
--       lemma (consˡ σ)    = left    ↭-refl σ
--       lemma (consʳ σ) with lemma σ
--       ... | left ρ σ' = left (↭-trans (swap _ _ ↭-refl) (prep _ ρ)) (R.consʳ σ')
--       lemma (divide x σ) with no-div₂ x
--       ... | ()

--     {- A weaker version of uncross, that permits permutations as the leaves -}
--     unxross : ∀ {a b c d ac ad bc bd}
--       → ac ∙₁ ad ≣ a → bc ∙₁ bd ≣ b → ac ∙₂ bc ≣ c → ad ∙₂ bd ≣ d
--       → Σ[ as ∈ List A × List A × List A × List A × List A ]
--         let a' , b' , c' , d' , z = as
--         in a ↭ a' × b ↭ b' × c ↭ c' × d ↭ d'
--           × a' ∙₂ b' ≣ z
--           × c' ∙₁ d' ≣ z

--     unxross [] σ₂ σ₃ σ₄ rewrite ∙-id⁻ˡ σ₃ | ∙-id⁻ˡ σ₄ =
--       -, ↭-refl , ↭-refl , ↭-refl , ↭-refl , ∙-idˡ , σ₂

--     unxross (consˡ σ₁) σ₂ σ₃ σ₄ with lemma σ₃
--     ... | left ρ σ₃′ with unxross σ₁ σ₂ σ₃′ σ₄
--     ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
--       -, prep _ ρ₁ , ρ₂  , ↭-trans (↭-sym ρ) (prep _ ρ₃) , ρ₄ , R.consˡ τ₁ , L.consˡ τ₂

--     unxross (divide x σ₁) σ₂ σ₃ σ₄ with lemma σ₃ | lemma σ₄
--     ... | left ρ σ₃′ | left ρ′ σ₄′ with unxross σ₁ σ₂ σ₃′ σ₄′
--     ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
--       -, prep _ ρ₁ , ρ₂ , ↭-trans (↭-sym ρ) (prep _ ρ₃) , ↭-trans (↭-sym ρ′) (prep _ ρ₄) , R.consˡ τ₁ , L.divide x τ₂

--     unxross (consʳ σ₁) σ₂ σ₃ σ₄ with lemma σ₄
--     ... | left ρ σ₄′ with unxross σ₁ σ₂ σ₃ σ₄′
--     ... | _ , ρ₁ , ρ₂ , ρ₃ , ρ₄ , τ₁ , τ₂ =
--       -, prep _ ρ₁ , ρ₂  , ρ₃ , ↭-trans (↭-sym ρ) (prep _ ρ₄) , R.consˡ τ₁ , L.consʳ τ₂
