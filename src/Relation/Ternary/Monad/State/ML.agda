open import Data.List
open import Data.Unit

open import Relation.Unary hiding (_∈_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad

module Relation.Ternary.Monad.State.ML
  {ℓ}
  {T : Set ℓ}
  (V : T → Pred (List T) ℓ)
  where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; subst; sym)
open import Relation.Ternary.Monad
open import Relation.Ternary.Construct.Product
open import Relation.Ternary.Data.Allstar T

open import Relation.Ternary.Construct.List.Overlapping T

open import Data.Product
open import Relation.Ternary.Construct.Market overlap-rel

module HeapOps
  -- inner monad
  (M : Pt Market ℓ)
  {{monad : Monad ⊤ (λ _ _ → M)}}
  where

  Cells : List T → List T → Set ℓ
  Cells Σ Φ = Allstar V Σ Φ
  
  Heap : List T → Set ℓ
  Heap = LeftOver Cells

  open import Relation.Ternary.Monad.State overlap-rel
  open StateTransformer M public

  -- Creating a reference to a new cell, filled with a given value.
  -- Note that in the market monoid, resources are preserved (supply and demand balance)!
  -- Because we get a reference that consumes the freshly created resource.
  mkref : ∀ {a} → ∀[ V a ⇒ StateT M Heap (Just a) ]
  mkref v ⟨ supplyᵣ σ₂ ⟩ (lift (subtract μ σ₁)) =
    let _ , τ₁ , τ₂ = ∙-assocₗ σ₁ σ₂
    in return (lift refl ∙⟨ supplyᵣ ∙-disjoint ⟩ lift (subtract (cons (v ∙⟨ ∙-comm τ₁ ⟩ μ)) (∙-disjointᵣₗ τ₂)))

  read : ∀ {a} → ∀[ Just a ⇒ StateT M Heap  (V a) ]

  -- A read that drops a cell if it is no longer referenced
  read refl ⟨ supplyᵣ σ₂ ⟩ lift (subtract st σ₁) with ∙-assocₗ σ₁ (∙-comm σ₂)
  ... | _ , σ₃ , σ₄ with read' (∙-comm σ₄) st
    where

      read' : ∀ {a} {as xs : List T} → [ a ] ∙ as ≣ xs → ∀[ Allstar V xs ⇒ V a ✴ Allstar V as ]
      read' (overlaps ptr) (cons (v ∙⟨ σ ⟩ vs)) with ✴-assocᵣ ((v ∙⟨ ∙-copy ⟩ v) ∙⟨ σ ⟩ vs)
      ... | c ∙⟨ σ' ⟩ vs' = c ∙⟨ σ' ⟩ subst (λ zs → Allstar _ (_ ∷ zs) _) (sym (∙-id⁻ˡ ptr)) (cons vs')
      read' (consˡ ptr) (cons (v ∙⟨ σ ⟩ vs)) rewrite ∙-id⁻ˡ ptr = v ∙⟨ σ ⟩ vs
      read' (consʳ ptr) (cons (w ∙⟨ σ ⟩ vs)) with ✴-rotateₗ (w ∙⟨ σ ⟩ (read' ptr vs))
      ... | (v ∙⟨ σ' ⟩ vs∙w) = v ∙⟨ σ' ⟩ cons (✴-swap vs∙w)

  ... | v ∙⟨ σ₅ ⟩ st' with ∙-assocₗ (∙-comm σ₃) σ₅
  ... | _ , σ₆ , σ₇ = return (lift v ∙⟨ supplyᵣ (∙-comm σ₆) ⟩ (lift (subtract st' (∙-comm σ₇))))

  -- -- Writing into a cell, returning the current contents
  -- write : ∀ {a b} → ∀[ Just b ✴ (V a) ⇒ StateT M Cells (Just a ✴ V b) ]
  -- write (refl ∙⟨ σ₁ ⟩ v) ⟨ supplyᵣ σ₃ ⟩ (lift st σ₂) with ∙-assocᵣ (∙-comm σ₁) σ₃
  -- -- first we reassociate the arguments in the order that we want to piece it back together
  -- ... | _ , τ₁ , τ₂ with ∙-assocᵣ (∙-comm τ₁) σ₂
  -- ... | _ , τ₃ , τ₄ with ∙-assocᵣ τ₂ τ₃
  -- ... | _ , τ₅ , τ₆ = {!!}
  -- then we reorganize the store internally to take out the unit value
  --   with repartition τ₅ st
  -- ... | cons (vb ∙⟨ σ₅ ⟩ nil) ∙⟨ σ₆ ⟩ st' rewrite ∙-id⁻ʳ σ₅ =
  --   let
  --     _ , κ₁ , κ₂ = ∙-assocₗ τ₄ (∙-comm σ₆)
  --     _ , κ₃ , κ₄ = ∙-assocᵣ κ₂ (∙-comm τ₆)
  --   in return (
  --     lift (refl ∙⟨ ? ⟩ vb)
  --       ∙⟨ supplyᵣ ? ⟩
  --     lift (cons (v ∙⟨ κ₁ ⟩ st')) (∙-disjointₗ (∙-comm κ₃)))

  -- -- A linear (strong) update on the store
  -- update! : ∀ {a b} → ∀[ Just a ⇒ (V a ─✴ StateT M Cells (V b)) ─✴ StateT M Cells (Just b) ]
  -- update! ptr ⟨ σ ⟩ f = do
  --   f ∙⟨ σ₁ ⟩ a ← read ptr &⟨ ∙-comm σ ⟩ f
  --   b           ← f ⟨ σ₁ ⟩ a
  --   mkref b
