open import Data.List
open import Data.Unit

open import Relation.Unary hiding (_∈_)
open import Relation.Unary.PredicateTransformer using (Pt)

module Relation.Ternary.Monad.State.Linear
  {ℓ}

  -- value types
  {T : Set ℓ}

  -- stored values
  (V : T → Pred (List T) ℓ)
  where

open import Level hiding (Lift)
open import Function using (_∘_; case_of_)
import Relation.Binary.HeterogeneousEquality as HEq
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Construct.Product
open import Relation.Ternary.Monad
open import Relation.Ternary.Respect.Propositional

open import Relation.Ternary.Construct.List.Disjoint T
open import Relation.Ternary.Construct.Market disjoint-split
open import Relation.Ternary.Data.Allstar T

open import Data.Product

module HeapOps
  -- inner monad
  (M : Pt Market ℓ)
  where

  Cells : List T → List T → Set ℓ
  Cells Σ Φ = Allstar V Σ Φ

  Heap : List T → Set ℓ
  Heap = LeftOver Cells

  open import Relation.Ternary.Monad.State disjoint-split
  open StateTransformer M public

  module _ {{monad : Monad ⊤ (λ _ _ → M) }} where

    -- Creating a reference to a new cell, filled with a given value.
    -- Note that in the market monoid this is pure!
    -- Because we get a reference that consumes the freshly created resource.
    mkref : ∀ {a} → ∀[ V a ⇒ StateT M Heap (Just a) ]
    mkref v ⟨ supplyᵣ σ₂ ⟩ (lift (subtract st σ₁)) =
      let _ , τ₁ , τ₂ = ∙-assocₗ σ₁ σ₂ in return (
        lift refl ∙⟨ supplyᵣ ∙-disjoint ⟩
        lift (subtract (cons (v ∙⟨ ∙-comm τ₁ ⟩ st)) (∙-disjointᵣₗ τ₂)))

    -- A linear read on a store: you lose the reference.
    -- Resources balance, because with the reference being lost, the cell is destroyed: no resources leak.
    read : ∀ {a} → ∀[ Just a ⇒ StateT M Heap (V a) ]
    read refl ⟨ supplyᵣ σ₂ ⟩ (lift (subtract st σ₁))
      with _ , σ₃ , σ₄ ← ∙-assocₗ σ₁ (∙-comm σ₂) with repartition (∙-comm σ₄) st
    ... | cons (v ∙⟨ σ₅ ⟩ nil) ∙⟨ σ₆ ⟩ st' with refl ← ∙-id⁻ʳ σ₅ with ∙-assocᵣ (∙-comm σ₆) σ₃
    ... | _ , τ₁ , τ₂ = return (lift v ∙⟨ supplyᵣ τ₂ ⟩ lift (subtract st' τ₁))

    -- -- Writing into a cell, returning the current contents
    -- write : ∀ {a b} → ∀[ Just b ✴ (V a) ⇒ StateT M Cells (Just a ✴ V b) ]
    -- write (refl ∙⟨ σ₁ ⟩ v) ⟨ supplyᵣ σ₃ ⟩ (lift st σ₂) with ∙-assocᵣ (∙-comm σ₁) σ₃
    -- -- first we reassociate the arguments in the order that we want to piece it back together
    -- ... | _ , τ₁ , τ₂ with ∙-assocᵣ (∙-comm τ₁) σ₂
    -- ... | _ , τ₃ , τ₄ with ∙-assocᵣ τ₂ τ₃
    -- ... | _ , τ₅ , τ₆
    -- -- then we reorganize the store internally to take out the unit value
    --   with repartition τ₅ st
    -- ... | cons (vb ∙⟨ σ₅ ⟩ nil) ∙⟨ σ₆ ⟩ st' rewrite ∙-id⁻ʳ σ₅ =
    --   let
    --     _ , κ₁ , κ₂ = ∙-assocₗ τ₄ (∙-comm σ₆)
    --     _ , κ₃ , κ₄ = ∙-assocᵣ κ₂ (∙-comm τ₆)
    --   in return (
    --     lift (refl ∙⟨ consˡ ∙-idˡ ⟩ vb)
    --       ∙⟨ supplyᵣ (consˡ κ₄) ⟩
    --     lift (cons (v ∙⟨ κ₁ ⟩ st')) (∙-disjointₗₗ (∙-comm κ₃)))

  module _ {{_ : Strong ⊤ (λ _ _ → M)}} where
    -- A linear (strong) update on the store
    update! : ∀ {a b} → ∀[ Just a ⇒ (V a ─✴ StateT M Heap (V b)) ─✴ StateT M Heap (Just b) ]
    update! ptr ⟨ σ ⟩ f = do
      f ∙⟨ σ₁ ⟩ a ← read ptr &⟨ ∙-comm σ ⟩ f
      b           ← f ⟨ σ₁ ⟩ a
      mkref b
