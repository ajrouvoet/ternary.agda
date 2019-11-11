open import Relation.Ternary.Separation
open import Relation.Ternary.Separation.Decoration
open import Relation.Unary

{- Flow is a decoration transformer -}
module Relation.Ternary.Separation.Decoration.Flow
  {ℓₐ} (A : Set ℓₐ)
  {{raw : RawSep A}}
  {u : A} {{_ : HasUnit⁺ raw u}}
  {d} {D : Pred A d} (𝑫 : Decoration D)
  where

open import Level
open import Function
open import Data.Product

private
  instance _ = 𝑫

Flow : A → Set _
Flow a = D a × D a

cut : ∀ {a} → Flow a → D a → Flow a × Flow a
cut  φ d = (proj₁ φ , d) , (d , proj₂ φ)

cutₗ : ∀ {a} → Flow a → D a → Flow a
cutₗ φ = proj₁ ∘ cut φ

cutᵣ : ∀ {a} → Flow a → D a → Flow a
cutᵣ φ = proj₂ ∘ cut φ

instance 𝑭 : Decoration Flow
Decoration.decorˡ 𝑭 σ = map (decorˡ σ) (decorˡ σ)
Decoration.decor-ε 𝑭  = decor-ε , decor-ε

FlowPred : (ℓ : Level) → Set _
FlowPred ℓ = Decorated 𝑭 → Set ℓ

-- Parallel flow predicate composition
--
--     __ P __
--    ╱       ╲
--  ─∙─── Q ───∙─
--
_∥_ : ∀ {p q} → FlowPred p → FlowPred q → FlowPred _ 
P ∥ Q = P ✴ Q

-- Lifting a decoration transformer to a flow predicate:
--
-- ─∙─ f ─∙─
--
data Through (f : ∀[ DT 𝑫 ]) : FlowPred ℓₐ where
  through : ∀ {a} {d : D a} → Through f (a , d , f d)

-- the identity flow predicate
--
-- ─∙─────∙─
--
𝑰 = Through id

-- 
--     __ P __
--    ╱       ╲
--  ─∙─────────∙─
--
Sidechannelₗ : ∀ {p} (P : FlowPred p) → FlowPred _
Sidechannelₗ P = P ∥ 𝑰

-- Sequential composition of flow predicates:
-- 
--     __ P ____________
--    ╱       ╲         ╲
--  ─∙─────────∙─── Q ───∙─
--
record _▹_ {p q} (P : FlowPred p) (Q : FlowPred q) (φ : Decorated 𝑭) : Set (ℓₐ ⊔ d ⊔ p ⊔ q) where
  constructor seq
  open Σ φ renaming (proj₂ to flow)
  field
    {inter} : _
    px      : Sidechannelₗ P (-, cutₗ flow inter)
    qx      : Q (-, Decoration.decorʳ 𝑭 (lower (Conj.sep px)) (cutᵣ flow inter))
