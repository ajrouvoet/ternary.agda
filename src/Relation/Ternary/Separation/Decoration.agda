open import Relation.Ternary.Separation

module Relation.Ternary.Separation.Decoration
  {ℓₐ} (A : Set ℓₐ)
  {{raw : RawSep A}}
  {{_   : IsSep raw}}
  where

open import Level
open import Function
open import Relation.Unary
open import Algebra.Core
open import Relation.Binary.PropositionalEquality

private
  variable
    a₁ a₂ a : A

-- Splittable decorations
record Decoration {d} (D : Pred A d) : Set (ℓₐ ⊔ d) where
  field
    decorˡ   : a₁ ⊎ a₂ ≣ a → D a → D a₁
    ⊎-decor  : a₁ ⊎ a₂ ≣ a → D a₁ → D a₂ → D a

  DT : A → Set _
  DT a = D a → D a

  decorʳ  : a₁ ⊎ a₂ ≣ a → D a → D a₂
  decorʳ σ = decorˡ (⊎-comm σ)

  redecʳ : a₁ ⊎ a₂ ≣ a → D a₂ → DT a
  redecʳ σ a₂ a = ⊎-decor σ (decorˡ σ a) a₂

  redecˡ : a₁ ⊎ a₂ ≣ a → D a₁ → DT a
  redecˡ σ a₁ a = ⊎-decor σ a₁ (decorʳ σ a)

-- Splittable Flow as a pair of input/output decorations
module Flow
  {ℓ} (D : Pred A ℓ) (decoration : Decoration D)
  where

  open Decoration decoration
  open import Data.Product renaming (proj₁ to inp; proj₂ to out)

  -- A carrier decorated with its flow attributes
  Flow : A → Set ℓ
  Flow a = D a × D a

  -- one can split flow over separations
  flowₗ : (a₁ ⊎ a₂ ≣ a) → Flow a → Flow a₁
  flowₗ σ = map (decorˡ σ) (decorˡ σ)

  flowᵣ : (a₁ ⊎ a₂ ≣ a) → Flow a → Flow a₂
  flowᵣ σ = map (decorʳ σ) (decorʳ σ)

  -- ...and project the input from either side of the split
  inputₗ : a₁ ⊎ a₂ ≣ a → Flow a → D a₁
  inputₗ σ = inp ∘ flowₗ σ

  inputᵣ : a₁ ⊎ a₂ ≣ a → Flow a → D a₂
  inputᵣ σ = inp ∘ flowᵣ σ

  -- ...or the output
  outputₗ : a₁ ⊎ a₂ ≣ a → Flow a → D a₁
  outputₗ σ = out ∘ flowₗ σ 

  outputᵣ : a₁ ⊎ a₂ ≣ a → Flow a → D a₂
  outputᵣ σ = out ∘ flowᵣ σ

  FlowPred : ∀ a ℓ → Set _
  FlowPred a ℓ = Flow a → Set ℓ

  _via_ : Flow a → DT a → Flow a
  (i , o) via f = i , f o

  -- Lifting a decoration transformer to a flow predicate:
  --
  -- ─∙─ f ─∙─
  --
  data Through (f : ∀[ DT ]) : FlowPred a ℓ where
    through : ∀ {a} {d : D a} → Through f (d , f d)


  -- the identity flow predicate
  --
  -- ─∙─────∙─
  --
  𝑰 = Through id


  -- Parallel composition of flow predicates:
  --
  --     __ P __
  --    ╱       ╲
  --  ─∙─── Q ───∙─
  --
  record _∥⟨_⟩_ {p q}
    (P : FlowPred a₁ p)
    (σ : a₁ ⊎ a₂ ≣ a)
    (Q : FlowPred a₂ q)
    (φ : Flow a)
    : Set (p ⊔ q ⊔ ℓₐ ⊔ ℓ) where
    constructor par
    field
      px : P (flowₗ σ φ)
      qx : Q (flowᵣ σ φ)

  -- 
  --     __ P __
  --    ╱       ╲
  --  ─∙─────────∙─
  --
  Bridge⟨_⟩ : ∀ {p} (σ : a₁ ⊎ a₂ ≣ a) (P : FlowPred a₁ p) → FlowPred a _
  Bridge⟨ σ ⟩ P = P ∥⟨ σ ⟩ 𝑰

  -- Sequential composition of flow predicates:
  -- 
  --     __ P ____________
  --    ╱       ╲         ╲
  --  ─∙─────────∙─── Q ───∙─
  --
  record _▹⟨_⟩_ {p q}
    (P : FlowPred a₁ p)
    (σ : a₁ ⊎ a₂ ≣ a)
    (Q : FlowPred a₂ q)
    (φ : Flow a)
    : Set (p ⊔ q ⊔ ℓₐ ⊔ ℓ) where
    constructor seq
    field
      {between} : _
      px  : Bridge⟨ σ        ⟩ P (inp φ , between)
      qx  : Bridge⟨ ⊎-comm σ ⟩ Q (between , out φ)
