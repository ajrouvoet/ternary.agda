{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures

module Relation.Ternary.Monad.Writer {ℓ} {C : Set ℓ} (r : Rel₃ C)
  {e u} {_≈_ : C → C → Set e}
  {{m : IsPartialMonoid _≈_ r u}}
  {{c : IsCommutative r}} where

private instance _ = r

open import Level
open import Function using (_∘_)
open import Data.Product
open import Data.Unit
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (Pt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Structures.Syntax
open import Relation.Ternary.Monad
open import Relation.Ternary.Data.IndexedMonoid using (IsIndexedMonoid)

module WriterTransformer
  {ℓi} {I : Set ℓi}
  (M : Pt C ℓ) {{strong : Strong ⊤ (λ _ _ → M)}}
  {W : I → I → Pred C ℓ} (wm : IsIndexedMonoid W) where

  open IsIndexedMonoid wm

  private
    variable
      i j k : I

  {- Insert "writer?! I hardly know her?" joke here. -}
  record WriterT (i j : I) (P : Pred C ℓ) Φ : Set ℓ where
    constructor writer
    field
      unwriter : M (W i j ✴ P) Φ

  open WriterT public

  instance
    writer-functor : Functor (WriterT i j)
    Functor.fmap writer-functor f (writer w) = writer do
      w ∙⟨ σ ⟩ px ← w
      return (w ∙⟨ σ ⟩ f px)

    writer-monad : Monad I WriterT
    Monad.return writer-monad px = writer (return (mempty ∙⟨ ∙-idˡ ⟩ px))
    Monad._=<<_ writer-monad f (writer mpx) = writer do
      w₁    ∙⟨ σ ⟩ px ← mpx
      let (writer mqx) = f px
      (w₁ ∙⟨ σ₁ ⟩ w₂) ∙⟨ σ₂ ⟩ qx ← ✴-assocₗ ⟨$⟩ (mqx &⟨ W _ _ # σ ⟩ w₁)
      return ((mappend w₁ ⟨ σ₁ ⟩ w₂) ∙⟨ σ₂ ⟩ qx)

    writer-strong : Strong I WriterT
    Strong.str writer-strong {Q = Q} qx ⟨ σ ⟩ (writer mpx) = writer do
      w ∙⟨ σ ⟩ px∙qx ← ✴-rotateₗ ⟨$⟩ (mpx &⟨ Q # σ ⟩ qx)
      return (w ∙⟨ σ ⟩ ✴-swap px∙qx)

  -- Output a single, unlabeled instruction
  tell : ∀[ W i j ⇒ WriterT i j Emp ]
  tell cs = writer (return (cs ∙⟨ ∙-idʳ ⟩ refl))

  -- Linear listen, stealing the output from a computation and returning it as a value instead
  listen : ∀ {P} → ∀[ WriterT i j P ⇒ WriterT k k (P ✴ W i j) ]
  listen (writer mpx) = writer do
    w✴px ← mpx
    return (mempty ∙⟨ ∙-idˡ ⟩ ✴-swap w✴px)

  pass : ∀ {P} → ∀[ WriterT i j ((W i j ─✴ W i j) ✴ P) ⇒ WriterT i j P ]
  pass (writer mpx) = writer do
    (w ∙⟨ σ₁ ⟩ f) ∙⟨ σ₂ ⟩ px ← ✴-assocₗ ⟨$⟩ mpx
    return ((f ⟨ ∙-comm σ₁ ⟩ w) ∙⟨ σ₂ ⟩ px)

module WriterMonad
  {ℓi} {I : Set ℓi}
  {W : I → I → Pred C ℓ} (wm : IsIndexedMonoid W) where

  open import Relation.Ternary.Monad.Identity
  open WriterTransformer {I = I} Id wm public renaming (WriterT to Writer)

  instance writer-respect : ∀ {i j P} → Respect _≈_ (Writer i j P)
  Respect.coe writer-respect eq (writer mp) = writer (coe eq mp)

  execWriter : ∀ {i j} {{_ : Respect _≈_ (W i j)}} → ∀[ Writer i j Emp ⇒ W i j ]
  execWriter (writer (bc ∙⟨ σ ⟩ refl)) = coe (∙-id⁻ʳ σ) bc
