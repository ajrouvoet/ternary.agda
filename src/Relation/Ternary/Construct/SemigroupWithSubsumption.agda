open import Algebra
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

-- We can construct a proof relevant semigroup from a total semigroup
-- and a subsumption relation, allowing one to pick arbitrary higher elements for the composite.
-- In other words: this is an 'affine' algebra.
module Relation.Ternary.Construct.SemigroupWithSubsumption {a e}
  {A : Set a}
  {_≈_ : A → A → Set e}
  {_≤_ : A → A → Set a}
  (≤-po : IsPreorder _≈_ _≤_)
  where

open import Level
open import Data.Product
open import Relation.Ternary.Core hiding (_∙_; _≤_)
open import Relation.Ternary.Structures

open IsPreorder hiding (isEquivalence)
open import Relation.Binary.Reasoning.Preorder (record { isPreorder = ≤-po })

record IsMonotone (_∙_ : Op₂ A) : Set a where
  field
    ∙-respects-≤ˡ : ∀ {a b c} → a ≤ b → (a ∙ c) ≤ (b ∙ c)
    ∙-respects-≤ʳ : ∀ {a b c} → a ≤ b → (c ∙ a) ≤ (c ∙ b)

record IsMonotoneSemigroup (_∙_ : Op₂ A) : Set (a ⊔ e) where
  field
    {{isSemigroup}} : IsSemigroup _≈_ _∙_
    {{isMonotone}}  : IsMonotone _∙_

open IsMonotone {{...}} public
open IsMonotoneSemigroup {{...}} public

module MonotoneSemigroup {_∙_ : Op₂ A} (msg : IsMonotoneSemigroup _∙_) where

  open IsSemigroup {{...}} public

  data _∙_≤_ : A → A → A → Set a where
    bysub : ∀ {a b c} → (a ∙ b) ≤ c →  a ∙ b ≤ c

  ∙≤-rel : Rel₃ A
  Rel₃._∙_≣_ ∙≤-rel = _∙_≤_

  instance ∙≤-isSemigroup : IsPartialSemigroup _≈_ ∙≤-rel
  IsPartialSemigroup.≈-equivalence ∙≤-isSemigroup = isEquivalence

  Respect.coe (IsPartialSemigroup.∙-respects-≈ ∙≤-isSemigroup) eq (bysub x) =
    bysub (∼-respʳ-≈ ≤-po eq x)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ˡ ∙≤-isSemigroup) eq (bysub x) =
    bysub (∼-respˡ-≈ ≤-po (∙-congʳ eq) x)
  Respect.coe (IsPartialSemigroup.∙-respects-≈ʳ ∙≤-isSemigroup) eq (bysub x) =
    bysub (∼-respˡ-≈ ≤-po (∙-congˡ eq) x)

  IsPartialSemigroup.∙-assocᵣ ∙≤-isSemigroup (bysub {a = a} {b = b} {c = ab} x) (bysub {b = c} {c = abc} y) =
     -, bysub
         (begin (a ∙ (b ∙ c))
           ≈⟨ sym (assoc a b c) ⟩ (a ∙ b) ∙ c
           ∼⟨ ∙-respects-≤ˡ x   ⟩ ab ∙ c
           ∼⟨ y                 ⟩ abc ∎)
      , bysub (IsPreorder.refl ≤-po)

  IsPartialSemigroup.∙-assocₗ ∙≤-isSemigroup (bysub {a = a} {c = abc} x) (bysub {a = b} {b = c} {c = bc} y) =
    -, bysub (IsPreorder.refl ≤-po)
     , bysub
         (begin ((a ∙ b) ∙ c)
           ≈⟨ assoc a b c     ⟩ a ∙ (b ∙ c)
           ∼⟨ ∙-respects-≤ʳ y ⟩ a ∙ bc
           ∼⟨ x               ⟩ abc ∎)

record IsMonotoneMonoid (_∙_ : Op₂ A) u : Set (a ⊔ e) where
  field
    {{isMonoid}}   : IsMonoid _≈_ _∙_ u
    {{isMonotone}} : IsMonotone _∙_

module MonotoneMonoid {_∙_ : Op₂ A} {u} (mm : IsMonotoneMonoid _∙_ u) where

  open IsMonotoneMonoid mm
  open IsMonoid {{...}}

  open MonotoneSemigroup (record { isSemigroup = IsMonoid.isSemigroup isMonoid })

  ∙≤-isMonoid : IsPartialMonoid _≈_ ∙≤-rel u
  IsPartialMonoid.ε-unique ∙≤-isMonoid eq = {!!}
  IsPartialMonoid.∙-idˡ ∙≤-isMonoid {Φ = Φ} = bysub (IsPreorder.reflexive ≤-po (identityˡ Φ))
  IsPartialMonoid.∙-idʳ ∙≤-isMonoid {Φ = Φ} = bysub (IsPreorder.reflexive ≤-po (identityʳ Φ))
  IsPartialMonoid.∙-id⁻ˡ ∙≤-isMonoid (bysub x) = {!!}
  IsPartialMonoid.∙-id⁻ʳ ∙≤-isMonoid σ = {!!}
