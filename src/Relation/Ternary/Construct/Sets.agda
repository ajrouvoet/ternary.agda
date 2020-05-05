{-# OPTIONS --without-K #-}
module Relation.Ternary.Construct.Sets where

open import Data.Product as Pr
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.These as These
open import Data.These.Properties
open import Level

open import Relation.Nullary hiding (Irrelevant)
open import Relation.Unary
open import Relation.Ternary.Core
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_∣_)
open import Relation.Binary.Structures
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open P.≡-Reasoning

open import Function using (id; case_of_; _∘_; Inverse; _$_)
open import Function.Structures
open import Function.Bundles

open import Relation.Ternary.Construct.Sets.Union

-- TODO move to Data.Unit.Properties?
⊤-prop : ∀ {tt tt' : ⊤} → tt ≡ tt'
⊤-prop {tt} {tt} = refl 

instance ⊔-rel : Rel₃ Set
Rel₃._∙_≣_ ⊔-rel = Union

instance ⊔-commutative : IsCommutative ⊔-rel 
IsCommutative.∙-comm ⊔-commutative σ = 
  union injb inja (These.swap ∘ from) prf₁ prf₂ prf
  where 
    open Union σ hiding (From⟨_,_,_⟩; this; that; these)
    module F = From (These.swap ∘ from)
    
    prf₁ : ∀ b → F.InjaInverses injb b
    prf₁ x with b-inv' x 
    ... | From.that _ i refl rewrite i = refl
    ... | From.these a .x i refl rewrite i = refl

    prf₂ : ∀ a → F.InjbInverses inja a
    prf₂ x with a-inv' x 
    ... | From.this .x i refl rewrite i = refl
    ... | From.these .x b i refl rewrite i = refl
    
    prf : ∀ c → F.RightInverses injb inja c
    prf ab with from-inv' ab
    ... | From.this _ i refl rewrite i = refl
    ... | From.that _ i refl rewrite i = refl
    ... | From.these _ _ i (fst , snd) rewrite i = snd , fst

⊔-semigroupˡ : IsPartialSemigroupˡ _↔_ ⊔-rel
IsPartialSemigroupˡ.≈-equivalence ⊔-semigroupˡ = equiv
  where
    sym : ∀ {A B : Set} → A ↔ B → B ↔ A
    sym e = record 
      { f = f⁻¹ 
      ; f⁻¹ = f 
      ; cong₁ = cong₂ 
      ; cong₂ = cong₁ 
      ; inverse = inverseʳ , inverseˡ }
      where open Inverse e

    open import Function.Construct.Identity
    open import Function.Construct.Composition

    equiv : IsEquivalence _↔_
    IsEquivalence.refl equiv      = id-↔ _
    IsEquivalence.sym equiv       = sym
    IsEquivalence.trans equiv x y = x ∘-↔ y

Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ ⊔-semigroupˡ {A} {B}) {C} {D} eq σ = 
  union (f ∘ inja) (f ∘ injb) (from ∘ f⁻¹) prf₁ prf₂ prf
  where 
    open Union σ
    open Inverse eq

    prf₁ : ∀ a → From.InjaInverses (from ∘ f⁻¹) (f ∘ inja) a
    prf₁ a with a-inv' a
    ... | From.this .a i refl    rewrite (P.cong from (inverseʳ (inja a))) | i = refl
    ... | From.these .a b i refl rewrite (P.cong from (inverseʳ (inja a))) | i = refl

    prf₂ : ∀ b → From.InjbInverses (from ∘ f⁻¹) (f ∘ injb) b
    prf₂ b with b-inv' b
    ... | From.that .b i refl    rewrite (P.cong from (inverseʳ (injb b))) | i = refl
    ... | From.these a .b i refl rewrite (P.cong from (inverseʳ (injb b))) | i = refl    

    prf : ∀ c → From.RightInverses (from ∘ f⁻¹) (f ∘ inja) (f ∘ injb) c
    prf d with from-inv' (f⁻¹ d)
    ... | this _ i px rewrite i = P.trans (P.cong f px) (inverseˡ _)
    ... | that _ i px rewrite i = P.trans (P.cong f px) (inverseˡ _)
    ... | these _ _ i (px , qx) rewrite i =
      P.trans (P.cong f px) (inverseˡ _) , P.trans (P.cong f qx) (inverseˡ _)

Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ ⊔-semigroupˡ {B} {C}) {A} {D} eq σ = 
  union (inja ∘ f⁻¹) injb from' prf₁ prf₂ prf
  where 
    open Union σ
    open Inverse eq

    from' : C → These D B
    from' = These.map₁ f ∘ from

    prf₁ : ∀ a → From.InjaInverses from' (inja ∘ f⁻¹) a
    prf₁ a with a-inv' (f⁻¹ a)
    ... | From.this .(f⁻¹ a) i refl    rewrite i = inverseˡ _
    ... | From.these .(f⁻¹ a) b i refl rewrite i = inverseˡ _

    prf₂ : ∀ b → From.InjbInverses from' injb b
    prf₂ b with b-inv' b
    ... | From.that .b i refl    rewrite i = refl
    ... | From.these a .b i refl rewrite i = refl

    prf : ∀ c → From.RightInverses from' (inja ∘ f⁻¹) injb c
    prf c with from-inv' c
    ... | this _ i px rewrite i = P.trans (P.cong inja (inverseʳ _)) px
    ... | that _ i px rewrite i = px
    ... | these _ _ i (px , qx) rewrite i = P.trans (P.cong inja (inverseʳ _)) px , qx

IsPartialSemigroupˡ.assocᵣ ⊔-semigroupˡ {A} {B} {AB} {C} {ABC} σ₁ σ₂ = 
  BC , union a→abc bc→abc ←abc a-inv bc-inv right
     , union b→bc c→bc ←bc b-inv c-inv c-right-inv
  where
    module U₁ = Union σ₁
    module U₂ = Union σ₂
    open U₁ using () renaming (inja to a→ab; injb to b→ab)
    open U₂ using () renaming (inja to ab→abc; injb to c→abc; _B≺_ to _C≺_; _A≺_ to _AB≺_)
    
    a→abc : A → ABC
    a→abc = ab→abc ∘ a→ab
    
    b→abc : B → ABC
    b→abc = ab→abc ∘ b→ab
    
    Condition = λ abc → U₂.From⟪ U₁.From⟪ ∅ , U , U ⟫ , U , U ⟫ abc
    BC = Σ[ abc ∈ ABC ] Condition abc

    bc-prop : Irrelevant Condition
    bc-prop {abc} a b with U₂.from-inv' abc
    bc-prop {abc} a b | From.this ab i refl with U₁.from-inv' ab
    ... | From.this a' i₁ refl                       = ⊥-elim (U₁.from-elim-a (U₂.from-elim-a a i) i₁)
    ... | From.that b' i₁ refl rewrite i | i₁        = ⊤-prop
    ... | From.these a₁ b₁ i₁ rx rewrite i | i₁      = ⊤-prop
    bc-prop {abc} a b | From.that c i refl rewrite i = ⊤-prop
    bc-prop {abc} a b | From.these ab _ i _ with U₁.from-inv' ab
    ... | From.this a' i₁ refl rewrite i | i₁        = ⊤-prop 
    ... | From.that b' i₁ refl rewrite i | i₁        = ⊤-prop
    ... | From.these a₁ b₁ i₁ _ rewrite i | i₁       = ⊤-prop

    bc→abc : BC → ABC
    bc→abc = proj₁

    ←abc : (abc : ABC) → These A BC
    ←abc abc with U₂.from-inv' abc
    ←abc abc | From.this ab i eq with U₁.from-inv' ab
    ... | From.this a i₁ eq' = this a
    ... | From.that b i₁ eq' = that (abc , U₂.intro-from-a i (U₁.intro-from-b i₁ tt))
    ... | From.these a b i₁ (fst , snd) = these a (abc , U₂.intro-from-a i (U₁.intro-from-ab i₁ tt))
    ←abc abc | From.that b i qx         = that (abc , U₂.intro-from-b i tt)
    ←abc abc | From.these ab c i rx with U₁.from-inv' ab
    ... | From.this a i₁ refl           = these a (abc , U₂.intro-from-ab i tt)
    ... | From.that b i₁ refl           = that (abc , U₂.intro-from-ab i tt)
    ... | From.these a b i₁ rx₁         = these a (abc , U₂.intro-from-ab i tt)

    right : (abc : ABC) → From.RightInverses ←abc a→abc bc→abc abc
    right abc with U₂.from-inv' abc
    right abc | From.this a i refl with U₁.from-inv' a
    ... | From.this a₁ i₁ refl             = refl
    ... | From.that b i₁ refl              = refl
    ... | From.these a₁ b i₁ (refl , snd)  = refl , refl
    right abc | From.that b i qx           = refl
    right abc | From.these a b i (refl , eq) with U₁.from-inv' a
    ... | From.this a₁ i₁ refl             = refl , refl
    ... | From.that b' i₁ refl             = refl
    ... | From.these a₁ b' i₁ (refl , snd) = refl , refl

    ←bc : BC → These B C
    ←bc (abc , ev) with U₂.from abc | ev
    ←bc (abc , ev) | this ab    | k with U₁.from ab
    ... | that b    = this b
    ... | these _ b = this b
    ←bc (abc , ev) | that c     | k = that c
    ←bc (abc , ev) | these ab c | k with U₁.from ab
    ... | this a = that c
    ... | that b = these b c
    ... | these a b = these b c

    a-inv : (a : A) → From.InjaInverses ←abc a→abc a
    a-inv a with U₂.from-inv' (a→abc a)
    a-inv a | From.this ab i px with U₁.from-inv' ab
    ... | From.this a' j refl             = U₁.inja-injective $ U₂.inja-injective px
    ... | From.that b  j qx               = U₁.¬B≺inja (P.trans (P.cong U₁.from (P.sym $ U₂.inja-injective px)) j)
    ... | From.these a₂ b i₁ (refl , rx2) = U₁.inja-injective $ U₂.inja-injective px
    a-inv a | From.that b i qx            = U₂.¬B≺inja i
    a-inv a | From.these ab c i (px , qx) with U₁.from-inv' ab
    ... | From.this a' j refl             = U₁.inja-injective $ U₂.inja-injective px
    ... | From.that b  j refl             = U₁.¬B≺inja (P.trans (P.cong U₁.from (P.sym $ U₂.inja-injective px)) j)
    ... | From.these a₂ b i₁ (refl , rx2) = U₁.inja-injective $ U₂.inja-injective px

    bc-inv : (bc : BC) → From.InjbInverses ←abc bc→abc bc
    bc-inv (abc , ev) with U₂.from-inv' abc
    bc-inv (abc , ev) | From.this ab i refl with U₁.from-inv' ab
    ... | From.this a i₁ refl              = U₁.from-elim-a (U₂.from-elim-a ev i) i₁
    ... | From.that b i₁ refl              = P.cong (_ ,_) (bc-prop _ _)
    ... | From.these a b i₁ (refl , _)     = P.cong (_ ,_) (bc-prop _ _)
    bc-inv (abc , ev) | From.that c i refl = P.cong (_ ,_) (bc-prop _ _)
    bc-inv (abc , ev) | From.these ab c i (refl , _) with U₁.from-inv' ab
    ... | From.this a i₁ refl              = P.cong (_ ,_) (bc-prop _ _)
    ... | From.that b i₁ refl              = P.cong (_ ,_) (bc-prop _ _)
    ... | From.these a b i₁ (refl , _)     = P.cong (_ ,_) (bc-prop _ _)

    module _ where
      module F = From ←bc

      -- Simultaneously computing and proving the inverses
      postulate b→bc' : (b : B) → Σ[ bc ∈ BC ] F.From⟪ (_≡ b) , ∅ , (_≡ b) ∘ proj₁ ⟫ bc
      -- b→bc' b with U₁.b-inv' b
      -- b→bc' b | From.that .b i refl with U₂.a-inv' (b→ab b)
      -- ... | From.this ._ i₁ refl     = (-, U₂.intro-from-a i₁ (U₁.intro-from-b i tt))
      --   , {!!}
      -- ... | From.these ._ c i₁ refl  = (-, U₂.intro-from-ab i₁ tt)
      --   , F.intro-from-ab {!!} refl
      -- b→bc' b | From.these a .b i refl with U₂.a-inv' (b→ab b)
      -- ... | From.this ._ i₁ refl     = (-, U₂.intro-from-a i₁ (U₁.intro-from-ab i tt))
      --   , {!!}
      -- ... | From.these ._ b₁ i₁ refl = (-, U₂.intro-from-ab i₁ tt)
      --   , {!!}

      postulate c→bc' : (c : C) → Σ[ bc ∈ BC ] F.From⟪ ∅ , (_≡ c) , (_≡ c) ∘ proj₂ ⟫ bc
      -- c→bc' c with U₂.b-inv' c
      -- ... | Union.that .c c≺abc refl        = (-, U₂.intro-from-b c≺abc tt)
      --   , {!!}
      -- ... | Union.these ab .c ab&c≺abc refl = (-, U₂.intro-from-ab ab&c≺abc tt)
      --   , {!!} 

    b→bc : B → BC
    b→bc = proj₁ ∘ b→bc'

    c→bc : C → BC
    c→bc = proj₁ ∘ c→bc'

    b-inv : (b : B) → From.InjaInverses ←bc b→bc b
    b-inv b = proj₂ $ b→bc' b

    c-inv : (c : C) → From.InjbInverses ←bc c→bc c
    c-inv c = proj₂ $ c→bc' c

    postulate c-right-inv : (c : BC) → F.RightInverses b→bc c→bc c

instance ⊔-semigroup : IsPartialSemigroup _↔_ ⊔-rel
⊔-semigroup = IsPartialSemigroupˡ.semigroupˡ ⊔-semigroupˡ

instance set-emptiness : Emptiness ⊥
set-emptiness = record {}

-- Union is a model with ex-falso as identity
⊔-monoidˡ : IsPartialMonoidˡ _↔_ ⊔-rel ⊥
IsPartialMonoidˡ.identityˡ ⊔-monoidˡ  =
  union ⊥-elim id that (λ ())
    (λ _ → refl)
    (λ _ → refl) 
IsPartialMonoidˡ.identity⁻ˡ ⊔-monoidˡ {b} {c} σ = prf
  where
    open Union σ

    prf : Inverse (P.setoid b) (P.setoid c)

    Inverse.f prf = injb
    Inverse.f⁻¹ prf c with from c
    ... | that b = b

    Inverse.cong₁ prf = P.cong injb
    Inverse.cong₂ prf refl = refl

    proj₁ (Inverse.inverse prf) c with from-inv' c
    ... | From.that _ i refl rewrite i = refl
    proj₂ (Inverse.inverse prf) b with b-inv' b
    ... | From.that .b i refl rewrite i = refl

instance ⊔-monoid : IsPartialMonoid _↔_ ⊔-rel ⊥
⊔-monoid = IsPartialMonoidˡ.partialMonoidˡ ⊔-monoidˡ

-- Homogeneous composition is an instance of Union
instance ⊔-intuitive : IsIntuitionistic U ⊔-rel
IsIntuitionistic.∙-copy ⊔-intuitive _ = union
  id id (λ x → these x x)
  (λ x → refl) (λ x → refl) (λ c → refl , refl)

-- Disjoint Set union is an instance of Union
disjoint-union : ∀ {A B : Set} → Union A B (A ⊎ B)
Union.inja disjoint-union = inj₁
Union.injb disjoint-union = inj₂
Union.from disjoint-union (inj₁ x) = this x
Union.from disjoint-union (inj₂ y) = that y

Union.a-inv disjoint-union a = refl
Union.b-inv disjoint-union b = refl
Union.from-inv disjoint-union (inj₁ x) = refl
Union.from-inv disjoint-union (inj₂ y) = refl
