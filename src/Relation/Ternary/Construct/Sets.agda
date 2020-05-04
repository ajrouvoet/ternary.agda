{-# OPTIONS --without-K #-}
module Relation.Ternary.Construct.Sets where

open import Data.Product as Pr
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.These as These
open import Data.These.Properties
open import Level

open import Relation.Nullary
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

-- TODO move to These.Properties 
¬this&that : ∀ {A B : Set} {x : These A B} {a b} → x ≡ this a → ¬ x ≡ that b
¬this&that refl ()

¬this&these : ∀ {A B : Set} {x : These A B} {a a' b} → x ≡ this a → ¬ x ≡ these a' b
¬this&these refl ()

¬that&these : ∀ {A B : Set} {x : These A B} {b' a' b} → x ≡ that b' → ¬ x ≡ these a' b
¬that&these refl ()
 
module From {A B C : Set} (from : C → These A B) where

  -- You can point out the elements of C that are only in A/B/in both A & B.
  module _ where

    _A≺_  = λ a c   → from c ≡ this a
    _B≺_  = λ b c   → from c ≡ that b
    _&_≺_ = λ a b c → from c ≡ these a b
    
  module _ (P : Pred A 0ℓ) (Q : Pred B 0ℓ) (R : Pred (A × B) 0ℓ) where

    From⟪_,_,_⟫ : C → Set
    From⟪_,_,_⟫ c = fold P Q (curry R) (from c)

    -- A useful view on applications of the 'from' function of the below structure.
    -- Helps avoid green slime and helps to remember equations.
    data From⟨_,_,_⟩  c : Set where
      this    : ∀ a → (i : a A≺ c) → (px : P a) → From⟨_,_,_⟩ c
      that    : ∀ b → (i : b B≺ c) → (qx : Q b) → From⟨_,_,_⟩ c
      these : ∀ a b → (i : a & b ≺ c) → (rx : R (a , b)) → From⟨_,_,_⟩ c

  -- Using UIP we can prove that from is propositional up-to the predicate witness
  module _ {P : Pred A 0ℓ} {Q : Pred B 0ℓ} {R : Pred (A × B) 0ℓ} where
  
    intro-from-a : ∀ {a c} → a A≺ c → P a → From⟪ P , Q , R ⟫ c
    intro-from-a eq px rewrite eq = px

    intro-from-b : ∀ {b c} → b B≺ c → Q b → From⟪ P , Q , R ⟫ c
    intro-from-b eq qx rewrite eq = qx
    
    intro-from-ab : ∀ {a b c} → a & b ≺ c → R (a , b) → From⟪ P , Q , R ⟫ c
    intro-from-ab eq qx rewrite eq = qx

    from-inv-a : ∀ {a c} → From⟪ P , Q , R ⟫ c → a A≺ c → P a
    from-inv-a f eq rewrite eq = f

    from-inv-b : ∀ {b c} → From⟪ P , Q , R ⟫ c → b B≺ c → Q b
    from-inv-b f eq rewrite eq = f

    from-inv-ab : ∀ {a b c} → From⟪ P , Q , R ⟫ c → a & b ≺ c → R (a , b)
    from-inv-ab f eq rewrite eq = f 

  --
  -- the types of the inverse functions
  --

  InjaInverses : (A → C) → A → Set
  InjaInverses inja a = From⟪ (_≡ a) , ∅ , (_≡ a) ∘ proj₁ ⟫ (inja a)

  InjbInverses : (B → C) → B → Set
  InjbInverses injb b = From⟪ ∅ , (_≡ b) , (_≡ b) ∘ proj₂ ⟫ (injb b)

  RightInverses : (A → C) → (B → C) → C → Set
  RightInverses inja injb c = 
    From⟪ (λ a → inja a ≡ c) 
        , (λ b → injb b ≡ c) 
        , (λ (a , b) → inja a ≡ c × injb b ≡ c) ⟫ c

-- A preunion, with the proofs that the functions are proper inverses of each-other
record Union (A B C : Set) : Set₁ where
  constructor union
  field
    inja : A → C
    injb : B → C
    from : C → These A B

  open From from public

  field
    a-inv   : ∀ a → InjaInverses inja a
    b-inv   : ∀ b → InjbInverses injb b
    from-inv : ∀ c → RightInverses inja injb c

  module _ where

    a-inv'    : ∀ a → From⟨ (λ a' → a ≡ a') 
              , ∅
              , (λ (a' , _) → a ≡ a') ⟩ (inja a)
    a-inv' a with from (inja a) | P.inspect from (inja a)
    ... | this x | P.[ eq ]     = this _ eq $ P.sym $ from-inv-a (a-inv a) eq
    ... | that x | P.[ eq ]     = that _ eq $ from-inv-b (a-inv a) eq
    ... | these x x₁ | P.[ eq ] = these _ _ eq $ P.sym $ from-inv-ab (a-inv a) eq

    b-inv'    : ∀ b → From⟨ ∅
              , (λ b' → b ≡ b') 
              , (λ (_ , b') → b ≡ b') ⟩ (injb b)
    b-inv' b with from (injb b) | P.inspect from (injb b)
    ... | this x | P.[ eq ]     = this _ eq $ from-inv-a (b-inv b) eq
    ... | that x | P.[ eq ]     = that _ eq $ P.sym $ from-inv-b (b-inv b) eq
    ... | these x x₁ | P.[ eq ] = these _ _ eq $ P.sym $ from-inv-ab (b-inv b) eq

    postulate from-inv' : ∀ c → From⟨ (λ a → inja a ≡ c) 
                        , (λ b → injb b ≡ c) 
                        , (λ (a , b) → inja a ≡ c × injb b ≡ c) ⟩ c
    -- from-inv' = {!!}

  module _ where
    A≺-inv : ∀ {a c} → a A≺ c → inja a ≡ c
    A≺-inv {a} {c} eq = from-inv-a (from-inv c) eq

    B≺-inv : ∀ {b c} → b B≺ c → injb b ≡ c
    B≺-inv {b} {c} eq = from-inv-b (from-inv c) eq

    A&B≺-inv : ∀ {a b c} → a & b ≺ c → inja a ≡ c × injb b ≡ c
    A&B≺-inv {a} {b} {c} eq = from-inv-ab (from-inv c) eq

  -- We can prove that inja, injb and from are injective using the inverses
  module _ where

    from-injective : ∀ {c c'} → from c ≡ from c' → c ≡ c'
    from-injective {c} {c'} eq with from-inv' c
    ... | From.this a i refl = from-inv-a (from-inv c') (P.trans (P.sym eq) i)
    ... | From.that b i refl = from-inv-b (from-inv c') (P.trans (P.sym eq) i)
    ... | From.these a b i (refl , eq') = begin
      inja a ≡⟨ P.sym eq' ⟩
      injb b ≡⟨ (proj₂ $ from-inv-ab (from-inv c') (P.trans (P.sym eq) i)) ⟩
      c' ∎

    inja-injective : ∀ {a a'} → inja a ≡ inja a' → a ≡ a'
    inja-injective {a} {a'} eq with a-inv' a
    ... | From.this a₁ i refl    = from-inv-a (a-inv a') (P.trans (P.cong from (P.sym eq)) i)
    ... | From.these a₁ b i refl = from-inv-ab (a-inv a') (P.trans (P.cong from (P.sym eq)) i)

    injb-injective : ∀ {b b'} → injb b ≡ injb b' → b ≡ b'
    injb-injective {b} {b'} eq with b-inv' b
    ... | From.that _ i refl    = from-inv-b (b-inv b') (P.trans (P.cong from (P.sym eq)) i)
    ... | From.these _ b i refl = from-inv-ab (b-inv b') (P.trans (P.cong from (P.sym eq)) i)

  module _ where

    a≺inja : ∀ {a a'} → a' A≺ inja a → a ≡ a'
    a≺inja p with q ← A≺-inv p = P.sym $ inja-injective q

    b≺injb : ∀ {b b'} → b' B≺ injb b → b ≡ b'
    b≺injb p with q ← B≺-inv p = P.sym $ injb-injective q

    a&b≺injb : ∀ {a b b'} → a & b' ≺ injb b → a & b ≺ injb b
    a&b≺injb eq with eq' ← proj₂ (A&B≺-inv eq) rewrite injb-injective eq' = eq

    a&b≺inja : ∀ {a b a'} → a' & b ≺ inja a → a & b ≺ inja a
    a&b≺inja eq with eq' ← proj₁ (A&B≺-inv eq) rewrite inja-injective eq' = eq

    ¬A≺injb : ∀ {a b} → ¬ (a A≺ injb b)
    ¬A≺injb {a} {b} eq with b-inv' b
    ... | that _ i qx     = ¬this&that eq i
    ... | these _ b₁ i rx = ¬this&these eq i

    ¬B≺inja : ∀ {a b} → ¬ (b B≺ inja a)
    ¬B≺inja {a} {b} eq with a-inv' a
    ... | this _ i qx     = ¬this&that i eq
    ... | these _ b₁ i rx = ¬that&these eq i

⊔-rel : Rel₃ Set
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

    postulate prf : ∀ c → From.RightInverses (from ∘ f⁻¹) (f ∘ inja) (f ∘ injb) c
    -- prf d with from-inv' (f⁻¹ d)
    -- ... | this _ i px = {!!} -- From.this _ i (P.trans (P.cong f px) (inverseˡ _))
    -- ... | that _ i px = {!!} -- From.that _ i (P.trans (P.cong f px) (inverseˡ _))
    -- ... | these _ _ i (px , qx) = {!!}
    --   -- From.these _ _ i (P.trans (P.cong f px) (inverseˡ _) , P.trans (P.cong f qx) (inverseˡ _))

Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ ⊔-semigroupˡ {B} {C}) {A} {D} eq σ = 
  {!!} -- union (inja ∘ f⁻¹) injb from' prf₁ prf₂ prf
  -- where 
  --   open Union σ
  --   open Inverse eq

  --   from' : C → These D B
  --   from' = These.map₁ f ∘ from
    
  --   prf₁ : ∀ a → From.InjaInverses from' (inja ∘ f⁻¹) a
  --   prf₁ a with a-inv' (f⁻¹ a)
  --   ... | From.this ._ i refl    = {!!}
  --     -- From.this _ (P.trans (P.cong (These.map f _) i) (P.cong this (inverseˡ _))) refl
  --   ... | From.these ._ b i refl = {!!}
  --     -- From.these _ _ (P.trans (P.cong (These.map f _) i) (P.cong (λ x → these x _) (inverseˡ _))) refl

  --   prf₂ : ∀ b → From.InjbInverses from' injb b
  --   prf₂ b with b-inv' b
  --   ... | From.that .b i refl = {!!} -- From.that _ (P.cong (These.map _ _) i) refl
  --   ... | From.these a .b i refl = {!!} -- From.these _ _ (P.cong (These.map _ _) i) refl
    
  --   prf : ∀ c → From.RightInverses from' (inja ∘ f⁻¹) injb c
  --   prf c with from-inv' c
  --   ... | this _ i px = {!!}
  --     -- From.this _ (P.cong (These.map₁ f) i) (P.trans (P.cong inja (inverseʳ _)) px)
  --   ... | that _ i px = {!!}
  --     -- From.that _ (P.cong (These.map₁ f) i) px
  --   ... | these _ _ i (px , qx) = {!!}
  --     -- From.these _ _ (P.cong (These.map _ _) i) (P.trans (P.cong inja (inverseʳ _)) px , qx)

IsPartialSemigroupˡ.assocᵣ ⊔-semigroupˡ {A} {B} {AB} {C} {ABC} σ₁ σ₂ = 
  BC , union a→abc bc→abc ←abc a-inv {!!} right , union b→bc c→bc ←bc {!!} {!!} {!!}
  where
    module U₁ = Union σ₁
    module U₂ = Union σ₂
    open U₁ using () renaming (inja to a→ab; injb to b→ab)
    open U₂ using () renaming (inja to ab→abc; injb to c→abc; _B≺_ to _C≺_; _A≺_ to _AB≺_)
    
    a→abc : A → ABC
    a→abc = ab→abc ∘ a→ab
    
    b→abc : B → ABC
    b→abc = ab→abc ∘ b→ab
    
    BC = Σ[ abc ∈ ABC ] U₂.From⟪ U₁.From⟪ ∅ , U , U ⟫ , U , U ⟫ abc

    bc→abc : BC → ABC
    bc→abc = proj₁

    b→bc : B → BC
    b→bc b with U₁.b-inv' b
    b→bc b | From.that .b i refl with U₂.a-inv' (b→ab b)
    ... | From.this .(Union.injb σ₁ b) i₁ refl     = -, U₂.intro-from-a i₁ (U₁.intro-from-b i tt)
    ... | From.these .(Union.injb σ₁ b) c i₁ refl  = -, U₂.intro-from-ab i₁ tt
    b→bc b | From.these a .b i refl with U₂.a-inv' (b→ab b)
    ... | From.this .(Union.injb σ₁ b) i₁ refl     = -, U₂.intro-from-a i₁ (U₁.intro-from-ab i tt)
    ... | From.these .(Union.injb σ₁ b) b₁ i₁ refl = -, U₂.intro-from-ab i₁ tt

    c→bc : C → BC
    c→bc c with U₂.b-inv' c
    ... | Union.that .c c≺abc refl        = _ , U₂.intro-from-b c≺abc tt
    ... | Union.these ab .c ab&c≺abc refl = _ , U₂.intro-from-ab ab&c≺abc tt

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
