{-# OPTIONS --safe #-}
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
open import Axiom.UniquenessOfIdentityProofs.WithK
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

RightInverses′ : ∀ {A B C : Set} → (A → C) → (B → C) → C → These A B → Set
RightInverses′ inja injb c = 
  fold 
    (λ a → inja a ≡ c) 
    (λ b → injb b ≡ c) 
    (λ a b → inja a ≡ c × injb b ≡ c)

RightInverses : ∀ {A B C : Set} → (A → C) → (B → C) → (C → These A B) → Set
RightInverses inja injb from = ∀ c → RightInverses′ inja injb c (from c)

record Union {ℓ} (A B C : Set) : Set ℓ where
  constructor union
  field
    inja : A → C
    injb : B → C
    from : C → These A B

  field
    inja-inverse   : from ∘ inja P.≗ this
    injb-inverse   : from ∘ injb P.≗ that
    right-inverses : RightInverses inja injb from

  -- You can point out the elements of C that are only in A/B/in both A & B.
  module _ where

    _A≺_  = λ a c   → from c ≡ this a
    _B≺_  = λ b c   → from c ≡ that b
    _&_≺_ = λ a b c → from c ≡ these a b

    A≺-inv : ∀ {a c} → a A≺ c → inja a ≡ c
    A≺-inv {a} {c} eq with from c | right-inverses c
    ... | this x | inv rewrite (this-injective eq) = inv

    B≺-inv : ∀ {b c} → b B≺ c → injb b ≡ c
    B≺-inv {b} {c} eq with from c | right-inverses c
    ... | that x | inv rewrite (that-injective eq) = inv

    A&B≺-inv : ∀ {a b c} → a & b ≺ c → inja a ≡ c × injb b ≡ c
    A&B≺-inv {a} {b} {c} eq with from c | right-inverses c
    ... | these _ _ | inv with refl , refl ← these-injective eq = inv

  -- We can prove that inja, injb and from are injective using the inverses
  module _ where
    inja-injective : ∀ {a a'} → inja a ≡ inja a' → a ≡ a'
    inja-injective {a} {a'} eq = this-injective $ begin
      this a         ≡⟨ P.sym $ inja-inverse a ⟩
      from (inja a)  ≡⟨ P.cong from eq ⟩
      from (inja a') ≡⟨ inja-inverse a' ⟩
      this a' ∎

    injb-injective : ∀ {b b'} → injb b ≡ injb b' → b ≡ b'
    injb-injective {b} {b'} eq = that-injective $ begin
      that b         ≡⟨ P.sym $ injb-inverse b ⟩
      from (injb b)  ≡⟨ P.cong from eq ⟩
      from (injb b') ≡⟨ injb-inverse b' ⟩
      that b' ∎

    from-injective : ∀ {c c'} → from c ≡ from c' → c ≡ c'
    from-injective {c} {c'} eq with from c | right-inverses c
    ... | this _ | inv = P.trans (P.sym inv) (A≺-inv (P.sym eq))
    ... | that _ | inv = P.trans (P.sym inv) (B≺-inv (P.sym eq))
    ... | these _ _ | inv₁ , inv₂ with eq₁ , eq₂ ← A&B≺-inv (P.sym eq)
      = P.trans (P.sym inv₁) eq₁

  module _ where

    a&b≺injb : ∀ {a b b'} → a & b' ≺ injb b → a & b ≺ injb b
    a&b≺injb eq with eq' ← proj₂ (A&B≺-inv eq) rewrite injb-injective eq' = eq

    a&b≺inja : ∀ {a b a'} → a' & b ≺ inja a → a & b ≺ inja a
    a&b≺inja eq with eq' ← proj₁ (A&B≺-inv eq) rewrite inja-injective eq' = eq

    ¬A≺injb : ∀ {a b} → ¬ (a A≺ injb b)
    ¬A≺injb eq = ¬this&that eq (injb-inverse _)

    ¬B≺inja : ∀ {a b} → ¬ (b B≺ inja a)
    ¬B≺inja eq = ¬this&that (inja-inverse _) eq

  module _ (P : Pred A 0ℓ) (Q : Pred B 0ℓ) (R : Pred (A × B) 0ℓ) where
    data From⟨_,_,_⟩  c : Set where
      fromA    : ∀ a → a A≺ c → P a → From⟨_,_,_⟩ c
      fromB    : ∀ b → b B≺ c → Q b → From⟨_,_,_⟩ c
      fromBoth : ∀ a b → a & b ≺ c → R (a , b) → From⟨_,_,_⟩ c

  data From c : Set where
    fromA    : ∀ a → a A≺ c → From c
    fromB    : ∀ b → b B≺ c → From c
    fromBoth : ∀ a b → a & b ≺ c → From c

  module _ {P : Pred A 0ℓ} {Q : Pred B 0ℓ} {R : Pred (A × B) 0ℓ} where
  
    from-elim-a : ∀ {a c} → (f : From⟨ P , Q , R ⟩ c) → (e : a A≺ c) → Σ[ pa ∈ P a ] f ≡ fromA a e pa
    from-elim-a (fromA a x pa) eq with this-injective (P.trans (P.sym eq) x)
    ... | refl with refl ← uip x eq = pa , refl
    from-elim-a (fromB b eq' _) eq = ⊥-elim (¬this&that eq eq')
    from-elim-a (fromBoth a b eq' _) eq = ⊥-elim (¬this&these eq eq')

    from-elim-b : ∀ {b c} → (f : From⟨ P , Q , R ⟩ c) → (e : b B≺ c) → Σ[ qb ∈ Q b ] f ≡ fromB b e qb
    from-elim-b (fromB b eq' qb) eq with that-injective (P.trans (P.sym eq') eq)
    ... | refl with refl ← uip eq eq' = qb , refl
    from-elim-b (fromA a eq' _) eq = ⊥-elim (¬this&that eq' eq)
    from-elim-b (fromBoth a b eq' _) eq = ⊥-elim (¬that&these eq eq')

    from-inv-a : ∀ {a c} → From⟨ P , Q , R ⟩ c → a A≺ c → P a
    from-inv-a f = proj₁ ∘ from-elim-a f

    from-inv-b : ∀ {b c} → From⟨ P , Q , R ⟩ c → b B≺ c → Q b
    from-inv-b f = proj₁ ∘ from-elim-b f
    
  break : (c : C) → From c
  break c with from c | P.inspect from c
  ... | this a | P.[ eq ] = fromA _ eq
  ... | that b | P.[ eq ] = fromB _ eq
  ... | these a b | P.[ eq ] = fromBoth _ _ eq

  -- breaking an injection from b
  breakB : (b : B) → From⟨ ∅ , _≡ b , ((_≡ b) ∘ proj₂) ⟩ (injb b)
  breakB b with break (injb b)
  ... | fromA a a≺c          = fromA a a≺c (¬A≺injb a≺c)
  ... | fromB b' b'≺c        = fromB b (injb-inverse _) refl
  ... | fromBoth a b' a&b'≺c = fromBoth a b (a&b≺injb a&b'≺c) refl

  -- breaking an injection from a
  breakA : (a : A) → From⟨ _≡ a , ∅ , ((_≡ a) ∘ proj₁) ⟩ (inja a)
  breakA a with break (inja a)
  ... | fromA a' a'≺c = fromA a (inja-inverse _) refl
  ... | fromB b b≺c = fromB b b≺c (¬B≺inja b≺c)
  ... | fromBoth a' b a'&b≺c = fromBoth a b (a&b≺inja a'&b≺c) refl

⊔-rel : Rel₃ Set
Rel₃._∙_≣_ ⊔-rel = Union

instance ⊔-commutative : IsCommutative ⊔-rel 
IsCommutative.∙-comm ⊔-commutative σ = 
  union injb inja (These.swap ∘ from) prf₁ prf₂ prf
  where 
    open Union σ
    
    prf₁ : (These.swap ∘ from ∘ injb) P.≗ this
    prf₁ x rewrite injb-inverse x = refl

    prf₂ : (These.swap ∘ from ∘ inja) P.≗ that
    prf₂ x rewrite inja-inverse x = refl
    
    prf : RightInverses injb inja (These.swap ∘ from)
    prf ab with from ab | right-inverses ab
    ... | this _ | inv = inv
    ... | that _ | inv = inv
    ... | these _ _ | inv = Pr.swap inv

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
  union (f ∘ inja) (f ∘ injb) (from ∘ f⁻¹) 
    (λ x → P.trans (P.cong from (inverseʳ _)) (inja-inverse _)) 
    (λ x → P.trans (P.cong from (inverseʳ _)) (injb-inverse _)) 
    prf
  where 
    open Union σ
    open Inverse eq
    
    prf : RightInverses (f ∘ inja) (f ∘ injb) (from ∘ f⁻¹)
    prf d with from (f⁻¹ d) | right-inverses (f⁻¹ d)
    ... | this x     | inv = P.trans (P.cong f inv) (inverseˡ _)
    ... | that x     | inv = P.trans (P.cong f inv) (inverseˡ _)
    ... | these x x₁ | inv₁ , inv₂ = 
      P.trans (P.cong f inv₁) (inverseˡ _) , P.trans (P.cong f inv₂) (inverseˡ _)

Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ ⊔-semigroupˡ {B} {C}) {A} {D} eq σ = 
  union (inja ∘ f⁻¹) injb from' prf₁ prf₂ prf
  where 
    open Union σ
    open Inverse eq

    from' : C → These D B
    from' = These.map₁ f ∘ from
    
    prf₂ : from' ∘ injb P.≗ that
    prf₂ b rewrite injb-inverse b = refl

    prf₁ : from' ∘ inja ∘ f⁻¹ P.≗ this
    prf₁ a rewrite inja-inverse (f⁻¹ a) = P.cong this (inverseˡ _)
    
    prf : RightInverses (inja ∘ f⁻¹) injb from'
    prf c with from c | right-inverses c
    ... | this x | inv rewrite inverseʳ x = inv
    ... | that x | inv = inv
    ... | these x y | inv₁ , inv₂ = P.trans (P.cong inja (inverseʳ x)) inv₁ , inv₂

IsPartialSemigroupˡ.assocᵣ ⊔-semigroupˡ {A} {B} {AB} {C} {ABC} σ₁ σ₂ = 
  BC
  , union a→abc bc→abc ←abc a→abc-inverse bc→abc-inverse ←abc-inverses
  , union b→bc c→bc ←bc {!!} {!!} {!!}
  where
    module U₁ = Union σ₁
    module U₂ = Union σ₂
    open U₁ using (fromA; fromB) renaming (inja to a→ab; injb to b→ab)
    open U₂ using (_&_≺_) renaming (inja to ab→abc; injb to c→abc; _B≺_ to _C≺_; _A≺_ to _AB≺_)
    
    -- We specify BC as the elements from ABC that are *not only in A* 
    BC-pred = λ abc → U₂.From⟨ U₁.From⟨ ∅ , U , U ⟩ , U , U ⟩ abc
    BC = Σ[ abc ∈ ABC ] BC-pred abc
    
    -- The second projection of BC is a proposition (using UIP)
    BC-prop : ∀ {abc} → (p q : BC-pred abc) → p ≡ q
    BC-prop (Union.fromA ab ab≺abc x₁) q with U₂.from-elim-a q ab≺abc
    BC-prop (Union.fromA ab ab≺abc (Union.fromB b b≺ab _)) ._ | z , refl 
      with _ , refl ← U₁.from-elim-b z b≺ab = refl
    BC-prop (Union.fromA ab ab≺abc (Union.fromBoth a b x x₁)) ._ | z , refl = {!!}
    BC-prop (Union.fromB b x x₁) q = {!!}
    BC-prop (Union.fromBoth a b x x₁) q = {!!}
    
    a→abc : A → ABC
    a→abc = ab→abc ∘ a→ab
    
    bc→abc : BC → ABC
    bc→abc = proj₁

    b→bc : B → BC
    b→bc b with ab→abc $ b→ab b | U₁.breakB b | U₂.breakA (b→ab b)
    ... | abc | Union.fromB .b b≺ab refl | Union.fromA ._ ab≺abc refl = 
      abc , U₂.fromA _ ab≺abc (fromB b b≺ab tt)
    ... | abc | Union.fromB .b b≺ab refl | Union.fromBoth ._ c ab&c≺abc refl = 
      abc , U₂.fromBoth _ _ ab&c≺abc tt
    ... | abc | Union.fromBoth a .b a&b≺ab refl | Union.fromA ._ ab≺abc refl = 
      abc ,  U₂.fromA _ ab≺abc (U₁.fromBoth _ _ a&b≺ab tt)
    ... | abc | Union.fromBoth a .b a&b≺ab refl | Union.fromBoth ._ c ab&c≺abc refl = 
      abc ,  U₂.fromBoth _ _ ab&c≺abc tt

    c→bc : C → BC
    c→bc c with U₂.breakB c
    ... | Union.fromB .c c≺abc refl         = _ , U₂.fromB c c≺abc tt
    ... | Union.fromBoth ab .c a&c≺abc refl = _ , U₂.fromBoth ab c a&c≺abc tt

    -- we simultaneously write the right inverses and its proofs
    ←abc' : (abc : ABC) → Σ (These A BC) (RightInverses′ a→abc bc→abc abc)
    ←abc' abc with U₂.break abc
    ←abc' abc | Union.fromA ab ab≺abc with U₁.break ab
    ... | Union.fromA a a≺ab = 
        this a 
      , P.trans (P.cong ab→abc (U₁.A≺-inv a≺ab)) (U₂.A≺-inv ab≺abc) 
    ... | Union.fromB b b≺ab =
        that (abc , U₂.fromA ab ab≺abc (fromB b b≺ab tt))
      , refl
    ... | Union.fromBoth a b a&b≺ab = 
        these a (abc , U₂.fromA ab ab≺abc (U₁.fromBoth a b a&b≺ab tt))
      , P.trans (P.cong ab→abc (proj₁ $ U₁.A&B≺-inv a&b≺ab)) (U₂.A≺-inv ab≺abc) 
      , refl
    ←abc' abc | Union.fromB c  c≺abc = 
        that (abc , U₂.fromB c c≺abc tt) 
      , refl
    ←abc' abc | Union.fromBoth ab c ab&c≺abc with U₁.break ab
    ... | Union.fromA a a≺ab = 
        these a (abc , U₂.fromBoth ab c ab&c≺abc tt) 
      , P.trans (P.cong ab→abc (U₁.A≺-inv a≺ab)) (proj₁ $ U₂.A&B≺-inv ab&c≺abc) 
      , refl
    ... | Union.fromB b b≺ab = 
        that (abc , U₂.fromBoth ab c ab&c≺abc tt) 
      , refl
    ... | Union.fromBoth a b a&b≺ab = 
        these a (abc , U₂.fromBoth ab c ab&c≺abc tt) 
      , P.trans (P.cong ab→abc (proj₁ $ U₁.A&B≺-inv a&b≺ab)) (proj₁ $ U₂.A&B≺-inv ab&c≺abc)  
      , refl

    ←abc : ABC → These A BC
    ←abc = proj₁ ∘ ←abc'

    ←abc-inverses : RightInverses a→abc bc→abc ←abc
    ←abc-inverses = proj₂ ∘ ←abc'

    a→abc-inverse : ←abc ∘ a→abc P.≗ this
    a→abc-inverse a with ←abc' (a→abc a)
    ... | this x , snd = 
      P.cong this (U₁.inja-injective $ U₂.inja-injective snd)
    ... | that (._ , snd) , refl = 
      ⊥-elim (U₁.from-inv-a (U₂.from-inv-a snd (U₂.inja-inverse (a→ab a))) (U₁.inja-inverse a))
    ... | these x (._ , snd) , fst , refl = 
      ⊥-elim (U₁.from-inv-a (U₂.from-inv-a snd (U₂.inja-inverse (a→ab a))) (U₁.inja-inverse a))

    bc→abc-inverse : ←abc ∘ bc→abc P.≗ that
    bc→abc-inverse b with ←abc' (bc→abc b)
    bc→abc-inverse (_ , px) | that (._ , qx) , refl = P.cong (that ∘ (_ ,_)) (BC-prop qx px)
    ... | these x x₁ , fst , snd = {!!}
    ... | this x , snd = {!!}

    ←bc : BC → These B C
    ←bc (abc , Union.fromA a _ (Union.fromB b _ _)) = this b
    ←bc (abc , Union.fromA a _ (Union.fromBoth _ b _ _)) = this b
    ←bc (abc , Union.fromB c _ _) = that c
    ←bc (abc , Union.fromBoth ab c _ e) with U₁.break ab
    ... | Union.fromA a _ = that c
    ... | Union.fromB b _ = these b c
    ... | Union.fromBoth _ b _ = these b c

instance ⊔-semigroup : IsPartialSemigroup _↔_ ⊔-rel
⊔-semigroup = IsPartialSemigroupˡ.semigroupˡ ⊔-semigroupˡ

instance set-emptiness : Emptiness ⊥
set-emptiness = record {}

⊔-monoidˡ : IsPartialMonoidˡ _↔_ ⊔-rel ⊥
IsPartialMonoidˡ.identityˡ ⊔-monoidˡ  = union ⊥-elim id that (λ ()) (λ _ → refl) (λ _ → refl)
IsPartialMonoidˡ.identity⁻ˡ ⊔-monoidˡ σ = {!!}

instance ⊔-monoid : IsPartialMonoid _↔_ ⊔-rel ⊥
⊔-monoid = IsPartialMonoidˡ.partialMonoidˡ ⊔-monoidˡ

instance ⊔-intuitive : IsIntuitionistic U ⊔-rel
IsIntuitionistic.∙-copy ⊔-intuitive _ = union id id (λ x → these x x) {!!} {!λ!} {!!}
