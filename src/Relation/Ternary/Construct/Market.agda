{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.Market {ℓ} {A : Set ℓ} (rel : Rel₃ A) where

open import Level hiding (Lift)
open import Data.Product
open import Function using (_∘_)

open import Relation.Unary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

private
  instance _ = rel

module _ where

  data Market : Set ℓ where
    supply  : (l : A) → Market
    demand : (r : A) → Market

module _
  {e} {_≈ₐ_ : A → A → Set e}
  {{sg : IsPartialSemigroup _≈ₐ_ rel}}
  {εₐ} {{_ : Emptiness {A = A} εₐ}}
  {{c : IsCommutative rel}} where

  data _≈_ : Market → Market → Set (ℓ ⊔ e) where
    supplys  : ∀ {a b} → a ≈ₐ b → supply a ≈ supply b
    demands : ∀ {a b} → a ≈ₐ b → demand a ≈ demand b

  data Split : Market → Market → Market → Set ℓ where
    supplyₗ : {r l₁ l₂ : A} (σ : l₂ ∙ r ≣ l₁) → Split (supply l₁) (demand r) (supply l₂)
    supplyᵣ : {r l₁ l₂ : A} (σ : r ∙ l₂ ≣ l₁) → Split (demand r) (supply l₁) (supply l₂)
    demand : {r₁ r₂ r : A} (σ : r₁ ∙ r₂ ≣ r) → Split (demand r₁) (demand r₂) (demand r)

  private
    assoc : ∀ {a b ab c abc} → Split a b ab → Split ab c abc → ∃ λ bc → (Split a bc abc) × (Split b c bc)
    assoc (supplyₗ σ₁) (supplyₗ σ₂) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₂ σ₁ in -, supplyₗ σ₃ , demand (∙-comm σ₄)
    assoc (supplyᵣ σ₁) (supplyₗ σ₂) =
      let _ , σ₃ , σ₄ = ∙-assocₗ σ₁ σ₂ in -, supplyᵣ σ₃ , supplyₗ σ₄
    assoc (demand σ₁) (supplyᵣ σ₂) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ (∙-comm σ₁) σ₂ in -, supplyᵣ σ₄ , supplyᵣ σ₃
    assoc (demand σ₁) (demand σ₂) =
      let _ , σ₃ , σ₄ = ∙-assocᵣ σ₁ σ₂ in -, demand σ₃ , demand σ₄

  instance ≈-equiv : IsEquivalence _≈_
  IsEquivalence.refl ≈-equiv {supply l}                = supplys ≈-refl
  IsEquivalence.refl ≈-equiv {demand r}               = demands ≈-refl
  IsEquivalence.sym ≈-equiv (supplys x)                = supplys (≈-sym x)
  IsEquivalence.sym ≈-equiv (demands x)               = demands (≈-sym x)
  IsEquivalence.trans ≈-equiv (supplys x) (supplys y)   = supplys (≈-trans x y)
  IsEquivalence.trans ≈-equiv (demands x) (demands y) = demands (≈-trans x y)

  instance market-rel : Rel₃ (Market)
  Rel₃._∙_≣_ market-rel = Split

  instance market-isCommutative : IsCommutative market-rel
  IsCommutative.∙-comm market-isCommutative (demand p) = demand (∙-comm p)
  IsCommutative.∙-comm market-isCommutative (supplyₗ σ) = supplyᵣ (∙-comm σ)
  IsCommutative.∙-comm market-isCommutative (supplyᵣ σ) = supplyₗ (∙-comm σ)

  instance market-empty : Emptiness {A = Market} (demand ε)
  market-empty = record {}

  private

    respˡ : ∀ {b ab} → Respect _≈_ (λ a → Split a b ab)
    Respect.coe respˡ (supplys x) (supplyₗ σ)  = supplyₗ (coe x σ)
    Respect.coe respˡ (demands x) (supplyᵣ σ) = supplyᵣ (coe x σ)
    Respect.coe respˡ (demands x) (demand σ) = demand (coe x σ)

    resp : ∀ {a b} → Respect _≈_ (λ ab → Split a b ab)
    Respect.coe resp (supplys x) (supplyₗ σ)  = supplyₗ (coe x σ)
    Respect.coe resp (demands x) (demand σ) = demand (coe x σ)
    Respect.coe resp (supplys x) (supplyᵣ σ)  = supplyᵣ (coe x σ)


    assoc' : RightAssoc market-rel
    assoc' (demand σ₁) (demand σ₂) with _ , σ₃ , σ₄ ← ∙-assocᵣ σ₁ σ₂ = -, demand σ₃ , demand σ₄
    assoc' (supplyₗ σ₁) (supplyₗ σ₂) with _ , σ₃ , σ₄ ← ∙-assocᵣ σ₂ σ₁ = -, supplyₗ σ₃ , demand (∙-comm σ₄)
    assoc' (supplyᵣ σ₁) (supplyₗ σ₂) with _ , σ₃ , σ₄ ← ∙-assocₗ σ₁ σ₂ = -, supplyᵣ σ₃ , supplyₗ σ₄
    assoc' (demand σ₁) (supplyᵣ σ₂) with _ , σ₃ , σ₄ ← ∙-assocᵣ (∙-comm σ₁) σ₂ = -, supplyᵣ σ₄ , supplyᵣ σ₃

  instance market-isSemigroup : IsPartialSemigroup _≈_ market-rel
  market-isSemigroup = IsPartialSemigroupˡ.semigroupˡ record
    { ∙-respects-≈ˡ = respˡ
    ; ∙-respects-≈  = resp
    ; assocᵣ = assoc'
    }

  data ○ {p} (P : Pred A p) : Pred (Market) (ℓ ⊔ p) where
    lift : ∀ {xs} → P xs → ○ P (demand xs)

  data ● {p} (P : Pred A p) : Pred (Market) (ℓ ⊔ p) where
    lift : ∀ {xs} → P xs → ● P (supply xs)

  ●-map : ∀ {p} {P Q : Pred A p} → ∀[ P ⇒ Q ] → ∀[ ● P ⇒ ● Q ]
  ●-map f (lift px) = lift (f px)

  record LeftOver {p} (P : A → A → Set p) rem : Set (ℓ ⊔ p) where
    constructor subtract
    field
      {sup dem} : A
      px  : P sup dem
      sub : dem ∙ rem ≣ sup


module _ {e} {_≈ₐ_ : A → A → Set e} {u}
  {{m    : IsPartialMonoid _≈ₐ_ rel u}}
  {{comm : IsCommutative rel}} where

  instance market-isMonoid : IsPartialMonoid _≈_ market-rel (demand ε)
  market-isMonoid = IsPartialMonoidˡ.partialMonoidˡ record
    { identityˡ  = λ where
        {supply l}  → supplyᵣ (IsPartialMonoid.∙-idˡ m)
        {demand r} → demand (IsPartialMonoid.∙-idˡ m)
    ; identity⁻ˡ = λ where
        (supplyᵣ σ) → supplys (≈-sym (IsPartialMonoid.∙-id⁻ˡ m σ))
        (demand σ) → demands (IsPartialMonoid.∙-id⁻ˡ m σ)
    }

  -- matching : ∀ {a b : A} {c d} → (demand a) ∙ (supply b) ≣ c → (demand (d ∙ a)) ∙ (supply (d ∙ b)) ≣ c
  -- matching (supplyᵣ σ) = supplyᵣ (∙-disjointₗ σ)

  -- module _ {p q} {P : Pred A p} {Q : Pred (A × A) q} where
    -- ○≺●ₗ : ∀[ P ⇒ (● Q ─✴ ● (Π₂ P ✴ Q)) ∘ demand ]
    -- ○≺●ₗ px ⟨ supplyₗ σ₁ ⟩ lift qx σ₂ with ∙-assocᵣ σ₁ σ₂
    -- ... | _ , σ₃ , σ₄ = lift (snd px ∙⟨ ∙-idˡ , σ₄ ⟩ qx ) σ₃

    -- ○≺●ᵣ : ∀[ ● (Π₂ P ✴ Q) ⇒ (○ P) ✴ ● Q ]
    -- ○≺●ᵣ (lift (snd px ∙⟨ σₗ , σᵣ ⟩ qx) σ₂) with ∙-assocₗ σ₂ σᵣ
    -- ... | _ , σ₃ , σ₄ = lift px ∙⟨ supplyᵣ (∙-comm σ₃) ⟩ lift qx (coe (≈-sym (∙-id⁻ˡ σₗ)) σ₄)

-- {- Complete with respect to a certain element -}
-- module _ {a} {A : Set a} {{r : Rel₃ A}} {u} {{ s : IsPartialMonoid r u }} where

--   open import Relation.Ternary.Separation.Construct.Product
--   open Morphism (market {A = A})

--   record _◑_ {p q} (P : Pred A p) (Q : Pred (A × A) q) (Φ : A × A) : Set (a ⊔ p ⊔ q) where
--     constructor _◑⟨_⟩_
--     field
--       {Φp Φq} : _
--       px  : P Φp
--       inc : proj₁ Φ ∙ Φp ≣ Φq
--       qx  : Q (Φq , proj₂ Φ)

--   -- the following cannot be proven unfortunately
--   -- _ : ∀[ (P ◑ Q₁) ✴ Q₂ ⇒ P ◑ (Q₁ ✴ Q₂) ]

--   absorb : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} →
--            ∀[ P ⇒ⱼ ● Q ─✴ ● (P ◑ Q) ]
--   app (absorb px) (lift qx k) (supplyᵣ σ) with ∙-assoc (∙-comm σ) k
--   ... | _ , σ₂ , σ₃ with ∙-assocₗ σ₂ (∙-comm σ₃)
--   ... | _ , σ₄ , σ₅ = lift (px ◑⟨ σ₅ ⟩ qx) σ₄

--   expell : ∀ {p q} {P : Pred A p} {Q : Pred (A × A) q} →
--            ∀[ ● (P ◑ Q) ⇒ J P ✴ ● Q ]
--   expell (lift (px ◑⟨ τ₁ ⟩ qx) k) with ∙-assocₗ (∙-comm τ₁) k
--   ... | _ , τ₃ , τ₄ = (inj px) ×⟨ supplyᵣ τ₃ ⟩ (lift qx τ₄)

-- {- Completion preserving updates -}
-- module _ {a} {A : Set a} {{r : Rel₃ A}} {u} {{ s : IsPartialMonoid r u }} where

--   open import Relation.Ternary.Separation.Construct.Product

--   record ⟰_ {p} (P : Pred (A × A) p) (Φᵢ : A × A) : Set (a ⊔ p) where
--     constructor complete
--     field
--       updater : ∀ {Φⱼ Φₖ} →
--                 Φᵢ ∙ Φⱼ ≣ (Φₖ , Φₖ) →
--                 ∃₂ λ Φₗ Φ → Φₗ ∙ Φⱼ ≣ (Φ , Φ) × P Φₗ
--   open ⟰_ public

--   ●-update : ∀ {p q} {P : Pred (A × A) p} {Q : Pred (A × A) q} →
--              ∀[ ○ (P ─✴ ⟰ Q) ⇒ ● P ─✴ ● Q ]
--   app (●-update (lift f)) (lift px σ₁) (supplyᵣ σ₂) with ∙-assoc (∙-comm σ₂) σ₁
--   ... | _ , σ₃ , σ₄ with updater (app f px (∙-idˡ , σ₄)) (∙-idʳ , ∙-comm σ₃)
--   ... | _ , _ , (σ₅ , σ₆) , qx with ∙-id⁻ʳ σ₅
--   ... | refl = lift qx (∙-comm σ₆)
