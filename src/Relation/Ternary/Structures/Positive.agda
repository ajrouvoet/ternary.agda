

-- record IsPositive {a e} {A : Set a} (Eq : A → A → Set e) (sep : Rel₃ A) ε : Set (suc a ⊔ e) where
--   open Rel₃ sep

--   field
--     overlap {{ isSep }} : IsSep Eq sep

--   field
--     ∙-εˡ : ∀ {Φ₁ Φ₂} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≡ ε

--   ∙-ε : ∀ {Φ₁ Φ₂} {{_ : HasUnit Eq sep ε}} → Φ₁ ∙ Φ₂ ≣ ε → Φ₁ ≡ ε × Φ₂ ≡ ε
--   ∙-ε σ with ∙-εˡ σ
--   ... | P.refl = P.refl , ε-unique (sym $ ∙-id⁻ˡ σ)
--     where open IsEquivalence {{...}}

-- open IsPositive ⦃...⦄ public

-- record HasCrossSplit⁺ {a e} {A : Set a} (Eq : A → A → Set e) (sep : Rel₃ A) : Set (suc a ⊔ e) where
--   open Rel₃ sep

--   field
--     overlap {{ isSep }} : IsSep Eq sep
--     cross : ∀ {a b c d z}
--       → a ∙ b ≣ z
--       → c ∙ d ≣ z
--       → Σ[ frags ∈ (A × A × A × A) ]
--         let ac , ad , bc , bd = frags
--         in ac ∙ ad ≣ a
--          × bc ∙ bd ≣ b
--          × ac ∙ bc ≣ c
--          × ad ∙ bd ≣ d

-- open HasCrossSplit⁺ ⦃...⦄ public

-- record HasCrossSplit⁻ {a e} {A : Set a} (Eq : A → A → Set e) (sep : Rel₃ A) : Set (suc a ⊔ e) where
--   open Rel₃ sep
--   field
--     overlap {{ isSep }} : IsSep Eq sep
--     uncross : ∀ {a b c d ac ad bc bd}
--       → ac ∙ ad ≣ a
--       → bc ∙ bd ≣ b
--       → ac ∙ bc ≣ c
--       → ad ∙ bd ≣ d
--       → Σ[ z ∈ A ]
--           a ∙ b ≣ z
--         × c ∙ d ≣ z

-- open HasCrossSplit⁻ {{...}} public

-- open Rel₃ {{...}} public
