{-# OPTIONS --safe #-}
module Relation.Ternary.Separation where

open import Relation.Ternary.Core public
  renaming
    ( _∙_≣_ to _⊎_≣_
    ; _∙⟨_⟩_ to _×⟨_⟩_
    ; _⊙_ to _✴_
    ; _─⊙_ to _─✴_)

open import Relation.Ternary.Structures public
