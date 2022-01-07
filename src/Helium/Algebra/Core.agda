------------------------------------------------------------------------
-- Agda Helium
--
-- More core algebraic definitions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Algebra.Core where

open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (¬_)

AlmostOp₁ : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set (a ⊔ ℓ)
AlmostOp₁ {A = A} _≈_ ε = ∀ {x} → ¬ x ≈ ε → A

AlmostOp₂ : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set (a ⊔ ℓ)
AlmostOp₂ {A = A} _≈_ ε = ∀ (x : A) {y} → ¬ y ≈ ε → A
