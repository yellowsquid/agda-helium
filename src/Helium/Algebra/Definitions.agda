------------------------------------------------------------------------
-- Agda Helium
--
-- More properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Helium.Algebra.Definitions
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality
  where

open import Algebra.Core
open import Data.Product using (_×_)
open import Helium.Algebra.Core
open import Relation.Nullary using (¬_)

AlmostCongruent₁ : ∀ {ε} → AlmostOp₁ _≈_ ε → Set _
AlmostCongruent₁ {ε} f =
  ∀ {x y} {x≉ε : ¬ x ≈ ε} {y≉ε : ¬ y ≈ ε} → x ≈ y → f x≉ε ≈ f y≉ε

AlmostLeftInverse : ∀ {ε} → A → AlmostOp₁ _≈_ ε → Op₂ A → Set _
AlmostLeftInverse {ε} e _⁻¹ _∙_ = ∀ {x} (x≉ε : ¬ x ≈ ε) → ((x≉ε ⁻¹) ∙ x) ≈ e

AlmostRightInverse : ∀ {ε} → A → AlmostOp₁ _≈_ ε → Op₂ A → Set _
AlmostRightInverse {ε} e _⁻¹ _∙_ = ∀ {x} (x≉ε : ¬ x ≈ ε) → (x ∙ (x≉ε ⁻¹)) ≈ e

AlmostInverse : ∀ {ε} → A → AlmostOp₁ _≈_ ε → Op₂ A → Set _
AlmostInverse e ⁻¹ ∙ = AlmostLeftInverse e ⁻¹ ∙ × AlmostRightInverse e ⁻¹ ∙
