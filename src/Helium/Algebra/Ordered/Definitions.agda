------------------------------------------------------------------------
-- Agda Helium
--
-- Ordering properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Helium.Algebra.Ordered.Definitions
  {a ℓ} {A : Set a} -- The underlying set
  (_≤_ : Rel A ℓ)   -- The underlying order
  where

open import Algebra.Core
open import Data.Product using (_×_)

LeftInvariant : Op₂ A → Set _
LeftInvariant _∙_ = ∀ {x y} z → x ≤ y → (z ∙ x) ≤ (z ∙ y)

RightInvariant : Op₂ A → Set _
RightInvariant _∙_ = ∀ {x y} z → x ≤ y → (x ∙ z) ≤ (y ∙ z)

Invariant : Op₂ A → Set _
Invariant ∙ = LeftInvariant ∙ × RightInvariant ∙

PreservesPositive : A → Op₂ A → Set _
PreservesPositive 0# _∙_ = ∀ {x y} → 0# ≤ x → 0# ≤ y → 0# ≤ (x ∙ y)
