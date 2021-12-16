{-# OPTIONS --without-K --safe #-}

module Helium.Algebra.Field where

open import Algebra
open import Level
open import Relation.Binary
open import Relation.Nullary

module _
  {a ℓ} {A : Set a}
  (_≈_ : Rel A ℓ)
  where

  record IsField (+ _*_ : Op₂ A) (- _⁻¹ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ) where
    field
      isCommutativeRing : IsCommutativeRing _≈_ + _*_ - 0# 1#
      ⁻¹-cong           : Congruent₁ _≈_ _⁻¹
      ⁻¹-inverseˡ       : ∀ x → ¬ x ≈ 0# → ((x ⁻¹) * x) ≈ 1#
      ⁻¹-inverseʳ       : ∀ x → ¬ x ≈ 0# → (x * (x ⁻¹)) ≈ 1#

    open IsCommutativeRing isCommutativeRing public
