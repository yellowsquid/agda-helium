------------------------------------------------------------------------
-- Agda Helium
--
-- Relations between properties of functions when the underlying relation is a setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Helium.Algebra.Consequences.Setoid {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Algebra.Core
open import Algebra.Definitions _≈_
open import Data.Product using (_,_)
open import Helium.Algebra.Core
open import Helium.Algebra.Definitions _≈_
open import Relation.Nullary using (¬_)

open import Relation.Binary.Reasoning.Setoid S

module _ {0# 1#} {_∙_ : Op₂ A} {_⁻¹ : AlmostOp₁ _≈_ 0#} (cong : Congruent₂ _∙_) where
  assoc+id+invʳ⇒invˡ-unique : Associative _∙_ →
                              Identity 1# _∙_ →
                              AlmostRightInverse 1# _⁻¹ _∙_ →
                              ∀ x {y} (y≉0 : ¬ y ≈ 0#) →
                              (x ∙ y) ≈ 1# → x ≈ (y≉0 ⁻¹)
  assoc+id+invʳ⇒invˡ-unique assoc (idˡ , idʳ) invʳ x {y} y≉0 eq = begin
    x                  ≈˘⟨ idʳ x ⟩
    x ∙ 1#             ≈˘⟨ cong refl (invʳ y≉0) ⟩
    x ∙ (y ∙ (y≉0 ⁻¹)) ≈˘⟨ assoc x y (y≉0 ⁻¹) ⟩
    (x ∙ y) ∙ (y≉0 ⁻¹) ≈⟨  cong eq refl ⟩
    1# ∙ (y≉0 ⁻¹)      ≈⟨  idˡ (y≉0 ⁻¹) ⟩
    y≉0 ⁻¹             ∎

  assoc+id+invˡ⇒invʳ-unique : Associative _∙_ →
                              Identity 1# _∙_ →
                              AlmostLeftInverse 1# _⁻¹ _∙_ →
                              ∀ {x} (x≉0 : ¬ x ≈ 0#)  y →
                              (x ∙ y) ≈ 1# → y ≈ (x≉0 ⁻¹)
  assoc+id+invˡ⇒invʳ-unique assoc (idˡ , idʳ) invˡ {x} x≉0 y eq = begin
    y                  ≈˘⟨ idˡ y ⟩
    1# ∙ y             ≈˘⟨ cong (invˡ x≉0) refl ⟩
    ((x≉0 ⁻¹) ∙ x) ∙ y ≈⟨  assoc (x≉0 ⁻¹) x y ⟩
    (x≉0 ⁻¹) ∙ (x ∙ y) ≈⟨  cong refl eq ⟩
    (x≉0 ⁻¹) ∙ 1#      ≈⟨  idʳ (x≉0 ⁻¹) ⟩
    x≉0 ⁻¹             ∎
