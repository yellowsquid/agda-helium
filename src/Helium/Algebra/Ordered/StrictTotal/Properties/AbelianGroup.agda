------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered abelian groups
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.AbelianGroup
  {ℓ₁ ℓ₂ ℓ₃}
  (abelianGroup : AbelianGroup ℓ₁ ℓ₂ ℓ₃)
  where

open AbelianGroup abelianGroup

open import Relation.Binary.Core
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.AbelianGroup Unordered.abelianGroup public
open import Algebra.Properties.CommutativeMonoid.Mult.TCOptimised Unordered.commutativeMonoid public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Group group public
  using (<⇒≱; ≤⇒≯; >⇒≉; ≈⇒≯; <⇒≉; ≈⇒≮; ≤∧≉⇒<; ≥∧≉⇒>; x<y⇒ε<yx⁻¹)

⁻¹-anti-mono : _⁻¹ Preserves _<_ ⟶ _>_
⁻¹-anti-mono {x} {y} x<y = begin-strict
  y ⁻¹            ≈˘⟨ identityˡ (y ⁻¹) ⟩
  ε ∙ y ⁻¹        <⟨  ∙-invariantʳ (y ⁻¹) (x<y⇒ε<yx⁻¹ x<y) ⟩
  y ∙ x ⁻¹ ∙ y ⁻¹ ≈⟨  xyx⁻¹≈y y (x ⁻¹) ⟩
  x ⁻¹            ∎
