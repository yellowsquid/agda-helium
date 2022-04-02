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
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )
open import Relation.Binary.Core
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.AbelianGroup Unordered.abelianGroup public
open import Algebra.Properties.CommutativeMonoid.Mult.TCOptimised Unordered.commutativeMonoid public
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Group group public
  using
  ( ∙-mono-<; ∙-monoˡ-<; ∙-monoʳ-<
  ; ∙-mono-≤; ∙-monoˡ-≤; ∙-monoʳ-≤

  ; ∙-cancelˡ-<; ∙-cancelʳ-<; ∙-cancel-<
  ; ∙-cancelˡ-≤; ∙-cancelʳ-≤; ∙-cancel-≤
  -- _∙_ pres signs
  ; x≥ε∧y>ε⇒x∙y>ε; x>ε∧y≥ε⇒x∙y>ε
  ; x≤ε∧y<ε⇒x∙y<ε; x<ε∧y≤ε⇒x∙y<ε
  ; x≥ε∧y≥ε⇒x∙y≥ε; x≤ε∧y≤ε⇒x∙y≤ε
  -- _∙_ resp signs
  ; x≤ε∧x∙y>ε⇒y>ε; x≤ε∧y∙x>ε⇒y>ε
  ; x<ε∧x∙y≥ε⇒y>ε; x<ε∧y∙x≥ε⇒y>ε
  ; x≥ε∧x∙y<ε⇒y<ε; x≥ε∧y∙x<ε⇒y<ε
  ; x>ε∧x∙y≤ε⇒y<ε; x>ε∧y∙x≤ε⇒y<ε
  ; x≤ε∧x∙y≥ε⇒y≥ε; x≤ε∧y∙x≥ε⇒y≥ε
  ; x≥ε∧x∙y≤ε⇒y≤ε; x≥ε∧y∙x≤ε⇒y≤ε

  ; ×-zeroˡ; ×-zeroʳ
  ; ×-identityˡ

  ; n≢0⇒×-monoˡ-<; x>ε⇒×-monoʳ-<; x<ε⇒×-anti-monoʳ-<
  ; ×-monoˡ-≤; x≥ε⇒×-monoʳ-≤; x≤ε⇒×-anti-monoʳ-≤

  ; ×-cancelˡ-<; x≥ε⇒×-cancelʳ-<; x≤ε⇒×-anti-cancelʳ-<
  ; n≢0⇒×-cancelˡ-≤; x>ε⇒×-cancelʳ-≤; x<ε⇒×-anti-cancelʳ-≤
  -- _×_ pres signs
  ; n≢0∧x>ε⇒n×x>ε; n≢0∧x<ε⇒n×x<ε
  ; x≥ε⇒n×x≥ε; x≤ε⇒n×x≤ε
  -- _×_ resp signs
  ; n×x>ε⇒x>ε; n×x<ε⇒x<ε
  ; n≢0∧n×x≥ε⇒x≥ε; n≢0∧n×x≤ε⇒x≤ε

  ; ⁻¹-anti-mono-<; ⁻¹-anti-mono-≤

  ; ⁻¹-cancel; ⁻¹-anti-cancel-<; ⁻¹-anti-cancel-≤

  ; x<ε⇒x⁻¹>ε; x>ε⇒x⁻¹<ε
  ; x≤ε⇒x⁻¹≥ε; x≥ε⇒x⁻¹≤ε

  ; x⁻¹<ε⇒x>ε; x⁻¹>ε⇒x<ε
  ; x⁻¹≤ε⇒x≥ε; x⁻¹≥ε⇒x≤ε

  ; x<y⇒ε<y∙x⁻¹ ; ε<y∙x⁻¹⇒x<y
  )
