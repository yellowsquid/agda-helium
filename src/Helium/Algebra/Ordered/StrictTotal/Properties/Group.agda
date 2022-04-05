------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered groups
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Group
  {ℓ₁ ℓ₂ ℓ₃}
  (group : Group ℓ₁ ℓ₂ ℓ₃)
  where

open Group group
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

open import Algebra.Definitions
open import Function using (_∘_; flip; Injective)
open import Relation.Binary.Core
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.Group Unordered.group public
open import Algebra.Properties.Monoid.Mult.TCOptimised Unordered.monoid public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Monoid monoid public
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
  )
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public

--------------------------------------------------------------------------------
---- Properties of _⁻¹

---- Congruences

-- _<_

⁻¹-anti-mono-< : _⁻¹ Preserves _<_ ⟶ _>_
⁻¹-anti-mono-< {x} {y} x<y = begin-strict
  y ⁻¹              ≈˘⟨ identityˡ (y ⁻¹) ⟩
  ε ∙ y ⁻¹          ≈˘⟨ ∙-congʳ (inverseˡ x) ⟩
  x ⁻¹ ∙ x ∙ y ⁻¹   <⟨  ∙-monoʳ-< (∙-monoˡ-< x<y) ⟩
  x ⁻¹ ∙ y ∙ y ⁻¹   ≈⟨  assoc (x ⁻¹) y (y ⁻¹) ⟩
  x ⁻¹ ∙ (y ∙ y ⁻¹) ≈⟨  ∙-congˡ (inverseʳ y) ⟩
  x ⁻¹ ∙ ε          ≈⟨  identityʳ (x ⁻¹) ⟩
  x ⁻¹              ∎

-- _≤_

⁻¹-anti-mono-≤ : _⁻¹ Preserves _≤_ ⟶ _≥_
⁻¹-anti-mono-≤ {x} {y} x≤y = begin
  y ⁻¹              ≈˘⟨ identityˡ (y ⁻¹) ⟩
  ε ∙ y ⁻¹          ≈˘⟨ ∙-congʳ (inverseˡ x) ⟩
  x ⁻¹ ∙ x ∙ y ⁻¹   ≤⟨  ∙-monoʳ-≤ (∙-monoˡ-≤ x≤y) ⟩
  x ⁻¹ ∙ y ∙ y ⁻¹   ≈⟨  assoc (x ⁻¹) y (y ⁻¹) ⟩
  x ⁻¹ ∙ (y ∙ y ⁻¹) ≈⟨  ∙-congˡ (inverseʳ y) ⟩
  x ⁻¹ ∙ ε          ≈⟨  identityʳ (x ⁻¹) ⟩
  x ⁻¹              ∎

---- Cancellative

-- _<_

⁻¹-anti-cancel-< : Injective _<_ _>_ _⁻¹
⁻¹-anti-cancel-< x⁻¹>y⁻¹ = ≰⇒> (<⇒≱ x⁻¹>y⁻¹ ∘ ⁻¹-anti-mono-≤)

-- _≤_

⁻¹-anti-cancel-≤ : Injective _≤_ _≥_ _⁻¹
⁻¹-anti-cancel-≤ x⁻¹≥y⁻¹ = ≮⇒≥ (≤⇒≯ x⁻¹≥y⁻¹ ∘ ⁻¹-anti-mono-<)

---- Preserves signs

-- _<_

x<ε⇒x⁻¹>ε : ∀ {x} → x < ε → x ⁻¹ > ε
x<ε⇒x⁻¹>ε {x} x<ε = begin-strict
  ε    ≈˘⟨ ε⁻¹≈ε ⟩
  ε ⁻¹ <⟨  ⁻¹-anti-mono-< x<ε ⟩
  x ⁻¹ ∎

x>ε⇒x⁻¹<ε : ∀ {x} → x > ε → x ⁻¹ < ε
x>ε⇒x⁻¹<ε {x} x>ε = begin-strict
  x ⁻¹ <⟨ ⁻¹-anti-mono-< x>ε ⟩
  ε ⁻¹ ≈⟨ ε⁻¹≈ε ⟩
  ε    ∎

-- _≤_

x≤ε⇒x⁻¹≥ε : ∀ {x} → x ≤ ε → x ⁻¹ ≥ ε
x≤ε⇒x⁻¹≥ε {x} x≤ε = begin
  ε    ≈˘⟨ ε⁻¹≈ε ⟩
  ε ⁻¹ ≤⟨  ⁻¹-anti-mono-≤ x≤ε ⟩
  x ⁻¹ ∎

x≥ε⇒x⁻¹≤ε : ∀ {x} → x ≥ ε → x ⁻¹ ≤ ε
x≥ε⇒x⁻¹≤ε {x} x≥ε = begin
  x ⁻¹ ≤⟨ ⁻¹-anti-mono-≤ x≥ε ⟩
  ε ⁻¹ ≈⟨ ε⁻¹≈ε ⟩
  ε    ∎

---- Respects signs

-- _<_

x⁻¹<ε⇒x>ε : ∀ {x} → x ⁻¹ < ε → x > ε
x⁻¹<ε⇒x>ε {x} x⁻¹<ε = begin-strict
  ε       <⟨ x<ε⇒x⁻¹>ε x⁻¹<ε ⟩
  x ⁻¹ ⁻¹ ≈⟨ ⁻¹-involutive x ⟩
  x       ∎

x⁻¹>ε⇒x<ε : ∀ {x} → x ⁻¹ > ε → x < ε
x⁻¹>ε⇒x<ε {x} x⁻¹>ε = begin-strict
  x       ≈˘⟨ ⁻¹-involutive x ⟩
  x ⁻¹ ⁻¹ <⟨  x>ε⇒x⁻¹<ε x⁻¹>ε ⟩
  ε       ∎

-- _≤_

x⁻¹≤ε⇒x≥ε : ∀ {x} → x ⁻¹ ≤ ε → x ≥ ε
x⁻¹≤ε⇒x≥ε {x} x⁻¹≤ε = begin
  ε       ≤⟨ x≤ε⇒x⁻¹≥ε x⁻¹≤ε ⟩
  x ⁻¹ ⁻¹ ≈⟨ ⁻¹-involutive x ⟩
  x       ∎

x⁻¹≥ε⇒x≤ε : ∀ {x} → x ⁻¹ ≥ ε → x ≤ ε
x⁻¹≥ε⇒x≤ε {x} x⁻¹≥ε = begin
  x       ≈˘⟨ ⁻¹-involutive x ⟩
  x ⁻¹ ⁻¹ ≤⟨  x≥ε⇒x⁻¹≤ε x⁻¹≥ε ⟩
  ε       ∎

---- Preserves and respects signs (_≈_)

x≈ε⇒x⁻¹≈ε : ∀ {x} → x ≈ ε → x ⁻¹ ≈ ε
x≈ε⇒x⁻¹≈ε {x} x≈ε = ≮∧≯⇒≈ (<-irrefl (Eq.sym x≈ε) ∘ x⁻¹<ε⇒x>ε) (<-irrefl x≈ε ∘ x⁻¹>ε⇒x<ε)

x⁻¹≈ε⇒x≈ε : ∀ {x} → x ⁻¹ ≈ ε → x ≈ ε
x⁻¹≈ε⇒x≈ε {x} x⁻¹≈ε = ≮∧≯⇒≈ (<-irrefl (Eq.sym x⁻¹≈ε) ∘ x<ε⇒x⁻¹>ε) (<-irrefl x⁻¹≈ε ∘ x>ε⇒x⁻¹<ε)

-- ---- Infer signs

-- -- _≈_

-- x⁻¹≈x⇒x≈ε : ∀ {x} → x ⁻¹ ≈ x → x ≈ ε
-- x⁻¹≈x⇒x≈ε {x} x⁻¹≈x = ≮∧≯⇒≈
--   (λ x<ε → <-asym x<ε (begin-strict
--     ε    <⟨ x<ε⇒x⁻¹>ε x<ε ⟩
--     x ⁻¹ ≈⟨ x⁻¹≈x ⟩
--     x    ∎))
--   (λ x>ε → <-asym x>ε (begin-strict
--     x    ≈˘⟨ x⁻¹≈x ⟩
--     x ⁻¹ <⟨  x>ε⇒x⁻¹<ε x>ε ⟩
--     ε    ∎))

-- -- _<_

-- x⁻¹<x⇒x>ε : ∀ {x} → x ⁻¹ < x → x > ε
-- x⁻¹<x⇒x>ε x⁻¹<x = ≰⇒> (<⇒≱ x⁻¹<x ∘ λ x≤ε → ≤-trans x≤ε (x≤ε⇒x⁻¹≥ε x≤ε))

-- x⁻¹>x⇒x<ε : ∀ {x} → x ⁻¹ > x → x < ε
-- x⁻¹>x⇒x<ε x⁻¹>x = ≰⇒> (<⇒≱ x⁻¹>x ∘ λ x≥ε → ≤-trans (x≥ε⇒x⁻¹≤ε x≥ε) x≥ε)

-- -- _≤_

---- Miscellaneous

x<y⇒ε<y∙x⁻¹ : ∀ {x y} → x < y → ε < y ∙ x ⁻¹
x<y⇒ε<y∙x⁻¹ {x} {y} x<y = begin-strict
  ε        ≈˘⟨ inverseʳ x ⟩
  x ∙ x ⁻¹ <⟨  ∙-monoʳ-< x<y ⟩
  y ∙ x ⁻¹ ∎

ε<y∙x⁻¹⇒x<y : ∀ {x y} → ε < y ∙ x ⁻¹ → x < y
ε<y∙x⁻¹⇒x<y {x} {y} ε<yx⁻¹ = begin-strict
  x              ≈˘⟨ identityˡ x ⟩
  ε ∙ x          <⟨  ∙-monoʳ-< ε<yx⁻¹ ⟩
  y ∙ x ⁻¹ ∙ x   ≈⟨  assoc y (x ⁻¹) x ⟩
  y ∙ (x ⁻¹ ∙ x) ≈⟨  ∙-congˡ (inverseˡ x) ⟩
  y ∙ ε          ≈⟨  identityʳ y ⟩
  y              ∎
