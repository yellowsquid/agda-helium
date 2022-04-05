------------------------------------------------------------------------
--  Agda Helium
--
-- Algebraic properties of ordered division rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.DivisionRing
  {ℓ₁ ℓ₂ ℓ₃}
  (divisionRing : DivisionRing ℓ₁ ℓ₂ ℓ₃)
  where

open DivisionRing divisionRing
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  ; 0<a+0<b⇒0<ab to x>0∧y>0⇒x*y>0
  )

open import Function using (_∘_)
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.Ring Unordered.ring public
  renaming (-0#≈0# to -0≈0)
open import Helium.Algebra.Properties.AlmostGroup *-almostGroup public
  renaming
  ( x≉0⇒∙-cancelˡ to x≉0⇒*-cancelˡ
  ; x≉0⇒∙-cancelʳ to x≉0⇒*-cancelʳ
  ; ⁻¹-anti-homo-∙ to ⁻¹-anti-homo-*
  ; identityˡ-unique to *-identityˡ-unique
  ; identityʳ-unique to *-identityʳ-unique
  ; inverseˡ-unique to *-inverseˡ-unique
  ; inverseʳ-unique to *-inverseʳ-unique
  )
open import Algebra.Properties.Semiring.Mult.TCOptimised Unordered.semiring public
open import Algebra.Properties.Semiring.Exp.TCOptimised Unordered.semiring public
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Ring ring public
  using
  ( +-mono-<; +-monoˡ-<; +-monoʳ-<
  ; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤

  ; +-cancel-<; +-cancelˡ-<; +-cancelʳ-<
  ; +-cancel-≤; +-cancelˡ-≤; +-cancelʳ-≤

  ; x≥0∧y>0⇒x+y>0 ; x>0∧y≥0⇒x+y>0
  ; x≤0∧y<0⇒x+y<0 ; x<0∧y≤0⇒x+y<0
  ; x≥0∧y≥0⇒x+y≥0 ; x≤0∧y≤0⇒x+y≤0

  ; x≤0∧x+y>0⇒y>0 ; x≤0∧y+x>0⇒y>0 ; x<0∧x+y≥0⇒y>0 ; x<0∧y+x≥0⇒y>0
  ; x≥0∧x+y<0⇒y<0 ; x≥0∧y+x<0⇒y<0 ; x>0∧x+y≤0⇒y<0 ; x>0∧y+x≤0⇒y<0
  ; x≤0∧x+y≥0⇒y≥0 ; x≤0∧y+x≥0⇒y≥0
  ; x≥0∧x+y≤0⇒y≤0 ; x≥0∧y+x≤0⇒y≤0

  ; ×-zeroˡ; ×-zeroʳ
  ; ×-identityˡ

  ; n≢0⇒×-monoˡ-< ; x>0⇒×-monoʳ-< ; x<0⇒×-anti-monoʳ-<
  ; ×-monoˡ-≤; x≥0⇒×-monoʳ-≤; x≤0⇒×-anti-monoʳ-≤

  ; ×-cancelˡ-<; x≥0⇒×-cancelʳ-<; x≤0⇒×-anti-cancelʳ-<
  ; n≢0⇒×-cancelˡ-≤ ; x>0⇒×-cancelʳ-≤ ; x<0⇒×-anti-cancelʳ-≤

  ; n≢0∧x>0⇒n×x>0; n≢0∧x<0⇒n×x<0
  ; x≥0⇒n×x≥0; x≤0⇒n×x≤0

  ; n×x>0⇒x>0; n×x<0⇒x<0
  ; n≢0∧n×x≥0⇒x≥0; n≢0∧n×x≤0⇒x≤0

  ; -‿anti-mono-<; -‿anti-mono-≤
  ; -‿anti-cancel-<; -‿anti-cancel-≤

  ; x≈0⇒-x≈0 ; x<0⇒-x>0; x>0⇒-x<0; x≤0⇒-x≥0; x≥0⇒-x≤0
  ; -x≈0⇒x≈0 ; -x<0⇒x>0; -x>0⇒x<0; -x≤0⇒x≥0; -x≥0⇒x≤0

  ; x<y⇒0<y-x; 0<y-x⇒x<y
  ; x≤y⇒0≤y-x; 0≤y-x⇒x≤y

  ; x<y+z⇒x-z<y

  ; 0≤1; 1≈0⇒x≈y; x≉y⇒0<1; x<y⇒0<1

  ; x>0⇒*-monoˡ-<; x>0⇒*-monoʳ-<; x<0⇒*-anti-monoˡ-<; x<0⇒*-anti-monoʳ-<
  ; x≥0⇒*-monoˡ-≤; x≥0⇒*-monoʳ-≤; x≤0⇒*-anti-monoˡ-≤; x≤0⇒*-anti-monoʳ-≤

  ; x≥0⇒*-cancelˡ-<; x≥0⇒*-cancelʳ-<; x≤0⇒*-anti-cancelˡ-<; x≤0⇒*-anti-cancelʳ-<
  ; x>0⇒*-cancelˡ-≤; x>0⇒*-cancelʳ-≤; x<0⇒*-anti-cancelˡ-≤; x<0⇒*-anti-cancelʳ-≤

  ; x≈0⇒x*y≈0; x≈0⇒y*x≈0

  ; -x*-y≈x*y
  ;                x>0∧y<0⇒x*y<0; x<0∧y>0⇒x*y<0; x<0∧y<0⇒x*y>0
  ; x≥0∧y≥0⇒x*y≥0; x≥0∧y≤0⇒x*y≤0; x≤0∧y≥0⇒x*y≤0; x≤0∧y≤0⇒x*y≥0

  ; x>1∧y≥1⇒x*y>1; x≥1∧y>1⇒x*y>1; 0≤x<1∧y≤1⇒x*y<1; x≤1∧0≤y<1⇒x*y<1
  ; x≥1∧y≥1⇒x*y≥1; 0≤x≤1∧y≤1⇒x*y≤1; x≤1∧0≤y≤1⇒x*y≤1

  ; x*x≥0; x*y≈0⇒x≈0⊎y≈0

  ; ^-zeroˡ; ^-zeroʳ
  ; ^-identityʳ

  ; n≢0⇒0^n≈0
  ; x>1⇒^-monoˡ-<; 0<x<1⇒^-anti-monoˡ-<
  ; x≥1⇒^-monoˡ-≤; 0≤x≤1⇒^-anti-monoˡ-≤

  ; x>0⇒x^n>0
  ; x≥0⇒x^n≥0

  ; x^n≈0⇒x≈0

  ; x>1∧n≢0⇒x^n>1; 0≤x<1∧n≢0⇒x^n<1
  ; x≥1⇒x^n≥1; 0≤x≤1⇒x^n≤1
  )

--------------------------------------------------------------------------------
---- Properties of _⁻¹

---- Miscellaneous

x≉0⇒x⁻¹≉0 : ∀ {x} → (x≉0 : x ≉ 0#) → x≉0 ⁻¹ ≉ 0#
x≉0⇒x⁻¹≉0 {x} x≉0 x⁻¹≈0 = x≉0 (begin-equality
  x              ≈˘⟨ *-identityˡ x ⟩
  1# * x         ≈˘⟨ *-congʳ (⁻¹-inverseʳ x≉0) ⟩
  x * x≉0 ⁻¹ * x ≈⟨  *-congʳ (*-congˡ x⁻¹≈0) ⟩
  x * 0# * x     ≈⟨  *-congʳ (zeroʳ x) ⟩
  0# * x         ≈⟨  zeroˡ x ⟩
  0#             ∎)

---- Preserves signs

x>0⇒x⁻¹>0 : ∀ {x} → (x>0 : x > 0#) → (<⇒≉ x>0 ∘ Eq.sym) ⁻¹ > 0#
x>0⇒x⁻¹>0 {x} x>0 = ≰⇒> (λ x⁻¹≤0 → <⇒≱ (x<y⇒0<1 x>0) (begin
  1#                        ≈˘⟨ ⁻¹-inverseʳ (<⇒≉ x>0 ∘ Eq.sym) ⟩
  x * (<⇒≉ x>0 ∘ Eq.sym) ⁻¹ ≤⟨  x≥0∧y≤0⇒x*y≤0 (<⇒≤ x>0) x⁻¹≤0 ⟩
  0#                        ∎))

x<0⇒x⁻¹<0 : ∀ {x} → (x<0 : x < 0#) → (<⇒≉ x<0) ⁻¹ < 0#
x<0⇒x⁻¹<0 {x} x<0 = ≰⇒> (λ x⁻¹≥0 → <⇒≱ (x<y⇒0<1 x<0) (begin
  1#               ≈˘⟨ ⁻¹-inverseʳ (<⇒≉ x<0) ⟩
  x * (<⇒≉ x<0) ⁻¹ ≤⟨  x≤0∧y≥0⇒x*y≤0 (<⇒≤ x<0) x⁻¹≥0 ⟩
  0#               ∎))

---- Respects signs

x⁻¹>0⇒x>0 : ∀ {x} {x≉0 : x ≉ 0#} → x≉0 ⁻¹ > 0# → x > 0#
x⁻¹>0⇒x>0 {x} {x≉0} x⁻¹>0 = begin-strict
  0#                      <⟨ x>0⇒x⁻¹>0 x⁻¹>0 ⟩
  (<⇒≉ x⁻¹>0 ∘ Eq.sym) ⁻¹ ≈⟨ ⁻¹-involutive x≉0 (<⇒≉ x⁻¹>0 ∘ Eq.sym) ⟩
  x                       ∎

x⁻¹<0⇒x<0 : ∀ {x} {x≉0 : x ≉ 0#} → x≉0 ⁻¹ < 0# → x < 0#
x⁻¹<0⇒x<0 {x} {x≉0} x⁻¹<0 = begin-strict
  x              ≈˘⟨ ⁻¹-involutive x≉0 (<⇒≉ x⁻¹<0) ⟩
  (<⇒≉ x⁻¹<0) ⁻¹ <⟨  x<0⇒x⁻¹<0 x⁻¹<0 ⟩
  0#             ∎

---- Preserves size

x>1⇒x⁻¹<1 : ∀ {x} → (x>1 : x > 1#) → (<⇒≉ (≤-<-trans 0≤1 x>1) ∘ Eq.sym) ⁻¹ < 1#
x>1⇒x⁻¹<1 {x} x>1 = ≰⇒>
  ( <-irrefl (Eq.sym (⁻¹-inverseʳ (<⇒≉ (≤-<-trans 0≤1 x>1) ∘ Eq.sym)))
  ∘ x>1∧y≥1⇒x*y>1 x>1
  )

0<x<1⇒x⁻¹>1 : ∀ {x} (0<x : 0# < x) → x < 1# → (<⇒≉ 0<x ∘ Eq.sym) ⁻¹ > 1#
0<x<1⇒x⁻¹>1 {x} 0<x x<1 = ≰⇒>
  ( <-irrefl (⁻¹-inverseʳ (<⇒≉ 0<x ∘ Eq.sym))
  ∘ 0≤x<1∧y≤1⇒x*y<1 (<⇒≤ 0<x) x<1
  )

---- Respects size

x⁻¹>1⇒x<1 : ∀ {x} {x≉0 : x ≉ 0#} → x≉0 ⁻¹ > 1# → x < 1#
x⁻¹>1⇒x<1 {x} {x≉0} x⁻¹>1 = ≰⇒>
  ( <-irrefl (Eq.sym (⁻¹-inverseˡ x≉0))
  ∘ x>1∧y≥1⇒x*y>1 x⁻¹>1
  )

0<x⁻¹<1⇒x>1 : ∀ {x} {x≉0 : x ≉ 0#} → 0# < x≉0 ⁻¹ → x≉0 ⁻¹ < 1# → x > 1#
0<x⁻¹<1⇒x>1 {x} {x≉0} 0<x⁻¹ x⁻¹<1 = ≰⇒>
  ( <-irrefl (⁻¹-inverseˡ x≉0)
  ∘ 0≤x<1∧y≤1⇒x*y<1 (<⇒≤ 0<x⁻¹) x⁻¹<1
  )

---- Miscellaneous

y>0∧x<y⇒x*y⁻¹<1 : ∀ {x y} (y>0 : y > 0#) → x < y → x * (<⇒≉ y>0 ∘ Eq.sym) ⁻¹ < 1#
y>0∧x<y⇒x*y⁻¹<1 {x} {y} y>0 x<y = x≥0⇒*-cancelʳ-< (<⇒≤ y>0) (begin-strict
  x * y≉0 ⁻¹ * y   ≈⟨  *-assoc x _ y ⟩
  x * (y≉0 ⁻¹ * y) ≈⟨  *-congˡ (⁻¹-inverseˡ y≉0) ⟩
  x * 1#           ≈⟨  *-identityʳ x ⟩
  x                <⟨  x<y ⟩
  y                ≈˘⟨ *-identityˡ y ⟩
  1# * y           ∎)
  where y≉0 = <⇒≉ y>0 ∘ Eq.sym

--------------------------------------------------------------------------------
---- Properties of -_ and _⁻¹

-‿⁻¹-comm : ∀ {x} (x≉0 : x ≉ 0#) → - x≉0 ⁻¹ ≈ (x≉0 ∘ -x≈0⇒x≈0) ⁻¹
-‿⁻¹-comm {x} x≉0 = *-inverseˡ-unique (x≉0 ∘ -x≈0⇒x≈0) (begin-equality
  - x≉0 ⁻¹ * - x ≈⟨ -x*-y≈x*y (x≉0 ⁻¹) x ⟩
  x≉0 ⁻¹ * x     ≈⟨ ⁻¹-inverseˡ x≉0 ⟩
  1#             ∎)

-- ---- Congruences

-- -- _<_

-- ⁻¹-anti-mono-< : ∀ {x y} (x≉0 : x ≉ 0#) (y≉0 : y ≉ 0#) → x < y → x≉0 ⁻¹ > y≉0 ⁻¹
-- ⁻¹-anti-mono-< {x} {y} x≉0 y≉0 x<y = begin-strict
--   y≉0 ⁻¹                ≈˘⟨ *-identityˡ (y≉0 ⁻¹) ⟩
--   1# * y≉0 ⁻¹           ≈˘⟨ *-congʳ (⁻¹-inverseˡ x≉0) ⟩
--   x≉0 ⁻¹ * x * y≉0 ⁻¹   <⟨  {!!} ⟩
--   x≉0 ⁻¹ * y * y≉0 ⁻¹   ≈⟨  *-assoc (x≉0 ⁻¹) y (y≉0 ⁻¹) ⟩
--   x≉0 ⁻¹ * (y * y≉0 ⁻¹) ≈⟨  *-congˡ (⁻¹-inverseʳ y≉0) ⟩
--   x≉0 ⁻¹ * 1#           ≈⟨  *-identityʳ (x≉0 ⁻¹) ⟩
--   x≉0 ⁻¹                ∎
