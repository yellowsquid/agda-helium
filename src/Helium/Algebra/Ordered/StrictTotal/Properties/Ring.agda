------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered rings
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Ring
  {ℓ₁ ℓ₂ ℓ₃}
  (ring : Ring ℓ₁ ℓ₂ ℓ₃)
  where

open Ring ring
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  ; 0<a+0<b⇒0<ab to x>0∧y>0⇒x*y>0
  )

open import Algebra.Definitions
open import Data.Nat as ℕ using (suc; NonZero)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Function.Definitions
open import Helium.Algebra.Ordered.StrictTotal.Consequences strictTotalOrder
open import Relation.Binary.Core
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.Ring Unordered.ring public
  renaming (-0#≈0# to -0≈0)

open import Algebra.Properties.Semiring.Mult.TCOptimised Unordered.semiring public
open import Algebra.Properties.Semiring.Exp.TCOptimised Unordered.semiring public
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public
open import Helium.Algebra.Ordered.StrictTotal.Properties.AbelianGroup +-abelianGroup public
  using
  ( ×-zeroˡ; ×-zeroʳ
  ; ×-identityˡ
  ; n≢0⇒×-monoˡ-<; ×-monoˡ-≤
  ; ×-cancelˡ-<; n≢0⇒×-cancelˡ-≤
  )
  renaming
  ( ∙-mono-<  to +-mono-<
  ; ∙-monoˡ-< to +-monoˡ-<
  ; ∙-monoʳ-< to +-monoʳ-<
  ; ∙-mono-≤  to +-mono-≤
  ; ∙-monoˡ-≤ to +-monoˡ-≤
  ; ∙-monoʳ-≤ to +-monoʳ-≤

  ; ∙-cancelˡ-< to +-cancelˡ-<
  ; ∙-cancelʳ-< to +-cancelʳ-<
  ; ∙-cancel-<  to +-cancel-<
  ; ∙-cancelˡ-≤ to +-cancelˡ-≤
  ; ∙-cancelʳ-≤ to +-cancelʳ-≤
  ; ∙-cancel-≤  to +-cancel-≤
  -- _∙_ pres signs
  ; x≥ε∧y>ε⇒x∙y>ε to x≥0∧y>0⇒x+y>0
  ; x>ε∧y≥ε⇒x∙y>ε to x>0∧y≥0⇒x+y>0
  ; x≤ε∧y<ε⇒x∙y<ε to x≤0∧y<0⇒x+y<0
  ; x<ε∧y≤ε⇒x∙y<ε to x<0∧y≤0⇒x+y<0
  ; x≥ε∧y≥ε⇒x∙y≥ε to x≥0∧y≥0⇒x+y≥0
  ; x≤ε∧y≤ε⇒x∙y≤ε to x≤0∧y≤0⇒x+y≤0
  -- _∙_ resp signs
  ; x≤ε∧x∙y>ε⇒y>ε to x≤0∧x+y>0⇒y>0
  ; x≤ε∧y∙x>ε⇒y>ε to x≤0∧y+x>0⇒y>0
  ; x<ε∧x∙y≥ε⇒y>ε to x<0∧x+y≥0⇒y>0
  ; x<ε∧y∙x≥ε⇒y>ε to x<0∧y+x≥0⇒y>0
  ; x≥ε∧x∙y<ε⇒y<ε to x≥0∧x+y<0⇒y<0
  ; x≥ε∧y∙x<ε⇒y<ε to x≥0∧y+x<0⇒y<0
  ; x>ε∧x∙y≤ε⇒y<ε to x>0∧x+y≤0⇒y<0
  ; x>ε∧y∙x≤ε⇒y<ε to x>0∧y+x≤0⇒y<0
  ; x≤ε∧x∙y≥ε⇒y≥ε to x≤0∧x+y≥0⇒y≥0
  ; x≤ε∧y∙x≥ε⇒y≥ε to x≤0∧y+x≥0⇒y≥0
  ; x≥ε∧x∙y≤ε⇒y≤ε to x≥0∧x+y≤0⇒y≤0
  ; x≥ε∧y∙x≤ε⇒y≤ε to x≥0∧y+x≤0⇒y≤0

  ; x>ε⇒×-monoʳ-<      to x>0⇒×-monoʳ-<
  ; x<ε⇒×-anti-monoʳ-< to x<0⇒×-anti-monoʳ-<
  ; x≥ε⇒×-monoʳ-≤      to x≥0⇒×-monoʳ-≤
  ; x≤ε⇒×-anti-monoʳ-≤ to x≤0⇒×-anti-monoʳ-≤

  ; x≥ε⇒×-cancelʳ-<      to x≥0⇒×-cancelʳ-<
  ; x≤ε⇒×-anti-cancelʳ-< to x≤0⇒×-anti-cancelʳ-<
  ; x>ε⇒×-cancelʳ-≤      to x>0⇒×-cancelʳ-≤
  ; x<ε⇒×-anti-cancelʳ-≤ to x<0⇒×-anti-cancelʳ-≤
  -- _×_ pres signs
  ; n≢0∧x>ε⇒n×x>ε to n≢0∧x>0⇒n×x>0
  ; n≢0∧x<ε⇒n×x<ε to n≢0∧x<0⇒n×x<0
  ; x≥ε⇒n×x≥ε     to x≥0⇒n×x≥0
  ; x≤ε⇒n×x≤ε     to x≤0⇒n×x≤0
  -- _×_ resp signs
  ; n×x>ε⇒x>ε     to n×x>0⇒x>0
  ; n×x<ε⇒x<ε     to n×x<0⇒x<0
  ; n≢0∧n×x≥ε⇒x≥ε to n≢0∧n×x≥0⇒x≥0
  ; n≢0∧n×x≤ε⇒x≤ε to n≢0∧n×x≤0⇒x≤0

  ; ⁻¹-anti-mono-< to -‿anti-mono-<
  ; ⁻¹-anti-mono-≤ to -‿anti-mono-≤

  ; ⁻¹-anti-cancel-< to -‿anti-cancel-<
  ; ⁻¹-anti-cancel-≤ to -‿anti-cancel-≤

  ; x≈ε⇒x⁻¹≈ε to x≈0⇒-x≈0
  ; x<ε⇒x⁻¹>ε to x<0⇒-x>0
  ; x>ε⇒x⁻¹<ε to x>0⇒-x<0
  ; x≤ε⇒x⁻¹≥ε to x≤0⇒-x≥0
  ; x≥ε⇒x⁻¹≤ε to x≥0⇒-x≤0

  ; x⁻¹≈ε⇒x≈ε to -x≈0⇒x≈0
  ; x⁻¹<ε⇒x>ε to -x<0⇒x>0
  ; x⁻¹>ε⇒x<ε to -x>0⇒x<0
  ; x⁻¹≤ε⇒x≥ε to -x≤0⇒x≥0
  ; x⁻¹≥ε⇒x≤ε to -x≥0⇒x≤0

  ; x<y⇒ε<y∙x⁻¹ to x<y⇒0<y-x
  ; ε<y∙x⁻¹⇒x<y to 0<y-x⇒x<y
  ; x≤y⇒ε≤y∙x⁻¹ to x≤y⇒0≤y-x
  ; ε≤y∙x⁻¹⇒x≤y to 0≤y-x⇒x≤y
  )

--------------------------------------------------------------------------------
---- Properties of _*_ and -_

-x*-y≈x*y : ∀ x y → - x * - y ≈ x * y
-x*-y≈x*y x y = begin-equality
  - x * - y   ≈˘⟨ -‿distribˡ-* x (- y) ⟩
  - (x * - y) ≈˘⟨ -‿cong (-‿distribʳ-* x y) ⟩
  - - (x * y) ≈⟨  -‿involutive (x * y) ⟩
  x * y       ∎

--------------------------------------------------------------------------------
---- Properties of _*_

---- Congruences

-- _<_

x>0⇒*-monoˡ-< : ∀ {x} → x > 0# → Congruent₁ _<_ (x *_)
x>0⇒*-monoˡ-< {x} x>0 {y} {z} y<z = begin-strict
  x * y                         ≈˘⟨ +-identityˡ (x * y) ⟩
  0# + x * y                    ≈˘⟨ +-cong (-‿inverseʳ (x * z)) (-x*-y≈x*y x y) ⟩
  x * z - x * z + - x * - y     ≈⟨  +-congʳ (+-congˡ (-‿distribˡ-* x z)) ⟩
  x * z + - x * z + - x * - y   ≈⟨  +-assoc (x * z) (- x * z) (- x * - y) ⟩
  x * z + (- x * z + - x * - y) ≈˘⟨ +-congˡ (distribˡ (- x) z (- y)) ⟩
  x * z + - x * (z - y)         ≈˘⟨ +-congˡ (-‿distribˡ-* x (z - y)) ⟩
  x * z - x * (z - y)           <⟨  +-monoˡ-< (x>0⇒-x<0 (x>0∧y>0⇒x*y>0 x>0 (x<y⇒0<y-x y<z))) ⟩
  x * z + 0#                    ≈⟨  +-identityʳ (x * z) ⟩
  x * z                         ∎

x>0⇒*-monoʳ-< : ∀ {x} → x > 0# → Congruent₁ _<_ (_* x)
x>0⇒*-monoʳ-< {x} x>0 {y} {z} y<z = begin-strict
  y * x                         ≈˘⟨ +-identityˡ (y * x) ⟩
  0# + y * x                    ≈˘⟨ +-cong (-‿inverseʳ (z * x)) (-x*-y≈x*y y x) ⟩
  z * x - z * x + - y * - x     ≈⟨  +-congʳ (+-congˡ (-‿distribʳ-* z x)) ⟩
  z * x + z * - x + - y * - x   ≈⟨  +-assoc (z * x) (z * - x) (- y * - x) ⟩
  z * x + (z * - x + - y * - x) ≈˘⟨ +-congˡ (distribʳ (- x) z (- y)) ⟩
  z * x + (z - y) * - x         ≈˘⟨ +-congˡ (-‿distribʳ-* (z - y) x) ⟩
  z * x - (z - y) * x           <⟨  +-monoˡ-< (x>0⇒-x<0 (x>0∧y>0⇒x*y>0 (x<y⇒0<y-x y<z) x>0)) ⟩
  z * x + 0#                    ≈⟨  +-identityʳ (z * x) ⟩
  z * x                         ∎

x<0⇒*-anti-monoˡ-< : ∀ {x} → x < 0# → (x *_) Preserves _<_ ⟶ _>_
x<0⇒*-anti-monoˡ-< {x} x<0 {y} {z} y<z = begin-strict
  x * z                         ≈˘⟨ +-identityʳ (x * z) ⟩
  x * z + 0#                    <⟨  +-monoˡ-< (x>0∧y>0⇒x*y>0 (x<0⇒-x>0 x<0) (x<y⇒0<y-x y<z)) ⟩
  x * z + - x * (z - y)         ≈⟨  +-congˡ (distribˡ (- x) z (- y)) ⟩
  x * z + (- x * z + - x * - y) ≈˘⟨ +-assoc (x * z) (- x * z) (- x * - y) ⟩
  x * z + - x * z + - x * - y   ≈˘⟨ +-congʳ (+-congˡ (-‿distribˡ-* x z)) ⟩
  x * z - x * z + - x * - y     ≈⟨  +-cong (-‿inverseʳ (x * z)) (-x*-y≈x*y x y) ⟩
  0# + x * y                    ≈⟨  +-identityˡ (x * y) ⟩
  x * y                         ∎

x<0⇒*-anti-monoʳ-< : ∀ {x} → x < 0# → (_* x) Preserves _<_ ⟶ _>_
x<0⇒*-anti-monoʳ-< {x} x<0 {y} {z} y<z = begin-strict
  z * x                         ≈˘⟨ +-identityʳ (z * x) ⟩
  z * x + 0#                    <⟨  +-monoˡ-< (x>0∧y>0⇒x*y>0 (x<y⇒0<y-x y<z) (x<0⇒-x>0 x<0)) ⟩
  z * x + (z - y) * - x         ≈⟨  +-congˡ (distribʳ (- x) z (- y)) ⟩
  z * x + (z * - x + - y * - x) ≈˘⟨ +-assoc (z * x) (z * - x) (- y * - x) ⟩
  z * x + z * - x + - y * - x   ≈˘⟨ +-congʳ (+-congˡ (-‿distribʳ-* z x)) ⟩
  z * x - z * x + - y * - x     ≈⟨  +-cong (-‿inverseʳ (z * x)) (-x*-y≈x*y y x) ⟩
  0# + y * x                    ≈⟨  +-identityˡ (y * x) ⟩
  y * x                         ∎

-- _≤_

x≥0⇒*-monoˡ-≤ : ∀ {x} → x ≥ 0# → Congruent₁ _≤_ (x *_)
x≥0⇒*-monoˡ-≤     (inj₁ x>0)         y≤z = cong₁+mono₁-<⇒mono₁-≤ *-congˡ (x>0⇒*-monoˡ-< x>0) y≤z
x≥0⇒*-monoˡ-≤ {x} (inj₂ 0≈x) {y} {z} y≤z = ≤-reflexive (begin-equality
  x * y  ≈˘⟨ *-congʳ 0≈x ⟩
  0# * y ≈⟨  zeroˡ y ⟩
  0#     ≈˘⟨ zeroˡ z ⟩
  0# * z ≈⟨  *-congʳ 0≈x ⟩
  x * z  ∎)

x≥0⇒*-monoʳ-≤ : ∀ {x} → x ≥ 0# → Congruent₁ _≤_ (_* x)
x≥0⇒*-monoʳ-≤     (inj₁ x>0)         y≤z = cong₁+mono₁-<⇒mono₁-≤ *-congʳ (x>0⇒*-monoʳ-< x>0) y≤z
x≥0⇒*-monoʳ-≤ {x} (inj₂ 0≈x) {y} {z} y≤z = ≤-reflexive (begin-equality
  y * x  ≈˘⟨ *-congˡ 0≈x ⟩
  y * 0# ≈⟨  zeroʳ y ⟩
  0#     ≈˘⟨ zeroʳ z ⟩
  z * 0# ≈⟨  *-congˡ 0≈x ⟩
  z * x  ∎)

x≤0⇒*-anti-monoˡ-≤ : ∀ {x} → x ≤ 0# → (x *_) Preserves _≤_ ⟶ _≥_
x≤0⇒*-anti-monoˡ-≤     (inj₁ x<0)         y≤z = cong₁+anti-mono₁-<⇒anti-mono₁-≤ *-congˡ (x<0⇒*-anti-monoˡ-< x<0) y≤z
x≤0⇒*-anti-monoˡ-≤ {x} (inj₂ x≈0) {y} {z} y≤z = ≤-reflexive (begin-equality
  x * z  ≈⟨  *-congʳ x≈0 ⟩
  0# * z ≈⟨  zeroˡ z ⟩
  0#     ≈˘⟨ zeroˡ y ⟩
  0# * y ≈˘⟨ *-congʳ x≈0 ⟩
  x * y  ∎)

x≤0⇒*-anti-monoʳ-≤ : ∀ {x} → x ≤ 0# → (_* x) Preserves _≤_ ⟶ _≥_
x≤0⇒*-anti-monoʳ-≤     (inj₁ x<0)         y≤z = cong₁+anti-mono₁-<⇒anti-mono₁-≤ *-congʳ (x<0⇒*-anti-monoʳ-< x<0) y≤z
x≤0⇒*-anti-monoʳ-≤ {x} (inj₂ x≈0) {y} {z} y≤z = ≤-reflexive (begin-equality
  z * x  ≈⟨  *-congˡ x≈0 ⟩
  z * 0# ≈⟨  zeroʳ z ⟩
  0#     ≈˘⟨ zeroʳ y ⟩
  y * 0# ≈˘⟨ *-congˡ x≈0 ⟩
  y * x  ∎)

---- Cancellative

-- _≈_

x>0⇒*-cancelˡ : ∀ {x} → x > 0# → Injective _≈_ _≈_ (x *_)
x>0⇒*-cancelˡ x>0 = mono₁-<⇒cancel₁ (x>0⇒*-monoˡ-< x>0)

x>0⇒*-cancelʳ : ∀ {x} → x > 0# → Injective _≈_ _≈_ (_* x)
x>0⇒*-cancelʳ x>0 = mono₁-<⇒cancel₁ (x>0⇒*-monoʳ-< x>0)

x<0⇒*-cancelˡ : ∀ {x} → x < 0# → Injective _≈_ _≈_ (x *_)
x<0⇒*-cancelˡ x<0 = anti-mono₁-<⇒cancel₁ (x<0⇒*-anti-monoˡ-< x<0)

x<0⇒*-cancelʳ : ∀ {x} → x < 0# → Injective _≈_ _≈_ (_* x)
x<0⇒*-cancelʳ x<0 = anti-mono₁-<⇒cancel₁ (x<0⇒*-anti-monoʳ-< x<0)

-- _<_

x≥0⇒*-cancelˡ-< : ∀ {x} → x ≥ 0# → Injective _<_ _<_ (x *_)
x≥0⇒*-cancelˡ-< = mono₁-≤⇒cancel₁-< ∘ x≥0⇒*-monoˡ-≤

x≥0⇒*-cancelʳ-< : ∀ {x} → x ≥ 0# → Injective _<_ _<_ (_* x)
x≥0⇒*-cancelʳ-< = mono₁-≤⇒cancel₁-< ∘ x≥0⇒*-monoʳ-≤

x≤0⇒*-anti-cancelˡ-< : ∀ {x} → x ≤ 0# → Injective _<_ _>_ (x *_)
x≤0⇒*-anti-cancelˡ-< = anti-mono₁-≤⇒anti-cancel₁-< ∘ x≤0⇒*-anti-monoˡ-≤

x≤0⇒*-anti-cancelʳ-< : ∀ {x} → x ≤ 0# → Injective _<_ _>_ (_* x)
x≤0⇒*-anti-cancelʳ-< = anti-mono₁-≤⇒anti-cancel₁-< ∘ x≤0⇒*-anti-monoʳ-≤

-- _≤_

x>0⇒*-cancelˡ-≤ : ∀ {x} → x > 0# → Injective _≤_ _≤_ (x *_)
x>0⇒*-cancelˡ-≤ = mono₁-<⇒cancel₁-≤ ∘ x>0⇒*-monoˡ-<

x>0⇒*-cancelʳ-≤ : ∀ {x} → x > 0# → Injective _≤_ _≤_ (_* x)
x>0⇒*-cancelʳ-≤ = mono₁-<⇒cancel₁-≤ ∘ x>0⇒*-monoʳ-<

x<0⇒*-anti-cancelˡ-≤ : ∀ {x} → x < 0# → Injective _≤_ _≥_ (x *_)
x<0⇒*-anti-cancelˡ-≤ = anti-mono₁-<⇒anti-cancel₁-≤ ∘ x<0⇒*-anti-monoˡ-<

x<0⇒*-anti-cancelʳ-≤ : ∀ {x} → x < 0# → Injective _≤_ _≥_ (_* x)
x<0⇒*-anti-cancelʳ-≤ = anti-mono₁-<⇒anti-cancel₁-≤ ∘ x<0⇒*-anti-monoʳ-<

---- Preserves signs

-- _≈_

x≈0⇒x*y≈0 : ∀ {x} → x ≈ 0# → ∀ y → x * y ≈ 0#
x≈0⇒x*y≈0 {x} x≈0 y = begin-equality
  x * y  ≈⟨ *-congʳ x≈0 ⟩
  0# * y ≈⟨ zeroˡ y ⟩
  0#     ∎

x≈0⇒y*x≈0 : ∀ {x} → x ≈ 0# → ∀ y → y * x ≈ 0#
x≈0⇒y*x≈0 {x} x≈0 y = begin-equality
  y * x  ≈⟨ *-congˡ x≈0 ⟩
  y * 0# ≈⟨ zeroʳ y ⟩
  0#     ∎

-- _<_

-- Have x>0∧y>0⇒x*y>0 by ring

x>0∧y<0⇒x*y<0 : ∀ {x y} → x > 0# → y < 0# → x * y < 0#
x>0∧y<0⇒x*y<0 {x} {y} x>0 y<0 = -x>0⇒x<0 (begin-strict
  0#        <⟨  x>0∧y>0⇒x*y>0 x>0 (x<0⇒-x>0 y<0) ⟩
  x * - y   ≈˘⟨ -‿distribʳ-* x y ⟩
  - (x * y) ∎)

x<0∧y>0⇒x*y<0 : ∀ {x y} → x < 0# → y > 0# → x * y < 0#
x<0∧y>0⇒x*y<0 {x} {y} x<0 y>0 = -x>0⇒x<0 (begin-strict
  0#        <⟨  x>0∧y>0⇒x*y>0 (x<0⇒-x>0 x<0) y>0  ⟩
  - x * y   ≈˘⟨ -‿distribˡ-* x y ⟩
  - (x * y) ∎)

x<0∧y<0⇒x*y>0 : ∀ {x y} → x < 0# → y < 0# → x * y > 0#
x<0∧y<0⇒x*y>0 {x} {y} x<0 y<0 = begin-strict
  0#        <⟨ x>0∧y>0⇒x*y>0 (x<0⇒-x>0 x<0) (x<0⇒-x>0 y<0) ⟩
  - x * - y ≈⟨ -x*-y≈x*y x y ⟩
  x * y     ∎

-- _≤_

x≥0∧y≥0⇒x*y≥0 : ∀ {x y} → x ≥ 0# → y ≥ 0# → x * y ≥ 0#
x≥0∧y≥0⇒x*y≥0 {x} {y} (inj₁ x>0) (inj₁ y>0) = <⇒≤ (x>0∧y>0⇒x*y>0 x>0 y>0)
x≥0∧y≥0⇒x*y≥0 {x} {y} (inj₁ x>0) (inj₂ 0≈y) = ≤-reflexive (Eq.sym (x≈0⇒y*x≈0 (Eq.sym 0≈y) x))
x≥0∧y≥0⇒x*y≥0 {x} {y} (inj₂ 0≈x) y≥0        = ≤-reflexive (Eq.sym (x≈0⇒x*y≈0 (Eq.sym 0≈x) y))

x≥0∧y≤0⇒x*y≤0 : ∀ {x y} → x ≥ 0# → y ≤ 0# → x * y ≤ 0#
x≥0∧y≤0⇒x*y≤0 {x} {y} (inj₁ x>0) (inj₁ y<0) = <⇒≤ (x>0∧y<0⇒x*y<0 x>0 y<0)
x≥0∧y≤0⇒x*y≤0 {x} {y} (inj₁ x>0) (inj₂ y≈0) = ≤-reflexive (x≈0⇒y*x≈0 y≈0 x)
x≥0∧y≤0⇒x*y≤0 {x} {y} (inj₂ 0≈x) y≤0        = ≤-reflexive (x≈0⇒x*y≈0 (Eq.sym 0≈x) y)

x≤0∧y≥0⇒x*y≤0 : ∀ {x y} → x ≤ 0# → y ≥ 0# → x * y ≤ 0#
x≤0∧y≥0⇒x*y≤0 {x} {y} (inj₁ x<0) (inj₁ y>0) = <⇒≤ (x<0∧y>0⇒x*y<0 x<0 y>0)
x≤0∧y≥0⇒x*y≤0 {x} {y} (inj₁ x<0) (inj₂ 0≈y) = ≤-reflexive (x≈0⇒y*x≈0 (Eq.sym 0≈y) x)
x≤0∧y≥0⇒x*y≤0 {x} {y} (inj₂ x≈0) y≥0        = ≤-reflexive (x≈0⇒x*y≈0 x≈0 y)

x≤0∧y≤0⇒x*y≥0 : ∀ {x y} → x ≤ 0# → y ≤ 0# → x * y ≥ 0#
x≤0∧y≤0⇒x*y≥0 {x} {y} (inj₁ x<0) (inj₁ y<0) = <⇒≤ (x<0∧y<0⇒x*y>0 x<0 y<0)
x≤0∧y≤0⇒x*y≥0 {x} {y} (inj₁ x<0) (inj₂ y≈0) = ≤-reflexive (Eq.sym (x≈0⇒y*x≈0 y≈0 x))
x≤0∧y≤0⇒x*y≥0 {x} {y} (inj₂ x≈0) y≤0        = ≤-reflexive (Eq.sym (x≈0⇒x*y≈0 x≈0 y))

---- Respects signs

-- _<_

-- x>0∧x*y>0⇒y>0
-- x>0∧x*y<0⇒y<0
-- x>0∧y*x>0⇒y>0
-- x>0∧y*x<0⇒y<0
-- x<0∧x*y>0⇒y<0
-- x<0∧x*y<0⇒y>0
-- x<0∧y*x>0⇒y<0
-- x<0∧y*x<0⇒y>0

-- _≤_

-- x>0∧x*y≥0⇒y≥0
-- x>0∧x*y≤0⇒y≤0
-- x>0∧y*x≥0⇒y≥0
-- x>0∧y*x≤0⇒y≤0
-- x<0∧x*y≥0⇒y≤0
-- x<0∧x*y≤0⇒y≥0
-- x<0∧y*x≥0⇒y≤0
-- x<0∧y*x≤0⇒y≥0

--------------------------------------------------------------------------------
---- Properties of 0 and 1

0≤1 : 0# ≤ 1#
0≤1 = ≮⇒≥ (λ 0>1 → <-asym 0>1 (begin-strict
  0#      <⟨ x<0∧y<0⇒x*y>0 0>1 0>1 ⟩
  1# * 1# ≈⟨ *-identity² ⟩
  1#      ∎))

1≈0⇒x≈y : ∀ {x y} → 1# ≈ 0# → x ≈ y
1≈0⇒x≈y {x} {y} 1≈0 = begin-equality
  x      ≈˘⟨ *-identityʳ x ⟩
  x * 1# ≈⟨  x≈0⇒y*x≈0 1≈0 x ⟩
  0#     ≈˘⟨ x≈0⇒y*x≈0 1≈0 y ⟩
  y * 1# ≈⟨  *-identityʳ y ⟩
  y      ∎

x≉y⇒0<1 : ∀ {x y} → x ≉ y → 0# < 1#
x≉y⇒0<1 x≉y = ≤∧≉⇒< 0≤1 (x≉y ∘ 1≈0⇒x≈y ∘ Eq.sym)

x<y⇒0<1 : ∀ {x y} → x < y → 0# < 1#
x<y⇒0<1 = x≉y⇒0<1 ∘ <⇒≉

--------------------------------------------------------------------------------
---- Properties of _*_ (again)

---- Preserves size

-- _<_

x>1∧y≥1⇒x*y>1 : ∀ {x y} → x > 1# → y ≥ 1# → x * y > 1#
x>1∧y≥1⇒x*y>1 {x} {y} x>1 y≥1 = begin-strict
  1#      ≈˘⟨ *-identity² ⟩
  1# * 1# <⟨  x>0⇒*-monoʳ-< (x<y⇒0<1 x>1) x>1 ⟩
  x * 1#  ≤⟨  x≥0⇒*-monoˡ-≤ (≤-trans 0≤1 (<⇒≤ x>1)) y≥1 ⟩
  x * y   ∎

x≥1∧y>1⇒x*y>1 : ∀ {x y} → x ≥ 1# → y > 1# → x * y > 1#
x≥1∧y>1⇒x*y>1 {x} {y} x≥1 y>1 = begin-strict
  1#      ≈˘⟨ *-identity² ⟩
  1# * 1# <⟨  x>0⇒*-monoˡ-< (x<y⇒0<1 y>1) y>1 ⟩
  1# * y  ≤⟨  x≥0⇒*-monoʳ-≤ (≤-trans 0≤1 (<⇒≤ y>1)) x≥1 ⟩
  x * y   ∎

0≤x<1∧y≤1⇒x*y<1 : ∀ {x y} → 0# ≤ x → x < 1# → y ≤ 1# → x * y < 1#
0≤x<1∧y≤1⇒x*y<1 {x} {y} 0≤x x<1 y≤1 = begin-strict
  x * y   ≤⟨ x≥0⇒*-monoˡ-≤ 0≤x y≤1 ⟩
  x * 1#  <⟨ x>0⇒*-monoʳ-< (x<y⇒0<1 x<1) x<1 ⟩
  1# * 1# ≈⟨ *-identity² ⟩
  1#      ∎

x≤1∧0≤y<1⇒x*y<1 : ∀ {x y} → x ≤ 1# → 0# ≤ y → y < 1# → x * y < 1#
x≤1∧0≤y<1⇒x*y<1 {x} {y} x≤1 0≤y y<1 = begin-strict
  x * y   ≤⟨ x≥0⇒*-monoʳ-≤ 0≤y x≤1 ⟩
  1# * y  <⟨ x>0⇒*-monoˡ-< (x<y⇒0<1 y<1) y<1 ⟩
  1# * 1# ≈⟨ *-identity² ⟩
  1#      ∎

-- _≤_

x≥1∧y≥1⇒x*y≥1 : ∀ {x y} → x ≥ 1# → y ≥ 1# → x * y ≥ 1#
x≥1∧y≥1⇒x*y≥1 {x} {y} x≥1 y≥1 = begin
  1#      ≈˘⟨ *-identity² ⟩
  1# * 1# ≤⟨  x≥0⇒*-monoʳ-≤ 0≤1 x≥1 ⟩
  x * 1#  ≤⟨  x≥0⇒*-monoˡ-≤ (≤-trans 0≤1 x≥1) y≥1 ⟩
  x * y   ∎

0≤x≤1∧y≤1⇒x*y≤1 : ∀ {x y} → 0# ≤ x → x ≤ 1# → y ≤ 1# → x * y ≤ 1#
0≤x≤1∧y≤1⇒x*y≤1 {x} {y} 0≤x x≤1 y≤1 = begin
  x * y   ≤⟨ x≥0⇒*-monoˡ-≤ 0≤x y≤1 ⟩
  x * 1#  ≤⟨ x≥0⇒*-monoʳ-≤ 0≤1 x≤1 ⟩
  1# * 1# ≈⟨ *-identity² ⟩
  1#      ∎

x≤1∧0≤y≤1⇒x*y≤1 : ∀ {x y} → x ≤ 1# → 0# ≤ y → y ≤ 1# → x * y ≤ 1#
x≤1∧0≤y≤1⇒x*y≤1 {x} {y} x≤1 0≤y y≤1 = begin
  x * y   ≤⟨ x≥0⇒*-monoʳ-≤ 0≤y x≤1 ⟩
  1# * y  ≤⟨ x≥0⇒*-monoˡ-≤ 0≤1 y≤1 ⟩
  1# * 1# ≈⟨ *-identity² ⟩
  1#      ∎

---- Miscellaneous

x*x≥0 : ∀ x → x * x ≥ 0#
x*x≥0 x with compare x 0#
... | tri< x<0 _ _ = <⇒≤ (x<0∧y<0⇒x*y>0 x<0 x<0)
... | tri≈ _ x≈0 _ = ≤-reflexive (Eq.sym (x≈0⇒x*y≈0 x≈0 x))
... | tri> _ _ x>0 = <⇒≤ (x>0∧y>0⇒x*y>0 x>0 x>0)

--------------------------------------------------------------------------------
---- Properties of _^_

---- Zero

^-zeroˡ : ∀ n → 1# ^ n ≈ 1#
^-zeroˡ 0       = Eq.refl
^-zeroˡ (suc n) = begin-equality
  1# ^ suc n  ≈⟨ ^-homo-* 1# 1 n ⟩
  1# * 1# ^ n ≈⟨ *-congˡ (^-zeroˡ n) ⟩
  1# * 1#     ≈⟨ *-identity² ⟩
  1#          ∎

^-zeroʳ : ∀ x → x ^ 0 ≈ 1#
^-zeroʳ x = Eq.refl

---- Identity

^-identityʳ : ∀ x → x ^ 1 ≈ x
^-identityʳ x = Eq.refl

---- Preserves sign

-- _≤_

x≥0⇒x^n≥0 : ∀ {x} → x ≥ 0# → ∀ n → x ^ n ≥ 0#
x≥0⇒x^n≥0 {x} x≥0 0       = 0≤1
x≥0⇒x^n≥0 {x} x≥0 (suc n) = begin
  0#        ≤⟨  x≥0∧y≥0⇒x*y≥0 x≥0 (x≥0⇒x^n≥0 x≥0 n) ⟩
  x * x ^ n ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n ∎

-- _<_

x>0⇒x^n>0 : ∀ {x} → x > 0# → ∀ n → x ^ n > 0#
x>0⇒x^n>0 {x} x>0 0       = x<y⇒0<1 x>0
x>0⇒x^n>0 {x} x>0 (suc n) = begin-strict
  0#        <⟨  x>0∧y>0⇒x*y>0 x>0 (x>0⇒x^n>0 x>0 n) ⟩
  x * x ^ n ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n ∎

---- Preserves size

-- _≤_

x≥1⇒x^n≥1 : ∀ {x} → x ≥ 1# → ∀ n → x ^ n ≥ 1#
x≥1⇒x^n≥1 {x} x≥1 0       = ≤-refl
x≥1⇒x^n≥1 {x} x≥1 (suc n) = begin
  1#        ≤⟨  x≥1∧y≥1⇒x*y≥1 x≥1 (x≥1⇒x^n≥1 x≥1 n) ⟩
  x * x ^ n ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n ∎

0≤x≤1⇒x^n≤1 : ∀ {x} → 0# ≤ x → x ≤ 1# → ∀ n → x ^ n ≤ 1#
0≤x≤1⇒x^n≤1 {x} 0≤x x≤1 0       = ≤-refl
0≤x≤1⇒x^n≤1 {x} 0≤x x≤1 (suc n) = begin
  x ^ suc n ≈⟨ ^-homo-* x 1 n ⟩
  x * x ^ n ≤⟨ 0≤x≤1∧y≤1⇒x*y≤1 0≤x x≤1 (0≤x≤1⇒x^n≤1 0≤x x≤1 n) ⟩
  1#        ∎

-- _<_

x>1∧n≢0⇒x^n>1 : ∀ {x} → x > 1# → ∀ n → ⦃ NonZero n ⦄ → x ^ n > 1#
x>1∧n≢0⇒x^n>1 {x} x>1 (suc n) = begin-strict
  1#        <⟨  x>1∧y≥1⇒x*y>1 x>1 (x≥1⇒x^n≥1 (<⇒≤ x>1) n) ⟩
  x * x ^ n ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n ∎

0≤x<1∧n≢0⇒x^n<1 : ∀ {x} → 0# ≤ x → x < 1# → ∀ n → ⦃ NonZero n ⦄ → x ^ n < 1#
0≤x<1∧n≢0⇒x^n<1 {x} 0≤x x<1 (suc n) = begin-strict
  x ^ suc n ≈⟨ ^-homo-* x 1 n ⟩
  x * x ^ n <⟨ 0≤x<1∧y≤1⇒x*y<1 0≤x x<1 (0≤x≤1⇒x^n≤1 0≤x (<⇒≤ x<1) n) ⟩
  1#        ∎

---- Congruences

-- _≈_

n≢0⇒0^n≈0 : ∀ n → ⦃ NonZero n ⦄ → 0# ^ n ≈ 0#
n≢0⇒0^n≈0 (suc n) = begin-equality
  0# ^ suc n  ≈⟨ ^-homo-* 0# 1 n ⟩
  0# * 0# ^ n ≈⟨ zeroˡ (0# ^ n) ⟩
  0#          ∎

-- _≤_

x≥1⇒^-monoˡ-≤ : ∀ {x} → x ≥ 1# → (x ^_) Preserves ℕ._≤_ ⟶ _≤_
x≥1⇒^-monoˡ-≤ {x} x≥1 {.0}     {n}      ℕ.z≤n       = x≥1⇒x^n≥1 x≥1 n
x≥1⇒^-monoˡ-≤ {x} x≥1 {.suc m} {.suc n} (ℕ.s≤s m≤n) = begin
  x ^ suc m ≈⟨  ^-homo-* x 1 m ⟩
  x * x ^ m ≤⟨  x≥0⇒*-monoˡ-≤ (≤-trans 0≤1 x≥1) (x≥1⇒^-monoˡ-≤ x≥1 m≤n) ⟩
  x * x ^ n ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n ∎

0≤x≤1⇒^-anti-monoˡ-≤ : ∀ {x} → 0# ≤ x → x ≤ 1# → (x ^_) Preserves ℕ._≤_ ⟶ _≥_
0≤x≤1⇒^-anti-monoˡ-≤ {x} 0≤x x≤1 {.0}     {n}      ℕ.z≤n       = 0≤x≤1⇒x^n≤1 0≤x x≤1 n
0≤x≤1⇒^-anti-monoˡ-≤ {x} 0≤x x≤1 {.suc m} {.suc n} (ℕ.s≤s m≤n) = begin
  x ^ suc n ≈⟨  ^-homo-* x 1 n ⟩
  x * x ^ n ≤⟨  x≥0⇒*-monoˡ-≤ 0≤x (0≤x≤1⇒^-anti-monoˡ-≤ 0≤x x≤1 m≤n) ⟩
  x * x ^ m ≈˘⟨ ^-homo-* x 1 m ⟩
  x ^ suc m ∎

-- _<_

x>1⇒^-monoˡ-< : ∀ {x} → x > 1# → (x ^_) Preserves ℕ._<_ ⟶ _<_
x>1⇒^-monoˡ-< {x} x>1 {m} {.suc n} (ℕ.s≤s m≤n) = begin-strict
  x ^ m      ≤⟨  x≥1⇒^-monoˡ-≤ (<⇒≤ x>1) m≤n ⟩
  x ^ n      ≈˘⟨ *-identityˡ (x ^ n) ⟩
  1# * x ^ n <⟨  x>0⇒*-monoʳ-< (x>0⇒x^n>0 (≤-<-trans 0≤1 x>1) n) x>1 ⟩
  x * x ^ n  ≈˘⟨ ^-homo-* x 1 n ⟩
  x ^ suc n  ∎

0<x<1⇒^-anti-monoˡ-< : ∀ {x} → 0# < x → x < 1# → (x ^_) Preserves ℕ._<_ ⟶ _>_
0<x<1⇒^-anti-monoˡ-< {x} 0<x x<1 {m} {.suc n} (ℕ.s≤s m≤n) = begin-strict
  x ^ suc n  ≈⟨ ^-homo-* x 1 n ⟩
  x * x ^ n  <⟨ x>0⇒*-monoʳ-< (x>0⇒x^n>0 0<x n) x<1 ⟩
  1# * x ^ n ≈⟨ *-identityˡ (x ^ n) ⟩
  x ^ n      ≤⟨ 0≤x≤1⇒^-anti-monoˡ-≤ (<⇒≤ 0<x) (<⇒≤ x<1) m≤n ⟩
  x ^ m      ∎
