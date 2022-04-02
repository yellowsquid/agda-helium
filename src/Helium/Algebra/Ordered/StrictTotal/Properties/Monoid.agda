------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered monoids
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Monoid
  {ℓ₁ ℓ₂ ℓ₃}
  (monoid : Monoid ℓ₁ ℓ₂ ℓ₃)
  where

open Monoid monoid
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

open import Algebra.Definitions
open import Data.Nat as ℕ using (suc; NonZero)
import Data.Nat.Properties as ℕₚ
open import Function using (_∘_; flip)
open import Function.Definitions
open import Helium.Algebra.Ordered.StrictTotal.Consequences strictTotalOrder
open import Relation.Binary.Core

open import Algebra.Properties.Monoid.Mult.TCOptimised Unordered.monoid public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Semigroup semigroup public
  using
  ( ∙-mono-<; ∙-monoˡ-<; ∙-monoʳ-<
  ; ∙-mono-≤; ∙-monoˡ-≤; ∙-monoʳ-≤
  ; ∙-cancelˡ; ∙-cancelʳ; ∙-cancel
  ; ∙-cancelˡ-<; ∙-cancelʳ-<; ∙-cancel-<
  ; ∙-cancelˡ-≤; ∙-cancelʳ-≤; ∙-cancel-≤
  )
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public

open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

--------------------------------------------------------------------------------
---- Properties of _∙_

---- Preserves signs

-- _<_

x≥ε∧y>ε⇒x∙y>ε : ∀ {x y} → x ≥ ε → y > ε → x ∙ y > ε
x≥ε∧y>ε⇒x∙y>ε {x} {y} x≥ε y>ε = begin-strict
  ε     ≈˘⟨ identity² ⟩
  ε ∙ ε <⟨  ∙-monoˡ-< y>ε ⟩
  ε ∙ y ≤⟨  ∙-monoʳ-≤ x≥ε ⟩
  x ∙ y ∎

x>ε∧y≥ε⇒x∙y>ε : ∀ {x y} → x > ε → y ≥ ε → x ∙ y > ε
x>ε∧y≥ε⇒x∙y>ε {x} {y} x>ε y≤ε = begin-strict
  ε     ≈˘⟨ identity² ⟩
  ε ∙ ε ≤⟨  ∙-monoˡ-≤ y≤ε ⟩
  ε ∙ y <⟨  ∙-monoʳ-< x>ε ⟩
  x ∙ y ∎

x≤ε∧y<ε⇒x∙y<ε : ∀ {x y} → x ≤ ε → y < ε → x ∙ y < ε
x≤ε∧y<ε⇒x∙y<ε {x} {y} x≤ε y<ε = begin-strict
  x ∙ y ≤⟨ ∙-monoʳ-≤ x≤ε ⟩
  ε ∙ y <⟨ ∙-monoˡ-< y<ε ⟩
  ε ∙ ε ≈⟨ identity² ⟩
  ε     ∎

x<ε∧y≤ε⇒x∙y<ε : ∀ {x y} → x < ε → y ≤ ε → x ∙ y < ε
x<ε∧y≤ε⇒x∙y<ε {x} {y} x<ε y≤ε = begin-strict
  x ∙ y <⟨ ∙-monoʳ-< x<ε ⟩
  ε ∙ y ≤⟨ ∙-monoˡ-≤ y≤ε ⟩
  ε ∙ ε ≈⟨ identity² ⟩
  ε     ∎

-- _≤_

x≥ε∧y≥ε⇒x∙y≥ε : ∀ {x y} → x ≥ ε → y ≥ ε → x ∙ y ≥ ε
x≥ε∧y≥ε⇒x∙y≥ε {x} {y} x≥ε y≥ε = begin
  ε     ≈˘⟨ identity² ⟩
  ε ∙ ε ≤⟨  ∙-mono-≤ x≥ε y≥ε ⟩
  x ∙ y ∎

x≤ε∧y≤ε⇒x∙y≤ε : ∀ {x y} → x ≤ ε → y ≤ ε → x ∙ y ≤ ε
x≤ε∧y≤ε⇒x∙y≤ε {x} {y} x≥ε y≥ε = begin
  x ∙ y ≤⟨ ∙-mono-≤ x≥ε y≥ε ⟩
  ε ∙ ε ≈⟨ identity² ⟩
  ε     ∎

---- Respects signs

-- _<_

x≤ε∧x∙y>ε⇒y>ε : ∀ {x y} → x ≤ ε → x ∙ y > ε → y > ε
x≤ε∧x∙y>ε⇒y>ε x≤ε x∙y>ε = ≰⇒> (<⇒≱ x∙y>ε ∘ x≤ε∧y≤ε⇒x∙y≤ε x≤ε)

x≤ε∧y∙x>ε⇒y>ε : ∀ {x y} → x ≤ ε → y ∙ x > ε → y > ε
x≤ε∧y∙x>ε⇒y>ε x≤ε y∙x>ε = ≰⇒> (<⇒≱ y∙x>ε ∘ flip x≤ε∧y≤ε⇒x∙y≤ε x≤ε)

x<ε∧x∙y≥ε⇒y>ε : ∀ {x y} → x < ε → x ∙ y ≥ ε → y > ε
x<ε∧x∙y≥ε⇒y>ε x<ε x∙y≥ε = ≰⇒> (≤⇒≯ x∙y≥ε ∘ x<ε∧y≤ε⇒x∙y<ε x<ε)

x<ε∧y∙x≥ε⇒y>ε : ∀ {x y} → x < ε → y ∙ x ≥ ε → y > ε
x<ε∧y∙x≥ε⇒y>ε x<ε y∙x≥ε = ≰⇒> (≤⇒≯ y∙x≥ε ∘ flip x≤ε∧y<ε⇒x∙y<ε x<ε)

x≥ε∧x∙y<ε⇒y<ε : ∀ {x y} → x ≥ ε → x ∙ y < ε → y < ε
x≥ε∧x∙y<ε⇒y<ε x≥ε x∙y<ε = ≰⇒> (<⇒≱ x∙y<ε ∘ x≥ε∧y≥ε⇒x∙y≥ε x≥ε)

x≥ε∧y∙x<ε⇒y<ε : ∀ {x y} → x ≥ ε → y ∙ x < ε → y < ε
x≥ε∧y∙x<ε⇒y<ε x≥ε y∙x<ε = ≰⇒> (<⇒≱ y∙x<ε ∘ flip x≥ε∧y≥ε⇒x∙y≥ε x≥ε)

x>ε∧x∙y≤ε⇒y<ε : ∀ {x y} → x > ε → x ∙ y ≤ ε → y < ε
x>ε∧x∙y≤ε⇒y<ε x>ε x∙y≤ε = ≰⇒> (≤⇒≯ x∙y≤ε ∘ x>ε∧y≥ε⇒x∙y>ε x>ε)

x>ε∧y∙x≤ε⇒y<ε : ∀ {x y} → x > ε → y ∙ x ≤ ε → y < ε
x>ε∧y∙x≤ε⇒y<ε x>ε y∙x≤ε = ≰⇒> (≤⇒≯ y∙x≤ε ∘ flip x≥ε∧y>ε⇒x∙y>ε x>ε)

-- _≤_

x≤ε∧x∙y≥ε⇒y≥ε : ∀ {x y} → x ≤ ε → x ∙ y ≥ ε → y ≥ ε
x≤ε∧x∙y≥ε⇒y≥ε x≤ε x∙y≥ε = ≮⇒≥ (≤⇒≯ x∙y≥ε ∘ x≤ε∧y<ε⇒x∙y<ε x≤ε)

x≤ε∧y∙x≥ε⇒y≥ε : ∀ {x y} → x ≤ ε → y ∙ x ≥ ε → y ≥ ε
x≤ε∧y∙x≥ε⇒y≥ε x≤ε y∙x≥ε = ≮⇒≥ (≤⇒≯ y∙x≥ε ∘ flip x<ε∧y≤ε⇒x∙y<ε x≤ε)

x≥ε∧x∙y≤ε⇒y≤ε : ∀ {x y} → x ≥ ε → x ∙ y ≤ ε → y ≤ ε
x≥ε∧x∙y≤ε⇒y≤ε x≥ε x∙y≤ε = ≮⇒≥ (≤⇒≯ x∙y≤ε ∘ x≥ε∧y>ε⇒x∙y>ε x≥ε)

x≥ε∧y∙x≤ε⇒y≤ε : ∀ {x y} → x ≥ ε → y ∙ x ≤ ε → y ≤ ε
x≥ε∧y∙x≤ε⇒y≤ε x≥ε y∙x≤ε = ≮⇒≥ (≤⇒≯ y∙x≤ε ∘ flip x>ε∧y≥ε⇒x∙y>ε x≥ε)

-- ---- Infer signs

-- -- _≈_

-- x∙y≈x⇒y≈ε : ∀ {x y} → x ∙ y ≈ x → y ≈ ε
-- x∙y≈x⇒y≈ε {x} {y} x∙y≈x = ∙-cancelˡ x (Eq.trans x∙y≈x (Eq.sym (identityʳ x)))

-- x∙y≈y⇒x≈ε : ∀ {x y} → x ∙ y ≈ y → x ≈ ε
-- x∙y≈y⇒x≈ε {x} {y} x∙y≈y = ∙-cancelʳ x ε (Eq.trans x∙y≈y (Eq.sym (identityˡ y)))

-- -- _<_

-- x∙y<x⇒y<ε : ∀ {x y} → x ∙ y < x → y < ε
-- x∙y<x⇒y<ε {x} {y} x∙y<x = ∙-cancelˡ-< x (<-respʳ-≈ (Eq.sym (identityʳ x)) x∙y<x)

-- x∙y<y⇒x<ε : ∀ {x y} → x ∙ y < y → x < ε
-- x∙y<y⇒x<ε {x} {y} x∙y<y = ∙-cancelʳ-< x ε (<-respʳ-≈ (Eq.sym (identityˡ y)) x∙y<y)

-- x∙y>x⇒y>ε : ∀ {x y} → x ∙ y > x → y > ε
-- x∙y>x⇒y>ε {x} {y} x∙y>x = ∙-cancelˡ-< x (<-respˡ-≈ (Eq.sym (identityʳ x)) x∙y>x)

-- x∙y>y⇒x>ε : ∀ {x y} → x ∙ y > y → x > ε
-- x∙y>y⇒x>ε {x} {y} x∙y>y = ∙-cancelʳ-< ε x (<-respˡ-≈ (Eq.sym (identityˡ y)) x∙y>y)

-- -- _≤_

-- x∙y≤x⇒y≤ε : ∀ {x y} → x ∙ y ≤ x → y ≤ ε
-- x∙y≤x⇒y≤ε {x} {y} x∙y≤x = ∙-cancelˡ-≤ x (≤-respʳ-≈ (Eq.sym (identityʳ x)) x∙y≤x)

-- x∙y≤y⇒x≤ε : ∀ {x y} → x ∙ y ≤ y → x ≤ ε
-- x∙y≤y⇒x≤ε {x} {y} x∙y≤y = ∙-cancelʳ-≤ x ε (≤-respʳ-≈ (Eq.sym (identityˡ y)) x∙y≤y)

-- x∙y≥x⇒y≥ε : ∀ {x y} → x ∙ y ≥ x → y ≥ ε
-- x∙y≥x⇒y≥ε {x} {y} x∙y≥x = ∙-cancelˡ-≤ x (≤-respˡ-≈ (Eq.sym (identityʳ x)) x∙y≥x)

-- x∙y≥y⇒x≥ε : ∀ {x y} → x ∙ y ≥ y → x ≥ ε
-- x∙y≥y⇒x≥ε {x} {y} x∙y≥y = ∙-cancelʳ-≤ ε x (≤-respˡ-≈ (Eq.sym (identityˡ y)) x∙y≥y)

-- --------------------------------------------------------------------------------
---- Properties of _×_

---- Zero

×-zeroˡ : ∀ x → 0 × x ≈ ε
×-zeroˡ x = Eq.refl

×-zeroʳ : ∀ n → n × ε ≈ ε
×-zeroʳ 0       = Eq.refl
×-zeroʳ (suc n) = begin-equality
  suc n × ε ≈⟨ 1+× n ε ⟩
  ε ∙ n × ε ≈⟨ ∙-congˡ (×-zeroʳ n) ⟩
  ε ∙ ε     ≈⟨ identity² ⟩
  ε         ∎

---- Identity

×-identityˡ : ∀ x → 1 × x ≈ x
×-identityˡ x = Eq.refl

---- Preserves signs

-- _≤_

x≥ε⇒n×x≥ε : ∀ n {x} → x ≥ ε → n × x ≥ ε
x≥ε⇒n×x≥ε 0       {x} x≥ε = ≤-refl
x≥ε⇒n×x≥ε (suc n) {x} x≥ε = begin
  ε         ≤⟨  x≥ε∧y≥ε⇒x∙y≥ε x≥ε (x≥ε⇒n×x≥ε n x≥ε) ⟩
  x ∙ n × x ≈˘⟨ 1+× n x ⟩
  suc n × x ∎

x≤ε⇒n×x≤ε : ∀ n {x} → x ≤ ε → n × x ≤ ε
x≤ε⇒n×x≤ε 0       {x} x≤ε = ≤-refl
x≤ε⇒n×x≤ε (suc n) {x} x≤ε = begin
  suc n × x ≈⟨ 1+× n x ⟩
  x ∙ n × x ≤⟨ x≤ε∧y≤ε⇒x∙y≤ε x≤ε (x≤ε⇒n×x≤ε n x≤ε) ⟩
  ε         ∎

-- _<_

n≢0∧x>ε⇒n×x>ε : ∀ n {x} → ⦃ NonZero n ⦄ → x > ε → n × x > ε
n≢0∧x>ε⇒n×x>ε (suc n) {x} x>ε = begin-strict
  ε         <⟨  x>ε∧y≥ε⇒x∙y>ε x>ε (x≥ε⇒n×x≥ε n (<⇒≤ x>ε)) ⟩
  x ∙ n × x ≈˘⟨ 1+× n x ⟩
  suc n × x ∎

n≢0∧x<ε⇒n×x<ε : ∀ n {x} → ⦃ NonZero n ⦄ → x < ε → n × x < ε
n≢0∧x<ε⇒n×x<ε (suc n) {x} x<ε = begin-strict
  suc n × x ≈⟨ 1+× n x ⟩
  x ∙ n × x <⟨ x<ε∧y≤ε⇒x∙y<ε x<ε (x≤ε⇒n×x≤ε n (<⇒≤ x<ε)) ⟩
  ε         ∎

---- Congruences

-- _≤_

×-monoˡ-≤ : ∀ n → Congruent₁ _≤_ (n ×_)
×-monoˡ-≤ 0               x≤y = ≤-refl
×-monoˡ-≤ (suc n) {x} {y} x≤y = begin
  suc n × x ≈⟨  1+× n x ⟩
  x ∙ n × x ≤⟨  ∙-mono-≤ x≤y (×-monoˡ-≤ n x≤y) ⟩
  y ∙ n × y ≈˘⟨ 1+× n y ⟩
  suc n × y ∎

x≥ε⇒×-monoʳ-≤ : ∀ {x} → x ≥ ε → (_× x) Preserves ℕ._≤_ ⟶ _≤_
x≥ε⇒×-monoʳ-≤ {x} x≥ε {.0}     {n}      ℕ.z≤n       = x≥ε⇒n×x≥ε n x≥ε
x≥ε⇒×-monoʳ-≤ {x} x≥ε {.suc m} {.suc n} (ℕ.s≤s m≤n) = begin
  suc m × x ≈⟨  1+× m x ⟩
  x ∙ m × x ≤⟨  ∙-monoˡ-≤ (x≥ε⇒×-monoʳ-≤ x≥ε m≤n) ⟩
  x ∙ n × x ≈˘⟨ 1+× n x ⟩
  suc n × x ∎

x≤ε⇒×-anti-monoʳ-≤ : ∀ {x} → x ≤ ε → (_× x) Preserves ℕ._≤_ ⟶ _≥_
x≤ε⇒×-anti-monoʳ-≤ {x} x≤ε {.0}     {n}      ℕ.z≤n       = x≤ε⇒n×x≤ε n x≤ε
x≤ε⇒×-anti-monoʳ-≤ {x} x≤ε {.suc m} {.suc n} (ℕ.s≤s m≤n) = begin
  suc n × x ≈⟨  1+× n x ⟩
  x ∙ n × x ≤⟨  ∙-monoˡ-≤ (x≤ε⇒×-anti-monoʳ-≤ x≤ε m≤n) ⟩
  x ∙ m × x ≈˘⟨ 1+× m x ⟩
  suc m × x ∎

-- _<_

n≢0⇒×-monoˡ-< : ∀ n → ⦃ NonZero n ⦄ → Congruent₁ _<_ (n ×_)
n≢0⇒×-monoˡ-< (suc n) {x} {y} x<y = begin-strict
  suc n × x ≈⟨  1+× n x ⟩
  x ∙ n × x ≤⟨  ∙-monoˡ-≤ (×-monoˡ-≤ n (<⇒≤ x<y)) ⟩
  x ∙ n × y <⟨  ∙-monoʳ-< x<y ⟩
  y ∙ n × y ≈˘⟨ 1+× n y ⟩
  suc n × y ∎

x>ε⇒×-monoʳ-< : ∀ {x} → x > ε → (_× x) Preserves ℕ._<_ ⟶ _<_
x>ε⇒×-monoʳ-< {x} x>ε {m} {.suc n} (ℕ.s≤s m≤n) = begin-strict
  m × x     ≈˘⟨ identityˡ (m × x) ⟩
  ε ∙ m × x ≤⟨  ∙-monoˡ-≤ (x≥ε⇒×-monoʳ-≤ (<⇒≤ x>ε) m≤n) ⟩
  ε ∙ n × x <⟨  ∙-monoʳ-< x>ε ⟩
  x ∙ n × x ≈˘⟨ 1+× n x ⟩
  suc n × x ∎

x<ε⇒×-anti-monoʳ-< : ∀ {x} → x < ε → (_× x) Preserves ℕ._<_ ⟶ _>_
x<ε⇒×-anti-monoʳ-< {x} x<ε {m} {.suc n} (ℕ.s≤s m≤n) = begin-strict
  suc n × x ≈⟨ 1+× n x ⟩
  x ∙ n × x <⟨ ∙-monoʳ-< x<ε ⟩
  ε ∙ n × x ≤⟨ ∙-monoˡ-≤ (x≤ε⇒×-anti-monoʳ-≤ (<⇒≤ x<ε) m≤n) ⟩
  ε ∙ m × x ≈⟨ identityˡ (m × x) ⟩
  m × x     ∎

---- Cancellative

-- _<_

×-cancelˡ-< : ∀ n → Injective _<_ _<_ (n ×_)
×-cancelˡ-< n = mono₁-≤⇒cancel₁-< (×-monoˡ-≤ n)

x≥ε⇒×-cancelʳ-< : ∀ {x} → x ≥ ε → Injective ℕ._<_ _<_ (_× x)
x≥ε⇒×-cancelʳ-< x≥ε m×x<n×x = ℕₚ.≰⇒> (<⇒≱ m×x<n×x ∘ x≥ε⇒×-monoʳ-≤ x≥ε)

x≤ε⇒×-anti-cancelʳ-< : ∀ {x} → x ≤ ε → Injective ℕ._<_ _>_ (_× x)
x≤ε⇒×-anti-cancelʳ-< x≤ε m×x>n×x = ℕₚ.≰⇒> (<⇒≱ m×x>n×x ∘ x≤ε⇒×-anti-monoʳ-≤ x≤ε)

-- _≤_

n≢0⇒×-cancelˡ-≤ : ∀ n → ⦃ NonZero n ⦄ → Injective _≤_ _≤_ (n ×_)
n≢0⇒×-cancelˡ-≤ n = mono₁-<⇒cancel₁-≤ (n≢0⇒×-monoˡ-< n)

x>ε⇒×-cancelʳ-≤ : ∀ {x} → x > ε → Injective ℕ._≤_ _≤_ (_× x)
x>ε⇒×-cancelʳ-≤ x>ε m×x≤n×x = ℕₚ.≮⇒≥ (≤⇒≯ m×x≤n×x ∘ x>ε⇒×-monoʳ-< x>ε)

x<ε⇒×-anti-cancelʳ-≤ : ∀ {x} → x < ε → Injective ℕ._≤_ _≥_ (_× x)
x<ε⇒×-anti-cancelʳ-≤ x<ε m×x≥n×x = ℕₚ.≮⇒≥ (≤⇒≯ m×x≥n×x ∘ x<ε⇒×-anti-monoʳ-< x<ε)

---- Respects signs

-- _<_

n×x>ε⇒x>ε : ∀ {n x} → n × x > ε → x > ε
n×x>ε⇒x>ε {n} n×x>ε = ≰⇒> (<⇒≱ n×x>ε ∘ x≤ε⇒n×x≤ε n)

n×x<ε⇒x<ε : ∀ {n x} → n × x < ε → x < ε
n×x<ε⇒x<ε {n} n×x<ε = ≰⇒> (<⇒≱ n×x<ε ∘ x≥ε⇒n×x≥ε n)

-- _≥_

n≢0∧n×x≥ε⇒x≥ε : ∀ {n x} → ⦃ NonZero n ⦄ → n × x ≥ ε → x ≥ ε
n≢0∧n×x≥ε⇒x≥ε {n} n×x≥ε = ≮⇒≥ (≤⇒≯ n×x≥ε ∘ n≢0∧x<ε⇒n×x<ε n)

n≢0∧n×x≤ε⇒x≤ε : ∀ {n x} → ⦃ NonZero n ⦄ → n × x ≤ ε → x ≤ ε
n≢0∧n×x≤ε⇒x≤ε {n} n×x≤ε = ≮⇒≥ (≤⇒≯ n×x≤ε ∘ n≢0∧x>ε⇒n×x>ε n)

-- ---- Infer signs

-- -- _≈_

-- n≢0∧n×x≈x⇒x≈ε : ∀ n {x} → ⦃ NonZero n ⦄ → n × x ≈ x → x ≈ ε
-- n≢0∧n×x≈x⇒x≈ε n n×x≈x = ≮∧≯⇒≈
--   (λ x<ε → <-irrefl n×x≈x (<-trans (n≢0∧x<ε⇒n×x<ε {!!} {!!}) {!!}))
--   (λ x>ε → {!!})
