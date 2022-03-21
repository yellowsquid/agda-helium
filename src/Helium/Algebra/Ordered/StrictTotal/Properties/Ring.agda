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

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Nat using (suc; NonZero)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Properties.Ring Unordered.ring public
  renaming (-0#≈0# to -0≈0)
open import Algebra.Properties.Semiring.Mult.TCOptimised Unordered.semiring public
open import Algebra.Properties.Semiring.Exp.TCOptimised Unordered.semiring public
open import Helium.Algebra.Ordered.StrictTotal.Properties.AbelianGroup +-abelianGroup public
  using (<⇒≱; ≤⇒≯; >⇒≉; ≈⇒≯; <⇒≉; ≈⇒≮; ≤∧≉⇒<; ≥∧≉⇒>)
  renaming
    ( x<y⇒ε<yx⁻¹ to x<y⇒0<y-x
    ; ⁻¹-anti-mono to -‿anti-mono
    )

instance
  ⊤′ : ∀ {ℓ} → ⊤ {ℓ = ℓ}
  ⊤′ = _

  number : Number Carrier
  number = record
    { Constraint = λ _ → ⊤
    ; fromNat = _× 1#
    }

  negative : Negative Carrier
  negative = record
    { Constraint = λ _ → ⊤
    ; fromNeg = λ x → - (x × 1#)
    }

0≤1 : 0 ≤ 1
0≤1 with compare 0 1
... | tri< 0<1 _ _ = inj₁ 0<1
... | tri≈ _ 0≈1 _ = inj₂ 0≈1
... | tri> _ _ 0>1 = inj₁ (begin-strict
  0          <⟨  0<a+0<b⇒0<ab 0<-1 0<-1 ⟩
  -1 * -1    ≈˘⟨ -‿distribˡ-* 1 -1 ⟩
  - (1 * -1) ≈⟨  -‿cong (*-identityˡ -1) ⟩
  - -1       ≈⟨  -‿involutive 1 ⟩
  1          ∎)
  where
  0<-1 = begin-strict
    0   ≈˘⟨ -0≈0 ⟩
    - 0 <⟨  -‿anti-mono 0>1 ⟩
    -1  ∎

1≉0+n≉0⇒0<+n : 1 ≉ 0 → ∀ n → {{NonZero n}} → 0 < fromNat n
1≉0+n≉0⇒0<+n 1≉0 (suc 0)       = ≥∧≉⇒> 0≤1 1≉0
1≉0+n≉0⇒0<+n 1≉0 (suc (suc n)) = begin-strict
  0                   ≈˘⟨ +-identity² ⟩
  0 + 0               <⟨  +-invariantˡ 0 (≥∧≉⇒> 0≤1 1≉0) ⟩
  0 + 1               <⟨  +-invariantʳ 1 (1≉0+n≉0⇒0<+n 1≉0 (suc n)) ⟩
  fromNat (suc n) + 1 ∎

1≉0+n≉0⇒-n<0 : 1 ≉ 0 → ∀ n → {{NonZero n}} → fromNeg n < 0
1≉0+n≉0⇒-n<0 1≉0 n = begin-strict
  - fromNat n <⟨ -‿anti-mono (1≉0+n≉0⇒0<+n 1≉0 n) ⟩
  - 0         ≈⟨ -0≈0 ⟩
  0           ∎
