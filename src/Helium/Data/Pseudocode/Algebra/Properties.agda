------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of types used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Data.Pseudocode.Algebra.Properties
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
import Helium.Algebra.Ordered.StrictTotal.Properties.CommutativeRing as CommRingₚ
open import Data.Nat using (NonZero)

private
  module pseudocode = Pseudocode pseudocode

open pseudocode public
  hiding
  (1≉0; module ℤ; module ℤ′; module ℝ; module ℝ′; module ℤ-Reasoning; module ℝ-Reasoning)

module ℤ where
  open pseudocode.ℤ public hiding (ℤ; 0ℤ; 1ℤ)
  module Reasoning = pseudocode.ℤ-Reasoning

  open CommRingₚ integerRing public
    hiding (1≉0+n≉0⇒0<+n; 1≉0+n≉0⇒-n<0)

  1≉0 : 1 ≉ 0
  1≉0 = pseudocode.1≉0

  n≉0⇒0<+n : ∀ n → {{NonZero n}} → 0 < fromNat n
  n≉0⇒0<+n = CommRingₚ.1≉0+n≉0⇒0<+n integerRing 1≉0

  n≉0⇒-n<0 : ∀ n → {{NonZero n}} → fromNeg n < 0
  n≉0⇒-n<0 = CommRingₚ.1≉0+n≉0⇒-n<0 integerRing 1≉0

module ℝ where
  open pseudocode.ℝ public hiding (ℝ; 0ℝ; 1ℝ)
  module Reasoning = pseudocode.ℝ-Reasoning

  open CommRingₚ commutativeRing public
    hiding ()

  1≉0 : 1 ≉ 0
  1≉0 1≈0 = ℤ.1≉0 (begin-equality
    1        ≈˘⟨ ⌊⌋∘/1≗id 1 ⟩
    ⌊ 1 /1 ⌋ ≈⟨  ⌊⌋.cong /1.1#-homo ⟩
    ⌊ 1 ⌋    ≈⟨  ⌊⌋.cong 1≈0 ⟩
    ⌊ 0 ⌋    ≈˘⟨ ⌊⌋.cong /1.0#-homo ⟩
    ⌊ 0 /1 ⌋ ≈⟨  ⌊⌋∘/1≗id 0 ⟩
    0        ∎)
    where open ℤ.Reasoning

  n≉0⇒0<+n : ∀ n → {{NonZero n}} → 0 < fromNat n
  n≉0⇒0<+n = CommRingₚ.1≉0+n≉0⇒0<+n commutativeRing 1≉0

  n≉0⇒-n<0 : ∀ n → {{NonZero n}} → fromNeg n < 0
  n≉0⇒-n<0 = CommRingₚ.1≉0+n≉0⇒-n<0 commutativeRing 1≉0
