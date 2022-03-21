------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered commutative rings
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.CommutativeRing
  {ℓ₁ ℓ₂ ℓ₃}
  (commutativeRing : CommutativeRing ℓ₁ ℓ₂ ℓ₃)
  where

open CommutativeRing commutativeRing

open import Algebra.Properties.Ring Unordered.ring public
  renaming (-0#≈0# to -0≈0)
open import Algebra.Properties.Semiring.Mult.TCOptimised Unordered.semiring public
open import Algebra.Properties.CommutativeSemiring.Exp.TCOptimised Unordered.commutativeSemiring public
open import Helium.Algebra.Ordered.StrictTotal.Properties.Ring ring public
  using
  ( <⇒≱; ≤⇒≯; >⇒≉; ≈⇒≯; <⇒≉; ≈⇒≮; ≤∧≉⇒<; ≥∧≉⇒>
  ; x<y⇒0<y-x; -‿anti-mono
  ; ⊤′; number; negative
  ; 0≤1; 1≉0+n≉0⇒0<+n; 1≉0+n≉0⇒-n<0)
