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
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  ; 0<a+0<b⇒0<ab to x>0∧y>0⇒x*y>0
  )

open import Algebra.Properties.Ring Unordered.ring public
  renaming (-0#≈0# to -0≈0)
open import Algebra.Properties.Semiring.Mult.TCOptimised Unordered.semiring public
open import Algebra.Properties.CommutativeSemiring.Exp.TCOptimised Unordered.commutativeSemiring public
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

  ; x*x≥0

  ; ^-zeroˡ; ^-zeroʳ
  ; ^-identityʳ

  ; n≢0⇒0^n≈0
  ; x>1⇒^-monoˡ-<; 0<x<1⇒^-anti-monoˡ-<
  ; x≥1⇒^-monoˡ-≤; 0≤x≤1⇒^-anti-monoˡ-≤

  ; x>0⇒x^n>0
  ; x≥0⇒x^n≥0

  ; x>1∧n≢0⇒x^n>1; 0≤x<1∧n≢0⇒x^n<1
  ; x≥1⇒x^n≥1; 0≤x≤1⇒x^n≤1
  )
