------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered semigroups
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Semigroup
  {ℓ₁ ℓ₂ ℓ₃}
  (semigroup : Semigroup ℓ₁ ℓ₂ ℓ₃)
  where

open Semigroup semigroup
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

open import Helium.Algebra.Ordered.StrictTotal.Properties.Magma magma public
  using
  ( ∙-mono-<; ∙-monoˡ-<; ∙-monoʳ-<
  ; ∙-mono-≤; ∙-monoˡ-≤; ∙-monoʳ-≤
  ; ∙-cancelˡ; ∙-cancelʳ; ∙-cancel
  ; ∙-cancelˡ-<; ∙-cancelʳ-<; ∙-cancel-<
  ; ∙-cancelˡ-≤; ∙-cancelʳ-≤; ∙-cancel-≤
  )
open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public
