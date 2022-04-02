------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered magmas
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Magma
  {ℓ₁ ℓ₂ ℓ₃}
  (magma : Magma ℓ₁ ℓ₂ ℓ₃)
  where

open Magma magma
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

open import Algebra.Definitions
open import Data.Product using (_,_)
open import Helium.Algebra.Ordered.StrictTotal.Consequences strictTotalOrder

open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder public

--------------------------------------------------------------------------------
-- Properties of _∙_

---- Congruences

-- _<_

∙-mono-< : Congruent₂ _<_ _∙_
∙-mono-< = invariant⇒mono-< ∙-invariant

∙-monoˡ-< : LeftCongruent _<_ _∙_
∙-monoˡ-< = invariantˡ⇒monoˡ-< ∙-invariantˡ

∙-monoʳ-< : RightCongruent _<_ _∙_
∙-monoʳ-< = invariantʳ⇒monoʳ-< ∙-invariantʳ

-- _≤_

∙-mono-≤ : Congruent₂ _≤_ _∙_
∙-mono-≤ = cong+invariant⇒mono-≤ ∙-cong ∙-invariant

∙-monoˡ-≤ : LeftCongruent _≤_ _∙_
∙-monoˡ-≤ {x} = congˡ+monoˡ-<⇒monoˡ-≤ (∙-congˡ {x}) (∙-monoˡ-< {x}) {x}

∙-monoʳ-≤ : RightCongruent _≤_ _∙_
∙-monoʳ-≤ {x} = congʳ+monoʳ-<⇒monoʳ-≤ (∙-congʳ {x}) (∙-monoʳ-< {x}) {x}

---- Cancelling

-- _≈_

∙-cancelˡ : LeftCancellative _≈_ _∙_
∙-cancelˡ = monoˡ-<⇒cancelˡ ∙-monoˡ-<

∙-cancelʳ : RightCancellative _≈_ _∙_
∙-cancelʳ {x} = monoʳ-<⇒cancelʳ (∙-monoʳ-< {x}) {x}

∙-cancel : Cancellative _≈_ _∙_
∙-cancel = ∙-cancelˡ , ∙-cancelʳ

-- _<_

∙-cancelˡ-< : LeftCancellative _<_ _∙_
∙-cancelˡ-< = monoˡ-≤⇒cancelˡ-< ∙-monoˡ-≤

∙-cancelʳ-< : RightCancellative _<_ _∙_
∙-cancelʳ-< {x} = monoʳ-≤⇒cancelʳ-< (∙-monoʳ-≤ {x}) {x}

∙-cancel-< : Cancellative _<_ _∙_
∙-cancel-< = ∙-cancelˡ-< , ∙-cancelʳ-<

-- _≤_

∙-cancelˡ-≤ : LeftCancellative _≤_ _∙_
∙-cancelˡ-≤ = monoˡ-<⇒cancelˡ-≤ ∙-monoˡ-<

∙-cancelʳ-≤ : RightCancellative _≤_ _∙_
∙-cancelʳ-≤ {x} = monoʳ-<⇒cancelʳ-≤ (∙-monoʳ-< {x}) {x}

∙-cancel-≤ : Cancellative _≤_ _∙_
∙-cancel-≤ = ∙-cancelˡ-≤ , ∙-cancelʳ-≤
