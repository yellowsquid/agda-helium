------------------------------------------------------------------------
-- Agda Helium
--
-- Redefine Ring monomorphisms to resolve problems with overloading.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Algebra.Morphism.Structures where

open import Algebra.Bundles using (RawRing)
open import Algebra.Morphism.Structures
  hiding (IsRingHomomorphism; module RingMorphisms)
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module RingMorphisms (R₁ : RawRing a ℓ₁) (R₂ : RawRing b ℓ₂) where
  module R₁ = RawRing R₁ renaming (Carrier to A)
  module R₂ = RawRing R₂ renaming (Carrier to B)
  open R₁ using (A)
  open R₂ using (B)

  private
    module +′ = GroupMorphisms R₁.+-rawGroup R₂.+-rawGroup
    module *′ = MonoidMorphisms R₁.*-rawMonoid R₂.*-rawMonoid

  record IsRingHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      +-isGroupHomomorphism  : +′.IsGroupHomomorphism  ⟦_⟧
      *-isMonoidHomomorphism : *′.IsMonoidHomomorphism ⟦_⟧

    open +′.IsGroupHomomorphism +-isGroupHomomorphism public
      renaming (homo to +-homo; ε-homo to 0#-homo; ⁻¹-homo to -‿homo)

    open *′.IsMonoidHomomorphism *-isMonoidHomomorphism public
      hiding (⟦⟧-cong)
      renaming (homo to *-homo; ε-homo to 1#-homo)

open RingMorphisms public
