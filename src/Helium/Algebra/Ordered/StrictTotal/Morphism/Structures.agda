------------------------------------------------------------------------
-- Agda Helium
--
-- Morphisms for ordered algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Algebra.Ordered.StrictTotal.Morphism.Structures where

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Helium.Algebra.Ordered.StrictTotal.Bundles
open import Level using (Level; _⊔_)
open import Relation.Binary.Morphism.Structures

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

module MagmaMorphisms (M₁ : RawMagma a ℓ₁ ℓ₂) (M₂ : RawMagma b ℓ₃ ℓ₄) where
  private
    module M₁ = RawMagma M₁
    module M₂ = RawMagma M₂

  open M₁ using () renaming (Carrier to A)
  open M₂ using () renaming (Carrier to B)
  open MorphismDefinitions A B M₂._≈_

  record IsMagmaHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      isOrderHomomorphism : IsOrderHomomorphism M₁._≈_ M₂._≈_ M₁._<_ M₂._<_ ⟦_⟧
      homo                : Homomorphic₂ ⟦_⟧ M₁._∙_ M₂._∙_

    open IsOrderHomomorphism isOrderHomomorphism public

module MonoidMorphisms (M₁ : RawMonoid a ℓ₁ ℓ₂) (M₂ : RawMonoid b ℓ₃ ℓ₄) where
  private
    module M₁ = RawMonoid M₁
    module M₂ = RawMonoid M₂

  open M₁ using () renaming (Carrier to A)
  open M₂ using () renaming (Carrier to B)
  open MorphismDefinitions A B M₂._≈_
  open MagmaMorphisms M₁.rawMagma M₂.rawMagma

  record IsMonoidHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      isMagmaHomomorphism : IsMagmaHomomorphism ⟦_⟧
      ε-homo              : Homomorphic₀ ⟦_⟧ M₁.ε M₂.ε

    open IsMagmaHomomorphism isMagmaHomomorphism public

module GroupMorphisms (G₁ : RawGroup a ℓ₁ ℓ₂) (G₂ : RawGroup b ℓ₃ ℓ₄) where
  private
    module G₁ = RawGroup G₁
    module G₂ = RawGroup G₂

  open G₁ using () renaming (Carrier to A)
  open G₂ using () renaming (Carrier to B)
  open MorphismDefinitions A B G₂._≈_
  open MonoidMorphisms G₁.rawMonoid G₂.rawMonoid

  record IsGroupHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      ⁻¹-homo              : Homomorphic₁ ⟦_⟧ G₁._⁻¹ G₂._⁻¹

    open IsMonoidHomomorphism isMonoidHomomorphism public

module RingMorphisms (R₁ : RawRing a ℓ₁ ℓ₂) (R₂ : RawRing b ℓ₃ ℓ₄) where
  private
    module R₁ = RawRing R₁
    module R₂ = RawRing R₂

  open R₁ using () renaming (Carrier to A)
  open R₂ using () renaming (Carrier to B)
  open MorphismDefinitions A B R₂._≈_
  open GroupMorphisms R₁.+-rawGroup R₂.+-rawGroup

  record IsRingHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      +-isGroupHomomorphism : IsGroupHomomorphism ⟦_⟧
      *-homo                : Homomorphic₂ ⟦_⟧ R₁._*_ R₂._*_
      1#-homo               : Homomorphic₀ ⟦_⟧ R₁.1# R₂.1#

    open IsGroupHomomorphism +-isGroupHomomorphism public
      renaming
      ( homo to +-homo
      ; ε-homo to 0#-homo
      ; ⁻¹-homo to -‿homo
      ; isMagmaHomomorphism to +-isMagmaHomomorphism
      ; isMonoidHomomorphism to +-isMonoidHomomorphism
      )

open MagmaMorphisms public
open MonoidMorphisms public
open GroupMorphisms public
open RingMorphisms public
