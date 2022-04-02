------------------------------------------------------------------------
--  Agda Helium
--
-- Properties of almost groups
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Helium.Algebra.Bundles

module Helium.Algebra.Properties.AlmostGroup
  {g₁ g₂}
  (almostGroup : AlmostGroup g₁ g₂)
  where

open AlmostGroup almostGroup
open import Algebra.Definitions _≈_
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
open import Data.Product

1≉0⇒1⁻¹≈1 : (1≉0 : 1# ≉ 0#) → 1≉0 ⁻¹ ≈ 1#
1≉0⇒1⁻¹≈1 1≉0 = begin
  1≉0 ⁻¹      ≈˘⟨ identityʳ (1≉0 ⁻¹) ⟩
  1≉0 ⁻¹ ∙ 1# ≈⟨ inverseˡ 1≉0 ⟩
  1#          ∎

⁻¹-irrelevant : ∀ {x} → (x≉0 x≉0′ : x ≉ 0#) → x≉0 ⁻¹ ≈ x≉0′ ⁻¹
⁻¹-irrelevant {x} x≉0 x≉0′ = begin
  x≉0 ⁻¹                 ≈˘⟨ identityˡ (x≉0 ⁻¹) ⟩
  1# ∙ x≉0 ⁻¹            ≈˘⟨ ∙-congʳ (inverseˡ x≉0′) ⟩
  x≉0′ ⁻¹ ∙ x ∙ x≉0 ⁻¹   ≈⟨  assoc (x≉0′ ⁻¹) x (x≉0 ⁻¹) ⟩
  x≉0′ ⁻¹ ∙ (x ∙ x≉0 ⁻¹) ≈⟨  ∙-congˡ (inverseʳ x≉0) ⟩
  x≉0′ ⁻¹ ∙ 1#           ≈⟨  identityʳ (x≉0′ ⁻¹) ⟩
  x≉0′ ⁻¹                ∎

private

  left-helper : ∀ x {y} (y≉0 : y ≉ 0#) → (x ∙ y) ∙ y≉0 ⁻¹ ≈ x
  left-helper x {y} y≉0 = begin
    x ∙ y ∙ y≉0 ⁻¹   ≈⟨ assoc x y (y≉0 ⁻¹) ⟩
    x ∙ (y ∙ y≉0 ⁻¹) ≈⟨ ∙-congˡ (inverseʳ y≉0) ⟩
    x ∙ 1#           ≈⟨ identityʳ x ⟩
    x                ∎

  right-helper : ∀ {x} (x≉0 : x ≉ 0#) y → x≉0 ⁻¹ ∙ (x ∙ y) ≈ y
  right-helper {x} x≉0 y = begin
    x≉0 ⁻¹ ∙ (x ∙ y) ≈˘⟨ assoc (x≉0 ⁻¹) x y ⟩
    x≉0 ⁻¹ ∙ x ∙ y   ≈⟨  ∙-congʳ (inverseˡ x≉0) ⟩
    1# ∙ y           ≈⟨  identityˡ y ⟩
    y                ∎

x≉0⇒∙-cancelˡ : ∀ {x} → x ≉ 0# → Injective _≈_ _≈_ (x ∙_)
x≉0⇒∙-cancelˡ {x} x≉0 {y} {z} x∙y≈x∙z = begin
  y                ≈˘⟨ right-helper x≉0 y ⟩
  x≉0 ⁻¹ ∙ (x ∙ y) ≈⟨  ∙-congˡ x∙y≈x∙z ⟩
  x≉0 ⁻¹ ∙ (x ∙ z) ≈⟨  right-helper x≉0 z ⟩
  z                ∎

x≉0⇒∙-cancelʳ : ∀ {x} → x ≉ 0# → Injective _≈_ _≈_ (_∙ x)
x≉0⇒∙-cancelʳ {x} x≉0 {y} {z} y∙x≈z∙x = begin
  y              ≈˘⟨ left-helper y x≉0 ⟩
  y ∙ x ∙ x≉0 ⁻¹ ≈⟨  ∙-congʳ y∙x≈z∙x ⟩
  z ∙ x ∙ x≉0 ⁻¹ ≈⟨  left-helper z x≉0 ⟩
  z              ∎

⁻¹-involutive : ∀ {x} → (x≉0 : x ≉ 0#) → (x⁻¹≉0 : x≉0 ⁻¹ ≉ 0#) → x⁻¹≉0 ⁻¹ ≈ x
⁻¹-involutive {x} x≉0 x⁻¹≉0 = begin
  x⁻¹≉0 ⁻¹                ≈˘⟨ identityʳ (x⁻¹≉0 ⁻¹) ⟩
  x⁻¹≉0 ⁻¹ ∙ 1#           ≈˘⟨ ∙-congˡ (inverseˡ x≉0) ⟩
  x⁻¹≉0 ⁻¹ ∙ (x≉0 ⁻¹ ∙ x) ≈⟨  right-helper x⁻¹≉0 x ⟩
  x                       ∎

⁻¹-injective : ∀ {x y} {x≉0 : x ≉ 0#} {y≉0 : y ≉ 0#} → x≉0 ⁻¹ ≈ y≉0 ⁻¹ → x ≈ y
⁻¹-injective {x} {y} {x≉0} {y≉0} x⁻¹≈y⁻¹ = begin
  x                ≈˘⟨ identityˡ x ⟩
  1# ∙ x           ≈˘⟨ ∙-congʳ (inverseʳ y≉0) ⟩
  y ∙ y≉0 ⁻¹ ∙ x   ≈˘⟨ ∙-congʳ (∙-congˡ x⁻¹≈y⁻¹) ⟩
  y ∙ x≉0 ⁻¹ ∙ x   ≈⟨  assoc y (x≉0 ⁻¹) x ⟩
  y ∙ (x≉0 ⁻¹ ∙ x) ≈⟨  ∙-congˡ (inverseˡ x≉0) ⟩
  y ∙ 1#           ≈⟨  identityʳ y ⟩
  y                ∎

⁻¹-anti-homo-∙ : ∀ {x y} (x≉0 : x ≉ 0#) (y≉0 : y ≉ 0#) (x∙y≉0 : x ∙ y ≉ 0#) → x∙y≉0 ⁻¹ ≈ y≉0 ⁻¹ ∙ x≉0 ⁻¹
⁻¹-anti-homo-∙ {x} {y} x≉0 y≉0 x∙y≉0 = x≉0⇒∙-cancelˡ x∙y≉0 (begin
  x ∙ y ∙ x∙y≉0 ⁻¹          ≈⟨  inverseʳ x∙y≉0 ⟩
  1#                        ≈˘⟨ inverseʳ x≉0 ⟩
  x ∙ x≉0 ⁻¹                ≈˘⟨ ∙-congʳ (left-helper x y≉0) ⟩
  x ∙ y ∙ y≉0 ⁻¹ ∙ x≉0 ⁻¹   ≈⟨  assoc (x ∙ y) (y≉0 ⁻¹) (x≉0 ⁻¹) ⟩
  x ∙ y ∙ (y≉0 ⁻¹ ∙ x≉0 ⁻¹) ∎)

identityˡ-unique : ∀ {x} {y} → y ≉ 0# → x ∙ y ≈ y → x ≈ 1#
identityˡ-unique {x} {y} y≉0 x∙y≈y = begin
  x              ≈˘⟨ left-helper x y≉0 ⟩
  x ∙ y ∙ y≉0 ⁻¹ ≈⟨  ∙-congʳ x∙y≈y ⟩
  y ∙ y≉0 ⁻¹     ≈⟨  inverseʳ y≉0 ⟩
  1#             ∎

identityʳ-unique : ∀ {x} {y} → y ≉ 0# → y ∙ x ≈ y → x ≈ 1#
identityʳ-unique {x} {y} y≉0 y∙x≈y = begin
  x                ≈˘⟨ right-helper y≉0 x ⟩
  y≉0 ⁻¹ ∙ (y ∙ x) ≈⟨  ∙-congˡ y∙x≈y ⟩
  y≉0 ⁻¹ ∙ y       ≈⟨  inverseˡ y≉0 ⟩
  1#               ∎

inverseˡ-unique : ∀ {x} {y} (y≉0 : y ≉ 0#) → x ∙ y ≈ 1# → x ≈ y≉0 ⁻¹
inverseˡ-unique {x} {y} y≉0 x∙y≈1 = begin
  x              ≈˘⟨ left-helper x y≉0 ⟩
  x ∙ y ∙ y≉0 ⁻¹ ≈⟨  ∙-congʳ x∙y≈1 ⟩
  1# ∙ y≉0 ⁻¹    ≈⟨  identityˡ (y≉0 ⁻¹) ⟩
  y≉0 ⁻¹         ∎

inverseʳ-unique : ∀ {x} {y} (y≉0 : y ≉ 0#) → y ∙ x ≈ 1# → x ≈ y≉0 ⁻¹
inverseʳ-unique {x} {y} y≉0 y∙x≈1 = begin
  x                ≈˘⟨ right-helper y≉0 x ⟩
  y≉0 ⁻¹ ∙ (y ∙ x) ≈⟨  ∙-congˡ y∙x≈1 ⟩
  y≉0 ⁻¹ ∙ 1#      ≈⟨  identityʳ (y≉0 ⁻¹) ⟩
  y≉0 ⁻¹           ∎
