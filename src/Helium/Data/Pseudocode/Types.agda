------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of types and operations used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Types where

open import Algebra.Core
import Algebra.Definitions.RawSemiring as RS
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin hiding (cast)
import Data.Fin.Properties as Fₚ
import Data.Fin.Induction as Induction
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pwₚ
open import Function using (_$_; _∘′_; id)
open import Helium.Algebra.Ordered.StrictTotal.Bundles
open import Helium.Algebra.Decidable.Bundles
  using (BooleanAlgebra; RawBooleanAlgebra)
import Helium.Algebra.Decidable.Construct.Pointwise as Pw
open import Helium.Algebra.Morphism.Structures
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Reasoning.StrictPartialOrder as Reasoning
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable.Core
  using (False; toWitnessFalse; fromWitnessFalse)

record RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    bitRawBooleanAlgebra : RawBooleanAlgebra b₁ b₂
    integerRawRing : RawRing i₁ i₂ i₃
    realRawField : RawField r₁ r₂ r₃

  bitsRawBooleanAlgebra : ℕ → RawBooleanAlgebra b₁ b₂
  bitsRawBooleanAlgebra =  Pw.rawBooleanAlgebra  bitRawBooleanAlgebra

  module 𝔹 = RawBooleanAlgebra bitRawBooleanAlgebra
    renaming (Carrier to Bit; ⊤ to 1𝔹; ⊥ to 0𝔹)
  module Bits {n} = RawBooleanAlgebra (bitsRawBooleanAlgebra n)
    renaming (⊤ to ones; ⊥ to zeros)
  module ℤ = RawRing integerRawRing renaming (Carrier to ℤ; 1# to 1ℤ; 0# to 0ℤ)
  module ℝ = RawField realRawField renaming (Carrier to ℝ; 1# to 1ℝ; 0# to 0ℝ)
  module ℤ′ = RS ℤ.Unordered.rawSemiring
  module ℝ′ = RS ℝ.Unordered.rawSemiring

  Bits : ℕ → Set b₁
  Bits n = Bits.Carrier {n}

  open 𝔹 public using (Bit; 1𝔹; 0𝔹)
  open Bits public using (ones; zeros)
  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

  infix 4 _≟ᶻ_ _<ᶻ?_ _≟ʳ_ _<ʳ?_ _≟ᵇ₁_ _≟ᵇ_
  field
    _≟ᶻ_  : Decidable ℤ._≈_
    _<ᶻ?_ : Decidable ℤ._<_
    _≟ʳ_  : Decidable ℝ._≈_
    _<ʳ?_ : Decidable ℝ._<_
    _≟ᵇ₁_ : Decidable 𝔹._≈_

  _≟ᵇ_ : ∀ {n} → Decidable (Bits._≈_ {n})
  _≟ᵇ_ = Pwₚ.decidable _≟ᵇ₁_

  field
    _/1 : ℤ → ℝ
    ⌊_⌋ : ℝ → ℤ

record Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ :
                  Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    bitBooleanAlgebra : BooleanAlgebra b₁ b₂
    integerRing       : CommutativeRing i₁ i₂ i₃
    realField         : Field r₁ r₂ r₃

  bitsBooleanAlgebra : ℕ → BooleanAlgebra b₁ b₂
  bitsBooleanAlgebra = Pw.booleanAlgebra bitBooleanAlgebra

  module 𝔹 = BooleanAlgebra bitBooleanAlgebra
    renaming (Carrier to Bit; ⊤ to 1𝔹; ⊥ to 0𝔹)
  module Bits {n} = BooleanAlgebra (bitsBooleanAlgebra n)
    renaming (⊤ to ones; ⊥ to zeros)
  module ℤ = CommutativeRing integerRing
    renaming (Carrier to ℤ; 1# to 1ℤ; 0# to 0ℤ)
  module ℝ = Field realField
    renaming (Carrier to ℝ; 1# to 1ℝ; 0# to 0ℝ)

  Bits : ℕ → Set b₁
  Bits n = Bits.Carrier {n}

  open 𝔹 public using (Bit; 1𝔹; 0𝔹)
  open Bits public using (ones; zeros)
  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

  module ℤ-Reasoning = Reasoning ℤ.strictPartialOrder
  module ℝ-Reasoning = Reasoning ℝ.strictPartialOrder

  field
    integerDiscrete : ∀ x y → y ℤ.≤ x ⊎ x ℤ.+ 1ℤ ℤ.≤ y
    1≉0 : 1ℤ ℤ.≉ 0ℤ

    _/1 : ℤ → ℝ
    ⌊_⌋ : ℝ → ℤ
    /1-isHomo : IsRingHomomorphism ℤ.Unordered.rawRing ℝ.Unordered.rawRing _/1
    ⌊⌋-isHomo : IsRingHomomorphism ℝ.Unordered.rawRing ℤ.Unordered.rawRing ⌊_⌋
    /1-mono : ∀ x y → x ℤ.< y → x /1 ℝ.< y /1
    ⌊⌋-floor : ∀ x y → x ℤ.≤ ⌊ y ⌋ → ⌊ y ⌋ ℤ.< x ℤ.+ 1ℤ
    ⌊⌋∘/1≗id : ∀ x → ⌊ x /1 ⌋ ℤ.≈ x

  module /1 = IsRingHomomorphism /1-isHomo renaming (⟦⟧-cong to cong)
  module ⌊⌋ = IsRingHomomorphism ⌊⌋-isHomo renaming (⟦⟧-cong to cong)

  bitRawBooleanAlgebra : RawBooleanAlgebra b₁ b₂
  bitRawBooleanAlgebra = record
    { _≈_ = _≈_
    ; _∨_ = _∨_
    ; _∧_ = _∧_
    ; ¬_  = ¬_
    ; ⊤   = ⊤
    ; ⊥   = ⊥
    }
    where open BooleanAlgebra bitBooleanAlgebra

  rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃
  rawPseudocode = record
    { bitRawBooleanAlgebra = bitRawBooleanAlgebra
    ; integerRawRing = ℤ.rawRing
    ; realRawField = ℝ.rawField
    ; _≟ᶻ_ = ℤ._≟_
    ; _<ᶻ?_ = ℤ._<?_
    ; _≟ʳ_ = ℝ._≟_
    ; _<ʳ?_ = ℝ._<?_
    ; _≟ᵇ₁_ = 𝔹._≟_
    ; _/1 = _/1
    ; ⌊_⌋ = ⌊_⌋
    }

  open RawPseudocode rawPseudocode using (module ℤ′; module ℝ′) public
