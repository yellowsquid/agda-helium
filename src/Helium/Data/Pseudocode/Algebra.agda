------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of types and operations used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Algebra where

open import Algebra.Core
import Algebra.Definitions.RawSemiring as RS
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin hiding (cast; _<_)
import Data.Fin.Properties as Fₚ
import Data.Fin.Induction as Induction
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pwₚ
open import Function using (_$_; _∘′_; id)
open import Helium.Algebra.Decidable.Bundles
  using (BooleanAlgebra; RawBooleanAlgebra)
open import Helium.Algebra.Ordered.StrictTotal.Bundles
open import Helium.Algebra.Ordered.StrictTotal.Morphism.Structures
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Construct.StrictToNonStrict as ToNonStrict
open import Relation.Binary.Definitions
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Reasoning.StrictPartialOrder as RawReasoning
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (does; yes; no) renaming (¬_ to ¬′_)
open import Relation.Nullary.Decidable.Core
  using (False; toWitnessFalse; fromWitnessFalse)

record RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    bitRawBooleanAlgebra : RawBooleanAlgebra b₁ b₂
    integerRawRing : RawRing i₁ i₂ i₃
    realRawField : RawField r₁ r₂ r₃

  infix 4 _≟ᶻ_ _<ᶻ?_ _≟ʳ_ _<ʳ?_ _≟ᵇ_
  field
    _≟ᶻ_  : Decidable (RawRing._≈_ integerRawRing)
    _<ᶻ?_ : Decidable (RawRing._<_ integerRawRing)
    _≟ʳ_  : Decidable (RawField._≈_ realRawField)
    _<ʳ?_ : Decidable (RawField._<_ realRawField)
    _≟ᵇ_  : Decidable (RawBooleanAlgebra._≈_ bitRawBooleanAlgebra)

  field
    _/1 : RawRing.Carrier integerRawRing → RawField.Carrier realRawField
    ⌊_⌋ : RawField.Carrier realRawField → RawRing.Carrier integerRawRing

  module Bit where
    open RawBooleanAlgebra bitRawBooleanAlgebra public
      renaming (Carrier to Bit; ⊤ to 1𝔹; ⊥ to 0𝔹)

    _≟_ : Decidable _≈_
    _≟_ = _≟ᵇ_

  module ℤ where
    open RawRing integerRawRing public
      renaming (Carrier to ℤ; 1# to 1ℤ; 0# to 0ℤ)
    open RS Unordered.rawSemiring public
      hiding (_×_; _^_)
      renaming (_×′_ to _×_; _^′_ to _^_)

    _≟_ : Decidable _≈_
    _≟_ = _≟ᶻ_

    _<?_ : Decidable _<_
    _<?_ = _<ᶻ?_

  module ℝ where
    open RawField realRawField public
      renaming (Carrier to ℝ; 1# to 1ℝ; 0# to 0ℝ)
    open RS Unordered.rawSemiring public
      hiding (_×_; _^_)
      renaming (_×′_ to _×_; _^′_ to _^_)

    _≟_ : Decidable _≈_
    _≟_ = _≟ʳ_

    _<?_ : Decidable _<_
    _<?_ = _<ʳ?_

  open Bit public using (Bit; 1𝔹; 0𝔹)
  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

record Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ :
                  Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    bitBooleanAlgebra : BooleanAlgebra b₁ b₂
    integerRing       : CommutativeRing i₁ i₂ i₃
    realField         : Field r₁ r₂ r₃

  private
    module ℤ′ = CommutativeRing integerRing
    module ℝ′ = Field realField
    module ℤ-ord = ToNonStrict ℤ′._≈_ ℤ′._<_
    module ℝ-ord = ToNonStrict ℝ′._≈_ ℝ′._<_

  field
    integerDiscrete : ∀ x y → y ℤ-ord.≤ x ⊎ x ℤ′.+ ℤ′.1# ℤ-ord.≤ y
    1≉0 : ¬′ ℤ′.1# ℤ′.≈ ℤ′.0#

    _/1 : ℤ′.Carrier → ℝ′.Carrier
    ⌊_⌋ : ℝ′.Carrier → ℤ′.Carrier
    /1-isHomo : IsRingHomomorphism ℤ′.rawRing ℝ′.rawRing _/1
    ⌊⌋-isHomo : IsOrderHomomorphism ℝ′._≈_ ℤ′._≈_ ℝ-ord._≤_ ℤ-ord._≤_ ⌊_⌋
    ⌊⌋-floor : ∀ x y → x ℝ′.< y /1 → ⌊ x ⌋ ℤ′.< y
    ⌊x/1⌋≈x : ∀ x → ⌊ x /1 ⌋ ℤ′.≈ x

  module Bit where
    open BooleanAlgebra bitBooleanAlgebra public
      renaming (Carrier to Bit; ⊤ to 1𝔹; ⊥ to 0𝔹)

  module ℤ where
    open CommutativeRing integerRing public
      renaming (Carrier to ℤ; 1# to 1ℤ; 0# to 0ℤ)
    open RS Unordered.rawSemiring public

    module Reasoning = RawReasoning strictPartialOrder

  module ℝ where
    open Field realField public
      renaming (Carrier to ℝ; 1# to 1ℝ; 0# to 0ℝ)
    open RS Unordered.rawSemiring public

    module Reasoning = RawReasoning strictPartialOrder

  open Bit public using (Bit; 1𝔹; 0𝔹)
  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

  module /1 = IsRingHomomorphism /1-isHomo
  module ⌊⌋ = IsOrderHomomorphism ⌊⌋-isHomo

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
    ; _≟ᵇ_ = Bit._≟_
    ; _/1 = _/1
    ; ⌊_⌋ = ⌊_⌋
    }
