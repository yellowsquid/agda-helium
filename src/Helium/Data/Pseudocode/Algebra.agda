------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of types and operations used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Algebra where

open import Algebra.Core
import Algebra.Definitions.RawSemiring as RS
open import Data.Sum using (_⊎_)
open import Helium.Algebra.Ordered.StrictTotal.Bundles
open import Helium.Algebra.Ordered.StrictTotal.Morphism.Structures
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Construct.StrictToNonStrict as ToNonStrict
open import Relation.Binary.Definitions
open import Relation.Binary.Morphism.Structures
import Relation.Binary.Reasoning.StrictPartialOrder as RawReasoning
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (¬_)

record RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    integerRawRing : RawRing i₁ i₂ i₃
    realRawField : RawField r₁ r₂ r₃

  infix 4 _≟ᶻ_ _<ᶻ?_ _≟ʳ_ _<ʳ?_
  field
    _≟ᶻ_  : Decidable (RawRing._≈_ integerRawRing)
    _<ᶻ?_ : Decidable (RawRing._<_ integerRawRing)
    _≟ʳ_  : Decidable (RawField._≈_ realRawField)
    _<ʳ?_ : Decidable (RawField._<_ realRawField)

  field
    _/1 : RawRing.Carrier integerRawRing → RawField.Carrier realRawField
    ⌊_⌋ : RawField.Carrier realRawField → RawRing.Carrier integerRawRing

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

  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

record Pseudocode i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  field
    integerRing       : CommutativeRing i₁ i₂ i₃
    realField         : Field r₁ r₂ r₃

  private
    module ℤ′ = CommutativeRing integerRing
    module ℝ′ = Field realField
    module ℤ-ord = ToNonStrict ℤ′._≈_ ℤ′._<_
    module ℝ-ord = ToNonStrict ℝ′._≈_ ℝ′._<_

  field
    integerDiscrete : ∀ x y → y ℤ-ord.≤ x ⊎ x ℤ′.+ ℤ′.1# ℤ-ord.≤ y
    1≉0 : ¬ ℤ′.1# ℤ′.≈ ℤ′.0#

    _/1 : ℤ′.Carrier → ℝ′.Carrier
    ⌊_⌋ : ℝ′.Carrier → ℤ′.Carrier
    /1-isHomo : IsRingHomomorphism ℤ′.rawRing ℝ′.rawRing _/1
    ⌊⌋-isHomo : IsOrderHomomorphism ℝ′._≈_ ℤ′._≈_ ℝ-ord._≤_ ℤ-ord._≤_ ⌊_⌋
    ⌊⌋-floor : ∀ x y → x ℝ′.< y /1 → ⌊ x ⌋ ℤ′.< y
    ⌊x/1⌋≈x : ∀ x → ⌊ x /1 ⌋ ℤ′.≈ x

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

  open ℤ public using (ℤ; 1ℤ; 0ℤ)
  open ℝ public using (ℝ; 1ℝ; 0ℝ)

  module /1 = IsRingHomomorphism /1-isHomo
  module ⌊⌋ = IsOrderHomomorphism ⌊⌋-isHomo

  rawPseudocode : RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃
  rawPseudocode = record
    { integerRawRing = ℤ.rawRing
    ; realRawField = ℝ.rawField
    ; _≟ᶻ_ = ℤ._≟_
    ; _<ᶻ?_ = ℤ._<?_
    ; _≟ʳ_ = ℝ._≟_
    ; _<ʳ?_ = ℝ._<?_
    ; _/1 = _/1
    ; ⌊_⌋ = ⌊_⌋
    }
