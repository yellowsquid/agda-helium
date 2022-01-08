------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of types and operations used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode where

open import Algebra.Bundles using (RawRing)
open import Algebra.Core
import Algebra.Definitions.RawSemiring as RS
open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Fin.Base as Fin hiding (cast)
import Data.Fin.Properties as Fₚ
import Data.Fin.Induction as Induction
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Functional
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pwₚ
open import Function using (_$_; _∘′_; id)
open import Helium.Algebra.Bundles using (RawField; RawBooleanAlgebra)
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable.Core using (False; toWitnessFalse)

record RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  infix 6 _-ᶻ_
  infix 4 _≟ᵇ_ _≟ᶻ_ _<ᶻ_ _<ᶻ?_ _≟ʳ_ _<ʳ_ _<ʳ?_

  field
    bitRawBooleanAlgebra : RawBooleanAlgebra b₁ b₂
    integerRawRing : RawRing i₁ i₂
    realRawField : RawField r₁ r₂

  open RawBooleanAlgebra bitRawBooleanAlgebra public
    using ()
    renaming (Carrier to Bit; _≈_ to _≈ᵇ₁_; _≉_ to _≉ᵇ₁_; ⊤ to 1𝔹; ⊥ to 0𝔹)

  module bitsRawBooleanAlgebra {n} = RawBooleanAlgebra record
    { _≈_ = Pointwise (RawBooleanAlgebra._≈_ bitRawBooleanAlgebra) {n}
    ; _∨_ = zipWith (RawBooleanAlgebra._∨_ bitRawBooleanAlgebra)
    ; _∧_ = zipWith (RawBooleanAlgebra._∧_ bitRawBooleanAlgebra)
    ; ¬_ = map (RawBooleanAlgebra.¬_ bitRawBooleanAlgebra)
    ; ⊤ = replicate (RawBooleanAlgebra.⊤ bitRawBooleanAlgebra)
    ; ⊥ = replicate (RawBooleanAlgebra.⊥ bitRawBooleanAlgebra)
    }

  open bitsRawBooleanAlgebra public
    hiding (Carrier)
    renaming (_≈_ to _≈ᵇ_; _≉_ to _≉ᵇ_; ⊤ to ones; ⊥ to zeros)

  Bits = λ n → bitsRawBooleanAlgebra.Carrier {n}

  open RawRing integerRawRing public
    renaming
    ( Carrier to ℤ; _≈_ to _≈ᶻ_; _≉_ to _≉ᶻ_
    ; _+_ to _+ᶻ_; _*_ to _*ᶻ_; -_ to -ᶻ_; 0# to 0ℤ; 1# to 1ℤ
    ; rawSemiring to integerRawSemiring
    ; +-rawMagma to +ᶻ-rawMagma; +-rawMonoid to +ᶻ-rawMonoid
    ; *-rawMagma to *ᶻ-rawMagma; *-rawMonoid to *ᶻ-rawMonoid
    ; +-rawGroup to +ᶻ-rawGroup
    )

  _-ᶻ_ : Op₂ ℤ
  x -ᶻ y = x +ᶻ -ᶻ y

  open RS integerRawSemiring public using ()
    renaming
    ( _×_ to _×ᶻ_; _×′_ to _×′ᶻ_; sum to sumᶻ
    ; _^_ to _^ᶻ_; _^′_ to _^′ᶻ_; product to productᶻ
    )

  open RawField realRawField public
    renaming
    ( Carrier to ℝ; _≈_ to _≈ʳ_; _≉_ to _≉ʳ_
    ; _+_ to _+ʳ_; _*_ to _*ʳ_; -_ to -ʳ_; 0# to 0ℝ; 1# to 1ℝ; _-_ to _-ʳ_
    ; rawSemiring to realRawSemiring; rawRing to realRawRing
    ; +-rawMagma to +ʳ-rawMagma; +-rawMonoid to +ʳ-rawMonoid
    ; *-rawMagma to *ʳ-rawMagma; *-rawMonoid to *ʳ-rawMonoid
    ; +-rawGroup to +ʳ-rawGroup; *-rawAlmostGroup to *ʳ-rawAlmostGroup
    )

  open RS realRawSemiring public using ()
    renaming
    ( _×_ to _×ʳ_; _×′_ to _×′ʳ_; sum to sumʳ
    ; _^_ to _^ʳ_; _^′_ to _^′ʳ_; product to productʳ
    )

  field
    _≟ᶻ_  : Decidable _≈ᶻ_
    _<ᶻ_  : Rel ℤ i₃
    _<ᶻ?_ : Decidable _<ᶻ_

    _≟ʳ_  : Decidable _≈ʳ_
    _<ʳ_  : Rel ℝ r₃
    _<ʳ?_ : Decidable _<ʳ_

    _≟ᵇ₁_ : Decidable _≈ᵇ₁_

  _≟ᵇ_ : ∀ {n} → Decidable (_≈ᵇ_ {n})
  _≟ᵇ_ = Pwₚ.decidable _≟ᵇ₁_

  field
    float : ℤ → ℝ
    round : ℝ → ℤ

  cast : ∀ {m n} → .(eq : m ≡ n) → Bits m → Bits n
  cast eq x i = x $ Fin.cast (P.sym eq) i

  2ℤ : ℤ
  2ℤ = 2 ×′ᶻ 1ℤ

  getᵇ : ∀ {n} → Fin n → Bits n → Bit
  getᵇ i x = x (opposite i)

  setᵇ : ∀ {n} → Fin n → Bit → Op₁ (Bits n)
  setᵇ i b = updateAt (opposite i) λ _ → b

  sliceᵇ : ∀ {n} (i : Fin (suc n)) j → Bits n → Bits (toℕ (i - j))
  sliceᵇ         zero    zero    x = []
  sliceᵇ {suc n} (suc i) zero    x = getᵇ i x ∷ sliceᵇ i zero (tail x)
  sliceᵇ {suc n} (suc i) (suc j) x = sliceᵇ i j (tail x)

  updateᵇ : ∀ {n} (i : Fin (suc n)) j → Bits (toℕ (i - j)) → Op₁ (Bits n)
  updateᵇ {n} = Induction.<-weakInduction P (λ _ _ → id) helper
    where
    P : Fin (suc n) → Set b₁
    P i = ∀ j → Bits (toℕ (i - j)) → Op₁ (Bits n)

    eq : ∀ {n} {i : Fin n} → toℕ i ≡ toℕ (inject₁ i)
    eq = P.sym $ Fₚ.toℕ-inject₁ _

    eq′ : ∀ {n} {i : Fin n} j → toℕ (i - j) ≡ toℕ (inject₁ i - Fin.cast eq j)
    eq′             zero    = eq
    eq′ {i = suc _} (suc j) = eq′ j

    helper : ∀ i → P (inject₁ i) → P (suc i)
    helper i rec zero    y = rec zero (cast eq (tail y)) ∘′ setᵇ i (y zero)
    helper i rec (suc j) y = rec (Fin.cast eq j) (cast (eq′ j) y)

  hasBit : ∀ {n} → Fin n → Bits n → Bool
  hasBit i x = does (getᵇ i x ≟ᵇ₁ 1𝔹)

  infixl 7 _div_ _mod_

  _div_ : ∀ (x y : ℤ) → {y≉0 : False (float y ≟ʳ 0ℝ)} → ℤ
  (x div y) {y≉0} = round (float x *ʳ toWitnessFalse y≉0 ⁻¹)

  _mod_ : ∀ (x y : ℤ) → {y≉0 : False (float y ≟ʳ 0ℝ)} → ℤ
  (x mod y) {y≉0} = x -ᶻ y *ᶻ (x div y) {y≉0}

  infixl 5 _<<_
  _<<_ : ℤ → ℕ → ℤ
  x << n = x *ᶻ 2ℤ ^′ᶻ n

  module ShiftNotZero
    (1<<n≉0 : ∀ n → False (float (1ℤ << n) ≟ʳ 0ℝ))
    where

    infixl 5 _>>_
    _>>_ : ℤ → ℕ → ℤ
    x >> zero  = x
    x >> suc n = (x div (1ℤ << suc n)) {1<<n≉0 (suc n)}

    getᶻ : ℕ → ℤ → Bit
    getᶻ n x =
      if does ((x mod (1ℤ << suc n)) {1<<n≉0 (suc n)} <ᶻ? 1ℤ << n)
      then 1𝔹
      else 0𝔹

    sliceᶻ : ∀ n i → ℤ → Bits (n ℕ-ℕ i)
    sliceᶻ zero    zero    x = []
    sliceᶻ (suc n) zero    x = getᶻ n x ∷ sliceᶻ n zero x
    sliceᶻ (suc n) (suc i) x = sliceᶻ n i (x >> 1)

  uint : ∀ {n} → Bits n → ℤ
  uint x = sumᶻ λ i → if hasBit i x then 1ℤ << toℕ i else 0ℤ

  sint : ∀ {n} → Bits n → ℤ
  sint {zero}  x = 0ℤ
  sint {suc n} x = uint x -ᶻ (if hasBit (fromℕ n) x then 1ℤ << suc n else 0ℤ)
