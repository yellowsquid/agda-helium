------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of types and operations used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode where

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

  cast : ∀ {m n} → .(eq : m ≡ n) → Bits m → Bits n
  cast eq x i = x $ Fin.cast (P.sym eq) i

  2ℤ : ℤ
  2ℤ = 2 ℤ′.×′ 1ℤ

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

  _div_ : ∀ (x y : ℤ) → {y≉0 : False (y /1 ≟ʳ 0ℝ)} → ℤ
  (x div y) {y≉0} = ⌊ x /1 ℝ.* toWitnessFalse y≉0 ℝ.⁻¹ ⌋

  _mod_ : ∀ (x y : ℤ) → {y≉0 : False (y /1 ≟ʳ 0ℝ)} → ℤ
  (x mod y) {y≉0} = x ℤ.+ ℤ.- y ℤ.* (x div y) {y≉0}

  infixl 5 _<<_
  _<<_ : ℤ → ℕ → ℤ
  x << n = 2ℤ ℤ′.^′ n ℤ.* x

  module ShiftNotZero
    (1<<n≉0 : ∀ n → False ((1ℤ << n) /1 ≟ʳ 0ℝ))
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
  uint x = ℤ′.sum λ i → if hasBit i x then 1ℤ << toℕ i else 0ℤ

  sint : ∀ {n} → Bits n → ℤ
  sint {zero}  x = 0ℤ
  sint {suc n} x = uint x ℤ.+ ℤ.- (if hasBit (fromℕ n) x then 1ℤ << suc n else 0ℤ)

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

  open RawPseudocode rawPseudocode public
    using
    ( 2ℤ; cast; getᵇ; setᵇ; sliceᵇ; updateᵇ; hasBit
    ; _div_; _mod_; _<<_; uint; sint
    )

  private
    -- FIXME: move almost all of these proofs into a separate module
    a<b⇒ca<cb : ∀ {a b c} → 0ℤ ℤ.< c → a ℤ.< b → c ℤ.* a ℤ.< c ℤ.* b
    a<b⇒ca<cb {a} {b} {c} 0<c a<b = begin-strict
      c ℤ.* a                     ≈˘⟨ ℤ.+-identityʳ _ ⟩
      c ℤ.* a ℤ.+ 0ℤ              <⟨  ℤ.+-invariantˡ _ $ ℤ.0<a+0<b⇒0<ab 0<c 0<b-a ⟩
      c ℤ.* a ℤ.+ c ℤ.* (b ℤ.- a) ≈˘⟨ ℤ.distribˡ c a (b ℤ.- a) ⟩
      c ℤ.* (a ℤ.+ (b ℤ.- a))     ≈⟨  ℤ.*-congˡ $ ℤ.+-congˡ $ ℤ.+-comm b (ℤ.- a) ⟩
      c ℤ.* (a ℤ.+ (ℤ.- a ℤ.+ b)) ≈˘⟨ ℤ.*-congˡ $ ℤ.+-assoc a (ℤ.- a) b ⟩
      c ℤ.* ((a ℤ.+ ℤ.- a) ℤ.+ b) ≈⟨  ℤ.*-congˡ $ ℤ.+-congʳ $ ℤ.-‿inverseʳ a ⟩
      c ℤ.* (0ℤ ℤ.+ b)            ≈⟨  (ℤ.*-congˡ $ ℤ.+-identityˡ b) ⟩
      c ℤ.* b                     ∎
      where
      open ℤ-Reasoning

      0<b-a : 0ℤ ℤ.< b ℤ.- a
      0<b-a = begin-strict
        0ℤ      ≈˘⟨ ℤ.-‿inverseʳ a ⟩
        a ℤ.- a <⟨  ℤ.+-invariantʳ (ℤ.- a) a<b ⟩
        b ℤ.- a ∎

    -‿idem : ∀ x → ℤ.- (ℤ.- x) ℤ.≈ x
    -‿idem x = begin-equality
      ℤ.- (ℤ.- x)             ≈˘⟨ ℤ.+-identityˡ _ ⟩
      0ℤ ℤ.- ℤ.- x            ≈˘⟨ ℤ.+-congʳ $ ℤ.-‿inverseʳ x ⟩
      x ℤ.- x ℤ.- ℤ.- x       ≈⟨  ℤ.+-assoc x (ℤ.- x) _ ⟩
      x ℤ.+ (ℤ.- x ℤ.- ℤ.- x) ≈⟨  ℤ.+-congˡ $ ℤ.-‿inverseʳ (ℤ.- x) ⟩
      x ℤ.+ 0ℤ                ≈⟨  ℤ.+-identityʳ x ⟩
      x                       ∎
      where open ℤ-Reasoning

    -a*b≈-ab : ∀ a b → ℤ.- a ℤ.* b ℤ.≈ ℤ.- (a ℤ.* b)
    -a*b≈-ab a b = begin-equality
      ℤ.- a ℤ.* b                           ≈˘⟨ ℤ.+-identityʳ _ ⟩
      ℤ.- a ℤ.* b ℤ.+ 0ℤ                    ≈˘⟨ ℤ.+-congˡ $ ℤ.-‿inverseʳ _ ⟩
      ℤ.- a ℤ.* b ℤ.+ (a ℤ.* b ℤ.- a ℤ.* b) ≈˘⟨ ℤ.+-assoc _ _ _ ⟩
      ℤ.- a ℤ.* b ℤ.+ a ℤ.* b ℤ.- a ℤ.* b   ≈˘⟨ ℤ.+-congʳ $ ℤ.distribʳ b _ a ⟩
      (ℤ.- a ℤ.+ a) ℤ.* b ℤ.- a ℤ.* b       ≈⟨  ℤ.+-congʳ $ ℤ.*-congʳ $ ℤ.-‿inverseˡ a ⟩
      0ℤ ℤ.* b ℤ.- a ℤ.* b                  ≈⟨  ℤ.+-congʳ $ ℤ.zeroˡ b ⟩
      0ℤ ℤ.- a ℤ.* b                        ≈⟨  ℤ.+-identityˡ _ ⟩
      ℤ.- (a ℤ.* b)                         ∎
      where open ℤ-Reasoning

    a*-b≈-ab : ∀ a b → a ℤ.* ℤ.- b ℤ.≈ ℤ.- (a ℤ.* b)
    a*-b≈-ab a b = begin-equality
      a ℤ.* ℤ.- b   ≈⟨ ℤ.*-comm a (ℤ.- b) ⟩
      ℤ.- b ℤ.* a   ≈⟨ -a*b≈-ab b a ⟩
      ℤ.- (b ℤ.* a) ≈⟨ ℤ.-‿cong $ ℤ.*-comm b a ⟩
      ℤ.- (a ℤ.* b) ∎
      where open ℤ-Reasoning

    0<a⇒0>-a : ∀ {a} → 0ℤ ℤ.< a → 0ℤ ℤ.> ℤ.- a
    0<a⇒0>-a {a} 0<a = begin-strict
      ℤ.- a    ≈˘⟨ ℤ.+-identityˡ _ ⟩
      0ℤ ℤ.- a <⟨  ℤ.+-invariantʳ _ 0<a ⟩
      a ℤ.- a  ≈⟨  ℤ.-‿inverseʳ a ⟩
      0ℤ       ∎
      where open ℤ-Reasoning

    0>a⇒0<-a : ∀ {a} → 0ℤ ℤ.> a → 0ℤ ℤ.< ℤ.- a
    0>a⇒0<-a {a} 0>a = begin-strict
      0ℤ       ≈˘⟨ ℤ.-‿inverseʳ a ⟩
      a ℤ.- a  <⟨  ℤ.+-invariantʳ _ 0>a ⟩
      0ℤ ℤ.- a ≈⟨  ℤ.+-identityˡ _ ⟩
      ℤ.- a    ∎
      where open ℤ-Reasoning

    0<-a⇒0>a : ∀ {a} → 0ℤ ℤ.< ℤ.- a → 0ℤ ℤ.> a
    0<-a⇒0>a {a} 0<-a = begin-strict
      a        ≈˘⟨ ℤ.+-identityʳ a ⟩
      a ℤ.+ 0ℤ <⟨  ℤ.+-invariantˡ a 0<-a ⟩
      a ℤ.- a  ≈⟨  ℤ.-‿inverseʳ a ⟩
      0ℤ       ∎
      where open ℤ-Reasoning

    0>-a⇒0<a : ∀ {a} → 0ℤ ℤ.> ℤ.- a → 0ℤ ℤ.< a
    0>-a⇒0<a {a} 0>-a = begin-strict
      0ℤ       ≈˘⟨ ℤ.-‿inverseʳ a ⟩
      a ℤ.- a  <⟨  ℤ.+-invariantˡ a 0>-a ⟩
      a ℤ.+ 0ℤ ≈⟨  ℤ.+-identityʳ a ⟩
      a        ∎
      where open ℤ-Reasoning

    0>a+0<b⇒0>ab : ∀ {a b} → 0ℤ ℤ.> a → 0ℤ ℤ.< b → 0ℤ ℤ.> a ℤ.* b
    0>a+0<b⇒0>ab {a} {b} 0>a 0<b = 0<-a⇒0>a $ begin-strict
      0ℤ              <⟨ ℤ.0<a+0<b⇒0<ab (0>a⇒0<-a 0>a) 0<b ⟩
      ℤ.- a ℤ.* b     ≈⟨ -a*b≈-ab a b ⟩
      ℤ.- (a ℤ.* b)   ∎
      where open ℤ-Reasoning

    0<a+0>b⇒0>ab : ∀ {a b} → 0ℤ ℤ.< a → 0ℤ ℤ.> b → 0ℤ ℤ.> a ℤ.* b
    0<a+0>b⇒0>ab {a} {b} 0<a 0>b = 0<-a⇒0>a $ begin-strict
      0ℤ              <⟨ ℤ.0<a+0<b⇒0<ab 0<a (0>a⇒0<-a 0>b) ⟩
      a ℤ.* ℤ.- b     ≈⟨ a*-b≈-ab a b ⟩
      ℤ.- (a ℤ.* b)   ∎
      where open ℤ-Reasoning

    0>a+0>b⇒0<ab : ∀ {a b} → 0ℤ ℤ.> a → 0ℤ ℤ.> b → 0ℤ ℤ.< a ℤ.* b
    0>a+0>b⇒0<ab {a} {b} 0>a 0>b = begin-strict
      0ℤ                  <⟨ ℤ.0<a+0<b⇒0<ab (0>a⇒0<-a 0>a) (0>a⇒0<-a 0>b) ⟩
      ℤ.- a ℤ.* ℤ.- b     ≈⟨ -a*b≈-ab a (ℤ.- b) ⟩
      ℤ.- (a ℤ.* ℤ.- b)   ≈⟨ ℤ.-‿cong $ a*-b≈-ab a b ⟩
      ℤ.- (ℤ.- (a ℤ.* b)) ≈⟨ -‿idem (a ℤ.* b) ⟩
      a ℤ.* b             ∎
      where open ℤ-Reasoning

    a≉0+b≉0⇒ab≉0 : ∀ {a b} → a ℤ.≉ 0ℤ → b ℤ.≉ 0ℤ → a ℤ.* b ℤ.≉ 0ℤ
    a≉0+b≉0⇒ab≉0 {a} {b} a≉0 b≉0 ab≈0 with ℤ.compare a 0ℤ | ℤ.compare b 0ℤ
    ... | tri< a<0 _ _ | tri< b<0 _ _ = ℤ.irrefl (ℤ.Eq.sym ab≈0) $ 0>a+0>b⇒0<ab a<0 b<0
    ... | tri< a<0 _ _ | tri≈ _ b≈0 _ = b≉0 b≈0
    ... | tri< a<0 _ _ | tri> _ _ b>0 = ℤ.irrefl ab≈0 $ 0>a+0<b⇒0>ab a<0 b>0
    ... | tri≈ _ a≈0 _ | _            = a≉0 a≈0
    ... | tri> _ _ a>0 | tri< b<0 _ _ = ℤ.irrefl ab≈0 $ 0<a+0>b⇒0>ab a>0 b<0
    ... | tri> _ _ a>0 | tri≈ _ b≈0 _ = b≉0 b≈0
    ... | tri> _ _ a>0 | tri> _ _ b>0 = ℤ.irrefl (ℤ.Eq.sym ab≈0) $ ℤ.0<a+0<b⇒0<ab a>0 b>0

    ab≈0⇒a≈0⊎b≈0 : ∀ {a b} → a ℤ.* b ℤ.≈ 0ℤ → a ℤ.≈ 0ℤ ⊎ b ℤ.≈ 0ℤ
    ab≈0⇒a≈0⊎b≈0 {a} {b} ab≈0 with a ℤ.≟ 0ℤ | b ℤ.≟ 0ℤ
    ... | yes a≈0 | _       = inj₁ a≈0
    ... | no a≉0  | yes b≈0 = inj₂ b≈0
    ... | no a≉0  | no b≉0  = ⊥-elim (a≉0+b≉0⇒ab≉0 a≉0 b≉0 ab≈0)

    2a<<n≈a<<1+n : ∀ a n → 2ℤ ℤ.* (a << n) ℤ.≈ a << suc n
    2a<<n≈a<<1+n a zero    = ℤ.*-congˡ $ ℤ.*-identityˡ a
    2a<<n≈a<<1+n a (suc n) = begin-equality
      2ℤ ℤ.* (a << suc n) ≈˘⟨ ℤ.*-assoc 2ℤ _ a ⟩
      (2ℤ ℤ.* _) ℤ.* a    ≈⟨  ℤ.*-congʳ $ ℤ.*-comm 2ℤ _ ⟩
      a << suc (suc n)    ∎
      where open ℤ-Reasoning

    0<1 : 0ℤ ℤ.< 1ℤ
    0<1 with ℤ.compare 0ℤ 1ℤ
    ... | tri< 0<1 _ _ = 0<1
    ... | tri≈ _ 0≈1 _ = ⊥-elim (1≉0 (ℤ.Eq.sym 0≈1))
    ... | tri> _ _ 0>1 = begin-strict
        0ℤ                  ≈˘⟨ ℤ.zeroʳ (ℤ.- 1ℤ) ⟩
        ℤ.- 1ℤ ℤ.* 0ℤ       <⟨  a<b⇒ca<cb (0>a⇒0<-a 0>1) (0>a⇒0<-a 0>1) ⟩
        ℤ.- 1ℤ ℤ.* ℤ.- 1ℤ   ≈⟨  -a*b≈-ab 1ℤ (ℤ.- 1ℤ) ⟩
        ℤ.- (1ℤ ℤ.* ℤ.- 1ℤ) ≈⟨  ℤ.-‿cong $ ℤ.*-identityˡ (ℤ.- 1ℤ) ⟩
        ℤ.- (ℤ.- 1ℤ)        ≈⟨  -‿idem 1ℤ ⟩
        1ℤ                  ∎
      where open ℤ-Reasoning

    0<2 : 0ℤ ℤ.< 2ℤ
    0<2 = begin-strict
      0ℤ        ≈˘⟨ ℤ.+-identity² ⟩
      0ℤ ℤ.+ 0ℤ <⟨  ℤ.+-invariantˡ 0ℤ 0<1 ⟩
      0ℤ ℤ.+ 1ℤ <⟨  ℤ.+-invariantʳ 1ℤ 0<1 ⟩
      2ℤ        ∎
      where open ℤ-Reasoning

    1<<n≉0 : ∀ n → 1ℤ << n ℤ.≉ 0ℤ
    1<<n≉0 zero          eq = 1≉0 1≈0
      where
      open ℤ-Reasoning
      1≈0 = begin-equality
        1ℤ        ≈˘⟨ ℤ.*-identity² ⟩
        1ℤ ℤ.* 1ℤ ≈⟨  eq ⟩
        0ℤ        ∎
    1<<n≉0 (suc zero)    eq = ℤ.irrefl 0≈2 0<2
      where
      open ℤ-Reasoning
      0≈2 = begin-equality
        0ℤ        ≈˘⟨ eq ⟩
        2ℤ ℤ.* 1ℤ ≈⟨  ℤ.*-identityʳ 2ℤ ⟩
        2ℤ        ∎
    1<<n≉0 (suc (suc n)) eq =
      [ (λ 2≈0 → ℤ.irrefl (ℤ.Eq.sym 2≈0) 0<2) , 1<<n≉0 (suc n) ]′
      $ ab≈0⇒a≈0⊎b≈0 $ ℤ.Eq.trans (2a<<n≈a<<1+n 1ℤ (suc n)) eq

    1<<n≉0ℝ : ∀ n → (1ℤ << n) /1 ℝ.≉ 0ℝ
    1<<n≉0ℝ n eq = 1<<n≉0 n $ (begin-equality
      1ℤ << n          ≈˘⟨ ⌊⌋∘/1≗id (1ℤ << n) ⟩
      ⌊ (1ℤ << n) /1 ⌋ ≈⟨  ⌊⌋.cong $ eq ⟩
      ⌊ 0ℝ ⌋           ≈⟨  ⌊⌋.0#-homo ⟩
      0ℤ               ∎)
      where open ℤ-Reasoning

    open RawPseudocode rawPseudocode using (module ShiftNotZero)

  open ShiftNotZero (λ n → fromWitnessFalse (1<<n≉0ℝ n)) public
