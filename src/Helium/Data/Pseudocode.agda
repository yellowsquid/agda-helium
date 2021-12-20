{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode where

open import Algebra.Core
open import Data.Bool using (if_then_else_)
open import Data.Fin hiding (_+_; cast)
import Data.Fin.Properties as Finₚ
open import Data.Nat using (ℕ; zero; suc; _+_; _^_)
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary using (REL; Rel; Symmetric; Transitive; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; does)
open import Relation.Nullary.Decidable

private
  map-False : ∀ {p q} {P : Set p} {Q : Set q} {P? : Dec P} {Q? : Dec Q} → (P → Q) → False Q? → False P?
  map-False ⇒ f = fromWitnessFalse (λ x → toWitnessFalse f (⇒ x))

record RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃ : Set (ℓsuc (b₁ ⊔ b₂ ⊔ i₁ ⊔ i₂ ⊔ i₃ ⊔ r₁ ⊔ r₂ ⊔ r₃)) where
  infix 9 _^ᶻ_ _^ʳ_
  infix 8 _⁻¹
  infix 7 _*ᶻ_ _*ʳ_
  infix 6 -ᶻ_ -ʳ_
  infix 5 _+ᶻ_ _+ʳ_
  infix 4 _≈ᵇ_ _≟ᵇ_ _≈ᶻ_ _≟ᶻ_ _<ᶻ_ _<?ᶻ_ _≈ʳ_ _≟ʳ_ _<ʳ_ _<?ʳ_

  field
    -- Types
    Bits : ℕ → Set b₁
    ℤ    : Set i₁
    ℝ    : Set r₁

  field
    -- Relations
    _≈ᵇ_ : ∀ {m n} → REL (Bits m) (Bits n) b₂
    _≟ᵇ_ : ∀ {m n} → Decidable (_≈ᵇ_ {m} {n})
    _≈ᶻ_ : Rel ℤ i₂
    _≟ᶻ_ : Decidable _≈ᶻ_
    _<ᶻ_ : Rel ℤ i₃
    _<?ᶻ_ : Decidable _<ᶻ_
    _≈ʳ_ : Rel ℝ r₂
    _≟ʳ_ : Decidable _≈ʳ_
    _<ʳ_ : Rel ℝ r₃
    _<?ʳ_ : Decidable _<ʳ_

    -- Constants
    [] : Bits 0
    0b : Bits 1
    1b : Bits 1
    0ℤ : ℤ
    1ℤ : ℤ
    0ℝ : ℝ
    1ℝ : ℝ

  field
    -- Bitstring operations
    ofFin : ∀ {n} → Fin (2 ^ n) → Bits n
    cast  : ∀ {m n} → .(eq : m ≡ n) → Bits m → Bits n
    not   : ∀ {n} → Op₁ (Bits n)
    _and_ : ∀ {n} → Op₂ (Bits n)
    _or_  : ∀ {n} → Op₂ (Bits n)
    _∶_ : ∀ {m n} → Bits m → Bits n → Bits (m + n)
    sliceᵇ  : ∀ {n} (i : Fin (suc n)) j → Bits n → Bits (toℕ (i - j))
    updateᵇ : ∀ {n} (i : Fin (suc n)) j → Bits (toℕ (i - j)) → Op₁ (Bits n)
    signed : ∀ {n} → Bits n → ℤ
    unsigned : ∀ {n} → Bits n → ℤ

  field
    -- Arithmetic operations
    ⟦_⟧ : ℤ → ℝ
    round : ℝ → ℤ
    _+ᶻ_ : Op₂ ℤ
    _+ʳ_ : Op₂ ℝ
    _*ᶻ_ : Op₂ ℤ
    _*ʳ_ : Op₂ ℝ
    -ᶻ_  : Op₁ ℤ
    -ʳ_  : Op₁ ℝ
    _⁻¹  : ∀ (y : ℝ) → .{False (y ≟ʳ 0ℝ)} → ℝ

  -- Convenience operations
  module divmod
    (≈ᶻ-trans : Transitive _≈ᶻ_)
    (round∘⟦⟧ : ∀ x → x ≈ᶻ round ⟦ x ⟧)
    (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
    (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
    where

    infix 7 _div_ _mod_

    _div_ : ∀ (x y : ℤ) → .{≢0 : False (y ≟ᶻ 0ℤ)} → ℤ
    (x div y) {≢0} =
      let f = (λ y≈0 → ≈ᶻ-trans (round∘⟦⟧ y) (≈ᶻ-trans (round-cong y≈0) 0#-homo-round)) in
      round (⟦ x ⟧ *ʳ (⟦ y ⟧ ⁻¹) {map-False f ≢0})

    _mod_ : ∀ (x y : ℤ) → .{≢0 : False (y ≟ᶻ 0ℤ)} → ℤ
    (x mod y) {≢0} = x +ᶻ -ᶻ y *ᶻ (x div y) {≢0}

  _^ᶻ_ : ℤ → ℕ → ℤ
  x ^ᶻ zero  = 1ℤ
  x ^ᶻ suc y = x *ᶻ x ^ᶻ y

  _^ʳ_ : ℝ → ℕ → ℝ
  x ^ʳ zero  = 1ℝ
  x ^ʳ suc y = x *ʳ x ^ʳ y

  -- Stray constant cannot live with the others, because + is not yet defined.
  2ℤ : ℤ
  2ℤ = 1ℤ +ᶻ 1ℤ

  _<<_ : ℤ → ℕ → ℤ
  x << n = x *ᶻ 2ℤ ^ᶻ n

  module 2^n≢0
    (≈ᶻ-trans : Transitive _≈ᶻ_)
    (round∘⟦⟧ : ∀ x → x ≈ᶻ round ⟦ x ⟧)
    (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
    (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
    (2^n≢0 : ∀ n → False (2ℤ ^ᶻ n ≟ᶻ 0ℤ))
    where

    open divmod ≈ᶻ-trans round∘⟦⟧ round-cong 0#-homo-round

    _>>_ : ℤ → ℕ → ℤ
    x >> n = (x div (2ℤ ^ᶻ n)) {2^n≢0 n}

    getᶻ : ℕ → ℤ → Bits 1
    getᶻ i x = if (does ((x mod (2ℤ ^ᶻ suc i)) {2^n≢0 (suc i)} <?ᶻ 2ℤ ^ᶻ i)) then 0b else 1b

  module sliceᶻ
    (≈ᶻ-trans : Transitive _≈ᶻ_)
    (round∘⟦⟧ : ∀ x → x ≈ᶻ round ⟦ x ⟧)
    (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
    (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
    (2^n≢0 : ∀ n → False (2ℤ ^ᶻ n ≟ᶻ 0ℤ))
    (*ᶻ-identityʳ : ∀ x → x *ᶻ 1ℤ ≈ᶻ x)
    where

    infix 5 _+ᵇ_

    open divmod ≈ᶻ-trans round∘⟦⟧ round-cong 0#-homo-round
    open 2^n≢0 ≈ᶻ-trans round∘⟦⟧ round-cong 0#-homo-round 2^n≢0

    sliceᶻ : ∀ n i → ℤ → Bits (n ℕ-ℕ i)
    sliceᶻ zero    zero    z = []
    sliceᶻ (suc n) zero    z = getᶻ n z ∶ sliceᶻ n zero z
    sliceᶻ (suc n) (suc i) z = sliceᶻ n i ((z div 2ℤ) {2≢0})
      where
      2≢0 = map-False (≈ᶻ-trans (*ᶻ-identityʳ 2ℤ)) (2^n≢0 1)

    _+ᵇ_ : ∀ {n} → Op₂ (Bits n)
    x +ᵇ y = sliceᶻ _ zero (unsigned x +ᶻ unsigned y)

  _eor_ : ∀ {n} → Op₂ (Bits n)
  x eor y = (x or y) and not (x and y)

  getᵇ : ∀ {n} → Fin n → Bits n → Bits 1
  getᵇ i x = cast (eq i) (sliceᵇ (suc i) (inject₁ (strengthen i)) x)
    where
    eq : ∀ {n} (i : Fin n) → toℕ (suc i - inject₁ (strengthen i)) ≡ 1
    eq zero    = refl
    eq (suc i) = eq i

  setᵇ : ∀ {n} → Fin n → Bits 1 → Op₁ (Bits n)
  setᵇ i y = updateᵇ (suc i) (inject₁ (strengthen i)) (cast (sym (eq i)) y)
    where
    eq : ∀ {n} (i : Fin n) → toℕ (suc i - inject₁ (strengthen i)) ≡ 1
    eq zero    = refl
    eq (suc i) = eq i

  -- Conveniences

  zeros : ∀ {n} → Bits n
  zeros {zero}  = []
  zeros {suc n} = 0b ∶ zeros
