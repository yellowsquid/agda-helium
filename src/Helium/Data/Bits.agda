{-# OPTIONS --safe --without-K #-}

module Helium.Data.Bits where

open import Algebra
open import Algebra.Morphism.Definitions
open import Data.Fin as Fin hiding (_+_; _≟_)
import Data.Fin.Properties as Finₚ
open import Data.Nat as ℕ using (ℕ; suc; _+_)
import Data.Nat.Properties as ℕₚ
open import Function
open import Level using (_⊔_) renaming (suc to ℓsuc)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
  variable
    k l m n : ℕ


module _
  {a ℓ} {A : ℕ → Set a}
  (_≈_ : ∀ {m n} → REL (A m) (A n) ℓ)
  where

  private
    variable
      u v x y z : A n

    infix 4 _≗_

    _≗_ : ∀ {b} {B : Set b} → REL (B → A m) (B → A n) (b ⊔ ℓ)
    f ≗ g = ∀ {x} → f x ≈ g x

  record IsBits (_∨_ _∧_ : ∀ {n} → Op₂ (A n))
                (¬_ : ∀ {n} → Op₁ (A n))
                (0# 1# : ∀ {n} → A n)
                (_∶_ : ∀ {m n} → A m → A n → A (m + n))
                (slice : ∀ {n} (i : Fin (suc n)) j → A n → A (toℕ (i - j)))
                (update : ∀ {n} (i : Fin (suc n)) j → Op₁ (A (toℕ (i - j))) → Op₁ (A n))
                : Set (a ⊔ ℓ) where
    infix 4 _≟_
    field
      -- boolean algebraic properties
      isBooleanAlgebra : IsBooleanAlgebra (_≈_ {n}) _∨_ _∧_ ¬_ 0# 1#
      _≟_ : Decidable (_≈_ {m} {n})

      -- _∶_ properties
      ∶-cong      : x ≈ y → u ≈ v → (x ∶ u) ≈ (y ∶ v)
      ∶-assoc     : ((x ∶ y) ∶ z) ≈ (x ∶ (y ∶ z))
      ∶-identityˡ : ∀ {ε : A 0} → (ε ∶ x) ≈ x
      ∶-identityʳ : ∀ {ε : A 0} → (x ∶ ε) ≈ x
      ∶-swap-∨ : ((x ∨ y) ∶ (u ∨ v)) ≈ ((x ∶ u) ∨ (y ∶ v))
      ∶-swap-∧ : ((x ∧ y) ∶ (u ∧ v)) ≈ ((x ∶ u) ∧ (y ∶ v))
      ∶-homo-¬ : ((¬ x) ∶ (¬ y)) ≈ (¬ (x ∶ y))
      1#∶1# : (1# {m} ∶ 1# {n}) ≈ 1# {m + n}
      0#∶0# : (0# {m} ∶ 0# {n}) ≈ 0# {m + n}

      -- slice properties
      slice-cong : ∀ {i j} → x ≈ y → slice i j x ≈ slice i j y
      slice-fromℕ-zero : ∀ {x : A n} → slice (fromℕ n) zero x ≈ x
      slice-inject : ∀ {x : A m} {y : A n} {i i′ j j′} →
        .(i≡i′ : toℕ i P.≡ toℕ i′) .(j≡j′ : toℕ j P.≡ toℕ j′) →
        slice i′ j′ (x ∶ y) ≈ slice i j y
      slice-raise : ∀ {x : A m} {y : A n} {i i′ j j′} →
        .(n+i≡i′ : n + toℕ i P.≡ toℕ i′) .(n+j≡j′ : n + toℕ j P.≡ toℕ j′) →
        slice i′ j′ (x ∶ y) ≈ slice i j x

      -- update properties
      update-cong : ∀ {i j f} → (∀ {x y} → x ≈ y → f x ≈ f y) → x ≈ y → update i j f x ≈ update i j f y
      update² : ∀ {i j f g} → update i j f ∘ update {n} i j g ≗ update {n} i j (f ∘ g)
      slice-update : ∀ {i j f} → slice {n} i j ∘ update {n} i j f ≗ f ∘ slice i j

record RawBits a ℓ : Set (ℓsuc a ⊔ ℓsuc ℓ) where
  infix 8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infixr 5 _∶_
  infix 4 _≈_
  field
    BitVec : ℕ → Set a
    _≈_    : REL (BitVec m) (BitVec n) ℓ
    _∨_    : Op₂ (BitVec n)
    _∧_    : Op₂ (BitVec n)
    ¬_     : Op₁ (BitVec n)
    0#     : BitVec n
    1#     : BitVec n
    _∶_    : BitVec m → BitVec n → BitVec (m + n)
    slice  : ∀ (i : Fin (suc n)) j → BitVec n → BitVec (toℕ (i - j))
    update : ∀ (i : Fin (suc n)) j → Op₁ (BitVec (toℕ (i - j))) → Op₁ (BitVec n)

record Bits a ℓ : Set (ℓsuc a ⊔ ℓsuc ℓ) where
  infix 8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infixr 5 _∶_
  infix 4 _≈_
  field
    BitVec : ℕ → Set a
    _≈_    : REL (BitVec m) (BitVec n) ℓ
    _∨_    : Op₂ (BitVec n)
    _∧_    : Op₂ (BitVec n)
    ¬_     : Op₁ (BitVec n)
    0#     : BitVec n
    1#     : BitVec n
    _∶_    : BitVec m → BitVec n → BitVec (m + n)
    slice  : ∀ (i : Fin (suc n)) j → BitVec n → BitVec (toℕ (i - j))
    update : ∀ (i : Fin (suc n)) j → Op₁ (BitVec (toℕ (i - j))) → Op₁ (BitVec n)
    isBits : IsBits _≈_ _∨_ _∧_ ¬_ 0# 1# _∶_ slice update
