{-# OPTIONS --safe --without-K #-}

module Helium.Instructions where

open import Data.Bool
open import Data.Fin
open import Data.Nat
open import Data.Sum
open import Relation.Binary.PropositionalEquality

GenReg : Set
GenReg = Fin 16

VecReg : Set
VecReg = Fin 8

module VAdd
  where

  record VAdd : Set where
    field
      size : Fin 3
      dest : VecReg
      src₁ : VecReg
      src₂ : GenReg ⊎ VecReg

  esize : VAdd → Fin 33
  esize record { size = zero }             = # 8
  esize record { size = (suc zero) }       = # 16
  esize record { size = (suc (suc zero)) } = # 32

  elements : VAdd → Fin 5
  elements record { size = zero }             = # 4
  elements record { size = (suc zero) }       = # 2
  elements record { size = (suc (suc zero)) } = # 1

  elem*esize≡32 : ∀ d → toℕ (elements d) * toℕ (esize d) ≡ 32
  elem*esize≡32 record { size = zero }             = refl
  elem*esize≡32 record { size = (suc zero) }       = refl
  elem*esize≡32 record { size = (suc (suc zero)) } = refl

module VHSub
  where

  record VHSub : Set where
    field
      unsigned : Bool
      size : Fin 3
      dest : VecReg
      src₁ : VecReg
      src₂ : GenReg ⊎ VecReg

  esize : VHSub → Fin 33
  esize record { size = zero }             = # 8
  esize record { size = (suc zero) }       = # 16
  esize record { size = (suc (suc zero)) } = # 32

  elements : VHSub → Fin 5
  elements record { size = zero }             = # 4
  elements record { size = (suc zero) }       = # 2
  elements record { size = (suc (suc zero)) } = # 1

  elem*esize≡32 : ∀ d → toℕ (elements d) * toℕ (esize d) ≡ 32
  elem*esize≡32 record { size = zero }             = refl
  elem*esize≡32 record { size = (suc zero) }       = refl
  elem*esize≡32 record { size = (suc (suc zero)) } = refl

module VMul
  where

  record VMul : Set where
    field
      size : Fin 3
      dest : VecReg
      src₁ : VecReg
      src₂ : GenReg ⊎ VecReg

  esize : VMul → Fin 33
  esize record { size = zero }             = # 8
  esize record { size = (suc zero) }       = # 16
  esize record { size = (suc (suc zero)) } = # 32

  elements : VMul → Fin 5
  elements record { size = zero }             = # 4
  elements record { size = (suc zero) }       = # 2
  elements record { size = (suc (suc zero)) } = # 1

  elem*esize≡32 : ∀ d → toℕ (elements d) * toℕ (esize d) ≡ 32
  elem*esize≡32 record { size = zero }             = refl
  elem*esize≡32 record { size = (suc zero) }       = refl
  elem*esize≡32 record { size = (suc (suc zero)) } = refl
