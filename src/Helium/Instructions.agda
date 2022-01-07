------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions of a subset of Armv8-M instructions.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Instructions where

open import Data.Bool
open import Data.Fin
open import Data.Nat hiding (pred)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum
open import Relation.Binary.PropositionalEquality

GenReg : Set
GenReg = Fin 16

VecReg : Set
VecReg = Fin 8

record VecOp₂ : Set where
  field
    size : Fin 3
    dest : VecReg
    src₁ : VecReg
    src₂ : GenReg ⊎ VecReg

  private
    split32 : ∃ λ (elements : Fin 5) → ∃ λ (esize>>3-1 : Fin 4) → ∃ λ (esize-1 : Fin 32) → (8 * toℕ (suc esize>>3-1) ≡ toℕ (suc esize-1)) × (toℕ elements * toℕ (suc esize-1) ≡ 32) × (toℕ elements * toℕ (suc esize>>3-1) ≡ 4)
    split32 = helper size
      where
      helper : _ → _
      helper zero             = # 4 , # 0 , # 7 , refl , refl , refl
      helper (suc zero)       = # 2 , # 1 , # 15 , refl , refl , refl
      helper (suc (suc zero)) = # 1 , # 3 , # 31 , refl , refl , refl

  elements : Fin 5
  elements with (elmt , _ ) ← split32 = elmt

  esize>>3-1 : Fin 4
  esize>>3-1 with (_ , esize>>3-1 , _) ← split32 = esize>>3-1

  esize>>3 : Fin 5
  esize>>3 = suc esize>>3-1

  esize-1 : Fin 32
  esize-1 with (_ , _ , esize-1 , _) ← split32 = esize-1

  esize : Fin 33
  esize = suc esize-1

  8*e>>3≡e : 8 * toℕ esize>>3 ≡ toℕ esize
  8*e>>3≡e with (_ , _ , _ , eq , _) ← split32 = eq

  e*e≡32 : toℕ elements * toℕ esize ≡ 32
  e*e≡32 with (_ , _ , _ , _ , eq , _) ← split32 = eq

  e*e>>3≡4 : toℕ elements * toℕ esize>>3 ≡ 4
  e*e>>3≡4 with (_ , _ , _ , _ , _ , eq) ← split32 = eq

VAdd = VecOp₂

VSub = VecOp₂

record VHSub : Set where
  field
    op₂ : VecOp₂
    unsigned : Bool

  open VecOp₂ op₂ public

VMul = VecOp₂

record VMulH : Set where
  field
    op₂ : VecOp₂
    unsigned : Bool
    rounding : Bool

  open VecOp₂ op₂ public

record VQDMulH : Set where
  field
    op₂ : VecOp₂
    rounding : Bool

  open VecOp₂ op₂ public

data Instruction : Set where
  vadd : VAdd → Instruction
  vsub : VSub → Instruction
  vmul : VMul → Instruction
  vmulh : VMulH → Instruction
  vqdmulh : VQDMulH → Instruction
