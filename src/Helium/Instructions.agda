{-# OPTIONS --safe --without-K #-}

module Helium.Instructions where

open import Data.Bool
open import Data.Fin
open import Data.Nat hiding (pred)
open import Data.Product using (∃; _,_)
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
    split32 : ∃ λ (elements : Fin 5) → ∃ λ (esize-1 : Fin 32) → toℕ elements * toℕ (suc esize-1) ≡ 32
    split32 = helper size
      where
      helper : _ → _
      helper zero             = # 4 , # 7 , refl
      helper (suc zero)       = # 2 , # 15 , refl
      helper (suc (suc zero)) = # 1 , # 31 , refl

  elements : Fin 5
  elements with (elmt , _ , _) ← split32 = elmt

  esize-1 : Fin 32
  esize-1 with (_ , esize-1 , _) ← split32 = esize-1

  esize : Fin 33
  esize = suc esize-1

  e*e≡32 : toℕ elements * toℕ esize ≡ 32
  e*e≡32 with (_ , _ , eq) ← split32 = eq

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
