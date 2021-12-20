{-# OPTIONS --safe --without-K #-}

module Helium.Instructions where

open import Data.Bool
open import Data.Fin
open import Data.Nat
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

  split32 : ∃ λ (elements : Fin 5) → ∃ λ (esize : Fin 33) → toℕ elements * toℕ esize ≡ 32
  split32 = helper size
    where
    helper : _ → _
    helper zero             = # 4 , # 8 , refl
    helper (suc zero)       = # 2 , # 16 , refl
    helper (suc (suc zero)) = # 1 , # 32 , refl

  elements : Fin 5
  elements with (elmt , _ , _) ← split32 = elmt

  esize : Fin 33
  esize with (_ , esize , _) ← split32 = esize

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
