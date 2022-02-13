------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions of the data for a subset of Armv8-M instructions.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Instructions.Core where

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

data VecOpSize : Set where
  8bit  : VecOpSize
  16bit : VecOpSize
  32bit : VecOpSize

module Size (size : VecOpSize) where
  elements-1 : Fin 4
  elements-1 = helper size
    where
    helper : VecOpSize → Fin 4
    helper 8bit  = # 3
    helper 16bit = # 1
    helper 32bit = # 0

  elements : Fin 5
  elements = suc elements-1

  esize-1 : Fin 32
  esize-1 = helper size
    where
    helper : VecOpSize → Fin 32
    helper 8bit  = # 7
    helper 16bit = # 15
    helper 32bit = # 31

  esize : Fin 33
  esize = suc esize-1

record VecOp₂ : Set where
  field
    size : VecOpSize
    dest : VecReg
    src₁ : VecReg
    src₂ : GenReg ⊎ VecReg

  open Size size public

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

  open VecOp₂ op₂ public

record VRMulH : Set where
  field
    op₂ : VecOp₂
    unsigned : Bool

  open VecOp₂ op₂ public

VQDMulH = VecOp₂
VQRDMulH = VecOp₂

data Instruction : Set where
  vadd : VAdd → Instruction
  vsub : VSub → Instruction
  vmul : VMul → Instruction
  vmulh : VMulH → Instruction
  vqdmulh : VQDMulH → Instruction
