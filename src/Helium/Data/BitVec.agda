{-# OPTIONS --safe --without-K #-}

module Helium.Data.BitVec where

open import Algebra.Core
open import Data.Bool as B using () renaming (Bool to Bit; false to 0#; true to 1#)
open import Data.Fin hiding (_+_; _-_)
open import Data.Fin.Properties using (toℕ-fromℕ)
open import Data.Nat as N hiding (_+_)
open import Data.Product
open import Data.Vec hiding (map; replicate)
open import Relation.Binary.PropositionalEquality using (cong)

private
  variable
    l m n : ℕ

infixr 6 _∧_ _+_ _-_
infixr 5 _∨_ _xor_


-- Type

BitVec : ℕ → Set
BitVec = Vec Bit


-- Constants

replicate : Bit → BitVec n
replicate {zero}  b = []
replicate {suc n} b = b ∷ replicate b

zeroes : BitVec n
zeroes = replicate 0#

ones : BitVec n
ones = replicate 1#

one : BitVec (suc n)
one {zero}  = 1# ∷ []
one {suc n} = 0# ∷ one


-- Bitwise operations

bitwise : Op₁ Bit → Op₁ (BitVec n)
bitwise f [] = []
bitwise f (x ∷ xs) = f x ∷ bitwise f xs

bitwise₂ : Op₂ Bit → Op₂ (BitVec n)
bitwise₂ _∙_ []       []       = []
bitwise₂ _∙_ (x ∷ xs) (y ∷ ys) = x ∙ y ∷ bitwise₂ _∙_ xs ys

not : BitVec n → BitVec n
not = bitwise B.not

_∧_ : BitVec n → BitVec n → BitVec n
_∧_ = bitwise₂ B._∧_

_∨_ : BitVec n → BitVec n → BitVec n
_∨_ = bitwise₂ B._∨_

_xor_ : BitVec n → BitVec n → BitVec n
_xor_ = bitwise₂ B._xor_


-- Arithmetic operations

add-carry : Bit → BitVec n → BitVec n → Bit
add-carry c  []       []      = c
add-carry c (x ∷ xs) (y ∷ ys) = add-carry c xs ys B.∧ (x B.xor y) B.xor (x B.∧ y)

add-rem : Bit → BitVec n → BitVec n → BitVec n
add-rem c []       []       = []
add-rem c (x ∷ xs) (y ∷ ys) = (add-carry c xs ys B.xor x B.xor y) ∷ add-rem c xs ys

add : Bit → BitVec n → BitVec n → BitVec (suc n)
add c xs ys = add-carry c xs ys ∷ add-rem c xs ys

_+_ : BitVec n → BitVec n → BitVec n
xs + ys = add-rem 0# xs ys

_-_ : BitVec n → BitVec n → BitVec n
xs - ys = add-rem 1# xs (not ys)


-- Conversions

bitToFin : Bit → Fin 2
bitToFin 0# = zero
bitToFin 1# = suc zero

finToBit : Fin 2 → Bit
finToBit zero       = 0#
finToBit (suc zero) = 1#

toFin : BitVec n → Fin (2 ^ n)
toFin         []       = zero
toFin         (b ∷ bs) = combine (bitToFin b) (toFin bs)

fromFin : Fin (2 ^ n) → BitVec n
fromFin {zero}  x = []
fromFin {suc n} x = uncurry (_∷_) (map finToBit fromFin (remQuot (2 ^ n) x))
