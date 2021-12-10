{-# OPTIONS --safe --without-K #-}

module Helium.Data.BitVec.Properties where

import Algebra.Definitions as Algebra
open import Data.Bool as B using () renaming (Bool to Bit; false to 0#; true to 1#)
open import Data.Empty
open import Data.Fin as F hiding (_+_; _<_; _≥_)
open import Data.Fin.Properties as FP
import Data.Bool.Properties as B
open import Data.Nat as N hiding (_+_; _*_)
import Data.Nat.Properties as NP
open import Data.Product
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Properties using (∷-injective; ∷-injectiveʳ)
open import Function
open import Helium.Data.BitVec
open import Relation.Binary.PropositionalEquality as ≡

private
  variable
    l m n : ℕ

module A n = Algebra (_≡_ {A = BitVec n})
  renaming ( _DistributesOverʳ_ to ₍_₎_DistributesOverʳ_
           ; _DistributesOverˡ_ to ₍_₎_DistributesOverˡ_
           ; _DistributesOver_ to ₍_₎_DistributesOver_
           ; _IdempotentOn_ to ₍_₎_IdempotentOn_
           ; _Absorbs_ to ₍_₎_Absorbs_
           )


--- Bitwise operations

-- bitwise

bitwise-injective : ∀ f → Injective _≡_ _≡_ f → Injective _≡_ _≡_ (bitwise {n} f)
bitwise-injective f inj {[]}     {[]}     eq = refl
bitwise-injective f inj {x ∷ xs} {y ∷ ys} eq = uncurry (cong₂ _∷_) (dmap inj (bitwise-injective f inj) (∷-injective eq))

bitwise-idem : ∀ f → Algebra.IdempotentFun _≡_ f → A.IdempotentFun n (bitwise f)
bitwise-idem f idem []       = refl
bitwise-idem f idem (x ∷ xs) = cong₂ _∷_ (idem x) (bitwise-idem f idem xs)

bitwise-involutive : ∀ f → Algebra.Involutive _≡_ f → A.Involutive n (bitwise f)
bitwise-involutive f inv []       = refl
bitwise-involutive f inv (x ∷ xs) = cong₂ _∷_ (inv x) (bitwise-involutive f inv xs)

-- bitwise₂

bitwise₂-assoc : ∀ ∙ → Algebra.Associative _≡_ ∙ → A.Associative n (bitwise₂ ∙)
bitwise₂-assoc ∙ assoc [] [] [] = refl
bitwise₂-assoc ∙ assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (assoc x y z) (bitwise₂-assoc ∙ assoc xs ys zs)

bitwise₂-comm : ∀ ∙ → Algebra.Commutative _≡_ ∙ → A.Commutative n (bitwise₂ ∙)
bitwise₂-comm ∙ comm [] [] = refl
bitwise₂-comm ∙ comm (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (comm x y) (bitwise₂-comm ∙ comm xs ys)

bitwise₂-identityˡ : ∀ b ∙ → Algebra.LeftIdentity _≡_ b ∙ → A.LeftIdentity n (replicate b) (bitwise₂ ∙)
bitwise₂-identityˡ b ∙ id [] = refl
bitwise₂-identityˡ b ∙ id (x ∷ xs) = cong₂ _∷_ (id x) (bitwise₂-identityˡ b ∙ id xs)

bitwise₂-identityʳ : ∀ b ∙ → Algebra.RightIdentity _≡_ b ∙ → A.RightIdentity n (replicate b) (bitwise₂ ∙)
bitwise₂-identityʳ b ∙ id [] = refl
bitwise₂-identityʳ b ∙ id (x ∷ xs) = cong₂ _∷_ (id x) (bitwise₂-identityʳ b ∙ id xs)

bitwise₂-identity : ∀ b ∙ → Algebra.Identity _≡_ b ∙ → A.Identity n (replicate b) (bitwise₂ ∙)
bitwise₂-identity b ∙ = dmap (bitwise₂-identityˡ b ∙) (bitwise₂-identityʳ b ∙)

bitwise₂-zeroˡ : ∀ b ∙ → Algebra.LeftZero _≡_ b ∙ → A.LeftZero n (replicate b) (bitwise₂ ∙)
bitwise₂-zeroˡ b ∙ z [] = refl
bitwise₂-zeroˡ b ∙ z (x ∷ xs) = cong₂ _∷_ (z x) (bitwise₂-zeroˡ b ∙ z xs)

bitwise₂-zeroʳ : ∀ b ∙ → Algebra.RightZero _≡_ b ∙ → A.RightZero n (replicate b) (bitwise₂ ∙)
bitwise₂-zeroʳ b ∙ z [] = refl
bitwise₂-zeroʳ b ∙ z (x ∷ xs) = cong₂ _∷_ (z x) (bitwise₂-zeroʳ b ∙ z xs)

bitwise₂-zero : ∀ b ∙ → Algebra.Zero _≡_ b ∙ → A.Zero n (replicate b) (bitwise₂ ∙)
bitwise₂-zero b ∙ = dmap (bitwise₂-zeroˡ b ∙) (bitwise₂-zeroʳ b ∙)

bitwise₂-inverseˡ : ∀ b f ∙ → Algebra.LeftInverse _≡_ b f ∙ → A.LeftInverse n (replicate b) (bitwise f) (bitwise₂ ∙)
bitwise₂-inverseˡ b f ∙ id [] = refl
bitwise₂-inverseˡ b f ∙ id (x ∷ xs) = cong₂ _∷_ (id x) (bitwise₂-inverseˡ b f ∙ id xs)

bitwise₂-inverseʳ : ∀ b f ∙ → Algebra.RightInverse _≡_ b f ∙ → A.RightInverse n (replicate b) (bitwise f) (bitwise₂ ∙)
bitwise₂-inverseʳ b f ∙ id [] = refl
bitwise₂-inverseʳ b f ∙ id (x ∷ xs) = cong₂ _∷_ (id x) (bitwise₂-inverseʳ b f ∙ id xs)

bitwise₂-inverse : ∀ b f ∙ → Algebra.Inverse _≡_ b f ∙ → A.Inverse n (replicate b) (bitwise f) (bitwise₂ ∙)
bitwise₂-inverse b f ∙ = dmap (bitwise₂-inverseˡ b f ∙) (bitwise₂-inverseʳ b f ∙)

bitwise₂-conicalˡ : ∀ b ∙ → Algebra.LeftConical _≡_ b ∙ → A.LeftConical n (replicate b) (bitwise₂ ∙)
bitwise₂-conicalˡ b ∙ conical [] [] eq = refl
bitwise₂-conicalˡ b ∙ conical (x ∷ xs) (y ∷ ys) eq = uncurry (cong₂ _∷_) (dmap (conical x y) (bitwise₂-conicalˡ b ∙ conical xs ys) (∷-injective eq))

bitwise₂-conicalʳ : ∀ b ∙ → Algebra.RightConical _≡_ b ∙ → A.RightConical n (replicate b) (bitwise₂ ∙)
bitwise₂-conicalʳ b ∙ conical [] [] eq = refl
bitwise₂-conicalʳ b ∙ conical (x ∷ xs) (y ∷ ys) eq = uncurry (cong₂ _∷_) (dmap (conical x y) (bitwise₂-conicalʳ b ∙ conical xs ys) (∷-injective eq))

bitwise₂-conical : ∀ b ∙ → Algebra.Conical _≡_ b ∙ → A.Conical n (replicate b) (bitwise₂ ∙)
bitwise₂-conical b ∙ = dmap (bitwise₂-conicalˡ b ∙) (bitwise₂-conicalʳ b ∙)

bitwise₂-distribˡ : ∀ * ∙ → Algebra._DistributesOverˡ_ _≡_ * ∙ → A.₍ n ₎ (bitwise₂ *) DistributesOverˡ (bitwise₂ ∙)
bitwise₂-distribˡ * ∙ distrib [] [] [] = refl
bitwise₂-distribˡ * ∙ distrib (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (distrib x y z) (bitwise₂-distribˡ * ∙ distrib xs ys zs)

bitwise₂-distribʳ : ∀ * ∙ → Algebra._DistributesOverʳ_ _≡_ * ∙ → A.₍ n ₎ (bitwise₂ *) DistributesOverʳ (bitwise₂ ∙)
bitwise₂-distribʳ * ∙ distrib [] [] [] = refl
bitwise₂-distribʳ * ∙ distrib (x ∷ xs) (y ∷ ys) (z ∷ zs) = cong₂ _∷_ (distrib x y z) (bitwise₂-distribʳ * ∙ distrib xs ys zs)

bitwise₂-distrib : ∀ * ∙ → Algebra._DistributesOver_ _≡_ * ∙ → A.₍ n ₎ (bitwise₂ *) DistributesOver (bitwise₂ ∙)
bitwise₂-distrib * ∙ = dmap (bitwise₂-distribˡ * ∙) (bitwise₂-distribʳ * ∙)

bitwise₂-idemOn : ∀ ∙ b → Algebra._IdempotentOn_ _≡_ ∙ b → A.₍ n ₎ (bitwise₂ ∙) IdempotentOn (replicate b)
bitwise₂-idemOn {zero}  ∙ b idem = refl
bitwise₂-idemOn {suc n} ∙ b idem = cong₂ _∷_ idem (bitwise₂-idemOn ∙ b idem)

bitwise₂-idem : ∀ ∙ → Algebra.Idempotent _≡_ ∙ → A.Idempotent n (bitwise₂ ∙)
bitwise₂-idem ∙ idem [] = refl
bitwise₂-idem ∙ idem (x ∷ xs) = cong₂ _∷_ (idem x) (bitwise₂-idem ∙ idem xs)

bitwise₂-absorbs : ∀ * ∙ → Algebra._Absorbs_ _≡_ * ∙ → A.₍ n ₎ (bitwise₂ *) Absorbs (bitwise₂ ∙)
bitwise₂-absorbs * ∙ absorbs [] [] = refl
bitwise₂-absorbs * ∙ absorbs (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (absorbs x y) (bitwise₂-absorbs * ∙ absorbs xs ys)

bitwise₂-absorptive : ∀ * ∙ → Algebra.Absorptive _≡_ * ∙ → A.Absorptive n (bitwise₂ *) (bitwise₂ ∙)
bitwise₂-absorptive * ∙ = dmap (bitwise₂-absorbs * ∙) (bitwise₂-absorbs ∙ *)

bitwise₂-cancelˡ : ∀ ∙ → Algebra.LeftCancellative _≡_ ∙ → A.LeftCancellative n (bitwise₂ ∙)
bitwise₂-cancelˡ ∙ cancel [] {[]} {[]} eq = refl
bitwise₂-cancelˡ ∙ cancel (x ∷ xs) {y ∷ ys} {z ∷ zs} eq = uncurry (cong₂ _∷_) (dmap (cancel x) (bitwise₂-cancelˡ ∙ cancel xs) (∷-injective eq))

bitwise₂-cancelʳ : ∀ ∙ → Algebra.RightCancellative _≡_ ∙ → A.RightCancellative n (bitwise₂ ∙)
bitwise₂-cancelʳ ∙ cancel [] [] eq = refl
bitwise₂-cancelʳ ∙ cancel {x ∷ xs} (y ∷ ys) (z ∷ zs) eq = uncurry (cong₂ _∷_) (dmap (cancel y z) (bitwise₂-cancelʳ ∙ cancel ys zs) (∷-injective eq))

bitwise₂-cancel : ∀ ∙ → Algebra.Cancellative _≡_ ∙ → A.Cancellative n (bitwise₂ ∙)
bitwise₂-cancel ∙ = dmap (bitwise₂-cancelˡ ∙) (bitwise₂-cancelʳ ∙)

bitwise₂-interchangable : ∀ * ∙ → Algebra.Interchangable _≡_ * ∙ → A.Interchangable n (bitwise₂ *) (bitwise₂ ∙)
bitwise₂-interchangable * ∙ inter [] [] [] [] = refl
bitwise₂-interchangable * ∙ inter (x ∷ xs) (y ∷ ys) (z ∷ zs) (w ∷ ws) = cong₂ _∷_ (inter x y z w) (bitwise₂-interchangable * ∙ inter xs ys zs ws)

-- not

not-involutive : A.Involutive n not
not-involutive = bitwise-involutive B.not B.not-involutive

not-injective : Injective _≡_ _≡_ (not {n})
not-injective = bitwise-injective B.not B.not-injective

not-0 : not {n} zeroes ≡ ones
not-0 {zero}  = refl
not-0 {suc n} = cong (1# ∷_) not-0

not-1 : not {n} ones ≡ zeroes
not-1 {zero}  = refl
not-1 {suc n} = cong (0# ∷_) not-1

-- ∧

∧-assoc : A.Associative n _∧_
∧-assoc = bitwise₂-assoc B._∧_ B.∧-assoc

∧-comm : A.Commutative n _∧_
∧-comm = bitwise₂-comm B._∧_ B.∧-comm

∧-identityˡ : A.LeftIdentity n ones _∧_
∧-identityˡ = bitwise₂-identityˡ 1# B._∧_ B.∧-identityˡ

∧-identityʳ : A.RightIdentity n ones _∧_
∧-identityʳ = bitwise₂-identityʳ 1# B._∧_ B.∧-identityʳ

∧-identity : A.Identity n ones _∧_
∧-identity = ∧-identityˡ , ∧-identityʳ

∧-zeroˡ : A.LeftZero n zeroes _∧_
∧-zeroˡ = bitwise₂-zeroˡ 0# B._∧_ B.∧-zeroˡ

∧-zeroʳ : A.RightZero n zeroes _∧_
∧-zeroʳ = bitwise₂-zeroʳ 0# B._∧_ B.∧-zeroʳ

∧-zero : A.Zero n zeroes _∧_
∧-zero = ∧-zeroˡ , ∧-zeroʳ

∧-inverseˡ : A.LeftInverse n zeroes not _∧_
∧-inverseˡ = bitwise₂-inverseˡ 0# B.not B._∧_ B.∧-inverseˡ

∧-inverseʳ : A.RightInverse n zeroes not _∧_
∧-inverseʳ = bitwise₂-inverseʳ 0# B.not B._∧_ B.∧-inverseʳ

∧-inverse : A.Inverse n zeroes not _∧_
∧-inverse = ∧-inverseˡ , ∧-inverseʳ

∧-conicalˡ : A.LeftConical n ones _∧_
∧-conicalˡ = bitwise₂-conicalˡ 1# B._∧_ λ { 1# 1# eq → refl }

∧-conicalʳ : A.RightConical n ones _∧_
∧-conicalʳ = bitwise₂-conicalʳ 1# B._∧_ λ { 1# 1# eq → refl }

∧-conical : A.Conical n ones _∧_
∧-conical = ∧-conicalˡ , ∧-conicalʳ

∧-idem : A.Idempotent n _∧_
∧-idem = bitwise₂-idem B._∧_ B.∧-idem

-- ∨

∨-assoc : A.Associative n _∨_
∨-assoc = bitwise₂-assoc B._∨_ B.∨-assoc

∨-comm : A.Commutative n _∨_
∨-comm = bitwise₂-comm B._∨_ B.∨-comm

∨-identityˡ : A.LeftIdentity n zeroes _∨_
∨-identityˡ = bitwise₂-identityˡ 0# B._∨_ B.∨-identityˡ

∨-identityʳ : A.RightIdentity n zeroes _∨_
∨-identityʳ = bitwise₂-identityʳ 0# B._∨_ B.∨-identityʳ

∨-identity : A.Identity n zeroes _∨_
∨-identity = ∨-identityˡ , ∨-identityʳ

∨-zeroˡ : A.LeftZero n ones _∨_
∨-zeroˡ = bitwise₂-zeroˡ 1# B._∨_ B.∨-zeroˡ

∨-zeroʳ : A.RightZero n ones _∨_
∨-zeroʳ = bitwise₂-zeroʳ 1# B._∨_ B.∨-zeroʳ

∨-zero : A.Zero n ones _∨_
∨-zero = ∨-zeroˡ , ∨-zeroʳ

∨-inverseˡ : A.LeftInverse n ones not _∨_
∨-inverseˡ = bitwise₂-inverseˡ 1# B.not B._∨_ B.∨-inverseˡ

∨-inverseʳ : A.RightInverse n ones not _∨_
∨-inverseʳ = bitwise₂-inverseʳ 1# B.not B._∨_ B.∨-inverseʳ

∨-inverse : A.Inverse n ones not _∨_
∨-inverse = ∨-inverseˡ , ∨-inverseʳ

∨-conicalˡ : A.LeftConical n zeroes _∨_
∨-conicalˡ = bitwise₂-conicalˡ 0# B._∨_ λ { 0# 0# eq → refl }

∨-conicalʳ : A.RightConical n zeroes _∨_
∨-conicalʳ = bitwise₂-conicalʳ 0# B._∨_ λ { 0# 0# eq → refl }

∨-conical : A.Conical n zeroes _∨_
∨-conical = ∨-conicalˡ , ∨-conicalʳ

∨-idem : A.Idempotent n _∨_
∨-idem = bitwise₂-idem B._∨_ B.∨-idem

-- ∧ and ∨

∧-distribˡ-∨ : A.₍ n ₎ _∧_ DistributesOverˡ _∨_
∧-distribˡ-∨ = bitwise₂-distribˡ B._∧_ B._∨_ B.∧-distribˡ-∨

∧-distribʳ-∨ : A.₍ n ₎ _∧_ DistributesOverʳ _∨_
∧-distribʳ-∨ = bitwise₂-distribʳ B._∧_ B._∨_ B.∧-distribʳ-∨

∧-distrib-∨ : A.₍ n ₎ _∧_ DistributesOver _∨_
∧-distrib-∨ = ∧-distribˡ-∨ , ∧-distribʳ-∨

∨-distribˡ-∧ : A.₍ n ₎ _∨_ DistributesOverˡ _∧_
∨-distribˡ-∧ = bitwise₂-distribˡ B._∨_ B._∧_ B.∨-distribˡ-∧

∨-distribʳ-∧ : A.₍ n ₎ _∨_ DistributesOverʳ _∧_
∨-distribʳ-∧ = bitwise₂-distribʳ B._∨_ B._∧_ B.∨-distribʳ-∧

∨-distrib-∧ : A.₍ n ₎ _∨_ DistributesOver _∧_
∨-distrib-∧ = ∨-distribˡ-∧ , ∨-distribʳ-∧

∧-abs-∨ : A.₍ n ₎ _∧_ Absorbs _∨_
∧-abs-∨ = bitwise₂-absorbs B._∧_ B._∨_ B.∧-abs-∨

∨-abs-∧ : A.₍ n ₎ _∨_ Absorbs _∧_
∨-abs-∧ = bitwise₂-absorbs B._∨_ B._∧_ B.∨-abs-∧

∧-∨-absorptive : A.Absorptive n _∧_ _∨_
∧-∨-absorptive = ∧-abs-∨ , ∨-abs-∧

-- xor

private
  bxor-comm : ∀ x y → x B.xor y ≡ y B.xor x
  bxor-comm 0# 0# = refl
  bxor-comm 0# 1# = refl
  bxor-comm 1# 0# = refl
  bxor-comm 1# 1# = refl

  bxor-identityʳ : ∀ x → x B.xor 0# ≡ x
  bxor-identityʳ 0# = refl
  bxor-identityʳ 1# = refl

  bxor-annihilate : ∀ x → x B.xor x ≡ 0#
  bxor-annihilate 0# = refl
  bxor-annihilate 1# = refl

  bxor-distribˡ-not : ∀ x y → B.not (x B.xor y) ≡ B.not x B.xor y
  bxor-distribˡ-not 0# y = refl
  bxor-distribˡ-not 1# y = B.not-involutive y

  bxor-distribʳ-not : ∀ x y → B.not (x B.xor y) ≡ x B.xor B.not y
  bxor-distribʳ-not 0# y = refl
  bxor-distribʳ-not 1# y = refl

xor-assoc : A.Associative n _xor_
xor-assoc = bitwise₂-assoc B._xor_ (λ
  { 0# y z → refl
  ; 1# y z → sym (bxor-distribˡ-not y z)
  })

xor-comm : A.Commutative n _xor_
xor-comm = bitwise₂-comm B._xor_ bxor-comm

xor-identityˡ : A.LeftIdentity n zeroes _xor_
xor-identityˡ = bitwise₂-identityˡ 0# B._xor_ λ _ → refl

xor-identityʳ : A.RightIdentity n zeroes _xor_
xor-identityʳ = bitwise₂-identityʳ 0# B._xor_ bxor-identityʳ

xor-identity : A.Identity n zeroes _xor_
xor-identity = xor-identityˡ , xor-identityʳ

xor-inverseˡ : A.LeftInverse n ones not _xor_
xor-inverseˡ = bitwise₂-inverseˡ 1# B.not B._xor_ (λ { 0# → refl ; 1# → refl })

xor-inverseʳ : A.RightInverse n ones not _xor_
xor-inverseʳ = bitwise₂-inverseʳ 1# B.not B._xor_ (λ { 0# → refl ; 1# → refl })

xor-inverse : A.Inverse n ones not _xor_
xor-inverse = xor-inverseˡ , xor-inverseʳ

xor-annihilate : ∀ (xs : BitVec n) → xs xor xs ≡ zeroes
xor-annihilate [] = refl
xor-annihilate (x ∷ xs) = cong₂ _∷_ (bxor-annihilate x) (xor-annihilate xs)

xor-cancelˡ : A.LeftCancellative n _xor_
xor-cancelˡ = bitwise₂-cancelˡ B._xor_ (λ { 0# eq → eq ; 1# eq → B.not-injective eq })

xor-cancelʳ : A.RightCancellative n _xor_
xor-cancelʳ = bitwise₂-cancelʳ B._xor_ (λ
  { 0# 0# eq → refl
  ; 0# 1# eq → ⊥-elim (B.not-¬ refl eq)
  ; 1# 0# eq → ⊥-elim (B.not-¬ refl (sym eq))
  ; 1# 1# eq → refl
  })

xor-cancel : A.Cancellative n _xor_
xor-cancel = xor-cancelˡ , xor-cancelʳ

-- not and xor

xor-distribˡ-not : ∀ (xs ys : BitVec n) → not (xs xor ys) ≡ not xs xor ys
xor-distribˡ-not [] [] = refl
xor-distribˡ-not (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (bxor-distribˡ-not x y) (xor-distribˡ-not xs ys)

xor-distribʳ-not : ∀ (xs ys : BitVec n) → not (xs xor ys) ≡ xs xor not ys
xor-distribʳ-not [] [] = refl
xor-distribʳ-not (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (bxor-distribʳ-not x y) (xor-distribʳ-not xs ys)

-- ∧ and xor

∧-distribˡ-xor : A.₍ n ₎ _∧_ DistributesOverˡ _xor_
∧-distribˡ-xor = bitwise₂-distribˡ B._∧_ B._xor_ (λ { 0# y z → refl ; 1# y z → refl })

∧-distribʳ-xor : A.₍ n ₎ _∧_ DistributesOverʳ _xor_
∧-distribʳ-xor = bitwise₂-distribʳ B._∧_ B._xor_ (λ
  { x 0# z  → refl
  ; x 1# 0# → sym (bxor-identityʳ x)
  ; x 1# 1# → sym (bxor-annihilate x)
  })

∧-distrib-xor : A.₍ n ₎ _∧_ DistributesOver _xor_
∧-distrib-xor = ∧-distribˡ-xor , ∧-distribʳ-xor

-- ∨ and xor

∨-squash-xor : ∀ (xs ys : BitVec n) → xs ∨ (xs xor ys) ≡ xs ∨ ys
∨-squash-xor [] [] = refl
∨-squash-xor (x ∷ xs) (y ∷ ys) =
  flip (cong₂ _∷_) (∨-squash-xor xs ys) (case x return (λ x → x B.∨ x B.xor y ≡ x B.∨ y) of λ
    { 0# → refl
    ; 1# → refl
    })


-- Conversions

-- bitToFin and finToBit

bitToFin-finToBit : ∀ x → bitToFin (finToBit x) ≡ x
bitToFin-finToBit zero       = refl
bitToFin-finToBit (suc zero) = refl

finToBit-bitToFin : ∀ x → finToBit (bitToFin x) ≡ x
finToBit-bitToFin 0# = refl
finToBit-bitToFin 1# = refl

-- toFin and fromFin

fromFin-toFin : ∀ xs → fromFin {n} (toFin {n} xs) ≡ xs
fromFin-toFin         []       = refl
fromFin-toFin {suc n} (x ∷ xs) with quotRem {2} (2 ^ n) (combine (bitToFin x) (toFin xs)) | remQuot-combine (bitToFin x) (toFin xs)
... | .(toFin xs) , .(bitToFin x) | refl = cong₂ _∷_ (finToBit-bitToFin x) (fromFin-toFin xs)

toFin-fromFin : ∀ x → toFin {n} (fromFin x) ≡ x
toFin-fromFin {zero}  zero = refl
toFin-fromFin {suc n} x = begin
  combine (bitToFin (finToBit (proj₁ rq))) (toFin (fromFin {n} (proj₂ rq))) ≡⟨ eq₁ ⟩
  combine (proj₁ rq) (proj₂ rq) ≡⟨ combine-remQuot (2 ^ n) x ⟩
  x ∎
  where
  open ≡-Reasoning
  rq = remQuot {2} (2 ^ n) x
  eq₁ = cong₂ combine (bitToFin-finToBit (proj₁ rq)) (toFin-fromFin {n} (proj₂ rq))

