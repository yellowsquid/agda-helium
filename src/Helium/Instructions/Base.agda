------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of instructions using the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Instructions.Base where

open import Data.Bool as Bool using (true; false)
open import Data.Fin as Fin using (Fin; Fin′; zero; suc; toℕ)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Sum using ([_,_]′; inj₂)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Function using (_$_)
open import Helium.Data.Pseudocode.Core as Core public
  hiding (module Code)
import Helium.Instructions.Core as Instr
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary.Decidable.Core using (True)

--- Types

beat : Type
beat = fin 4

elmtMask : Type
elmtMask = bits 4

--- State

State : Vec Type _
State = array (bits 32) 32      -- S
      ∷ array (bits 32) 16      -- R
      ∷ bits 16                 -- VPR-P0
      ∷ bits 8                  -- VPR-mask
      ∷ bit                     -- FPSCR-QC
      ∷ bool                    -- _AdvanceVPTState
      ∷ beat                    -- _BeatId
      ∷ []

open Core.Code State public

--- References

-- Direct from State

S : ∀ {n Γ} → Expression {n} Γ (array (bits 32) 32)
S = state 0F

R : ∀ {n Γ} → Expression {n} Γ (array (bits 32) 16)
R = state 1F

VPR-P0 : ∀ {n Γ} → Expression {n} Γ (bits 16)
VPR-P0 = state 2F

VPR-mask : ∀ {n Γ} → Expression {n} Γ (bits 8)
VPR-mask = state 3F

FPSCR-QC : ∀ {n Γ} → Expression {n} Γ bit
FPSCR-QC = state 4F

AdvanceVPTState : ∀ {n Γ} → Expression {n} Γ bool
AdvanceVPTState = state 5F

BeatId : ∀ {n Γ} → Expression {n} Γ beat
BeatId = state 6F

-- Indirect

group : ∀ {n Γ t k} m → Expression {n} Γ (asType t (k ℕ.* suc m)) → Expression Γ (array (asType t k) (suc m))
group {k = k} zero    x = [ cast (P.trans (ℕₚ.*-comm k 1) (ℕₚ.+-comm k 0)) x ]
group {k = k} (suc m) x = group m (slice x′ (lit (Fin.fromℕ k ′f))) ∶ [ slice (cast (ℕₚ.+-comm k _) x′) (lit (zero ′f))  ]
  where
  x′ = cast (P.trans (ℕₚ.*-comm k _) (P.cong (k ℕ.+_) (ℕₚ.*-comm _ k))) x

join : ∀ {n Γ t k m} → Expression {n} Γ (array (asType t k) (suc m)) → Expression Γ (asType t (k ℕ.* suc m))
join {k = k} {zero}  x = cast (P.trans (ℕₚ.+-comm 0 k) (ℕₚ.*-comm 1 k)) (unbox x)
join {k = k} {suc m} x = cast eq (join (slice x (lit (Fin.fromℕ 1 ′f))) ∶ unbox (slice {i = suc m} (cast (ℕₚ.+-comm 1 _) x) (lit (zero ′f))))
  where
  eq = P.trans (P.cong (k ℕ.+_) (ℕₚ.*-comm k (suc m))) (ℕₚ.*-comm (suc (suc m)) k)

index : ∀ {n Γ t m} → Expression {n} Γ (asType t (suc m)) → Expression Γ (fin (suc m)) → Expression Γ (elemType t)
index {m = m} x i = unbox (slice (cast (ℕₚ.+-comm 1 m) x) i)

Q : ∀ {n Γ} → Expression {n} Γ (array (array (bits 32) 4) 8)
Q = group 7 S

elem : ∀ {n Γ t k} m → Expression {n} Γ (asType t (k ℕ.* m)) → Expression Γ (fin k) → Expression Γ (asType t m)
elem {k = zero}  m       x i = abort i
elem {k = suc k} zero    x i = cast (ℕₚ.*-comm k 0) x
elem {k = suc k} (suc m) x i = index (group k (cast (ℕₚ.*-comm (suc k) (suc m)) x)) i

--- Other utiliies

hasBit : ∀ {n Γ m} → Expression {n} Γ (bits (suc m)) → Expression Γ (fin (suc m)) → Expression Γ bool
hasBit {n} x i = index x i ≟ lit (true ′x)

sliceⁱ : ∀ {n Γ m} → ℕ → Expression {n} Γ int → Expression Γ (bits m)
sliceⁱ {m = zero}  n i = lit ([] ′xs)
sliceⁱ {m = suc m} n i = sliceⁱ (suc n) i ∶ [ get n i ]

--- Functions

Int : ∀ {n} → Function (bits n ∷ bool ∷ []) int
Int = skip ∙return (if var 1F then uint (var 0F) else sint (var 0F))

-- arguments swapped, pred n
SignedSatQ : ∀ n → Function (int ∷ []) (tuple 2 (bits (suc n) ∷ bool ∷ []))
SignedSatQ n = declare (lit (true ′b)) (
  if max <? var 1F
  then
    var 1F ≔ max
  else if var 1F <? min
  then
    var 1F ≔ min
  else
    var 0F ≔ lit (false ′b)
  ∙return tup (sliceⁱ 0 (var 1F) ∷ var 0F ∷ []))
  where
  max = lit (2 ′i) ^ n + - lit (1 ′i)
  min = - (lit (2 ′i) ^ n)

-- actual shift if 'shift + 1'
LSL-C : ∀ {n} (shift : ℕ) → Function (bits n ∷ []) (tuple 2 (bits n ∷ bit ∷ []))
LSL-C {n} shift = declare (var 0F ∶ lit ((Vec.replicate {n = (suc shift)} false) ′xs))
  (skip ∙return tup
    ( slice (var 0F) (lit (zero ′f))
    ∷ unbox (slice (cast eq (var 0F)) (lit (Fin.inject+ shift (Fin.fromℕ n) ′f)))
    ∷ []))
  where
  eq = P.trans (ℕₚ.+-comm 1 (shift ℕ.+ n)) (P.cong (ℕ._+ 1) (ℕₚ.+-comm shift n))

--- Procedures

private
  div2 : All Fin (4 ∷ []) → Fin 2
  div2 (zero        ∷ []) = zero
  div2 (suc zero    ∷ []) = zero
  div2 (suc (suc i) ∷ []) = suc zero

copyMasked : Procedure (fin 8 ∷ bits 32 ∷ beat ∷ elmtMask ∷ [])
copyMasked = for 4
  -- 0:e 1:dest 2:result 3:beat 4:elmtMask
  ( if hasBit (var 4F) (var 0F)
    then
      elem 8 (index (index Q (var 1F)) (var 3F)) (var 0F) ≔ elem 8 (var 2F) (var 0F)
    else skip
  ) ∙end

VPTAdvance : Procedure (beat ∷ [])
VPTAdvance = declare (fin div2 (tup (var 0F ∷ []))) (
  declare (elem 4 VPR-mask (var 0F)) (
    -- 0:vptState 1:maskId 2:beat
    if var 0F ≟ lit ((true ∷ false ∷ false ∷ false ∷ []) ′xs)
    then
      var 0F ≔ lit (Vec.replicate false ′xs)
    else if inv (var 0F ≟ lit (Vec.replicate false ′xs))
    then (
      declare (lit (false ′x)) (
        -- 0:inv 1:vptState 2:maskId 3:beat
        tup (var 1F ∷ var 0F ∷ []) ≔ call (LSL-C 0) (var 1F ∷ []) ∙
        if var 0F ≟ lit (true ′x)
        then
          elem 4 VPR-P0 (var 3F) ≔ not (elem 4 VPR-P0 (var 3F))
        else skip))
    else skip ∙
    if get 0 (asInt (var 2F)) ≟ lit (true ′x)
    then
      elem 4 VPR-mask (var 1F) ≔ var 0F
    else skip))
    ∙end

VPTActive : Function (beat ∷ []) bool
VPTActive = skip ∙return inv (elem 4 VPR-mask (fin div2 (tup (var 0F ∷ []))) ≟ lit (Vec.replicate false ′xs))

GetCurInstrBeat : Function [] (tuple 2 (beat ∷ elmtMask ∷ []))
GetCurInstrBeat = declare (lit (Vec.replicate true ′xs)) (
  -- 0:elmtMask 1:beat
  if call VPTActive (BeatId ∷ [])
  then
    var 0F ≔ var 0F and elem 4 VPR-P0 BeatId
  else skip
  ∙return tup (BeatId ∷ var 0F ∷ []))

-- Assumes:
--   MAX_OVERLAPPING_INSTRS = 1
--   _InstInfo[0].Valid = 1
--   BEATS_PER_TICK = 4
--   procedure argument is action of DecodeExecute
-- and more!
ExecBeats : Procedure [] → Procedure []
ExecBeats DecodeExec =
  for 4 (
    -- 0:beatId
    BeatId ≔ var 0F ∙
    AdvanceVPTState ≔ lit (true ′b) ∙
    invoke DecodeExec [] ∙
    if AdvanceVPTState
    then
      invoke VPTAdvance (var 0F ∷ [])
    else skip)
  ∙end

from32 : ∀ size {n Γ} → Expression {n} Γ (bits 32) → Expression Γ (array (bits (toℕ (Instr.Size.esize size))) (toℕ (Instr.Size.elements size)))
from32 Instr.8bit  = group 3
from32 Instr.16bit = group 1
from32 Instr.32bit = group 0

to32 : ∀ size {n Γ} → Expression {n} Γ (array (bits (toℕ (Instr.Size.esize size))) (toℕ (Instr.Size.elements size))) → Expression Γ (bits 32)
to32 Instr.8bit  = join
to32 Instr.16bit = join
to32 Instr.32bit = join

module _ (d : Instr.VecOp₂) where
  open Instr.VecOp₂ d

 -- 0:op₂ 1:e 2:op₁ 3:result 4:elmtMask 5:curBeat
  vec-op₂′ : Statement (bits (toℕ esize) ∷ fin (toℕ elements) ∷ array (bits (toℕ esize)) (toℕ elements) ∷ array (bits (toℕ esize)) (toℕ elements) ∷ elmtMask ∷ beat ∷ []) → Procedure []
  vec-op₂′ op = declare (lit (zero ′f)) (
    declare (lit (Vec.replicate false ′xs)) (
    -- 0:elmtMask 1:curBeat
    tup (var 1F ∷ var 0F ∷ []) ≔ call GetCurInstrBeat [] ∙
    declare (lit ((Vec.replicate false ′xs) ′a)) (
    declare (from32 size (index (index Q (lit (src₁ ′f))) (var 2F))) (
    -- 0:op₁ 1:result 2:elmtMask 3:curBeat
    for (toℕ elements) (
       -- 0:e 1:op₁ 2:result 3:elmtMask 4:curBeat
      declare op₂ op ) ∙
    -- 0:op₁ 1:result 2:elmtMask 3:curBeat
    invoke copyMasked (lit (dest ′f) ∷ to32 size (var 1F) ∷ var 3F ∷ var 2F ∷ [])))))
    ∙end
    where
    -- 0:e 1:op₁ 2:result 3:elmtMask 4:curBeat
    op₂ =
      [ (λ src₂ → index (from32 size (index R (lit (src₂ ′f)))) (lit (zero ′f)))
      , (λ src₂ → index (from32 size (index (index Q (lit (src₂ ′f))) (var 4F))) (var 0F))
      ]′ src₂

  vec-op₂ : Function (bits (toℕ esize) ∷ bits (toℕ esize) ∷ []) (bits (toℕ esize)) → Procedure []
  vec-op₂ op = vec-op₂′ (index (var 3F) (var 1F) ≔ call op (index (var 2F) (var 1F) ∷ var 0F ∷ []))

vadd : Instr.VAdd → Procedure []
vadd d = vec-op₂ d (skip ∙return sliceⁱ 0 (uint (var 0F) + uint (var 1F)))

vsub : Instr.VSub → Procedure []
vsub d = vec-op₂ d (skip ∙return sliceⁱ 0 (uint (var 0F) - uint (var 1F)))

vhsub : Instr.VHSub → Procedure []
vhsub d = vec-op₂ op₂ (skip ∙return sliceⁱ 1 (toInt (var 0F) - toInt (var 1F)))
  where open Instr.VHSub d; toInt = λ i → call Int (i ∷ lit (unsigned ′b) ∷ [])

vmul : Instr.VMul → Procedure []
vmul d = vec-op₂ d (skip ∙return sliceⁱ 0 (sint (var 0F) * sint (var 1F)))

vmulh : Instr.VMulH → Procedure []
vmulh d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * toInt (var 1F)))
  where
  open Instr.VMulH d; toInt = λ i → call Int (i ∷ lit (unsigned ′b) ∷ [])

vrmulh : Instr.VRMulH → Procedure []
vrmulh d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * toInt (var 1F) + lit (1 ′i) << toℕ esize-1))
  where
  open Instr.VRMulH d; toInt = λ i → call Int (i ∷ lit (unsigned ′b) ∷ [])

vmla : Instr.VMlA → Procedure []
vmla d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * element₂ + toInt (var 1F)))
  where
  open Instr.VMlA d
  op₂ = record { size = size ; dest = acc ; src₁ = src₁ ; src₂ = inj₂ acc }
  toInt = λ i → call Int (i ∷ lit (unsigned ′b) ∷ [])
  element₂ = toInt (index (from32 size (index R (lit (src₂ ′f)))) (lit (zero ′f)))

private
  vqr?dmulh : Instr.VQDMulH → Function (int ∷ int ∷ []) int → Procedure []
  vqr?dmulh d f = vec-op₂′ d (
    -- 0:op₂ 1:e 2:op₁ 3:result 4:elmtMask 5:curBeat
    declare (call f (sint (index (var 2F) (var 1F)) ∷ sint (var 0F) ∷ [])) (
    declare (lit (false ′b)) (
      -- 0:sat 1:value 2:op₂ 3:e 4:op₁ 5:result 6:elmtMask 7:curBeat
      tup (index (var 5F) (var 3F) ∷ var 0F ∷ []) ≔ call (SignedSatQ (toℕ esize-1)) (var 1F ∷ []) ∙
      if var 0F && hasBit (var 6F) (fin e*esize>>3 (tup ((var 3F) ∷ [])))
      then
        FPSCR-QC ≔ lit (true ′x)
      else skip)))
    where
    open Instr.VecOp₂ d

    e*esize>>3 : All Fin (toℕ elements ∷ []) → Fin 4
    e*esize>>3 (x ∷ []) = helper size x
      where
      helper : ∀ size → Fin′ (Instr.Size.elements size) → Fin 4
      helper Instr.8bit  i = Fin.combine i (zero {0})
      helper Instr.16bit i = Fin.combine i (zero {1})
      helper Instr.32bit i = Fin.combine i zero

vqdmulh : Instr.VQDMulH → Procedure []
vqdmulh d = vqr?dmulh d (skip ∙return lit (2 ′i) * var 0F * var 1F >> toℕ esize)
  where open Instr.VecOp₂ d using (esize)

vqrdmulh : Instr.VQRDMulH → Procedure []
vqrdmulh d = vqr?dmulh d (skip ∙return lit (2 ′i) * var 0F * var 1F + lit (1 ′i) << toℕ esize-1 >> toℕ esize)
  where open Instr.VecOp₂ d using (esize; esize-1)
