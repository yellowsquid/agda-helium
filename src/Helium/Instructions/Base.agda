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
open import Data.Integer as ℤ using (1ℤ; 0ℤ; -1ℤ)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (uncurry)
open import Data.Sum using ([_,_]′; inj₂)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Function using (_$_)
open import Helium.Data.Pseudocode.Core as Core public
import Helium.Instructions.Core as Instr
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary.Decidable.Core using (True)

private
  variable
    k m n : ℕ
    t : Type
    Γ : Vec Type n

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

--- References

-- Direct from State

S : Reference State Γ (array (bits 32) 32)
S = state 0F

R : Reference State Γ (array (bits 32) 16)
R = state 1F

VPR-P0 : Reference State Γ (bits 16)
VPR-P0 = state 2F

VPR-mask : Reference State Γ (bits 8)
VPR-mask = state 3F

FPSCR-QC : Reference State Γ bit
FPSCR-QC = state 4F

AdvanceVPTState : Reference State Γ bool
AdvanceVPTState = state 5F

BeatId : Reference State Γ beat
BeatId = state 6F

-- Indirect

index : Expression State Γ (array t (suc m)) → Expression State Γ (fin (suc m)) → Expression State Γ t
index {m = m} x i = unbox (slice (cast (ℕₚ.+-comm 1 m) x) i)

*index : Reference State Γ (array t (suc m)) → Expression State Γ (fin (suc m)) → Reference State Γ t
*index {m = m} x i = unbox (slice (cast (ℕₚ.+-comm 1 m) x) i)

*index-group : Reference State Γ (array t (k ℕ.* suc m)) → Expression State Γ (fin (suc m)) → Reference State Γ (array t k)
*index-group {k = k} {m = m} x i = slice (cast eq x) (fin reindex (tup (i ∷ [])))
  where
  eq = P.trans (ℕₚ.*-comm k (suc m)) (ℕₚ.+-comm k (m ℕ.* k))

  reindex : ∀ {m n} → Fin (suc m) → Fin (suc (m ℕ.* n))
  reindex {m}     {n} 0F      = Fin.inject+ (m ℕ.* n) 0F
  reindex {suc m} {n} (suc i) = Fin.cast (ℕₚ.+-suc n (m ℕ.* n)) (Fin.raise n (reindex i))

index-group : Expression State Γ (array t (k ℕ.* suc m)) → Expression State Γ (fin (suc m)) → Expression State Γ (array t k)
index-group {k = k} {m = m} x i = slice (cast eq x) (fin reindex (tup (i ∷ [])))
  where
  eq = P.trans (ℕₚ.*-comm k (suc m)) (ℕₚ.+-comm k (m ℕ.* k))

  reindex : ∀ {m n} → Fin (suc m) → Fin (suc (m ℕ.* n))
  reindex {m}     {n} 0F      = Fin.inject+ (m ℕ.* n) 0F
  reindex {suc m} {n} (suc i) = Fin.cast (ℕₚ.+-suc n (m ℕ.* n)) (Fin.raise n (reindex i))

Q[_,_] : Expression State Γ (fin 8) → Expression State Γ (fin 4) → Reference State Γ (bits 32)
Q[ i , j ] = *index S (fin (uncurry Fin.combine) (tup (i ∷ j ∷ [])))

elem : ∀ m → Expression State Γ (array t (suc k ℕ.* m)) → Expression State Γ (fin (suc k)) → Expression State Γ (array t m)
elem {k = k} zero    x i = cast (ℕₚ.*-comm k 0) x
elem {k = k} (suc m) x i = index-group (cast (ℕₚ.*-comm (suc k) (suc m)) x) i

*elem : ∀ m → Reference State Γ (array t (suc k ℕ.* m)) → Expression State Γ (fin (suc k)) → Reference State Γ (array t m)
*elem {k = k} zero    x i = cast (ℕₚ.*-comm k 0) x
*elem {k = k} (suc m) x i = *index-group (cast (ℕₚ.*-comm (suc k) (suc m)) x) i

--- Other utiliies

hasBit : Expression State Γ (bits (suc m)) → Expression State Γ (fin (suc m)) → Expression State Γ bool
hasBit {n} x i = index x i ≟ lit true

sliceⁱ : ℕ → Expression State Γ int → Expression State Γ (bits m)
sliceⁱ {m = zero}  n i = lit []
sliceⁱ {m = suc m} n i = sliceⁱ (suc n) i ∶ [ getBit n i ]

--- Functions

Int : Function State (bits n ∷ bool ∷ []) int
Int = skip ∙return (if var 1F then uint (var 0F) else sint (var 0F))

-- arguments swapped, pred n
SignedSatQ : ∀ n → Function State (int ∷ []) (tuple (bits (suc n) ∷ bool ∷ []))
SignedSatQ n = declare (lit true) (
  if max <? var 1F
  then
    var 1F ≔ max
  else if var 1F <? min
  then
    var 1F ≔ min
  else
    var 0F ≔ lit false
  ∙return tup (sliceⁱ 0 (var 1F) ∷ var 0F ∷ []))
  where
  max = lit (ℤ.+ (2 ℕ.^ n) ℤ.+ -1ℤ)
  min = lit (ℤ.- ℤ.+ (2 ℕ.^ n))

-- actual shift if 'shift + 1'
LSL-C : ∀ (shift : ℕ) → Function State (bits n ∷ []) (tuple (bits n ∷ bit ∷ []))
LSL-C {n} shift = declare (var 0F ∶ lit ((Vec.replicate {n = (suc shift)} false)))
  (skip ∙return tup
    ( slice (var 0F) (lit 0F)
    ∷ unbox (slice (cast eq (var 0F)) (lit (Fin.inject+ shift (Fin.fromℕ n))))
    ∷ []))
  where
  eq = P.trans (ℕₚ.+-comm 1 (shift ℕ.+ n)) (P.cong (ℕ._+ 1) (ℕₚ.+-comm shift n))

--- Procedures

private
  div2 : Fin 4 → Fin 2
  div2 0F = 0F
  div2 1F = 0F
  div2 2F = 1F
  div2 3F = 1F

copyMasked : Procedure State (fin 8 ∷ bits 32 ∷ beat ∷ elmtMask ∷ [])
copyMasked = for 4
  -- 0:e 1:dest 2:result 3:beat 4:elmtMask
  ( if hasBit (var 4F) (var 0F)
    then
      *elem 8 Q[ var 1F , var 3F ] (var 0F) ≔ elem 8 (var 2F) (var 0F)
  ) ∙end

VPTAdvance : Procedure State (beat ∷ [])
VPTAdvance = declare (fin div2 (tup (var 0F ∷ []))) (
  declare (elem 4 (! VPR-mask) (var 0F)) (
    -- 0:vptState 1:maskId 2:beat
    if var 0F ≟ lit (true ∷ false ∷ false ∷ false ∷ [])
    then
      var 0F ≔ lit (Vec.replicate false)
    else if inv (var 0F ≟ lit (Vec.replicate false))
    then (
      declare (lit false) (
        -- 0:inv 1:vptState 2:maskId 3:beat
        cons (var 1F) (cons (var 0F) nil) ≔ call (LSL-C 0) (var 1F ∷ []) ∙
        if var 0F ≟ lit true
        then
          *elem 4 VPR-P0 (var 3F) ≔ not (elem 4 (! VPR-P0) (var 3F)))) ∙
    if getBit 0 (asInt (var 2F)) ≟ lit true
    then
      *elem 4 VPR-mask (var 1F) ≔ var 0F))
    ∙end

VPTActive : Function State (beat ∷ []) bool
VPTActive = skip ∙return inv (elem 4 (! VPR-mask) (fin div2 (tup (var 0F ∷ []))) ≟ lit (Vec.replicate false))

GetCurInstrBeat : Function State [] (tuple (beat ∷ elmtMask ∷ []))
GetCurInstrBeat = declare (lit (Vec.replicate true)) (
  -- 0:elmtMask 1:beat
  if call VPTActive (! BeatId ∷ [])
  then
    var 0F ≔ var 0F and elem 4 (! VPR-P0) (! BeatId)
  ∙return tup (! BeatId ∷ var 0F ∷ []))

-- Assumes:
--   MAX_OVERLAPPING_INSTRS = 1
--   _InstInfo[0].Valid = 1
--   BEATS_PER_TICK = 4
--   procedure argument is action of DecodeExecute
-- and more!
ExecBeats : Procedure State [] → Procedure State []
ExecBeats DecodeExec =
  for 4 (
    -- 0:beatId
    BeatId ≔ var 0F ∙
    AdvanceVPTState ≔ lit true ∙
    invoke DecodeExec [] ∙
    if ! AdvanceVPTState
    then
      invoke VPTAdvance (var 0F ∷ []))
  ∙end

*index-32 : ∀ size → Reference State Γ (bits 32) → Expression State Γ (fin (toℕ (Instr.Size.elements size))) → Reference State Γ (bits (toℕ (Instr.Size.esize size)))
*index-32 Instr.8bit  = *index-group
*index-32 Instr.16bit = *index-group
*index-32 Instr.32bit = *index-group

index-32 : ∀ size → Expression State Γ (bits 32) → Expression State Γ (fin (toℕ (Instr.Size.elements size))) → Expression State Γ (bits (toℕ (Instr.Size.esize size)))
index-32 Instr.8bit  = index-group
index-32 Instr.16bit = index-group
index-32 Instr.32bit = index-group

module _ (d : Instr.VecOp₂) where
  open Instr.VecOp₂ d

 -- 0:op₂ 1:e 2:op₁ 3:result 4:elmtMask 5:curBeat
  vec-op₂′ : Statement State (bits (toℕ esize) ∷ fin (toℕ elements) ∷ bits 32 ∷ bits 32 ∷ elmtMask ∷ beat ∷ []) → Procedure State []
  vec-op₂′ op = declare (lit 0F) (
    declare (lit (Vec.replicate false)) (
    -- 0:elmtMask 1:curBeat
    cons (var 1F) (cons (var 0F) nil) ≔ call GetCurInstrBeat [] ∙
    declare (lit (Vec.replicate false)) (
    declare (! Q[ lit src₁ , var 2F ]) (
    -- 0:op₁ 1:result 2:elmtMask 3:curBeat
    for (toℕ elements) (
       -- 0:e 1:op₁ 2:result 3:elmtMask 4:curBeat
      declare op₂ op ) ∙
    -- 0:op₁ 1:result 2:elmtMask 3:curBeat
    invoke copyMasked (lit dest ∷ var 1F ∷ var 3F ∷ var 2F ∷ [])))))
    ∙end
    where
    -- 0:e 1:op₁ 2:result 3:elmtMask 4:curBeat
    op₂ =
      [ (λ src₂ → index-32 size (index (! R) (lit src₂)) (lit 0F))
      , (λ src₂ → index-32 size (! Q[ lit src₂ , var 4F ]) (var 0F))
      ]′ src₂

  vec-op₂ : Function State (bits (toℕ esize) ∷ bits (toℕ esize) ∷ []) (bits (toℕ esize)) → Procedure State []
  vec-op₂ op = vec-op₂′ (*index-32 size (var 3F) (var 1F) ≔ call op (index-32 size (var 2F) (var 1F) ∷ var 0F ∷ []))

vadd : Instr.VAdd → Procedure State []
vadd d = vec-op₂ d (skip ∙return sliceⁱ 0 (uint (var 0F) + uint (var 1F)))

vsub : Instr.VSub → Procedure State []
vsub d = vec-op₂ d (skip ∙return sliceⁱ 0 (uint (var 0F) - uint (var 1F)))

vhsub : Instr.VHSub → Procedure State []
vhsub d = vec-op₂ op₂ (skip ∙return sliceⁱ 1 (toInt (var 0F) - toInt (var 1F)))
  where open Instr.VHSub d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vmul : Instr.VMul → Procedure State []
vmul d = vec-op₂ d (skip ∙return sliceⁱ 0 (sint (var 0F) * sint (var 1F)))

vmulh : Instr.VMulH → Procedure State []
vmulh d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * toInt (var 1F)))
  where
  open Instr.VMulH d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vrmulh : Instr.VRMulH → Procedure State []
vrmulh d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * toInt (var 1F) + lit 1ℤ << toℕ esize-1))
  where
  open Instr.VRMulH d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vmla : Instr.VMlA → Procedure State []
vmla d = vec-op₂ op₂ (skip ∙return sliceⁱ (toℕ esize) (toInt (var 0F) * element₂ + toInt (var 1F)))
  where
  open Instr.VMlA d
  op₂ = record { size = size ; dest = acc ; src₁ = src₁ ; src₂ = inj₂ acc }
  toInt = λ i → call Int (i ∷ lit unsigned ∷ [])
  element₂ = toInt (index-32 size (index (! R) (lit src₂)) (lit 0F))

private
  vqr?dmulh : Instr.VQDMulH → Function State (int ∷ int ∷ []) int → Procedure State []
  vqr?dmulh d f = vec-op₂′ d (
    -- 0:op₂ 1:e 2:op₁ 3:result 4:elmtMask 5:curBeat
    declare (call f (sint (index-32 size (var 2F) (var 1F)) ∷ sint (var 0F) ∷ [])) (
    declare (lit false) (
      -- 0:sat 1:value 2:op₂ 3:e 4:op₁ 5:result 6:elmtMask 7:curBeat
      cons (*index-32 size (var 5F) (var 3F)) (cons (var 0F) nil) ≔ call (SignedSatQ (toℕ esize-1)) (var 1F ∷ []) ∙
      if var 0F && hasBit (var 6F) (fin e*esize>>3 (tup ((var 3F) ∷ [])))
      then
        FPSCR-QC ≔ lit true)))
    where
    open Instr.VecOp₂ d

    e*esize>>3 : Fin (toℕ elements) → Fin 4
    e*esize>>3 x = helper size x
      where
      helper : ∀ size → Fin′ (Instr.Size.elements size) → Fin 4
      helper Instr.8bit  i = Fin.combine i (zero {0})
      helper Instr.16bit i = Fin.combine i (zero {1})
      helper Instr.32bit i = Fin.combine i zero

vqdmulh : Instr.VQDMulH → Procedure State []
vqdmulh d = vqr?dmulh d (skip ∙return lit (ℤ.+ 2) * var 0F * var 1F >> toℕ esize)
  where open Instr.VecOp₂ d using (esize)

vqrdmulh : Instr.VQRDMulH → Procedure State []
vqrdmulh d = vqr?dmulh d (skip ∙return lit (ℤ.+ 2) * var 0F * var 1F + lit 1ℤ << toℕ esize-1 >> toℕ esize)
  where open Instr.VecOp₂ d using (esize; esize-1)
