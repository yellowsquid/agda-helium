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
open import Data.Product using (_,_; uncurry)
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
    Σ Γ : Vec Type n

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

*index-group : Reference Σ Γ (array t (k ℕ.* suc m)) → Expression Σ Γ (fin (suc m)) → Reference Σ Γ (array t k)
*index-group {k = k} {m = m} x i = slice (cast eq x) (fin reindex (tup (i ∷ [])))
  where
  eq = P.trans (ℕₚ.*-comm k (suc m)) (ℕₚ.+-comm k (m ℕ.* k))

  reindex : ∀ {m n} → Fin (suc m) → Fin (suc (m ℕ.* n))
  reindex {m}     {n} 0F      = Fin.inject+ (m ℕ.* n) 0F
  reindex {suc m} {n} (suc i) = Fin.cast (ℕₚ.+-suc n (m ℕ.* n)) (Fin.raise n (reindex i))

index-group : Expression Σ Γ (array t (k ℕ.* suc m)) → Expression Σ Γ (fin (suc m)) → Expression Σ Γ (array t k)
index-group {k = k} {m = m} x i = slice (cast eq x) (fin reindex (tup (i ∷ [])))
  where
  eq = P.trans (ℕₚ.*-comm k (suc m)) (ℕₚ.+-comm k (m ℕ.* k))

  reindex : ∀ {m n} → Fin (suc m) → Fin (suc (m ℕ.* n))
  reindex {m}     {n} 0F      = Fin.inject+ (m ℕ.* n) 0F
  reindex {suc m} {n} (suc i) = Fin.cast (ℕₚ.+-suc n (m ℕ.* n)) (Fin.raise n (reindex i))

Q[_,_] : Expression State Γ (fin 8) → Expression State Γ (fin 4) → Reference State Γ (bits 32)
Q[ i , j ] = *index S (fin (uncurry Fin.combine) (tup (i ∷ j ∷ [])))

elem : ∀ m → Expression Σ Γ (array t (suc k ℕ.* m)) → Expression Σ Γ (fin (suc k)) → Expression Σ Γ (array t m)
elem {k = k} zero    x i = cast (ℕₚ.*-comm k 0) x
elem {k = k} (suc m) x i = index-group (cast (ℕₚ.*-comm (suc k) (suc m)) x) i

*elem : ∀ m → Reference Σ Γ (array t (suc k ℕ.* m)) → Expression Σ Γ (fin (suc k)) → Reference Σ Γ (array t m)
*elem {k = k} zero    x i = cast (ℕₚ.*-comm k 0) x
*elem {k = k} (suc m) x i = *index-group (cast (ℕₚ.*-comm (suc k) (suc m)) x) i

--- Other utiliies

hasBit : Expression Σ Γ (bits (suc m)) → Expression Σ Γ (fin (suc m)) → Expression Σ Γ bool
hasBit = index

sliceⁱ : ℕ → Function Σ (int ∷ []) (bits m)
sliceⁱ {m = 0}     offset = init lit [] ∙ skip end
sliceⁱ {m = suc m} offset =
  init
    lit (Vec.replicate false) ∙ (
    var 1F ≔ var 1F >> offset ∙
    for (suc m) (
      let x = var 2F in
      let ret = var 1F in
      let i = var 0F in
      **index ret i ≔ lit {t = int} ℤ.0ℤ <? !! x - lit (ℤ.+ 2) * (!! x >> 1) ∙
      x ≔ !! x >> 1
    ))
  end

--- Functions

Int : Function Σ (bits n ∷ bool ∷ []) int
Int =
  init (
    let x = var 0F in
    let unsigned = var 1F in
    if unsigned
    then
      call uint (x ∷ [])
    else
      call sint (x ∷ [])
    )
    ∙
    skip
  end

-- arguments swapped, pred n
SignedSatQ : ∀ n → Function Σ (int ∷ []) (tuple (bits (suc n) ∷ bool ∷ []))
SignedSatQ n =
  init
    lit (Vec.replicate false , true)
    ∙ (
      let x = var 1F in
      let ret₁ = head (var 0F) in
      let ret₂ = head (tail (var 0F)) in
      if max <? !! x
      then
        x ≔ max
      else if !! x <? min
      then
        x ≔ min
      else
        ret₂ ≔ lit false ∙
      ret₁ ≔ call (sliceⁱ 0) (!! x ∷ []))
  end
  where
  max = lit (ℤ.+ (2 ℕ.^ n) ℤ.+ -1ℤ)
  min = lit (ℤ.- ℤ.+ (2 ℕ.^ n))

LSL-C : (shift-1 : ℕ) → Function State (bits n ∷ []) (tuple (bits n ∷ bit ∷ []))
LSL-C {n} shift-1 =
  init
    lit (Vec.replicate false , false)
    ∙
    declare (var 1F ∶ lit (Vec.replicate {n = suc shift-1} false)) (
      var 1F ≔ tup (
        slice (var 0F) (lit 0F) ∷
        unbox (slice (cast eq (var 0F)) (lit (Fin.inject+ shift-1 (Fin.fromℕ n)))) ∷
        []))
  end
  where
  eq = P.trans (ℕₚ.+-comm 1 (shift-1 ℕ.+ n)) (P.cong (ℕ._+ 1) (ℕₚ.+-comm shift-1 n))

--- Procedures

private
  div2 : Fin 4 → Fin 2
  div2 0F = 0F
  div2 1F = 0F
  div2 2F = 1F
  div2 3F = 1F

copyMasked : Procedure State (fin 8 ∷ bits 32 ∷ beat ∷ elmtMask ∷ [])
copyMasked =
  for 4 (
    let e = var 0F in
    let dst = var 1F in
    let src = var 2F in
    let beat = var 3F in
    let elmtMask = var 4F in
    if hasBit elmtMask e
    then
      *elem 8 Q[ dst , beat ] e ≔ elem 8 src beat)
  ∙end

VPTAdvance : Procedure State (beat ∷ [])
VPTAdvance =
  declare (fin div2 (tup (var 0F ∷ []))) (
  declare (elem 4 (! VPR-mask) (var 0F)) (
    let vptState = var 0F in
    let maskId = var 1F in
    let beat = var 2F in
    if ! vptState ≟ lit (true ∷ false ∷ false ∷ false ∷ [])
    then
      vptState ≔ lit (Vec.replicate false)
    else if inv (! vptState ≟ lit (Vec.replicate false))
    then (
      declare (call (LSL-C 0) (! vptState ∷ [])) (
        let vptState′,i = var 0F in
        let vptState = var 1F in
        -- let maskId = var 2F in
        let beat = var 3F in
        vptState ≔ head vptState′,i ∙
        if head (tail vptState′,i)
        then
          *elem 4 VPR-P0 beat ≔ not (elem 4 (! VPR-P0) beat))) ∙
    if getBit 0 (asInt beat)
    then
      *elem 4 VPR-mask maskId ≔ ! vptState))
  ∙end

VPTActive : Function State (beat ∷ []) bool
VPTActive =
  init
    inv (elem 4 (! VPR-mask) (fin div2 (tup (var 0F ∷ []))) ≟ lit (Vec.replicate false))
    ∙
    skip
  end

GetCurInstrBeat : Function State [] (tuple (beat ∷ elmtMask ∷ []))
GetCurInstrBeat =
  init
    tup (! BeatId ∷ lit (Vec.replicate true) ∷ [])
    ∙ (
    let curBeat = head (var 0F) in
    let elmtMask = head (tail (var 0F)) in
    if call VPTActive (curBeat  ∷ [])
    then
      elmtMask ≔ !! elmtMask and elem 4 (! VPR-P0) curBeat)
  end

-- Assumes:
--   MAX_OVERLAPPING_INSTRS = 1
--   _InstInfo[0].Valid = 1
--   BEATS_PER_TICK = 4
--   procedure argument is action of DecodeExecute
-- and more!
ExecBeats : Procedure State [] → Procedure State []
ExecBeats DecodeExec =
  for 4 (
    let beatId = var 0F in
    BeatId ≔ beatId ∙
    AdvanceVPTState ≔ lit true ∙
    invoke DecodeExec [] ∙
    if ! AdvanceVPTState
    then
      invoke VPTAdvance (beatId ∷ []))
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

  private
    VecOpLocals : Vec Type 5
    VecOpLocals = bits (toℕ esize) ∷ fin (toℕ elements) ∷ bits 32 ∷ bits 32 ∷ tuple (beat ∷ elmtMask ∷ []) ∷ []

  -- NOTE: we accept a statement as we need to modify global variables
  --       and return a result value.
  -- The statement _must_ assign into `index-32 size result e` and no other
  -- local variable (expect those it declares itself).
  vec-op₂′ : Statement State VecOpLocals → Procedure State []
  vec-op₂′ op =
    declare (call GetCurInstrBeat []) (
      -- let elmtMast = head (tail (var 0F)) in
      let curBeat = head (var 0F) in
      declare (! Q[ lit src₁ , curBeat ]) (
      declare (lit (Vec.replicate false)) (
      let elmtMask = head (tail (var 2F)) in
      let curBeat = head (var 2F) in
      -- let op₁ = var 1F in
      let result = var 0F in
      for (toℕ elements) (
        declare op₂ op) ∙
      invoke copyMasked (lit dest ∷ result ∷ curBeat ∷ elmtMask ∷ [])
      ))) ∙end
    where
    op₂ =
      -- let elmtMast = head (tail (var 3F)) in
      let curBeat = head (var 3F) in
      -- let op₁ = var 2F in
      -- let result = var 1F in
      let i = var 0F in
      [ (λ src₂ → index-32 size (index (! R) (lit src₂)) i)
      , (λ src₂ → index-32 size (! Q[ lit src₂ , curBeat ]) i)
      ]′ src₂

  vec-op₂ : Function State (bits (toℕ esize) ∷ bits (toℕ esize) ∷ []) (bits (toℕ esize)) → Procedure State []
  vec-op₂ op = vec-op₂′ (
    let op₁ = var 3F in
    let result = var 2F in
    let i = var 1F in
    let op₂ = var 0F in
    *index-32 size result i ≔ call op (index-32 size op₁ i ∷ op₂ ∷ []))

vadd : Instr.VAdd → Procedure State []
vadd d = vec-op₂ d (init call (sliceⁱ 0) ((call uint (var 0F ∷ []) + call uint (var 1F ∷ [])) ∷ []) ∙ skip end)

vsub : Instr.VSub → Procedure State []
vsub d = vec-op₂ d (init call (sliceⁱ 0) ((call uint (var 0F ∷ []) - call uint (var 1F ∷ [])) ∷ []) ∙ skip end)

vhsub : Instr.VHSub → Procedure State []
vhsub d = vec-op₂ op₂ (init call (sliceⁱ 1) ((toInt (var 0F) - toInt (var 1F)) ∷ []) ∙ skip end)
  where open Instr.VHSub d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vmul : Instr.VMul → Procedure State []
vmul d = vec-op₂ d (init call (sliceⁱ 0) ((call sint (var 0F ∷ []) * call sint (var 1F ∷ [])) ∷ []) ∙ skip end)

vmulh : Instr.VMulH → Procedure State []
vmulh d = vec-op₂ op₂ (init call (sliceⁱ (toℕ esize)) ((toInt (var 0F) * toInt (var 1F)) ∷ []) ∙ skip end)
  where
  open Instr.VMulH d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vrmulh : Instr.VRMulH → Procedure State []
vrmulh d = vec-op₂ op₂ (init call (sliceⁱ (toℕ esize)) ((toInt (var 0F) * toInt (var 1F) + lit 1ℤ << toℕ esize-1) ∷ []) ∙ skip end)
  where
  open Instr.VRMulH d; toInt = λ i → call Int (i ∷ lit unsigned ∷ [])

vmla : Instr.VMlA → Procedure State []
vmla d = vec-op₂ op₂ (init call (sliceⁱ (toℕ esize)) ((toInt (var 0F) * element₂ + toInt (var 1F)) ∷ [])∙ skip end)
  where
  open Instr.VMlA d
  op₂ = record { size = size ; dest = acc ; src₁ = src₁ ; src₂ = inj₂ acc }
  toInt = λ i → call Int (i ∷ lit unsigned ∷ [])
  element₂ = toInt (index-32 size (index (! R) (lit src₂)) (lit 0F))

private
  vqr?dmulh : Instr.VQDMulH → Function State (int ∷ int ∷ []) int → Procedure State []
  vqr?dmulh d f = vec-op₂′ d (
    let op₁ = var 3F in
    let i = var 1F in
    let op₂ = var 0F in
    declare (call f (call sint (index-32 size op₁ i ∷ []) ∷ call sint (op₂ ∷ []) ∷ [])) (
    declare (call (SignedSatQ (toℕ esize-1)) (var 0F ∷ [])) (
      let elmtMask = head (tail (var 6F)) in
      let result = var 4F in
      let i = var 3F in
      let sat = head (tail (var 0F)) in
      let result′ = head (var 0F) in
      *index-32 size result i ≔ result′ ∙
      if sat && hasBit elmtMask (fin e*esize>>3 (tup (i ∷ [])))
      then
        FPSCR-QC ≔ lit true)
    ))
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
vqdmulh d = vqr?dmulh d (init lit (ℤ.+ 2) * var 0F * var 1F >> toℕ esize ∙ skip end)
  where open Instr.VecOp₂ d using (esize)

vqrdmulh : Instr.VQRDMulH → Procedure State []
vqrdmulh d = vqr?dmulh d (init lit (ℤ.+ 2) * var 0F * var 1F + lit 1ℤ << toℕ esize-1 >> toℕ esize ∙ skip end)
  where open Instr.VecOp₂ d using (esize; esize-1)
