------------------------------------------------------------------------
-- Agda Helium
--
-- Denotational semantics of Armv8-M instructions.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode

module Helium.Semantics.Denotational
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Algebra.Core using (Op₂)
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Fin as Fin hiding (cast; lift; _+_)
import Data.Fin.Properties as Finₚ
open import Data.List using (List; []; _∷_)
open import Data.Nat hiding (_⊔_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; dmap)
open import Data.Sum using ([_,_]′)
open import Data.Vec.Functional as V using (Vector)
open import Function using (_$_; _∘₂_)
open import Function.Nary.NonDependent.Base
import Helium.Instructions as Instr
import Helium.Semantics.Denotational.Core as Core
open import Level hiding (lift; zero; suc)
open import Relation.Binary using (Transitive)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

open RawPseudocode pseudocode

private
  ℓ : Level
  ℓ = b₁

record State : Set ℓ where
  field
    S : Vector (Bits 32) 32
    R : Vector (Bits 32) 16
    P0 : Bits 16
    mask : Bits 8
    QC : Bits 1
    advanceVPT : Bool

open Core State

Beat : Set
Beat = Fin 4

hilow : Beat → Fin 2
hilow zero          = zero
hilow (suc zero)    = zero
hilow (suc (suc _)) = suc zero

oddeven : Beat → Fin 2
oddeven zero                   = zero
oddeven (suc zero)             = suc zero
oddeven (suc (suc zero))       = zero
oddeven (suc (suc (suc zero))) = suc zero

ElmtMask : Set b₁
ElmtMask = Bits 4

-- State properties

&R : ∀ {n ls} {Γ : Sets n ls} → PureExpr n Γ (Fin 16) → Reference n Γ (Bits 32)
&R e = record
  { get = λ σ ρ → State.R σ (e σ ρ)
  ; set = λ x σ ρ → record σ { R = V.updateAt (e σ ρ) (λ _ → x) (State.R σ) } , ρ
  }

&S : ∀ {n ls} {Γ : Sets n ls} → PureExpr n Γ (Fin 32) → Reference n Γ (Bits 32)
&S e = record
  { get = λ σ ρ → State.S σ (e σ ρ)
  ; set = λ x σ ρ → record σ { S = V.updateAt (e σ ρ) (λ _ → x) (State.S σ) } , ρ
  }

&Q : ∀ {n ls} {Γ : Sets n ls} → PureExpr n Γ Instr.VecReg → PureExpr n Γ Beat → Reference n Γ (Bits 32)
&Q reg beat = &S λ σ ρ → combine (reg σ ρ) (beat σ ρ)

&FPSCR-QC : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ (Bits 1)
&FPSCR-QC = record
  { get = λ σ ρ → State.QC σ
  ; set = λ x σ ρ → record σ { QC = x } , ρ
  }

&VPR-P0 : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ (Bits 16)
&VPR-P0 = record
  { get = λ σ ρ → State.P0 σ
  ; set = λ x σ ρ → record σ { P0 = x } , ρ
  }

&VPR-mask : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ (Bits 8)
&VPR-mask = record
  { get = λ σ ρ → State.mask σ
  ; set = λ x σ ρ → record σ { mask = x } , ρ
  }

&AdvanceVPT : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ Bool
&AdvanceVPT = record
  { get = λ σ ρ → State.advanceVPT σ
  ; set = λ x σ ρ → record σ { advanceVPT = x } , ρ
  }

-- Reference properties

&cast : ∀ {k m n ls} {Γ : Sets n ls} → .(eq : k ≡ m) → Reference n Γ (Bits k) → Reference n Γ (Bits m)
&cast eq &v = record
  { get = λ σ ρ → cast eq (Reference.get &v σ ρ)
  ; set = λ x σ ρ → Reference.set &v (cast (sym eq) x) σ ρ
  }

slice : ∀ {k m n ls} {Γ : Sets n ls} → Reference n Γ (Bits m) → PureExpr n Γ (∃ λ (i : Fin (suc m)) → ∃ λ j → toℕ (i - j) ≡ k) → Reference n Γ (Bits k)
slice &v idx = record
  { get = λ σ ρ → let (i , j , i-j≡k) = idx σ ρ in cast i-j≡k (sliceᵇ i j (Reference.get &v σ ρ))
  ; set = λ v σ ρ →
    let (i , j , i-j≡k) = idx σ ρ in
    Reference.set &v (updateᵇ i j (cast (sym (i-j≡k)) v) (Reference.get &v σ ρ)) σ ρ
  }

elem : ∀ {k n ls} {Γ : Sets n ls} m → Reference n Γ (Bits (k * m)) → PureExpr n Γ (Fin k) → Reference n Γ (Bits m)
elem m &v idx = slice &v (λ σ ρ → helper _ _ (idx σ ρ))
  where
  helper : ∀ m n → Fin m → ∃ λ (i : Fin (suc (m * n))) → ∃ λ j → toℕ (i - j) ≡ n
  helper (suc m) n zero    = inject+ (m * n) (fromℕ n) , # 0 , eq
    where
    eq = trans (sym (Finₚ.toℕ-inject+ (m * n) (fromℕ n))) (Finₚ.toℕ-fromℕ n)
  helper (suc m) n (suc i) with x , y , x-y≡n ← helper m n i =
      u ,
      v ,
      trans
        (cast‿- (raise n x) (Fin.cast eq₂ (raise n y)) eq₁)
        (trans (raise‿- (suc (m * n)) n x y eq₂) x-y≡n)
    where
    eq₁ = ℕₚ.+-suc n (m * n)
    eq₂ = trans (ℕₚ.+-suc n (toℕ x)) (cong suc (sym (Finₚ.toℕ-raise n x)))
    eq₂′ = cong suc (sym (Finₚ.toℕ-cast eq₁ (raise n x)))
    u = Fin.cast eq₁ (raise n x)
    v = Fin.cast eq₂′ (Fin.cast eq₂ (raise n y))

    raise‿- : ∀ m n (x : Fin m) y .(eq : n + suc (toℕ x) ≡ suc (toℕ (raise n x))) → toℕ (raise n x - Fin.cast eq (raise n y)) ≡ toℕ (x - y)
    raise‿- m       ℕ.zero  x       zero    _ = refl
    raise‿- (suc m) ℕ.zero  (suc x) (suc y) p = raise‿- m ℕ.zero x y (ℕₚ.suc-injective p)
    raise‿- m       (suc n) x       y       p = raise‿- m n x y (ℕₚ.suc-injective p)

    cast‿- : ∀ {m n} (x : Fin m) y .(eq : m ≡ n) → toℕ (Fin.cast eq x - Fin.cast (cong suc (sym (Finₚ.toℕ-cast eq x))) y) ≡ toℕ (x - y)
    cast‿- {suc m} {suc n} x       zero    eq = Finₚ.toℕ-cast eq x
    cast‿- {suc m} {suc n} (suc x) (suc y) eq = cast‿- x y (ℕₚ.suc-injective eq)

-- General functions

copyMasked : Instr.VecReg → Procedure 3 (Bits 32 , Beat , ElmtMask , _)
copyMasked dest =
  for 4 (
    -- 0:e 1:result 2:beat 3:elmtMask
    if ⦇ (λ x y → does (getᵇ y x ≟ᵇ 1b)) (↓ !# 3) (↓ !# 0) ⦈
    then
      elem 8 (&Q (pure′ dest) (!# 2)) (!# 0) ≔ ↓! elem 8 (var (# 1)) (!# 0)
    else skip) ∙
  ⦇ _ ⦈

module fun-sliceᶻ
  (≈ᶻ-trans : Transitive _≈ᶻ_)
  (round∘float : ∀ x → x ≈ᶻ round (float x))
  (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
  (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
  (2^n≢0 : ∀ n → False (2ℤ ^ᶻ n ≟ᶻ 0ℤ))
  (*ᶻ-identityʳ : ∀ x → x *ᶻ 1ℤ ≈ᶻ x)
  where

  open sliceᶻ ≈ᶻ-trans round∘float round-cong 0#-homo-round 2^n≢0 *ᶻ-identityʳ

  signedSatQ : ∀ n → Function 1 (ℤ , _) (Bits (suc n) × Bool)
  signedSatQ n = declare ⦇ true ⦈ $
    -- 0:sat 1:x
    if ⦇ (λ i → does (1ℤ << n +ᶻ -ᶻ 1ℤ <?ᶻ i)) (↓ !# 1) ⦈
    then
      var (# 1) ≔ ⦇ (1ℤ << n +ᶻ -ᶻ 1ℤ) ⦈
    else if ⦇ (λ i → does (-ᶻ 1ℤ << n <?ᶻ i)) (↓ !# 1) ⦈
    then
      var (# 1) ≔ ⦇ (-ᶻ 1ℤ << n) ⦈
    else
      var (# 0) ≔ ⦇ false ⦈ ∙
    ⦇ ⦇ (sliceᶻ (suc n) zero) (↓ !# 1) ⦈ , (↓ !# 0) ⦈

advanceVPT : Procedure 1 (Beat , _)
advanceVPT = declare (↓! elem 4 &VPR-mask (hilow ∘₂ !# 0)) $
  -- 0:vptState 1:beat
  if ⦇ (λ x → does (x ≟ᵇ 1b ∶ 0b ∶ 0b ∶ 0b)) (↓ !# 0) ⦈
  then
    var (# 0) ≔ ⦇ zeros ⦈
  else if ⦇ (λ x → does (x ≟ᵇ zeros {4})) (↓ !# 0) ⦈
  then skip
  else (
    if ⦇ (hasBit (# 3)) (↓ !# 0) ⦈
    then
      elem 4 &VPR-P0 (!# 1) ⟵ not
    else skip ∙
    (var (# 0) ⟵ λ x → sliceᵇ (# 3) zero x ∶ 0b)) ∙
  if ⦇ (λ x → does (oddeven x Finₚ.≟ # 1)) (↓ !# 1) ⦈
  then
    elem 4 &VPR-mask (hilow ∘₂ !# 1) ≔ ↓ !# 0
  else skip ∙
  ⦇ _ ⦈

execBeats : Procedure 2 (Beat , ElmtMask , _) → Procedure 0 _
execBeats inst = declare ⦇ ones ⦈ $
  for 4 (
    -- 0:beat 1:elmtMask
    if ⦇ (λ x → does (x ≟ᵇ zeros {4})) (↓! elem 4 &VPR-mask (hilow ∘₂ !# 0)) ⦈
    then
      var (# 1) ≔ ⦇ ones ⦈
    else
      var (# 1) ≔ ↓! elem 4 &VPR-P0 (!# 0) ∙
    &AdvanceVPT ≔ ⦇ true ⦈ ∙
    invoke inst ⦇ ↓ !# 0 , ↓ !# 1 ⦈ ∙
    if ↓! &AdvanceVPT
    then
      invoke advanceVPT (↓ !# 0)
    else skip) ∙
  ⦇ _ ⦈

module _
  (d : Instr.VecOp₂)
  where

  open Instr.VecOp₂ d

  vec-op₂ : Op₂ (Bits (toℕ esize)) → Procedure 2 (Beat , ElmtMask , _)
  vec-op₂ op = declare ⦇ zeros ⦈ $ declare (↓! &Q (pure′ src₁) (!# 1)) $
    for (toℕ elements) (
      -- 0:e 1:op₁ 2:result 3:beat 4:elmntMask
      elem (toℕ esize) (&cast (sym e*e≡32) (var (# 2))) (!# 0) ≔
        (⦇ op
           (↓! elem (toℕ esize) (&cast (sym e*e≡32) (var (# 1))) (!# 0))
           ([ (λ src₂ → ↓! slice (&R (pure′ src₂)) (pure′ (esize , zero , refl)))
            , (λ src₂ → ↓! elem (toℕ esize) (&cast (sym e*e≡32) (&Q (pure′ src₂) (!# 3))) (!# 0))
            ]′ src₂) ⦈)) ∙
    invoke (copyMasked dest) ⦇ ↓ !# 1 , ⦇ ↓ !# 2 , ↓ !# 3 ⦈ ⦈ ∙
    ⦇ _ ⦈

-- Instruction semantics

module _
  (≈ᶻ-trans : Transitive _≈ᶻ_)
  (round∘float : ∀ x → x ≈ᶻ round (float x))
  (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
  (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
  (2^n≢0 : ∀ n → False (2ℤ ^ᶻ n ≟ᶻ 0ℤ))
  (*ᶻ-identityʳ : ∀ x → x *ᶻ 1ℤ ≈ᶻ x)
  where

  open sliceᶻ ≈ᶻ-trans round∘float round-cong 0#-homo-round 2^n≢0 *ᶻ-identityʳ
  open fun-sliceᶻ ≈ᶻ-trans round∘float round-cong 0#-homo-round 2^n≢0 *ᶻ-identityʳ

  vadd : Instr.VAdd → Procedure 2 (Beat , ElmtMask , _)
  vadd d = vec-op₂ d (λ x y → sliceᶻ _ zero (uint x +ᶻ uint y))

  vsub : Instr.VSub → Procedure 2 (Beat , ElmtMask , _)
  vsub d = vec-op₂ d (λ x y → sliceᶻ _ zero (uint x +ᶻ -ᶻ uint y))

  vhsub : Instr.VHSub → Procedure 2 (Beat , ElmtMask , _)
  vhsub d = vec-op₂ op₂ (λ x y → sliceᶻ _ (suc zero) (int x +ᶻ -ᶻ int y))
    where open Instr.VHSub d ; int = Bool.if unsigned then uint else sint

  vmul : Instr.VMul → Procedure 2 (Beat , ElmtMask , _)
  vmul d = vec-op₂ d (λ x y → sliceᶻ _ zero (sint x *ᶻ sint y))

  vmulh : Instr.VMulH → Procedure 2 (Beat , ElmtMask , _)
  vmulh d = vec-op₂ op₂ (λ x y → cast (eq _ esize) (sliceᶻ 2esize esize′ (int x *ᶻ int y +ᶻ rval)))
    where
    open Instr.VMulH d
    int = Bool.if unsigned then uint else sint
    rval = Bool.if rounding then 1ℤ << toℕ esize-1 else 0ℤ
    2esize = toℕ esize + toℕ esize
    esize′ = inject+ _ (strengthen esize)
    eq : ∀ {n} m (i : Fin n) → toℕ i + m ℕ-ℕ inject+ m (strengthen i) ≡ m
    eq m zero    = refl
    eq m (suc i) = eq m i

  vqdmulh : Instr.VQDMulH → Procedure 2 (Beat , ElmtMask , _)
  vqdmulh d = declare ⦇ zeros ⦈ $ declare (↓! &Q (pure′ src₁) (!# 1)) $ declare ⦇ false ⦈ $
    for (toℕ elements) (
      -- 0:e 1:sat 2:op₁ 3:result 4:beat 5:elmntMask
      elem (toℕ esize) (&cast (sym e*e≡32) (var (# 3))) (!# 0) ,′ var (# 1) ≔
      call (signedSatQ (toℕ esize-1))
           ⦇ (λ x y → (2ℤ *ᶻ sint x *ᶻ sint y +ᶻ rval) >> toℕ esize)
             (↓! elem (toℕ esize) (&cast (sym e*e≡32) (var (# 2))) (!# 0))
             ([ (λ src₂ → ↓! slice (&R (pure′ src₂)) (pure′ (esize , zero , refl)))
              , (λ src₂ → ↓! elem (toℕ esize) (&cast (sym e*e≡32) (&Q (pure′ src₂) (!# 4))) (!# 0))
              ]′ src₂) ⦈ ∙
      if ↓ !# 1
      then if ⦇ (λ m e → hasBit (combine e zero) (cast (sym e*e>>3≡4) m)) (↓ !# 5) (↓ !# 0) ⦈
      then
        &FPSCR-QC ≔ ⦇ 1b ⦈
      else skip
      else skip) ∙
    invoke (copyMasked dest) ⦇ ↓ !# 2 , ⦇ ↓ !# 3 , ↓ !# 4 ⦈ ⦈ ∙
    ⦇ _ ⦈
    where
    open Instr.VQDMulH d
    rval = Bool.if rounding then 1ℤ << toℕ esize-1 else 0ℤ

  ⟦_⟧₁ : Instr.Instruction → Procedure 0 _
  ⟦ Instr.vadd x ⟧₁ = execBeats (vadd x)
  ⟦ Instr.vsub x ⟧₁ = execBeats (vsub x)
  ⟦ Instr.vmul x ⟧₁ = execBeats (vmul x)
  ⟦ Instr.vmulh x ⟧₁ = execBeats (vmulh x)
  ⟦ Instr.vqdmulh x ⟧₁ = execBeats (vqdmulh x)

  ⟦_⟧ : List (Instr.Instruction) → Procedure 0 _
  ⟦ [] ⟧     = ⦇ _ ⦈
  ⟦ i ∷ is ⟧ = invoke ⟦ i ⟧₁ ⦇ _ ⦈ ∙ ⟦ is ⟧
