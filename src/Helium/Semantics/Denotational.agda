{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode

module Helium.Semantics.Denotational
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Data.Bool as Bool using (Bool)
open import Data.Fin as Fin hiding (cast; lift; _+_)
import Data.Fin.Properties as Finₚ
open import Data.Maybe using (just; nothing; _>>=_)
open import Data.Nat hiding (_⊔_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _,_; dmap)
open import Data.Sum using ([_,_]′)
open import Data.Vec.Functional as V using (Vector)
open import Function.Nary.NonDependent.Base
open import Helium.Instructions
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

open Core State

Beat : Set
Beat = Fin 4

ElmtMask : Set b₁
ElmtMask = Bits 4

-- State properties

&R : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ (Fin 16) → Reference n Γ (Bits 32)
&R e = record
  { get = λ σ ρ → e σ ρ >>= λ (σ , i) → just (σ , State.R σ i)
  ; set = λ σ ρ x → e σ ρ >>= λ (σ , i) → just (record σ { R = V.updateAt i (λ _ → x) (State.R σ) } , ρ)
  }

&S : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ (Fin 32) → Reference n Γ (Bits 32)
&S e = record
  { get = λ σ ρ → e σ ρ >>= λ (σ , i) → just (σ , State.S σ i)
  ; set = λ σ ρ x → e σ ρ >>= λ (σ , i) → just (record σ { S = V.updateAt i (λ _ → x) (State.S σ) } , ρ)
  }

&Q : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ VecReg → Expr n Γ Beat → Reference n Γ (Bits 32)
&Q reg beat = &S (λ σ ρ → reg σ ρ >>= λ (σ , reg) → beat σ ρ >>= λ (σ , beat) → just (σ , combine reg beat))

-- Reference properties

&cast : ∀ {k m n ls} {Γ : Sets n ls} → .(eq : k ≡ m) → Reference n Γ (Bits k) → Reference n Γ (Bits m)
&cast eq &v = record
  { get = λ σ ρ → Reference.get &v σ ρ >>= λ (σ , v) → just (σ , cast eq v)
  ; set = λ σ ρ x → Reference.set &v σ ρ (cast (sym eq) x)
  }

slice : ∀ {k m n ls} {Γ : Sets n ls} → Reference n Γ (Bits m) → Expr n Γ (∃ λ (i : Fin (suc m)) → ∃ λ j → toℕ (i - j) ≡ k) → Reference n Γ (Bits k)
slice &v idx = record
  { get = λ σ ρ → Reference.get &v σ ρ >>= λ (σ , v) → idx σ ρ >>= λ (σ , i , j , i-j≡k) → just (σ , cast i-j≡k (sliceᵇ i j v))
  ; set = λ σ ρ v → Reference.get &v σ ρ >>= λ (σ , v′) → idx σ ρ >>= λ (σ , i , j , i-j≡k) → Reference.set &v σ ρ (updateᵇ i j (cast (sym i-j≡k) v) v′)
  }

elem : ∀ {k n ls} {Γ : Sets n ls} m → Reference n Γ (Bits (k * m)) → Expr n Γ (Fin k) → Reference n Γ (Bits m)
elem m &v idx = slice &v λ σ ρ → idx σ ρ >>= λ (σ , i) → just (σ , helper _ _ i)
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

copy-masked : VecReg → Procedure 3 (Bits 32 , Beat , ElmtMask , _)
copy-masked dest = for 4 (lift (
  -- e result beat elmtMask
  if ⦇ (λ x y → does (getᵇ y x ≟ᵇ 1b)) (!# 3) (!# 0) ⦈
  then
    elem 8 (&Q ⦇ dest ⦈ (!# 2)) (!# 0) ≔ (! elem 8 (var (# 1)) (!# 0))
  else
    skip))

-- vec-op₂ : VecReg → GenReg → Op₂ (Bits n)

-- Instruction semantics

module _
  (≈ᶻ-trans : Transitive _≈ᶻ_)
  (round∘⟦⟧ : ∀ x → x ≈ᶻ round ⟦ x ⟧)
  (round-cong : ∀ {x y} → x ≈ʳ y → round x ≈ᶻ round y)
  (0#-homo-round : round 0ℝ ≈ᶻ 0ℤ)
  (2^n≢0 : ∀ n → False (2ℤ ^ᶻ n ≟ᶻ 0ℤ))
  (*ᶻ-identityʳ : ∀ x → x *ᶻ 1ℤ ≈ᶻ x)
  where

  open sliceᶻ ≈ᶻ-trans round∘⟦⟧ round-cong 0#-homo-round 2^n≢0 *ᶻ-identityʳ

  vadd : VAdd.VAdd → Procedure 2 (Beat , ElmtMask , _)
  vadd d = declare ⦇ zeros ⦈ (declare (! &Q ⦇ src₁ ⦈ (!# 1)) (
    -- op₁ result beat elmtMask
    for (toℕ elements) (lift (
      -- e op₁ result beat elmtMask
      elem (toℕ esize) (&cast (sym e*e≡32) (var (# 2))) (!# 0) ≔
      ⦇ _+ᵇ_
        (! elem (toℕ esize) (&cast (sym e*e≡32) (var (# 1))) (!# 0))
        ([ (λ src₂ → ! slice (&R ⦇ src₂ ⦈) ⦇ (esize , zero , refl) ⦈)
         , (λ src₂ → ! elem (toℕ esize) (&cast (sym e*e≡32) (&Q ⦇ src₂ ⦈ (!# 3))) (!# 0))
         ]′ src₂) ⦈
    )) ∙
    ignore (call (copy-masked dest) ⦇ !# 1 , ⦇ !# 2 , !# 3 ⦈ ⦈)))
    where
    open VAdd.VAdd d
    esize = VAdd.esize d
    elements = VAdd.elements d
    e*e≡32 = VAdd.elem*esize≡32 d

  vhsub : VHSub.VHSub → Procedure 2 (Beat , ElmtMask , _)
  vhsub d = declare ⦇ zeros ⦈ (declare (! &Q ⦇ src₁ ⦈ (!# 1)) (
    -- op₁ result beat elmtMask
    for (toℕ elements) (lift (
      -- e op₁ result beat elmtMask
      elem (toℕ esize) (&cast (sym e*e≡32) (var (# 2))) (!# 0) ≔
      ⦇ (λ x y → sliceᶻ (suc (toℕ esize)) (suc zero) (int x +ᶻ -ᶻ int y))
        (! elem (toℕ esize) (&cast (sym e*e≡32) (var (# 1))) (!# 0))
        ([ (λ src₂ → ! slice (&R ⦇ src₂ ⦈) ⦇ (esize , zero , refl) ⦈)
         , (λ src₂ → ! elem (toℕ esize) (&cast (sym e*e≡32) (&Q ⦇ src₂ ⦈ (!# 3))) (!# 0))
         ]′ src₂) ⦈
    )) ∙
    ignore (call (copy-masked dest) ⦇ !# 1 , ⦇ !# 2 , !# 3 ⦈ ⦈)))
    where
    open VHSub.VHSub d
    esize = VHSub.esize d
    elements = VHSub.elements d
    e*e≡32 = VHSub.elem*esize≡32 d
    int = Bool.if unsigned then uint else sint

  vmul : VMul.VMul → Procedure 2 (Beat , ElmtMask , _)
  vmul d = declare ⦇ zeros ⦈ (declare (! &Q ⦇ src₁ ⦈ (!# 1)) (
    -- op₁ result beat elmtMask
    for (toℕ elements) (lift (
      -- e op₁ result beat elmtMask
      elem (toℕ esize) (&cast (sym e*e≡32) (var (# 2))) (!# 0) ≔
      ⦇ (λ x y → sliceᶻ (toℕ esize) zero (sint x *ᶻ sint y))
        (! elem (toℕ esize) (&cast (sym e*e≡32) (var (# 1))) (!# 0))
        ([ (λ src₂ → ! slice (&R ⦇ src₂ ⦈) ⦇ (esize , zero , refl) ⦈)
         , (λ src₂ → ! elem (toℕ esize) (&cast (sym e*e≡32) (&Q ⦇ src₂ ⦈ (!# 3))) (!# 0))
         ]′ src₂) ⦈
    )) ∙
    ignore (call (copy-masked dest) ⦇ !# 1 , ⦇ !# 2 , !# 3 ⦈ ⦈)))
    where
    open VMul.VMul d
    esize = VMul.esize d
    elements = VMul.elements d
    e*e≡32 = VMul.elem*esize≡32 d
