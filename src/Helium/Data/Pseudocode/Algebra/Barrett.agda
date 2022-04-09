--------------------------------------------------------------------------------
-- Agda Helium
--
-- A proof of correctness for Barrett reduction.
--------------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Data.Pseudocode.Algebra.Barrett
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode

open import Data.Integer using () renaming (+_ to +ℤ_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _,_)
open import Data.Sum using (map)
open import Data.Unit
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Morphism

2ℝ : ℝ
2ℝ = 2 ℝ.× 1ℝ

2ℤ : ℤ
2ℤ = 2 ℤ.× 1ℤ

2>0 : 2ℝ ℝ.> 0ℝ
2>0 = ℝ.n≢0∧x>0⇒n×x>0 2 (ℝ.x≉y⇒0<1 ℝ.1≉0)

2≉0 : 2ℝ ℝ.≉ 0ℝ
2≉0 = ℝ.<⇒≉ 2>0 ∘ ℝ.Eq.sym

1/2 : ℝ
1/2 = 2≉0 ℝ.⁻¹

_mod_ : ∀ (x : ℤ) {y} → y /1 ℝ.≉ 0ℝ → ℤ
_mod_ x {y} y≉0 = x ℤ.- y ℤ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋

module mod where
  congˡ : ∀ x {y} (y≉0 y≉0′ : y /1 ℝ.≉ 0ℝ) → x mod y≉0 ℤ.≈ x mod y≉0′
  congˡ x {y} y≉0 y≉0′ = ℤ.+-congˡ (ℤ.-‿cong (ℤ.*-congˡ (⌊⌋.cong (ℝ.*-congˡ (ℝ.⁻¹-cong ℝ.Eq.refl)))))

  x≥0∧y>0⇒⌊x/y⌋≈[x-x‿mod‿y]/y :
    ∀ {x y} → x ℤ.≥ 0ℤ → (y>0 : y /1 ℝ.> 0ℝ) →
    let y≉0 = ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym in
    ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋ /1 ℝ.≈ (x ℤ.- x mod y≉0) /1 ℝ.* y≉0 ℝ.⁻¹
  x≥0∧y>0⇒⌊x/y⌋≈[x-x‿mod‿y]/y {x} {y} x≥0 y>0 = begin-equality
    lhs /1                            ≈˘⟨ ℝ.*-identityˡ _ ⟩
    1ℝ ℝ.* lhs /1                     ≈˘⟨ ℝ.*-congʳ (ℝ.⁻¹-inverseˡ y≉0) ⟩
    y≉0 ℝ.⁻¹ ℝ.* y /1 ℝ.* lhs /1      ≈⟨  ℝ.*-assoc _ _ _ ⟩
    y≉0 ℝ.⁻¹ ℝ.* (y /1 ℝ.* lhs /1)    ≈⟨  ℝ.*-comm _ _ ⟩
    y /1 ℝ.* lhs /1 ℝ.* y≉0 ℝ.⁻¹      ≈˘⟨ ℝ.*-congʳ (/1.*-homo y lhs) ⟩
    (y ℤ.* lhs) /1 ℝ.* y≉0 ℝ.⁻¹       ≈⟨  ℝ.*-congʳ (begin-equality
      (y ℤ.* lhs) /1                               ≈˘⟨ ℝ.-‿involutive _ ⟩
      ℝ.- ℝ.- (y ℤ.* lhs) /1                       ≈˘⟨ ℝ.-‿cong (/1.-‿homo _) ⟩
      ℝ.- (ℤ.- (y ℤ.* lhs)) /1                     ≈˘⟨ ℝ.+-identityˡ _ ⟩
      0ℝ ℝ.- (ℤ.- (y ℤ.* lhs)) /1                  ≈˘⟨ ℝ.+-congʳ (ℝ.-‿inverseʳ _) ⟩
      x /1 ℝ.- x /1 ℝ.- (ℤ.- (y ℤ.* lhs)) /1       ≈⟨  ℝ.+-assoc _ _ _ ⟩
      x /1 ℝ.+ (ℝ.- x /1 ℝ.- (ℤ.- (y ℤ.* lhs)) /1) ≈⟨  ℝ.+-congˡ (ℝ.-‿+-comm _ _) ⟩
      x /1 ℝ.- (x /1 ℝ.+ (ℤ.- (y ℤ.* lhs)) /1)     ≈˘⟨ ℝ.+-congˡ (ℝ.-‿cong (/1.+-homo x _)) ⟩
      x /1 ℝ.- (x ℤ.- y ℤ.* lhs) /1                ≡⟨⟩
      x /1 ℝ.- (x mod y≉0) /1                      ≈˘⟨ ℝ.+-congˡ (/1.-‿homo _) ⟩
      x /1 ℝ.+ (ℤ.- x mod y≉0) /1                  ≈˘⟨ /1.+-homo x (ℤ.- x mod y≉0) ⟩
      (x ℤ.- x mod y≉0) /1                         ∎) ⟩
    (x ℤ.- x mod y≉0) /1 ℝ.* y≉0 ℝ.⁻¹ ∎
    where
    open ℝ.Reasoning
    y≉0 = ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym
    lhs = ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋

  x≥0∧y>0⇒x‿mod‿y≥0 : ∀ {x y} → x ℤ.≥ 0ℤ → (y>0 : y /1 ℝ.> 0ℝ) → x mod (ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym) ℤ.≥ 0ℤ
  x≥0∧y>0⇒x‿mod‿y≥0 {x} {y} x≥0 y>0 = ℤ.x≤y⇒0≤y-x (/1.cancel-≤ (begin
    (y ℤ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1  ≈⟨  /1.*-homo y _ ⟩
    y /1 ℝ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋ /1 ≤⟨  ℝ.x≥0⇒*-monoˡ-≤ (ℝ.<⇒≤ y>0) (⌊⌋.⌊x⌋≤x _) ⟩
    y /1 ℝ.* (x /1 ℝ.* y≉0 ℝ.⁻¹)      ≈⟨  ℝ.*-congˡ (ℝ.*-comm (x /1) _) ⟩
    y /1 ℝ.* (y≉0 ℝ.⁻¹ ℝ.* x /1)      ≈˘⟨ ℝ.*-assoc (y /1) _ (x /1) ⟩
    y /1 ℝ.* y≉0 ℝ.⁻¹ ℝ.* x /1        ≈⟨  ℝ.*-congʳ (ℝ.⁻¹-inverseʳ y≉0) ⟩
    1ℝ ℝ.* x /1                       ≈⟨  ℝ.*-identityˡ (x /1) ⟩
    x /1                              ∎))
    where
    open ℝ.Reasoning
    y≉0 = ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym

  x≥0∧y>0⇒x‿mod‿y<y : ∀ {x y} → x ℤ.≥ 0ℤ → (y>0 : y /1 ℝ.> 0ℝ) → x mod (ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym) ℤ.< y
  x≥0∧y>0⇒x‿mod‿y<y {x} {y} x≥0 y>0 = ℤ.x<y+z⇒x-z<y (/1.cancel-< (ℝ.x≥0⇒*-cancelʳ-< y⁻¹≥0 (begin-strict
    x /1 ℝ.* y≉0 ℝ.⁻¹                                          <⟨  ⌊⌋.x<⌊x⌋+1 _ ⟩
    (⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋ ℤ.+ 1ℤ) /1                          ≈⟨  /1.cong (ℤ.+-comm _ 1ℤ) ⟩
    (1ℤ ℤ.+ ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1                          ≈˘⟨ ℝ.*-identityˡ _ ⟩
    1ℝ ℝ.* (1ℤ ℤ.+ ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1                   ≈˘⟨ ℝ.*-congʳ (ℝ.⁻¹-inverseˡ y≉0) ⟩
    y≉0 ℝ.⁻¹ ℝ.* y /1 ℝ.* (1ℤ ℤ.+ ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1    ≈⟨  ℝ.*-assoc _ _ _ ⟩
    y≉0 ℝ.⁻¹ ℝ.* (y /1 ℝ.* (1ℤ ℤ.+ ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1)  ≈˘⟨ ℝ.*-congˡ (/1.*-homo y _) ⟩
    y≉0 ℝ.⁻¹ ℝ.* (y ℤ.* (1ℤ ℤ.+ ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋)) /1     ≈⟨  ℝ.*-congˡ (/1.cong (ℤ.distribˡ y 1ℤ _)) ⟩
    y≉0 ℝ.⁻¹ ℝ.* (y ℤ.* 1ℤ ℤ.+ y ℤ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1 ≈⟨  ℝ.*-congˡ (/1.cong (ℤ.+-congʳ (ℤ.*-identityʳ y))) ⟩
    y≉0 ℝ.⁻¹ ℝ.* (y ℤ.+ y ℤ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1        ≈⟨  ℝ.*-comm _ _ ⟩
    (y ℤ.+ y ℤ.* ⌊ x /1 ℝ.* y≉0 ℝ.⁻¹ ⌋) /1 ℝ.* y≉0 ℝ.⁻¹        ∎)))
    where
    open ℝ.Reasoning
    y≉0 = ℝ.<⇒≉ y>0 ∘ ℝ.Eq.sym
    y⁻¹≥0 = ℝ.<⇒≤ (ℝ.x>0⇒x⁻¹>0 y>0)

module Flooring (k : ℕ) (n : ℤ) (n>0 : n ℤ.> 0ℤ)
  where

  n>0′ : n /1 ℝ.> 0ℝ
  n>0′ = ⌊⌋.cancel-< (begin-strict
   ⌊ 0ℝ ⌋   ≈⟨  ⌊⌋.0#-homo ⟩
   0ℤ       <⟨  n>0 ⟩
   n        ≈˘⟨ ⌊x/1⌋≈x n ⟩
   ⌊ n /1 ⌋ ∎)
    where open ℤ.Reasoning

  n≉0′ : n /1 ℝ.≉ 0ℝ
  n≉0′ = ℝ.<⇒≉ n>0′ ∘ ℝ.Eq.sym

  barrett-coeff : ℤ
  barrett-coeff = ⌊ 2ℝ ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ⌋

  barrett : ℤ → ℤ
  barrett z = z ℤ.- ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ ℤ.* n

  barrett-mods : ∀ z → ∃ λ a → barrett z ℤ.+ a ℤ.* n ℤ.≈ z
  barrett-mods z = q , (begin-equality
    z ℤ.- q ℤ.* n ℤ.+ q ℤ.* n         ≈⟨ ℤ.+-assoc z (ℤ.- (q ℤ.* n)) (q ℤ.* n) ⟩
    z ℤ.+ (ℤ.- (q ℤ.* n) ℤ.+ q ℤ.* n) ≈⟨ ℤ.+-congˡ (ℤ.-‿inverseˡ (q ℤ.* n)) ⟩
    z ℤ.+ 0ℤ                          ≈⟨ ℤ.+-identityʳ z ⟩
    z                                 ∎)
    where
    open ℤ.Reasoning
    q = ⌊ ((z ℤ.* barrett-coeff) /1) ℝ.* 1/2 ℝ.^ k ⌋

  barrett-positive : ∀ {z} → z ℤ.≥ 0ℤ → barrett z ℤ.≥ 0ℤ
  barrett-positive {z} z≥0 = ℤ.x≤y⇒0≤y-x (/1.cancel-≤ ( begin
   (⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ ℤ.* n) /1  ≈⟨ /1.*-homo _ _ ⟩
   ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ /1 ℝ.* n /1 ≤⟨ ℝ.x≥0⇒*-monoʳ-≤ (ℝ.<⇒≤ n>0′) (begin
     ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ /1 ≤⟨ ⌊⌋.⌊x⌋≤x _ ⟩
     (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k        ≈⟨ ℝ.*-congʳ (/1.*-homo z barrett-coeff) ⟩
     z /1 ℝ.* barrett-coeff /1 ℝ.* 1/2 ℝ.^ k       ≈⟨ ℝ.*-assoc _ _ _ ⟩
     z /1 ℝ.* (barrett-coeff /1 ℝ.* 1/2 ℝ.^ k)     ≤⟨ ℝ.x≥0⇒*-monoˡ-≤ z/1≥0 (begin
       ⌊ 2ℝ ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ⌋ /1 ℝ.* 1/2 ℝ.^ k ≤⟨  ℝ.x≥0⇒*-monoʳ-≤ 1/2ᵏ≥0 (⌊⌋.⌊x⌋≤x _) ⟩
       2ℝ ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ℝ.* 1/2 ℝ.^ k        ≈⟨  ℝ.*-congʳ (ℝ.*-comm _ _) ⟩
       n≉0′ ℝ.⁻¹ ℝ.* 2ℝ ℝ.^ k ℝ.* 1/2 ℝ.^ k        ≈⟨  ℝ.*-assoc _ _ _ ⟩
       n≉0′ ℝ.⁻¹ ℝ.* (2ℝ ℝ.^ k ℝ.* 1/2 ℝ.^ k)      ≈˘⟨ ℝ.*-congˡ (ℝ.^-distrib-* 2ℝ 1/2 k) ⟩
       n≉0′ ℝ.⁻¹ ℝ.* (2ℝ ℝ.* 1/2) ℝ.^ k            ≈⟨  ℝ.*-congˡ (ℝ.^-congˡ k (ℝ.⁻¹-inverseʳ 2≉0)) ⟩
       n≉0′ ℝ.⁻¹ ℝ.* 1ℝ ℝ.^ k                      ≈⟨  ℝ.*-congˡ (ℝ.^-zeroˡ k) ⟩
       n≉0′ ℝ.⁻¹ ℝ.* 1ℝ                            ≈⟨  ℝ.*-identityʳ (n≉0′ ℝ.⁻¹) ⟩
       n≉0′ ℝ.⁻¹                                   ∎) ⟩
     z /1 ℝ.* n≉0′ ℝ.⁻¹                            ∎) ⟩
   z /1 ℝ.* n≉0′ ℝ.⁻¹ ℝ.* n /1                            ≈⟨ ℝ.*-assoc (z /1) (n≉0′ ℝ.⁻¹) (n /1) ⟩
   z /1 ℝ.* (n≉0′ ℝ.⁻¹ ℝ.* n /1)                          ≈⟨ ℝ.*-congˡ (ℝ.⁻¹-inverseˡ n≉0′) ⟩
   z /1 ℝ.* 1ℝ                                            ≈⟨ ℝ.*-identityʳ (z /1) ⟩
   z /1 ∎))
    where
    open ℝ.Reasoning
    z/1≥0 = ℝ.≤-respˡ-≈ /1.0#-homo (/1.mono-≤ z≥0)
    1/2ᵏ≥0 = ℝ.x≥0⇒x^n≥0 (ℝ.<⇒≤ (ℝ.x>0⇒x⁻¹>0 2>0)) k

  barrett-limit : ∀ {z} → 0ℤ ℤ.≤ z → z ℤ.≤ 2ℤ ℤ.^ k → barrett z ℤ.< 2 ℤ.× n
  barrett-limit {z} 0≤z z≤2ᵏ = /1.cancel-< (begin-strict
    (z ℤ.- ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ ℤ.* n) /1
      ≈⟨ /1.+-homo z _ ⟩
    z /1 ℝ.+ (ℤ.- (⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ ℤ.* n)) /1
      ≈⟨ ℝ.+-congˡ (/1.-‿homo _) ⟩
    z /1 ℝ.- (⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ ℤ.* n) /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (/1.*-homo _ n)) ⟩
    z /1 ℝ.- ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 1/2 ℝ.^ k ⌋ /1 ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (/1.cong (⌊⌋.cong (ℝ.*-congˡ (ℝ.⁻¹-^-comm 2≉0 k)))))) ⟩
    z /1 ℝ.- ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 2ᵏ≉0 ℝ.⁻¹ ⌋ /1 ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (/1.cong (⌊⌋.cong (ℝ.*-congˡ (ℝ.⁻¹-cong 2ℝᵏ≈2ℤᵏ)))))) ⟩
    z /1 ℝ.- ⌊ (z ℤ.* barrett-coeff) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ⌋ /1 ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (mod.x≥0∧y>0⇒⌊x/y⌋≈[x-x‿mod‿y]/y (ℤ.x≥0∧y≥0⇒x*y≥0 0≤z lemma₅) 2ℤᵏ>0))) ⟩
    z /1 ℝ.- (z ℤ.* barrett-coeff ℤ.- (z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (/1.+-homo _ _)))) ⟩
    z /1 ℝ.- ((z ℤ.* barrett-coeff) /1 ℝ.+ (ℤ.- (z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1) ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (ℝ.+-cong (/1.*-homo _ _) (/1.-‿homo _))))) ⟩
    z /1 ℝ.- (z /1 ℝ.* barrett-coeff /1 ℝ.- ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1) ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ lemma₁ _ _ _ _ _ ⟩
    z /1 ℝ.- n /1 ℝ.* barrett-coeff /1 ℝ.* z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈˘⟨ ℝ.+-congʳ (ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (/1.*-homo n barrett-coeff))))) ⟩
    z /1 ℝ.- (n ℤ.* barrett-coeff) /1 ℝ.* z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congʳ (ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (/1.cong lemma₂))))) ⟩
    z /1 ℝ.- (2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.* z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congʳ (ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (/1.+-homo _ _))))) ⟩
    z /1 ℝ.- ((2ℤ ℤ.^ k) /1 ℝ.+ (ℤ.- ((2ℤ ℤ.^ k) mod n≉0′)) /1) ℝ.* z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congʳ (ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.*-congʳ (ℝ.+-congˡ (/1.-‿homo _)))))) ⟩
    z /1 ℝ.- ((2ℤ ℤ.^ k) /1 ℝ.- (((2ℤ ℤ.^ k) mod n≉0′) /1)) ℝ.* z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ lemma₃ _ _ _ _ _ _ ⟩
    z /1 ℝ.- (2ℤ ℤ.^ k) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* z /1 ℝ.+ z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congʳ (ℝ.+-congʳ (ℝ.+-congˡ (ℝ.-‿cong (ℝ.*-congʳ (ℝ.⁻¹-inverseʳ _))))) ⟩
    z /1 ℝ.- 1ℝ ℝ.* z /1 ℝ.+ z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ lemma₄ _ _ _ _ _ ⟩
    z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ ((z ℤ.* barrett-coeff) mod 2ℤᵏ≉0) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.*-congʳ (ℝ.*-congʳ (/1.cong (mod.congˡ _ _ _)))) ⟩
    z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ ((z ℤ.* barrett-coeff) mod (ℝ.<⇒≉ 2ℤᵏ>0 ∘ ℝ.Eq.sym)) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      <⟨ ℝ.+-monoˡ-< (ℝ.x>0⇒*-monoʳ-< n>0′ (ℝ.x>0⇒*-monoʳ-< (ℝ.x>0⇒x⁻¹>0 2ℤᵏ>0) (/1.mono-< (mod.x≥0∧y>0⇒x‿mod‿y<y (ℤ.x≥0∧y≥0⇒x*y≥0 0≤z lemma₅) 2ℤᵏ>0)))) ⟩
    z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ (2ℤ ℤ.^ k) /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* n /1
      ≈⟨ ℝ.+-congˡ (ℝ.*-congʳ (ℝ.⁻¹-inverseʳ 2ℤᵏ≉0)) ⟩
    z /1 ℝ.* 2ℤᵏ≉0 ℝ.⁻¹ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ 1ℝ ℝ.* n /1
      ≤⟨ ℝ.+-monoʳ-≤ (ℝ.x≥0⇒*-monoʳ-≤ (ℝ.≤-respˡ-≈ /1.0#-homo (/1.mono-≤ (mod.x≥0∧y>0⇒x‿mod‿y≥0 2ℤᵏ≥0 n>0′))) (ℝ.y>0∧x≤y⇒x*y⁻¹≤1 2ℤᵏ>0 (/1.mono-≤ z≤2ᵏ))) ⟩
    1ℝ ℝ.* ((2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.+ 1ℝ ℝ.* n /1
      <⟨ ℝ.+-monoʳ-< (ℝ.x>0⇒*-monoˡ-< (ℝ.x≉y⇒0<1 ℝ.1≉0) (/1.mono-< (mod.x≥0∧y>0⇒x‿mod‿y<y (ℤ.<⇒≤ (ℤ.x>0⇒x^n>0 (ℤ.n≢0∧x>0⇒n×x>0 2 (ℤ.x≉y⇒0<1 ℤ.1≉0)) k)) n>0′))) ⟩
    1ℝ ℝ.* n /1 ℝ.+ 1ℝ ℝ.* n /1
      ≈⟨ ℝ.+-cong (ℝ.*-identityˡ _) (ℝ.*-identityˡ _) ⟩
    n /1 ℝ.+ n /1
      ≈˘⟨ /1.+-homo n n ⟩
    (2 ℤ.× n) /1
      ∎)
    where
    open import Helium.Tactic.CommutativeRing.NonReflective ℝ.commutativeRing ℝ.1≉0
    open import Data.List using ([]; _∷_)

    2ᵏ≉0 = 2≉0 ∘ ℝ.x^n≈0⇒x≈0 2ℝ k

    2ℝᵏ≈2ℤᵏ = begin-equality
      2ℝ ℝ.^ k            ≈˘⟨ ℝ.^-congˡ k (ℝ.×-congʳ 2 /1.1#-homo) ⟩
      (2 ℝ.× 1ℤ /1) ℝ.^ k ≈˘⟨ ℝ.^-congˡ k (/1.×-homo 2 1ℤ) ⟩
      2ℤ /1 ℝ.^ k         ≈˘⟨ /1.^-homo 2ℤ k ⟩
      (2ℤ ℤ.^ k) /1       ∎
      where open ℝ.Reasoning

    2ℤᵏ≥0 = ℤ.x≥0⇒x^n≥0 (ℤ.x≥0⇒n×x≥0 2 ℤ.0≤1) k
    2ℤᵏ>0 = ℝ.<-respˡ-≈ /1.0#-homo (/1.mono-< (ℤ.x>0⇒x^n>0 (ℤ.n≢0∧x>0⇒n×x>0 2 (ℤ.x≉y⇒0<1 ℤ.1≉0)) k))

    2ℤᵏ≉0 : (2ℤ ℤ.^ k) /1 ℝ.≉ 0ℝ
    2ℤᵏ≉0 = ℝ.<⇒≉ 2ℤᵏ>0 ∘ ℝ.Eq.sym

    lemma₁ : ∀ z k mod 2⁻ᵏ n → z ℝ.- (z ℝ.* k ℝ.- mod) ℝ.* 2⁻ᵏ ℝ.* n ℝ.≈ z ℝ.- n ℝ.* k ℝ.* z ℝ.* 2⁻ᵏ ℝ.+ mod ℝ.* 2⁻ᵏ ℝ.* n
    lemma₁ = solve 5 (λ z k mod 2⁻ᵏ n → z ⊕ (⊝ ((z ⊗ k ⊕ ⊝ mod) ⊗ 2⁻ᵏ ⊗ n)) ⊜ (z ⊕ ⊝ (n ⊗ k ⊗ z ⊗ 2⁻ᵏ) ⊕ mod ⊗ 2⁻ᵏ ⊗ n)) λ {_ _ _ _ _} → ℝ.Eq.refl


    lemma₂ : n ℤ.* barrett-coeff ℤ.≈ 2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′
    lemma₂ = /1.injective (begin-equality
      (n ℤ.* barrett-coeff) /1                                       ≈⟨  /1.*-homo n barrett-coeff ⟩
      n /1 ℝ.* barrett-coeff /1                                      ≡⟨⟩
      n /1 ℝ.* ⌊ 2ℝ ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ⌋ /1                         ≈˘⟨ ℝ.*-congˡ (/1.cong (⌊⌋.cong (ℝ.*-congʳ (ℝ.^-congˡ k (ℝ.×-congʳ 2 /1.1#-homo))))) ⟩
      n /1 ℝ.* ⌊ (2 ℝ.× 1ℤ /1) ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ⌋ /1              ≈˘⟨ ℝ.*-congˡ (/1.cong (⌊⌋.cong (ℝ.*-congʳ (ℝ.^-congˡ k (/1.×-homo 2 1ℤ))))) ⟩
      n /1 ℝ.* ⌊ (2ℤ /1) ℝ.^ k ℝ.* n≉0′ ℝ.⁻¹ ⌋ /1                    ≈˘⟨ ℝ.*-congˡ (/1.cong (⌊⌋.cong (ℝ.*-congʳ (/1.^-homo 2ℤ k)))) ⟩
      n /1 ℝ.* ⌊ (2ℤ ℤ.^ k) /1 ℝ.* n≉0′ ℝ.⁻¹ ⌋ /1                    ≈⟨  ℝ.*-congˡ (mod.x≥0∧y>0⇒⌊x/y⌋≈[x-x‿mod‿y]/y 2ℤᵏ≥0 n>0′) ⟩
      n /1 ℝ.* ((2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1 ℝ.* n≉0′ ℝ.⁻¹) ≈⟨  ℝ.*-congˡ (ℝ.*-comm _ _) ⟩
      n /1 ℝ.* (n≉0′ ℝ.⁻¹ ℝ.* (2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1) ≈˘⟨ ℝ.*-assoc _ _ _ ⟩
      n /1 ℝ.* n≉0′ ℝ.⁻¹ ℝ.* (2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1   ≈⟨  ℝ.*-congʳ (ℝ.⁻¹-inverseʳ n≉0′) ⟩
      1ℝ ℝ.* (2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1                   ≈⟨  ℝ.*-identityˡ _ ⟩
      (2ℤ ℤ.^ k ℤ.- (2ℤ ℤ.^ k) mod n≉0′) /1                          ∎)
      where open ℝ.Reasoning

    lemma₃ : ∀ z 2ᵏ 2ᵏ-mod-n 2⁻ᵏ zm-mod-2ᵏ n →
             z ℝ.- (2ᵏ ℝ.- 2ᵏ-mod-n) ℝ.* z ℝ.* 2⁻ᵏ ℝ.+ zm-mod-2ᵏ ℝ.* 2⁻ᵏ ℝ.* n ℝ.≈
             z ℝ.- 2ᵏ ℝ.* 2⁻ᵏ ℝ.* z ℝ.+ z ℝ.* 2⁻ᵏ ℝ.* 2ᵏ-mod-n ℝ.+ zm-mod-2ᵏ ℝ.* 2⁻ᵏ ℝ.* n
    lemma₃ = solve 6
      (λ z 2ᵏ 2ᵏ-mod-n 2⁻ᵏ zm-mod-2ᵏ n →
        (z ⊕ ⊝ ((2ᵏ ⊕ ⊝ 2ᵏ-mod-n) ⊗ z ⊗ 2⁻ᵏ) ⊕ zm-mod-2ᵏ ⊗ 2⁻ᵏ ⊗ n) ⊜
        (z ⊕ ⊝ (2ᵏ ⊗ 2⁻ᵏ ⊗ z) ⊕ z ⊗ 2⁻ᵏ ⊗ 2ᵏ-mod-n ⊕ zm-mod-2ᵏ ⊗ 2⁻ᵏ ⊗ n))
      λ {_ _ _ _ _ _} → ℝ.Eq.refl

    lemma₄ : ∀ z 2⁻ᵏ 2ᵏ-mod-n zm-mod-2ᵏ n →
             z ℝ.- 1ℝ ℝ.* z ℝ.+ z ℝ.* 2⁻ᵏ ℝ.* 2ᵏ-mod-n ℝ.+ zm-mod-2ᵏ ℝ.* 2⁻ᵏ ℝ.* n ℝ.≈
             z ℝ.* 2⁻ᵏ ℝ.* 2ᵏ-mod-n ℝ.+ zm-mod-2ᵏ ℝ.* 2⁻ᵏ ℝ.* n
    lemma₄ = solve 5
      (λ z 2⁻ᵏ 2ᵏ-mod-n zm-mod-2ᵏ n →
        (z ⊕ ⊝ (Κ (+ℤ 1) ⊗ z) ⊕ z ⊗ 2⁻ᵏ ⊗ 2ᵏ-mod-n ⊕ zm-mod-2ᵏ ⊗ 2⁻ᵏ ⊗ n) ⊜
        (z ⊗ 2⁻ᵏ ⊗ 2ᵏ-mod-n ⊕ zm-mod-2ᵏ ⊗ 2⁻ᵏ ⊗ n))
      λ {_ _ _ _ _} → ℝ.Eq.refl

    lemma₅ : barrett-coeff ℤ.≥ 0ℤ
    lemma₅ = begin
      0ℤ            ≈˘⟨ ⌊⌋.0#-homo ⟩
      ⌊ 0ℝ ⌋        ≤⟨  ⌊⌋.mono-≤ (ℝ.x≥0∧y≥0⇒x*y≥0 (ℝ.x≥0⇒x^n≥0 (ℝ.<⇒≤ 2>0) k) (ℝ.<⇒≤ (ℝ.x>0⇒x⁻¹>0 n>0′))) ⟩
      barrett-coeff ∎
      where open ℤ.Reasoning

    open ℝ.Reasoning
