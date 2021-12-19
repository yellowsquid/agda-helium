{-# OPTIONS --safe --without-K #-}

module Helium.Data.Numeric where

open import Algebra
open import Algebra.Morphism.Structures
open import Data.Integer as ℤ hiding (_⊔_)
import Data.Integer.DivMod as DivMod
import Data.Integer.Properties as ℤₚ
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Sum using ([_,_]′)
open import Function using (_∘_; id; flip)
open import Helium.Algebra.Field
open import Level renaming (suc to ℓsuc)
open import Relation.Binary
import Relation.Binary.Construct.StrictToNonStrict as STNS
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

module _
  {a ℓ₁ ℓ₂} {A : Set a}
  (_≈_ : Rel A ℓ₁)
  (_<ʳ_ : Rel A ℓ₂)
  where

  record IsReal (_+_ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) (_⁻¹ : ∀ x {≢0 : ¬ x ≈ 0#} → A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isField : IsField _≈_ _+_ _*_ -_ 0# 1# _⁻¹
      isStrictTotalOrder : IsStrictTotalOrder _≈_ _<ʳ_

    open IsField isField public hiding (refl; reflexive; sym; trans)
    open IsStrictTotalOrder isStrictTotalOrder public

  record IsNumeric (+ʳ *ʳ : Op₂ A) (-ʳ : Op₁ A) (0ℝ 1ℝ : A)
                   (⁻¹ : ∀ x {≢0 : ¬ x ≈ 0ℝ} → A)
                   (⟦_⟧ : ℤ → A) (round : A → ℤ)
                   : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    private
      rawRing : RawRing a ℓ₁
      rawRing = record
        { Carrier = A
        ; _≈_ = _≈_
        ; _+_ = +ʳ
        ; _*_ = *ʳ
        ; -_ = -ʳ
        ; 0# = 0ℝ
        ; 1# = 1ℝ
        }

      _≤ʳ_ = STNS._≤_ _≈_ _<ʳ_

    field
      isReal : IsReal +ʳ *ʳ -ʳ 0ℝ 1ℝ ⁻¹
      ⟦⟧-isOrderMonomorphism : IsOrderMonomorphism _≡_ _≈_ _<_ _<ʳ_ ⟦_⟧
      ⟦⟧-isRingHomomorphism : IsRingHomomorphism (Ring.rawRing ℤₚ.+-*-ring) rawRing ⟦_⟧
      round-isOrderHomomorphism : IsOrderHomomorphism _≈_ _≡_ _≤ʳ_ _≤_ round
      round-isRingHomomorphism : IsRingHomomorphism rawRing (Ring.rawRing ℤₚ.+-*-ring) round
      round∘⟦⟧ : ∀ z → round ⟦ z ⟧ ≡ z
      round-down : ∀ {x z} → x <ʳ ⟦ z ⟧ → round x < z

    module real = IsReal isReal
    module ⟦⟧-order = IsOrderMonomorphism ⟦⟧-isOrderMonomorphism
    module ⟦⟧-ring = IsRingHomomorphism ⟦⟧-isRingHomomorphism
    module round-order = IsOrderHomomorphism round-isOrderHomomorphism
    module round-ring = IsRingHomomorphism round-isRingHomomorphism

private
  foldn : ∀ {a} {A : Set a} → ℕ → Op₁ A → Op₁ A
  foldn zero    f = id
  foldn (suc n) f = f ∘ foldn n f

record Numeric a ℓ₁ ℓ₂ : Set (ℓsuc a ⊔ ℓsuc ℓ₁ ⊔ ℓsuc ℓ₂) where
  infix  10 _⁻¹
  infix  9 _^_ _^ℕ_ _ℤ^ℕ_
  infix  8 -ʳ_
  infixl 7 _*ʳ_ _div_ _div′_ _mod_ _mod′_
  infixl 6 _+ʳ_
  infix  4 _≈ʳ_
  field
    ℝ : Set a
    _≈ʳ_ : Rel ℝ ℓ₁
    _<ʳ_ : Rel ℝ ℓ₂
    _+ʳ_ : Op₂ ℝ
    _*ʳ_ : Op₂ ℝ
    -ʳ_  : Op₁ ℝ
    0ℝ  : ℝ
    1ℝ  : ℝ
    _⁻¹  : ∀ x {≢0 : ¬ x ≈ʳ 0ℝ} → ℝ
    ⟦_⟧  : ℤ → ℝ
    round : ℝ → ℤ
    isNumeric : IsNumeric _≈ʳ_ _<ʳ_ _+ʳ_ _*ʳ_ -ʳ_ 0ℝ 1ℝ _⁻¹ ⟦_⟧ round

  open IsNumeric isNumeric public

  -- div and mod according to the manual
  _div_ : ∀ (x y : ℤ) → {≢0 : False (y ≟ 0ℤ)} → ℤ
  (x div y) {≢0} = round (⟦ x ⟧ *ʳ (⟦ y ⟧ ⁻¹) {⟦y⟧≢0})
    where
    open ≡-Reasoning
    ⟦y⟧≢0 = λ y≡0 → toWitnessFalse ≢0 (begin
      y           ≡˘⟨ round∘⟦⟧ y ⟩
      round ⟦ y ⟧ ≡⟨ round-order.cong y≡0 ⟩
      round 0ℝ    ≡⟨ round-ring.0#-homo ⟩
      0ℤ          ∎)

  _mod_ : ∀ (x y : ℤ) → {≢0 : False (y ≟ 0ℤ)} → ℤ
  (x mod y) {≢0} = x + - (y * ((x div y) {≢0}))

  -- regular integer division and modulus
  _div′_ : ∀ (x y : ℤ) → {≢0 : False (y ≟ 0ℤ)} → ℤ
  (x div′ y) {≢0} = (x DivMod.div y) {fromWitnessFalse (toWitnessFalse ≢0 ∘ ℤₚ.∣n∣≡0⇒n≡0)}

  _mod′_ : ∀ (x y : ℤ) → {≢0 : False (y ≟ 0ℤ)} → ℕ
  (x mod′ y) {≢0} = (x DivMod.mod y) {fromWitnessFalse (toWitnessFalse ≢0 ∘ ℤₚ.∣n∣≡0⇒n≡0)}

  _^ℕ_ : ℝ → ℕ → ℝ
  x ^ℕ zero  = 1ℝ
  x ^ℕ suc n = x *ʳ x ^ℕ n

  _^_ : ∀ x {≢0 : False (x real.≟ 0ℝ)} → ℤ → ℝ
  x ^ +0              = 1ℝ
  x ^ +[1+ n ]        = x ^ℕ (ℕ.suc n)
  _^_ x {≢0} -[1+ n ] = (x ⁻¹) {toWitnessFalse ≢0} ^ℕ (ℕ.suc n)

  _ℤ^ℕ_ : ℤ → ℕ → ℤ
  x ℤ^ℕ zero  = 1ℤ
  x ℤ^ℕ suc y = x * x ℤ^ℕ y

  x^y≡0⇒x≡0 : ∀ x y → x ℤ^ℕ y ≡ 0ℤ → x ≡ 0ℤ
  x^y≡0⇒x≡0 x (suc y) x^y≡0 = [ id , x^y≡0⇒x≡0 x y ]′ (ℤₚ.m*n≡0⇒m≡0∨n≡0 x x^y≡0)

  _<<_ : Op₂ ℤ
  x << +0       = x
  x << +[1+ n ] = x * ((+ 2) ℤ^ℕ (ℕ.suc n))
  x << -[1+ n ] = round (⟦ x ⟧ *ʳ (_^_ ⟦ + 2 ⟧ {≢0} -[1+ n ]))
    where
    open ≡-Reasoning
    ≢0 = fromWitnessFalse (λ 2≡0 → flip contradiction (λ ()) (begin
      + 2           ≡˘⟨ round∘⟦⟧ (+ 2) ⟩
      round ⟦ + 2 ⟧ ≡⟨  round-order.cong 2≡0 ⟩
      round 0ℝ      ≡⟨  round-ring.0#-homo ⟩
      0ℤ            ∎))

  _>>_ : Op₂ ℤ
  x >> n = x << (- n)

  x<<+y≡0⇒x≡0 : ∀ x y → x << (+ y) ≡ 0ℤ → x ≡ 0ℤ
  x<<+y≡0⇒x≡0 x zero eq = eq
  x<<+y≡0⇒x≡0 x (suc y) eq = [ id , flip contradiction (λ ()) ∘ x^y≡0⇒x≡0 (+ 2) (ℕ.suc y) ]′ (ℤₚ.m*n≡0⇒m≡0∨n≡0 x eq)

  hasBit : ∀ (i : ℕ) z →
           let 2<<1+i≢0 = fromWitnessFalse (contraposition (x<<+y≡0⇒x≡0 (+ 2) (ℕ.suc i)) λ ()) in
           Dec (+ (z mod′ (+ 2) << +[1+ i ]) {2<<1+i≢0} ≥ (+ 2) << (+ i))
  hasBit i z = (+ 2) << (+ i) ≤? + (z mod′ (+ 2) << +[1+ i ])
