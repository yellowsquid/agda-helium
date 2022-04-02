------------------------------------------------------------------------
-- Agda Helium
--
-- Relations between algebraic properties of ordered structures
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Helium.Algebra.Ordered.StrictTotal.Consequences
  {a ℓ₁ ℓ₂}
  (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open StrictTotalOrder strictTotalOrder
  renaming
  ( Carrier to A
  ; trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

open import Helium.Relation.Binary.Properties.StrictTotalOrder strictTotalOrder
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder

open import Algebra.Core
open import Algebra.Definitions
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Function.Definitions
open import Helium.Algebra.Ordered.Definitions
open import Relation.Nullary using (¬_)

----
-- Consequences for a single unary operation
module _ {f : Op₁ A} where
  cong₁+mono₁-<⇒mono₁-≤ : Congruent₁ _≈_ f → Congruent₁ _<_ f → Congruent₁ _≤_ f
  cong₁+mono₁-<⇒mono₁-≤ cong mono (inj₁ x<y) = inj₁ (mono x<y)
  cong₁+mono₁-<⇒mono₁-≤ cong mono (inj₂ x≈y) = inj₂ (cong x≈y)

  cong₁+anti-mono₁-<⇒anti-mono₁-≤ : Congruent₁ _≈_ f → f Preserves _<_ ⟶ _>_ → f Preserves _≤_ ⟶ _≥_
  cong₁+anti-mono₁-<⇒anti-mono₁-≤ cong anti-mono (inj₁ x<y) = inj₁ (anti-mono x<y)
  cong₁+anti-mono₁-<⇒anti-mono₁-≤ cong anti-mono (inj₂ x≈y) = inj₂ (cong (Eq.sym x≈y))

  mono₁-<⇒cancel₁-≤ : Congruent₁ _<_ f → Injective _≤_ _≤_ f
  mono₁-<⇒cancel₁-≤ mono fx≤fy = ≮⇒≥ (≤⇒≯ fx≤fy ∘ mono)

  mono₁-≤⇒cancel₁-< : Congruent₁ _≤_ f → Injective _<_ _<_ f
  mono₁-≤⇒cancel₁-< mono fx<fy = ≰⇒> (<⇒≱ fx<fy ∘ mono)

  cancel₁-<⇒mono₁-≤ : Injective _<_ _<_ f → Congruent₁ _≤_ f
  cancel₁-<⇒mono₁-≤ cancel x≤y = ≮⇒≥ (≤⇒≯ x≤y ∘ cancel)

  cancel₁-≤⇒mono₁-< : Injective _≤_ _≤_ f → Congruent₁ _<_ f
  cancel₁-≤⇒mono₁-< cancel x<y = ≰⇒> (<⇒≱ x<y ∘ cancel)

  anti-mono₁-<⇒anti-cancel₁-≤ : f Preserves _<_ ⟶ _>_ → Injective _≤_ _≥_ f
  anti-mono₁-<⇒anti-cancel₁-≤ anti-mono fx≥fy = ≮⇒≥ (≤⇒≯ fx≥fy ∘ anti-mono)

  anti-mono₁-≤⇒anti-cancel₁-< : f Preserves _≤_ ⟶ _≥_ → Injective _<_ _>_ f
  anti-mono₁-≤⇒anti-cancel₁-< anti-mono fx>fy = ≰⇒> (<⇒≱ fx>fy ∘ anti-mono)

  mono₁-<⇒cancel₁ : Congruent₁ _<_ f → Injective _≈_ _≈_ f
  mono₁-<⇒cancel₁ mono fx≈fy = ≮∧≯⇒≈ (<-irrefl fx≈fy ∘ mono) (<-irrefl (Eq.sym fx≈fy) ∘ mono)

  anti-mono₁-<⇒cancel₁ : f Preserves _<_ ⟶ _>_ → Injective _≈_ _≈_ f
  anti-mono₁-<⇒cancel₁ anti-mono fx≈fy = ≮∧≯⇒≈
    (<-irrefl (Eq.sym fx≈fy) ∘ anti-mono)
    (<-irrefl fx≈fy ∘ anti-mono)

----
-- Consequences for a single binary operation
module _ {_∙_ : Op₂ A} where
  invariant⇒mono-< : Invariant _<_ _∙_ → Congruent₂ _<_ _∙_
  invariant⇒mono-< (invˡ , invʳ) {x} {y} {u} {v} x<y u<v = begin-strict
    x ∙ u <⟨ invˡ x u<v ⟩
    x ∙ v <⟨ invʳ v x<y ⟩
    y ∙ v ∎

  invariantˡ⇒monoˡ-< : LeftInvariant _<_ _∙_ → LeftCongruent _<_ _∙_
  invariantˡ⇒monoˡ-< invˡ u<v = invˡ _ u<v

  invariantʳ⇒monoʳ-< : RightInvariant _<_ _∙_ → RightCongruent _<_ _∙_
  invariantʳ⇒monoʳ-< invʳ x<y = invʳ _ x<y

  cong+invariant⇒mono-≤ : Congruent₂ _≈_ _∙_ → Invariant _<_ _∙_ → Congruent₂ _≤_ _∙_
  cong+invariant⇒mono-≤ cong inv@(invˡ , invʳ) (inj₁ x<y) (inj₁ u<v) = inj₁ (invariant⇒mono-< inv x<y u<v)
  cong+invariant⇒mono-≤ cong inv@(invˡ , invʳ) (inj₁ x<y) (inj₂ u≈v) = inj₁ (<-respʳ-≈ (cong Eq.refl u≈v) (invʳ _ x<y))
  cong+invariant⇒mono-≤ cong inv@(invˡ , invʳ) (inj₂ x≈y) (inj₁ u<v) = inj₁ (<-respʳ-≈ (cong x≈y Eq.refl) (invˡ _ u<v))
  cong+invariant⇒mono-≤ cong inv@(invˡ , invʳ) (inj₂ x≈y) (inj₂ u≤v) = inj₂ (cong x≈y u≤v)

  congˡ+monoˡ-<⇒monoˡ-≤ : LeftCongruent _≈_ _∙_ → LeftCongruent _<_ _∙_ → LeftCongruent _≤_ _∙_
  congˡ+monoˡ-<⇒monoˡ-≤ congˡ monoˡ = cong₁+mono₁-<⇒mono₁-≤ congˡ monoˡ

  congʳ+monoʳ-<⇒monoʳ-≤ : RightCongruent _≈_ _∙_ → RightCongruent _<_ _∙_ → RightCongruent _≤_ _∙_
  congʳ+monoʳ-<⇒monoʳ-≤ congʳ monoʳ = cong₁+mono₁-<⇒mono₁-≤ congʳ monoʳ

  monoˡ-<⇒cancelˡ-≤ : LeftCongruent _<_ _∙_ → LeftCancellative _≤_ _∙_
  monoˡ-<⇒cancelˡ-≤ monoˡ _ = mono₁-<⇒cancel₁-≤ monoˡ

  monoʳ-<⇒cancelʳ-≤ : RightCongruent _<_ _∙_ → RightCancellative _≤_ _∙_
  monoʳ-<⇒cancelʳ-≤ monoʳ _ _ = mono₁-<⇒cancel₁-≤ monoʳ

  monoˡ-≤⇒cancelˡ-< : LeftCongruent _≤_ _∙_ → LeftCancellative _<_ _∙_
  monoˡ-≤⇒cancelˡ-< monoˡ _ = mono₁-≤⇒cancel₁-< monoˡ

  monoʳ-≤⇒cancelʳ-< : RightCongruent _≤_ _∙_ → RightCancellative _<_ _∙_
  monoʳ-≤⇒cancelʳ-< monoʳ _ _ = mono₁-≤⇒cancel₁-< monoʳ

  cancelˡ-<⇒monoˡ-≤ : LeftCancellative _<_ _∙_ → LeftCongruent _≤_ _∙_
  cancelˡ-<⇒monoˡ-≤ cancelˡ = cancel₁-<⇒mono₁-≤ (cancelˡ _)

  cancelʳ-<⇒monoʳ-≤ : RightCancellative _<_ _∙_ → RightCongruent _≤_ _∙_
  cancelʳ-<⇒monoʳ-≤ cancelʳ = cancel₁-<⇒mono₁-≤ (cancelʳ _ _)

  cancelˡ-≤⇒monoˡ-< : LeftCancellative _≤_ _∙_ → LeftCongruent _<_ _∙_
  cancelˡ-≤⇒monoˡ-< cancelˡ = cancel₁-≤⇒mono₁-< (cancelˡ _)

  cancelʳ-≤⇒monoʳ-< : RightCancellative _≤_ _∙_ → RightCongruent _<_ _∙_
  cancelʳ-≤⇒monoʳ-< cancelʳ = cancel₁-≤⇒mono₁-< (cancelʳ _ _)

  monoˡ-<⇒cancelˡ : LeftCongruent _<_ _∙_ → LeftCancellative _≈_ _∙_
  monoˡ-<⇒cancelˡ monoˡ _ = mono₁-<⇒cancel₁ monoˡ

  monoʳ-<⇒cancelʳ : RightCongruent _<_ _∙_ → RightCancellative _≈_ _∙_
  monoʳ-<⇒cancelʳ monoʳ _ _ = mono₁-<⇒cancel₁ monoʳ

  ¬comm-< : A → ¬ Commutative _<_ _∙_
  ¬comm-< a comm = <-irrefl Eq.refl (comm a a )

  -- cong+mono-<⇒mono-≤ : Congruent₂ _≈_ _∙_ → Congruent₂ _<_ _∙_ → Congruent₂ _≤_ _∙_
  -- cong+mono-<⇒mono-≤ cong mono (inj₁ x<y) (inj₁ u<v) = inj₁ (mono x<y u<v)
  -- cong+mono-<⇒mono-≤ cong mono (inj₁ x<y) (inj₂ u≈v) = inj₁ {!!}
  -- cong+mono-<⇒mono-≤ cong mono (inj₂ x≈y) (inj₁ u<v) = inj₁ {!!}
  -- cong+mono-<⇒mono-≤ cong mono (inj₂ x≈y) (inj₂ u≈v) = inj₂ (cong x≈y u≈v)
