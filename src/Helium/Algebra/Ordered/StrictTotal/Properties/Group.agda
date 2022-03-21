------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of ordered groups
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles

module Helium.Algebra.Ordered.StrictTotal.Properties.Group
  {ℓ₁ ℓ₂ ℓ₃}
  (group : Group ℓ₁ ℓ₂ ℓ₃)
  where

open Group group

open import Data.Sum using (inj₂; [_,_]′; fromInj₁)
open import Function using (_∘_; flip)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.Reasoning.StrictPartialOrder strictPartialOrder
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open import Algebra.Properties.Group Unordered.group public
open import Algebra.Properties.Monoid.Mult.TCOptimised Unordered.monoid public

<⇒≱ : ∀ {x y} → x < y → ¬ x ≥ y
<⇒≱ {x} {y} x<y x≥y with compare x y
... | tri< _   x≉y x≱y = [ x≱y , x≉y ∘ Eq.sym ]′ x≥y
... | tri≈ x≮y _   _   = x≮y x<y
... | tri> x≮y _   _   = x≮y x<y

≤⇒≯ : ∀ {x y} → x ≤ y → ¬ x > y
≤⇒≯ = flip <⇒≱

>⇒≉ : ∀ {x y} → x > y → x ≉ y
>⇒≉ x>y = <⇒≱ x>y ∘ inj₂

≈⇒≯ : ∀ {x y} → x ≈ y → ¬ x > y
≈⇒≯ = flip >⇒≉

<⇒≉ : ∀ {x y} → x < y → x ≉ y
<⇒≉ x<y = >⇒≉ x<y ∘ Eq.sym

≈⇒≮ : ∀ {x y} → x ≈ y → ¬ x < y
≈⇒≮ = flip <⇒≉

≤∧≉⇒< : ∀ {x y} → x ≤ y → x ≉ y → x < y
≤∧≉⇒< x≤y x≉y = fromInj₁ (λ x≈y → contradiction x≈y x≉y) x≤y

≥∧≉⇒> : ∀ {x y} → x ≥ y → x ≉ y → x > y
≥∧≉⇒> x≥y x≉y = ≤∧≉⇒< x≥y (x≉y ∘ Eq.sym)

x<y⇒ε<yx⁻¹ : ∀ {x y} → x < y → ε < y ∙ x ⁻¹
x<y⇒ε<yx⁻¹ {x} {y} x<y = begin-strict
  ε        ≈˘⟨ inverseʳ x ⟩
  x ∙ x ⁻¹ <⟨  ∙-invariantʳ (x ⁻¹) x<y ⟩
  y ∙ x ⁻¹ ∎
