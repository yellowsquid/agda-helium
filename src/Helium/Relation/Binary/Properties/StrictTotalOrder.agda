------------------------------------------------------------------------
-- Agda Helium
--
-- Relational properties of strict total orders
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Relation.Binary

module Helium.Relation.Binary.Properties.StrictTotalOrder
  {a ℓ₁ ℓ₂} (STO : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Sum using (inj₁; inj₂)
open import Function using (flip)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)

open StrictTotalOrder STO
  renaming
  ( trans to <-trans
  ; irrefl to <-irrefl
  ; asym to <-asym
  )

import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_ as ToNonStrict

infix 4 _≉_ _≮_ _≤_ _≰_ _>_ _≥_

_≉_ : Rel Carrier ℓ₁
x ≉ y = ¬ x ≈ y

_≮_ : Rel Carrier ℓ₂
x ≮ y = ¬ x < y

_≤_ : Rel Carrier _
_≤_ = ToNonStrict._≤_

_≰_ : Rel Carrier _
x ≰ y = ¬ x ≤ y

_>_ : Rel Carrier ℓ₂
_>_ = flip _<_

_≥_ : Rel Carrier _
_≥_ = flip _≤_


<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans = ToNonStrict.<-≤-trans <-trans <-respʳ-≈

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans = ToNonStrict.≤-<-trans Eq.sym <-trans <-respˡ-≈


≤-respˡ-≈ : _≤_ Respectsˡ _≈_
≤-respˡ-≈ = ToNonStrict.≤-respˡ-≈ Eq.sym Eq.trans <-respˡ-≈

≤-respʳ-≈ : _≤_ Respectsʳ _≈_
≤-respʳ-≈ = ToNonStrict.≤-respʳ-≈ Eq.trans <-respʳ-≈

≤-resp-≈ : _≤_ Respects₂ _≈_
≤-resp-≈ = ToNonStrict.≤-resp-≈ Eq.isEquivalence <-resp-≈

≤-reflexive : _≈_ ⇒ _≤_
≤-reflexive = ToNonStrict.reflexive

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive Eq.refl

≤-trans : Transitive _≤_
≤-trans = ToNonStrict.trans Eq.isEquivalence <-resp-≈ <-trans

≤-antisym : Antisymmetric _≈_ _≤_
≤-antisym = ToNonStrict.antisym Eq.isEquivalence <-trans <-irrefl

≤-total : Total _≤_
≤-total = ToNonStrict.total compare


<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = ToNonStrict.<⇒≤

<⇒≉ : Irreflexive _<_ _≈_
<⇒≉ = flip <-irrefl

≤∧≉⇒< : ∀ {x y} → x ≤ y → x ≉ y → x < y
≤∧≉⇒< (inj₁ x<y) x≉y = x<y
≤∧≉⇒< (inj₂ x≈y) x≉y = contradiction x≈y x≉y


≤∧≮⇒≈ : ∀ {x y} → x ≤ y → x ≮ y → x ≈ y
≤∧≮⇒≈ (inj₁ x<y) x≮y = contradiction x<y x≮y
≤∧≮⇒≈ (inj₂ x≈y) x≮y = x≈y


<⇒≱ : Irreflexive _<_ _≥_
<⇒≱ x<y (inj₁ x>y) = <-asym x<y x>y
<⇒≱ x<y (inj₂ y≈x) = <-irrefl (Eq.sym y≈x) x<y

≰⇒> : _≰_ ⇒ _>_
≰⇒> {x} {y} x≰y with compare x y
... | tri< x<y _ _ = contradiction (<⇒≤ x<y) x≰y
... | tri≈ _ x≈y _ = contradiction (≤-reflexive x≈y) x≰y
... | tri> _ _ x>y = x>y


≤⇒≯ : Irreflexive _≤_ _>_
≤⇒≯ = flip <⇒≱

≮⇒≥ : _≮_ ⇒ _≥_
≮⇒≥ {x} {y} x≮y with compare x y
... | tri< x<y _ _ = contradiction x<y x≮y
... | tri≈ _ x≈y _ = ≤-reflexive (Eq.sym x≈y)
... | tri> _ _ x>y = <⇒≤ x>y

≮∧≯⇒≈ : ∀ {x y} → x ≮ y → y ≮ x → x ≈ y
≮∧≯⇒≈ {x} {y} x≮y x≯y with compare x y
... | tri< x<y _ _ = contradiction x<y x≮y
... | tri≈ _ x≈y _ = x≈y
... | tri> _ _ x>y = contradiction x>y x≯y
