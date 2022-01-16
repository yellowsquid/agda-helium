------------------------------------------------------------------------
-- Agda Helium
--
-- Some ordered algebraic structures (not packed up with sets,
-- operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Helium.Algebra.Ordered.StrictTotal.Structures
  {a ℓ₁ ℓ₂} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ₁)      -- The underlying equality
  (_<_ : Rel A ℓ₂)      -- The underlying order
  where

import Algebra.Consequences.Setoid as Consequences
open import Algebra.Core
open import Algebra.Definitions _≈_
import Algebra.Structures _≈_ as Unordered
open import Data.Product using (_,_; proj₁; proj₂)
open import Helium.Algebra.Core
open import Helium.Algebra.Definitions _≈_
open import Helium.Algebra.Structures _≈_ using (IsAlmostGroup)
open import Helium.Algebra.Ordered.Definitions _<_
open import Level using (_⊔_)

record IsMagma (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_
    ∙-cong      : Congruent₂ ∙
    ∙-invariant : Invariant ∙

  open IsStrictTotalOrder isStrictTotalOrder public

  strictTotalOrder : StrictTotalOrder _ _ _
  strictTotalOrder = record { isStrictTotalOrder = isStrictTotalOrder }

  open module strictTotalOrder = StrictTotalOrder strictTotalOrder public
    using (strictPartialOrder)

  ∙-congˡ : LeftCongruent ∙
  ∙-congˡ y≈z = ∙-cong Eq.refl y≈z

  ∙-congʳ : RightCongruent ∙
  ∙-congʳ y≈z = ∙-cong y≈z Eq.refl

  ∙-invariantˡ : LeftInvariant ∙
  ∙-invariantˡ = proj₁ ∙-invariant

  ∙-invariantʳ : RightInvariant ∙
  ∙-invariantʳ = proj₂ ∙-invariant

record IsSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMagma : IsMagma ∙
    assoc   : Associative ∙

  open IsMagma isMagma public

record IsMonoid (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isSemigroup : IsSemigroup ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

  identityˡ : LeftIdentity ε ∙
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε ∙
  identityʳ = proj₂ identity

record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMonoid isMonoid public

  infixl 6 _-_
  _-_ : Op₂ A
  x - y = x ∙ (y ⁻¹)

  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse

  uniqueˡ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
  uniqueˡ-⁻¹ = Consequences.assoc+id+invʳ⇒invˡ-unique
                strictTotalOrder.Eq.setoid ∙-cong assoc identity inverseʳ

  uniqueʳ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
  uniqueʳ-⁻¹ = Consequences.assoc+id+invˡ⇒invʳ-unique
                strictTotalOrder.Eq.setoid ∙-cong assoc identity inverseˡ

record IsAbelianGroup (∙ : Op₂ A)
                      (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public

record IsRing (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isAbelianGroup  : IsAbelianGroup + 0# -_
    *-isMonoid        : Unordered.IsMonoid * 1#
    distrib           : * DistributesOver +
    zero              : Zero 0# *
    preservesPositive : PreservesPositive 0# *

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; inverse                to -‿inverse
    ; inverseˡ               to -‿inverseˡ
    ; inverseʳ               to -‿inverseʳ
    ; ⁻¹-cong                to -‿cong
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isGroup                to +-isGroup
    )

  open Unordered.IsMonoid *-isMonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    ; ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    )

  distribˡ : * DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : * DistributesOverʳ +
  distribʳ = proj₂ distrib

  zeroˡ : LeftZero 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# *
  zeroʳ = proj₂ zero

record IsCommutativeRing
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isRing : IsRing + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public

record IsDivisionRing
         (+ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (_⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isAbelianGroup  : IsAbelianGroup + 0# -_
    *-isAlmostGroup   : IsAlmostGroup _*_ 0# 1# _⁻¹
    distrib           : _*_ DistributesOver +
    zero              : Zero 0# _*_
    preservesPositive : PreservesPositive 0# _*_

  infixl 7 _/_
  _/_ : AlmostOp₂ _≈_ 0#
  x / y≉0 = x * (y≉0 ⁻¹)

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; inverse                to -‿inverse
    ; inverseˡ               to -‿inverseˡ
    ; inverseʳ               to -‿inverseʳ
    ; ⁻¹-cong                to -‿cong
    ; uniqueˡ-⁻¹             to uniqueˡ‿-
    ; uniqueʳ-⁻¹             to uniqueʳ‿-
    ; comm                   to +-comm
    ; isMagma                to +-isMagma
    ; isSemigroup            to +-isSemigroup
    ; isMonoid               to +-isMonoid
    ; isGroup                to +-isGroup
    )

  open IsAlmostGroup *-isAlmostGroup public
    using (⁻¹-cong; uniqueˡ-⁻¹; uniqueʳ-⁻¹)
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    ; ∙-congˡ     to *-congˡ
    ; ∙-congʳ     to *-congʳ
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; inverse     to ⁻¹-inverse
    ; inverseˡ    to ⁻¹-inverseˡ
    ; inverseʳ    to ⁻¹-inverseʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    ; isMonoid    to *-isMonoid
    )

  isRing : IsRing + _*_ -_ 0# 1#
  isRing = record
    { +-isAbelianGroup = +-isAbelianGroup
    ; *-isMonoid = *-isMonoid
    ; distrib = distrib
    ; zero = zero
    ; preservesPositive = preservesPositive
    }

  open IsRing isRing public
    using (distribˡ ; distribʳ ; zeroˡ ; zeroʳ)

record IsField
         (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isDivisionRing : IsDivisionRing + * -_ 0# 1# ⁻¹
    *-comm         : Commutative *

  open IsDivisionRing isDivisionRing public

  isCommutativeRing : IsCommutativeRing + * -_ 0# 1#
  isCommutativeRing = record
    { isRing = isRing
    ; *-comm = *-comm
    }
