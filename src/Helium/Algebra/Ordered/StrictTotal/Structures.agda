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
import Algebra.Structures _≈_ as NoOrder
open import Data.Product using (_,_; proj₁; proj₂)
open import Helium.Algebra.Core
open import Helium.Algebra.Definitions _≈_
import Helium.Algebra.Structures _≈_ as NoOrder′
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

  module Unordered where
    isMagma : NoOrder.IsMagma ∙
    isMagma = record { isEquivalence = isEquivalence ; ∙-cong = ∙-cong }

record IsSemigroup (∙ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMagma : IsMagma ∙
    assoc   : Associative ∙

  open IsMagma isMagma public
    hiding (module Unordered)

  module Unordered where
    isSemigroup : NoOrder.IsSemigroup ∙
    isSemigroup = record
      { isMagma = IsMagma.Unordered.isMagma isMagma
      ; assoc   = assoc
      }

    open NoOrder.IsSemigroup isSemigroup public
      using (isMagma)

record IsMonoid (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isSemigroup : IsSemigroup _∙_
    identity    : Identity ε _∙_

  open IsSemigroup isSemigroup public
    hiding (module Unordered)

  identityˡ : LeftIdentity ε _∙_
  identityˡ = proj₁ identity

  identityʳ : RightIdentity ε _∙_
  identityʳ = proj₂ identity

  identity² : (ε ∙ ε) ≈ ε
  identity² = identityˡ ε

  module Unordered where
    isMonoid : NoOrder.IsMonoid _∙_ ε
    isMonoid = record
      { isSemigroup = IsSemigroup.Unordered.isSemigroup isSemigroup
      ; identity    = identity
      }

    open NoOrder.IsMonoid isMonoid public
      using (isMagma; isSemigroup)

record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

  open IsMonoid isMonoid public
    hiding (module Unordered)

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

  module Unordered where
    isGroup : NoOrder.IsGroup _∙_ ε _⁻¹
    isGroup = record
      { isMonoid = IsMonoid.Unordered.isMonoid isMonoid
      ; inverse  = inverse
      ; ⁻¹-cong  = ⁻¹-cong
      }

    open NoOrder.IsGroup isGroup public
      using (isMagma; isSemigroup; isMonoid)

record IsAbelianGroup (∙ : Op₂ A)
                      (ε : A) (⁻¹ : Op₁ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isGroup : IsGroup ∙ ε ⁻¹
    comm    : Commutative ∙

  open IsGroup isGroup public
    hiding (module Unordered)

  module Unordered where
    isAbelianGroup : NoOrder.IsAbelianGroup ∙ ε ⁻¹
    isAbelianGroup = record
      { isGroup = IsGroup.Unordered.isGroup isGroup
      ; comm    = comm
      }

    open NoOrder.IsAbelianGroup isAbelianGroup public
      using (isMagma; isSemigroup; isMonoid; isGroup)

record IsRing (+ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isMonoid       : NoOrder.IsMonoid _*_ 1#
    distrib          : _*_ DistributesOver +
    zero             : Zero 0# _*_
    0<a+0<b⇒0<ab     : PreservesPositive 0# _*_

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; ∙-invariant            to +-invariant
    ; ∙-invariantˡ           to +-invariantˡ
    ; ∙-invariantʳ           to +-invariantʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; identity²              to +-identity²
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
    hiding (module Unordered)

  open NoOrder.IsMonoid *-isMonoid public
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

  *-identity² : (1# * 1#) ≈ 1#
  *-identity² = *-identityˡ 1#

  distribˡ : _*_ DistributesOverˡ +
  distribˡ = proj₁ distrib

  distribʳ : _*_ DistributesOverʳ +
  distribʳ = proj₂ distrib

  zeroˡ : LeftZero 0# _*_
  zeroˡ = proj₁ zero

  zeroʳ : RightZero 0# _*_
  zeroʳ = proj₂ zero

  module Unordered where
    isRing : NoOrder.IsRing + _*_ -_ 0# 1#
    isRing = record
      { +-isAbelianGroup = IsAbelianGroup.Unordered.isAbelianGroup +-isAbelianGroup
      ; *-isMonoid       = *-isMonoid
      ; distrib          = distrib
      ; zero             = zero
      }

    open NoOrder.IsRing isRing
      using (+-isMagma; +-isSemigroup; +-isMonoid; +-isGroup)

record IsCommutativeRing
         (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isRing : IsRing + * - 0# 1#
    *-comm : Commutative *

  open IsRing isRing public
    hiding (module Unordered)

  module Unordered where
    isCommutativeRing : NoOrder.IsCommutativeRing + * (-) 0# 1#
    isCommutativeRing = record
      { isRing = IsRing.Unordered.isRing isRing
      ; *-comm = *-comm
      }

    open NoOrder.IsCommutativeRing isCommutativeRing public
      using (+-isMagma; +-isSemigroup; +-isMonoid; +-isGroup; isRing)

record IsDivisionRing
         (+ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (_⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    *-isAlmostGroup  : NoOrder′.IsAlmostGroup _*_ 0# 1# _⁻¹
    distrib          : _*_ DistributesOver +
    zero             : Zero 0# _*_
    0<a+0<b⇒0<ab     : PreservesPositive 0# _*_

  infixl 7 _/_
  _/_ : AlmostOp₂ _≈_ 0#
  x / y≉0 = x * (y≉0 ⁻¹)

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc                  to +-assoc
    ; ∙-cong                 to +-cong
    ; ∙-congˡ                to +-congˡ
    ; ∙-congʳ                to +-congʳ
    ; ∙-invariant            to +-invariant
    ; ∙-invariantˡ           to +-invariantˡ
    ; ∙-invariantʳ           to +-invariantʳ
    ; identity               to +-identity
    ; identityˡ              to +-identityˡ
    ; identityʳ              to +-identityʳ
    ; identity²              to +-identity²
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
    hiding (module Unordered)

  open NoOrder′.IsAlmostGroup *-isAlmostGroup public
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
    ; 0<a+0<b⇒0<ab = 0<a+0<b⇒0<ab
    }

  open IsRing isRing public
    using (distribˡ ; distribʳ ; zeroˡ ; zeroʳ)

  module Unordered where
    isDivisionRing : NoOrder′.IsDivisionRing + _*_ -_ 0# 1# _⁻¹
    isDivisionRing = record
      { +-isAbelianGroup = IsAbelianGroup.Unordered.isAbelianGroup +-isAbelianGroup
      ; *-isAlmostGroup  = *-isAlmostGroup
      ; distrib          = distrib
      ; zero             = zero
      }

    open NoOrder′.IsDivisionRing isDivisionRing
      using (+-isMagma; +-isSemigroup; +-isMonoid; +-isGroup; isRing)

record IsField
         (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isDivisionRing : IsDivisionRing + * -_ 0# 1# ⁻¹
    *-comm         : Commutative *

  open IsDivisionRing isDivisionRing public
    hiding (module Unordered)

  isCommutativeRing : IsCommutativeRing + * -_ 0# 1#
  isCommutativeRing = record
    { isRing = isRing
    ; *-comm = *-comm
    }

  module Unordered where
    isField : NoOrder′.IsField + * -_ 0# 1# ⁻¹
    isField = record
      { isDivisionRing = IsDivisionRing.Unordered.isDivisionRing isDivisionRing
      ; *-comm         = *-comm
      }

    open NoOrder′.IsField isField
      using
      ( +-isMagma; +-isSemigroup; +-isMonoid; +-isGroup
      ; isRing; isDivisionRing
      )
