------------------------------------------------------------------------
-- Agda Helium
--
-- Some more algebraic structures
-- (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Core using (Rel)
module Helium.Algebra.Structures
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where

open import Algebra.Core
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
open import Data.Product using (proj₁; proj₂)
open import Helium.Algebra.Core
open import Helium.Algebra.Definitions _≈_
import Helium.Algebra.Consequences.Setoid as Consequences
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)

record IsAlmostGroup
         (_∙_ : Op₂ A) (0# 1# : A) (_⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ) where
  field
    isMonoid : IsMonoid _∙_ 1#
    inverse  : AlmostInverse 1# _⁻¹ _∙_
    ⁻¹-cong  : AlmostCongruent₁ _⁻¹

  open IsMonoid isMonoid public

  infixl 6 _-_
  _-_ : AlmostOp₂ _≈_ 0#
  x - y≉0 = x ∙ (y≉0 ⁻¹)

  inverseˡ : AlmostLeftInverse 1# _⁻¹ _∙_
  inverseˡ = proj₁ inverse

  inverseʳ : AlmostRightInverse 1# _⁻¹ _∙_
  inverseʳ = proj₂ inverse

  uniqueˡ-⁻¹ : ∀ x {y} (y≉0 : ¬ y ≈ 0#) → (x ∙ y) ≈ 1# → x ≈ (y≉0 ⁻¹)
  uniqueˡ-⁻¹ = Consequences.assoc+id+invʳ⇒invˡ-unique
                setoid ∙-cong assoc identity inverseʳ

  uniqueʳ-⁻¹ : ∀ {x} (x≉0 : ¬ x ≈ 0#) y → (x ∙ y) ≈ 1# → y ≈ (x≉0 ⁻¹)
  uniqueʳ-⁻¹ = Consequences.assoc+id+invˡ⇒invʳ-unique
                setoid ∙-cong assoc identity inverseˡ

record IsAlmostAbelianGroup
         (∙ : Op₂ A) (0# 1# : A) (⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ) where
  field
    isAlmostGroup : IsAlmostGroup ∙ 0# 1# ⁻¹
    comm          : Commutative ∙

  open IsAlmostGroup isAlmostGroup

  isCommutativeMonoid : IsCommutativeMonoid ∙ 1#
  isCommutativeMonoid = record
    { isMonoid = isMonoid
    ; comm     = comm
    }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isCommutativeMagma; isCommutativeSemigroup)

record IsDivisionRing
         (+ _*_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (_⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ) where
  field
    +-isAbelianGroup : IsAbelianGroup + 0# -_
    -- FIXME: unroll definition
    *-isAlmostGroup  : IsAlmostGroup _*_ 0# 1# _⁻¹
    distrib          : _*_ DistributesOver +
    zero             : Zero 0# _*_

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
    ; isCommutativeMagma     to +-isCommutativeMagma
    ; isCommutativeMonoid    to +-isCommutativeMonoid
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
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
    ; *-cong = *-cong
    ; *-assoc = *-assoc
    ; *-identity = *-identity
    ; distrib = distrib
    ; zero = zero
    }

  open IsRing isRing public
    using
    ( distribˡ ; distribʳ ; zeroˡ ; zeroʳ
    ; isNearSemiring ; isSemiringWithoutOne ; isSemiringWithoutAnnihilatingZero
    )

record IsField
         (+ * : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
         (⁻¹ : AlmostOp₁ _≈_ 0#) : Set (a ⊔ ℓ) where
  field
    isDivisionRing : IsDivisionRing + * -_ 0# 1# ⁻¹
    *-comm         : Commutative *

  open IsDivisionRing isDivisionRing public

  isCommutativeRing : IsCommutativeRing + * -_ 0# 1#
  isCommutativeRing = record
    { isRing = isRing
    ; *-comm = *-comm
    }

  open IsCommutativeRing isCommutativeRing public
    using
    ( isCommutativeSemiring
    ; isCommutativeSemiringWithoutOne
    ; *-isCommutativeMagma
    ; *-isCommutativeSemigroup
    ; *-isCommutativeMonoid
    )
