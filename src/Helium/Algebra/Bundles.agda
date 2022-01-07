------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions for more algebraic structures
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Algebra.Bundles where

open import Algebra.Bundles
open import Algebra.Core
open import Helium.Algebra.Core
open import Helium.Algebra.Structures
open import Level using (_⊔_; suc)
open import Relation.Binary.Core using (Rel)

record RawAlmostGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 8 _⁻¹
  infixl 7 _∙_
  infixl 6 _-_
  infix 4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    0#      : Carrier
    1#      : Carrier
    _⁻¹     : AlmostOp₁ _≈_ 0#

  _-_ : AlmostOp₂ _≈_ 0#
  x - y≉0 = x ∙ y≉0 ⁻¹

  rawMonoid : RawMonoid c ℓ
  rawMonoid = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε = 1#
    }

  open RawMonoid rawMonoid public
    using (_≉_; rawMagma)

record AlmostGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    _∙_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    _⁻¹           : AlmostOp₁ _≈_ 0#
    isAlmostGroup : IsAlmostGroup _≈_ _∙_ 0# 1# _⁻¹

  open IsAlmostGroup isAlmostGroup public

  rawAlmostGroup : RawAlmostGroup _ _
  rawAlmostGroup = record
    { _≈_ = _≈_
    ; _∙_ = _∙_
    ; 0# = 0#
    ; 1# = 1#
    ; _⁻¹ = _⁻¹
    }

  monoid : Monoid _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public
    using (_≉_; rawMagma; magma; semigroup; rawMonoid)

record AlmostAbelianGroup c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ
    _∙_                  : Op₂ Carrier
    0#                   : Carrier
    1#                   : Carrier
    _⁻¹                  : AlmostOp₁ _≈_ 0#
    isAlmostAbelianGroup : IsAlmostAbelianGroup _≈_ _∙_ 0# 1# _⁻¹

  open IsAlmostAbelianGroup isAlmostAbelianGroup public

  almostGroup : AlmostGroup _ _
  almostGroup = record { isAlmostGroup = isAlmostGroup }

  open AlmostGroup almostGroup public
    using (_≉_; rawMagma; magma; semigroup; monoid; rawMonoid; rawAlmostGroup)

  commutativeMonoid : CommutativeMonoid _ _
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public
    using (commutativeMagma; commutativeSemigroup)

record RawField c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_ _/_
  infixl 6 _+_ _-_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    _⁻¹     : AlmostOp₁ _≈_ 0#

  rawRing : RawRing c ℓ
  rawRing = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_ = -_
    ; 0# = 0#
    ; 1# = 1#
    }

  open RawRing rawRing public
    using
    ( _≉_
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; *-rawMagma; *-rawMonoid
    ; rawSemiring
    )

  *-rawAlmostGroup : RawAlmostGroup _ _
  *-rawAlmostGroup = record
                       { _≈_ = _≈_ ; _∙_ = _*_ ; 0# = 0# ; 1# = 1# ; _⁻¹ = _⁻¹ }

  _-_ : Op₂ Carrier
  x - y = x + - y

  _/_ : AlmostOp₂ _≈_ 0#
  x / y≉0 = x * y≉0 ⁻¹

record DivisionRing c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    -_             : Op₁ Carrier
    0#             : Carrier
    1#             : Carrier
    _⁻¹            : AlmostOp₁ _≈_ 0#
    isDivisionRing : IsDivisionRing _≈_ _+_ _*_ -_ 0# 1# _⁻¹

  open IsDivisionRing isDivisionRing public

  ring : Ring _ _
  ring = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_ = -_
    ; 0# = 0#
    ; 1# = 1#
    ; isRing = isRing
    }

  open Ring ring public
    using
    ( _≉_
    ; +-rawMagma; +-magma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-group; +-abelianGroup
    ; *-rawMagma; *-magma ; *-semigroup; *-rawMonoid; *-monoid
    ; nearSemiring ; semiringWithoutOne; semiringWithoutAnnihilatingZero
    ; semiring
    ; rawRing
    )

  rawField : RawField _ _
  rawField = record
    { _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_ = -_
    ; 0# = 0#
    ; 1# = 1#
    ; _⁻¹ = _⁻¹
    }

  open RawField rawField public
    using (+-rawGroup; *-rawAlmostGroup; rawSemiring)

  *-almostGroup : AlmostGroup _ _
  *-almostGroup = record { isAlmostGroup = *-isAlmostGroup }

record Field c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    _⁻¹     : AlmostOp₁ _≈_ 0#
    isField : IsField _≈_ _+_ _*_ -_ 0# 1# _⁻¹

  open IsField isField public

  divisionRing : DivisionRing _ _
  divisionRing = record { isDivisionRing = isDivisionRing }

  open DivisionRing divisionRing public
    using
    ( _≉_
    ; +-rawMagma; +-magma; +-commutativeMagma
    ; +-semigroup; +-commutativeSemigroup
    ; +-rawMonoid; +-monoid; +-commutativeMonoid
    ; +-rawGroup; +-group; +-abelianGroup
    ; *-rawMagma; *-magma ; *-semigroup
    ; *-rawMonoid; *-monoid
    ; *-rawAlmostGroup; *-almostGroup
    ; nearSemiring ; semiringWithoutOne; semiringWithoutAnnihilatingZero
    ; rawSemiring; semiring
    ; rawRing; ring; rawField
    )

  commutativeRing : CommutativeRing _ _
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  open CommutativeRing commutativeRing public
    using
    ( *-commutativeMagma; *-commutativeSemigroup; *-commutativeMonoid
    ; commutativeSemiringWithoutOne; commutativeSemiring
    )
