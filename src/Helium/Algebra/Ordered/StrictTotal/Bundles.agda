------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions of ordered algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Helium.Algebra.Ordered.StrictTotal.Bundles where

import Algebra.Bundles as Unordered
open import Algebra.Core
open import Data.Sum using (_⊎_)
open import Function using (flip)
open import Helium.Algebra.Core
open import Helium.Algebra.Bundles using
  (RawAlmostGroup; AlmostGroup; AlmostAbelianGroup)
open import Helium.Algebra.Ordered.StrictTotal.Structures
open import Level using (suc; _⊔_)
open import Relation.Binary
open import Relation.Nullary as N

record RawMagma c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _∙_     : Op₂ Carrier

  infix 4 _≉_ _≤_ _>_ _≥_
  _≉_ : Rel Carrier _
  x ≉ y = N.¬ x ≈ y

  _≤_ : Rel Carrier _
  x ≤ y = x < y ⊎ x ≈ y

  _>_ : Rel Carrier _
  _>_ = flip _<_

  _≥_ : Rel Carrier _
  _≥_ = flip _≤_

record Magma c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _∙_     : Op₂ Carrier
    isMagma : IsMagma _≈_ _<_ _∙_

  open IsMagma isMagma public

  rawMagma : RawMagma _ _ _
  rawMagma = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_ }

  open RawMagma rawMagma public
    using (_≉_; _≤_; _>_; _≥_)

record Semigroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ₁
    _<_         : Rel Carrier ℓ₂
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _≈_ _<_ _∙_

  open IsSemigroup isSemigroup public

  magma : Magma c ℓ₁ ℓ₂
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (_≉_; _≤_; _>_; _≥_; rawMagma)

record RawMonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _∙_     : Op₂ Carrier
    ε       : Carrier

  rawMagma : RawMagma c ℓ₁ ℓ₂
  rawMagma = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_ }

  open RawMagma rawMagma public
    using (_≉_; _≤_; _>_; _≥_)

record Monoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ₁
    _<_      : Rel Carrier ℓ₂
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≈_ _<_ _∙_ ε

  open IsMonoid isMonoid public

  semigroup : Semigroup _ _ _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public
    using (_≉_; _≤_; _>_; _≥_; rawMagma; magma)

  rawMonoid : RawMonoid _ _ _
  rawMonoid = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_; ε = ε}

record RawGroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier

  rawMonoid : RawMonoid c ℓ₁ ℓ₂
  rawMonoid = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_; ε = ε }

  open RawMonoid rawMonoid public
    using (_≉_; _≤_; _>_; _≥_; rawMagma)


record Group c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isGroup : IsGroup _≈_ _<_ _∙_ ε _⁻¹

  open IsGroup isGroup public

  rawGroup : RawGroup _ _ _
  rawGroup = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_; ε = ε; _⁻¹ = _⁻¹}

  monoid : Monoid _ _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public
    using (_≉_; _≤_; _>_; _≥_; rawMagma; magma; semigroup; rawMonoid)

record AbelianGroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_ _<_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _<_            : Rel Carrier ℓ₂
    _∙_            : Op₂ Carrier
    ε              : Carrier
    _⁻¹            : Op₁ Carrier
    isAbelianGroup : IsAbelianGroup _≈_ _<_ _∙_ ε _⁻¹

  open IsAbelianGroup isAbelianGroup public

  group : Group _ _ _
  group = record { isGroup = isGroup }

  open Group group public
    using
    ( _≉_; _≤_; _>_; _≥_
    ; magma; semigroup; monoid
    ; rawMagma; rawMonoid; rawGroup
    )

record RawRing c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier

  +-rawGroup : RawGroup c ℓ₁ ℓ₂
  +-rawGroup = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _+_; ε = 0#; _⁻¹ = -_ }

  open RawGroup +-rawGroup public
    using ( _≉_; _≤_; _>_; _≥_ )
    renaming
    ( rawMagma to +-rawMagma
    ; rawMonoid to +-rawMonoid
    )

  *-rawMonoid : Unordered.RawMonoid c ℓ₁
  *-rawMonoid = record { _≈_ = _≈_; _∙_ = _*_; ε = 1# }

  open Unordered.RawMonoid *-rawMonoid public
    using ()
    renaming ( rawMagma to *-rawMagma )

record Ring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁
    _<_     : Rel Carrier ℓ₂
    _+_     : Op₂ Carrier
    _*_     : Op₂ Carrier
    -_      : Op₁ Carrier
    0#      : Carrier
    1#      : Carrier
    isRing  : IsRing _≈_ _<_ _+_ _*_ -_ 0# 1#

  open IsRing isRing public

  rawRing : RawRing c ℓ₁ ℓ₂
  rawRing = record
    { _≈_ = _≈_
    ; _<_ = _<_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  +-abelianGroup : AbelianGroup _ _ _
  +-abelianGroup = record { isAbelianGroup = +-isAbelianGroup }

  open AbelianGroup +-abelianGroup public
    using ( _≉_; _≤_; _>_; _≥_ )
    renaming
    ( rawMagma to +-rawMagma
    ; rawMonoid to +-rawMonoid
    ; rawGroup to +-rawGroup
    ; magma to +-magma
    ; semigroup to +-semigroup
    ; monoid to +-monoid
    ; group to +-group
    )

  *-monoid : Unordered.Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open Unordered.Monoid *-monoid public
    using ()
    renaming
    ( rawMagma to *-rawMagma
    ; rawMonoid to *-rawMonoid
    ; magma to *-magma
    ; semigroup to *-semigroup
    )

record CommutativeRing c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ₁
    _<_                : Rel Carrier ℓ₂
    _+_                : Op₂ Carrier
    _*_                : Op₂ Carrier
    -_                 : Op₁ Carrier
    0#                 : Carrier
    1#                 : Carrier
    isCommutativeRing  : IsCommutativeRing _≈_ _<_ _+_ _*_ -_ 0# 1#

  open IsCommutativeRing isCommutativeRing public

  ring : Ring _ _ _
  ring = record { isRing = isRing }

  open Ring ring public
    using
    ( _≉_; _≤_; _>_; _≥_
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid
    ; *-magma; *-semigroup; *-monoid
    )

record RawField c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _<_             : Rel Carrier ℓ₂
    _+_             : Op₂ Carrier
    _*_             : Op₂ Carrier
    -_              : Op₁ Carrier
    0#              : Carrier
    1#              : Carrier
    _⁻¹             : AlmostOp₁ _≈_ 0#

  infixl 7 _/_
  _/_ : AlmostOp₂ _≈_ 0#
  x / y≉0 = x * y≉0 ⁻¹

  rawRing : RawRing c ℓ₁ ℓ₂
  rawRing = record
    { _≈_ = _≈_
    ; _<_ = _<_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    }

  open RawRing rawRing public
    using
    ( _≉_; _≤_; _>_; _≥_
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; *-rawMagma; *-rawMonoid
    )

  *-rawAlmostGroup : RawAlmostGroup c ℓ₁
  *-rawAlmostGroup = record
    { _≈_ = _≈_
    ; _∙_ = _*_
    ; 0#  = 0#
    ; 1#  = 1#
    ; _⁻¹ = _⁻¹
    }

record DivisionRing c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _<_             : Rel Carrier ℓ₂
    _+_             : Op₂ Carrier
    _*_             : Op₂ Carrier
    -_              : Op₁ Carrier
    0#              : Carrier
    1#              : Carrier
    _⁻¹             : AlmostOp₁ _≈_ 0#
    isDivisionRing  : IsDivisionRing _≈_ _<_ _+_ _*_ -_ 0# 1# _⁻¹

  open IsDivisionRing isDivisionRing public

  rawField : RawField c ℓ₁ ℓ₂
  rawField = record
    { _≈_ = _≈_
    ; _<_ = _<_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_  = -_
    ; 0#  = 0#
    ; 1#  = 1#
    ; _⁻¹ = _⁻¹
    }

  ring : Ring c ℓ₁ ℓ₂
  ring = record { isRing = isRing }

  open Ring ring public
    using
    ( _≉_; _≤_; _>_; _≥_
    ; rawRing
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid
    ; *-magma; *-semigroup; *-monoid
    )

  *-almostGroup : AlmostGroup _ _
  *-almostGroup = record { isAlmostGroup = *-isAlmostGroup }

  open AlmostGroup *-almostGroup public
    using ()
    renaming (rawAlmostGroup to *-rawAlmostGroup)

record Field c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  9 _⁻¹
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _<_
  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ₁
    _<_      : Rel Carrier ℓ₂
    _+_      : Op₂ Carrier
    _*_      : Op₂ Carrier
    -_       : Op₁ Carrier
    0#       : Carrier
    1#       : Carrier
    _⁻¹      : AlmostOp₁ _≈_ 0#
    isField  : IsField _≈_ _<_ _+_ _*_ -_ 0# 1# _⁻¹

  open IsField isField public

  divisionRing : DivisionRing c ℓ₁ ℓ₂
  divisionRing = record { isDivisionRing = isDivisionRing }

  open DivisionRing divisionRing
    using
    ( _≉_; _≤_; _>_; _≥_
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid; *-rawAlmostGroup
    ; *-magma; *-semigroup; *-monoid; *-almostGroup
    )
