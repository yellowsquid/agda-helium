------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions of ordered algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Helium.Algebra.Ordered.StrictTotal.Bundles where

import Algebra.Bundles as NoOrder
open import Algebra.Core
open import Data.Sum using (_⊎_)
open import Function using (flip)
open import Helium.Algebra.Core
import Helium.Algebra.Bundles as NoOrder′
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

  module Unordered where
    rawMagma : NoOrder.RawMagma c ℓ₁
    rawMagma = record { _≈_ = _≈_ ; _∙_ = _∙_ }

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
    hiding (module Unordered)

  rawMagma : RawMagma _ _ _
  rawMagma = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_ }

  module Unordered where
    magma : NoOrder.Magma c ℓ₁
    magma = record { isMagma = IsMagma.Unordered.isMagma isMagma }

    open NoOrder.Magma magma public
      using (rawMagma)

    open IsMagma.Unordered isMagma public

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
    hiding (module Unordered)

  magma : Magma c ℓ₁ ℓ₂
  magma = record { isMagma = isMagma }

  open Magma magma public
    using (rawMagma)

  module Unordered where
    semigroup : NoOrder.Semigroup c ℓ₁
    semigroup =
      record { isSemigroup = IsSemigroup.Unordered.isSemigroup isSemigroup }

    open NoOrder.Semigroup semigroup public
      using (rawMagma; magma)

    open IsSemigroup.Unordered isSemigroup public

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

  module Unordered where
    rawMonoid : NoOrder.RawMonoid c ℓ₁
    rawMonoid = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε }

    open NoOrder.RawMonoid rawMonoid public
      using (rawMagma)

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
    hiding (module Unordered)

  semigroup : Semigroup _ _ _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public
    using (rawMagma; magma)

  rawMonoid : RawMonoid _ _ _
  rawMonoid = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_; ε = ε}

  module Unordered where
    monoid : NoOrder.Monoid c ℓ₁
    monoid = record { isMonoid = IsMonoid.Unordered.isMonoid isMonoid }

    open NoOrder.Monoid monoid public
      using (rawMagma; rawMonoid; magma; semigroup)

    open IsMonoid.Unordered isMonoid public

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
    using (rawMagma)

  module Unordered where
    rawGroup : NoOrder.RawGroup c ℓ₁
    rawGroup = record { _≈_ = _≈_; _∙_ = _∙_; ε = ε; _⁻¹ = _⁻¹ }

    open NoOrder.RawGroup rawGroup public
      using (rawMagma; rawMonoid)

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
    hiding (module Unordered)

  rawGroup : RawGroup _ _ _
  rawGroup = record { _≈_ = _≈_; _<_ = _<_; _∙_ = _∙_; ε = ε; _⁻¹ = _⁻¹}

  monoid : Monoid _ _ _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid public
    using (rawMagma; magma; semigroup; rawMonoid)

  module Unordered where
    group : NoOrder.Group c ℓ₁
    group = record { isGroup = IsGroup.Unordered.isGroup isGroup }

    open NoOrder.Group group public
      using (rawMagma; rawMonoid; rawGroup; magma; semigroup; monoid)

    open IsGroup.Unordered isGroup public

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
    hiding (module Unordered)

  group : Group _ _ _
  group = record { isGroup = isGroup }

  open Group group public
    using
    ( magma; semigroup; monoid
    ; rawMagma; rawMonoid; rawGroup
    )

  module Unordered where
    abelianGroup : NoOrder.AbelianGroup c ℓ₁
    abelianGroup =
      record { isAbelianGroup = IsAbelianGroup.Unordered.isAbelianGroup isAbelianGroup }

    open NoOrder.AbelianGroup abelianGroup public
      using (rawMagma; rawMonoid; rawGroup; magma; semigroup; monoid; commutativeMonoid; group)

    open IsAbelianGroup.Unordered isAbelianGroup public

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
    using ()
    renaming
    ( rawMagma to +-rawMagma
    ; rawMonoid to +-rawMonoid
    )

  *-rawMonoid : NoOrder.RawMonoid c ℓ₁
  *-rawMonoid = record { _≈_ = _≈_; _∙_ = _*_; ε = 1# }

  open NoOrder.RawMonoid *-rawMonoid public
    using ()
    renaming ( rawMagma to *-rawMagma )

  module Unordered where
    rawRing : NoOrder.RawRing c ℓ₁
    rawRing =
      record { _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = -_ ; 0# = 0# ; 1# = 1# }

    open NoOrder.RawRing rawRing public
      using (+-rawMagma; +-rawMonoid; +-rawGroup; rawSemiring)

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
    hiding (module Unordered)

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
    using ()
    renaming
    ( rawMagma to +-rawMagma
    ; rawMonoid to +-rawMonoid
    ; rawGroup to +-rawGroup
    ; magma to +-magma
    ; semigroup to +-semigroup
    ; monoid to +-monoid
    ; group to +-group
    )

  *-monoid : NoOrder.Monoid _ _
  *-monoid = record { isMonoid = *-isMonoid }

  open NoOrder.Monoid *-monoid public
    using ()
    renaming
    ( rawMagma to *-rawMagma
    ; rawMonoid to *-rawMonoid
    ; magma to *-magma
    ; semigroup to *-semigroup
    )

  module Unordered where
    ring : NoOrder.Ring c ℓ₁
    ring = record { isRing = IsRing.Unordered.isRing isRing }

    open NoOrder.Ring ring public
      using
      ( +-rawMagma; +-rawMonoid
      ; +-magma; +-semigroup; +-monoid; +-commutativeMonoid; +-group; +-abelianGroup
      ; rawRing; semiring
      )

    open IsRing.Unordered isRing public

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
    hiding (module Unordered)

  ring : Ring _ _ _
  ring = record { isRing = isRing }

  open Ring ring public
    using
    ( rawRing
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid
    ; *-magma; *-semigroup; *-monoid
    )

  module Unordered where
    commutativeRing : NoOrder.CommutativeRing c ℓ₁
    commutativeRing =
      record { isCommutativeRing = IsCommutativeRing.Unordered.isCommutativeRing isCommutativeRing }

    open NoOrder.CommutativeRing commutativeRing public
      using
      ( +-rawMagma; +-rawMonoid
      ; +-magma; +-semigroup; +-monoid; +-commutativeMonoid; +-group; +-abelianGroup
      ; rawRing; semiring; commutativeSemiring; ring
      )

    open NoOrder.Semiring semiring public
      using (rawSemiring)

    open IsCommutativeRing.Unordered isCommutativeRing public

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
    ( +-rawMagma; +-rawMonoid; +-rawGroup
    ; *-rawMagma; *-rawMonoid
    )

  *-rawAlmostGroup : NoOrder′.RawAlmostGroup c ℓ₁
  *-rawAlmostGroup = record
    { _≈_ = _≈_
    ; _∙_ = _*_
    ; 0#  = 0#
    ; 1#  = 1#
    ; _⁻¹ = _⁻¹
    }

  module Unordered where
    rawField : NoOrder′.RawField c ℓ₁
    rawField = record
      { _≈_ = _≈_
      ; _+_ = _+_
      ; _*_ = _*_
      ; -_  = -_
      ; 0#  = 0#
      ; 1#  = 1#
      ; _⁻¹ = _⁻¹
      }

    open NoOrder′.RawField rawField public
      using (+-rawMagma; +-rawMonoid; +-rawGroup; rawSemiring; rawRing)

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
    hiding (module Unordered)

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
    ( rawRing
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid
    ; *-magma; *-semigroup; *-monoid
    )

  *-almostGroup : NoOrder′.AlmostGroup _ _
  *-almostGroup = record { isAlmostGroup = *-isAlmostGroup }

  open NoOrder′.AlmostGroup *-almostGroup public
    using ()
    renaming (rawAlmostGroup to *-rawAlmostGroup)

  module Unordered where
    divisionRing : NoOrder′.DivisionRing c ℓ₁
    divisionRing =
      record { isDivisionRing = IsDivisionRing.Unordered.isDivisionRing isDivisionRing }

    open NoOrder′.DivisionRing divisionRing public
      using
      ( +-rawMagma; +-rawMonoid
      ; +-magma; +-semigroup; +-monoid; +-commutativeMonoid; +-group; +-abelianGroup
      ; rawSemiring; rawRing
      ; semiring; ring
      )

    open IsDivisionRing.Unordered isDivisionRing public

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
    hiding (module Unordered)

  divisionRing : DivisionRing c ℓ₁ ℓ₂
  divisionRing = record { isDivisionRing = isDivisionRing }

  open DivisionRing divisionRing public
    using
    ( rawRing; rawField; ring
    ; +-rawMagma; +-rawMonoid; +-rawGroup
    ; +-magma; +-semigroup; +-monoid; +-group; +-abelianGroup
    ; *-rawMagma; *-rawMonoid; *-rawAlmostGroup
    ; *-magma; *-semigroup; *-monoid; *-almostGroup
    )

  commutativeRing : CommutativeRing c ℓ₁ ℓ₂
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  module Unordered where
    field′ : NoOrder′.Field c ℓ₁
    field′ =
      record { isField = IsField.Unordered.isField isField }

    open NoOrder′.Field field′ public
      using
      ( +-rawMagma; +-rawMonoid
      ; +-magma; +-semigroup; +-monoid; +-commutativeMonoid; +-group; +-abelianGroup
      ; rawSemiring; rawRing
      ; semiring; commutativeSemiring; ring; commutativeRing; divisionRing
      )

    open IsField.Unordered isField public
