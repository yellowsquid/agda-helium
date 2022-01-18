------------------------------------------------------------------------
-- Agda Helium
--
-- Definitions of decidable algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Helium.Algebra.Decidable.Bundles where

open import Algebra.Bundles using (RawLattice)
open import Algebra.Core
open import Helium.Algebra.Decidable.Structures
open import Level using (suc; _⊔_)
open import Relation.Binary.Bundles using (DecSetoid)
open import Relation.Binary.Core using (Rel)

record Lattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier   : Set c
    _≈_       : Rel Carrier ℓ
    _∨_       : Op₂ Carrier
    _∧_       : Op₂ Carrier
    isLattice : IsLattice _≈_ _∨_ _∧_

  open IsLattice isLattice public

  rawLattice : RawLattice c ℓ
  rawLattice = record
    { _≈_  = _≈_
    ; _∧_  = _∧_
    ; _∨_  = _∨_
    }

  open RawLattice rawLattice public
    using (∨-rawMagma; ∧-rawMagma)

  decSetoid : DecSetoid _ _
  decSetoid = record { isDecEquivalence = isDecEquivalence }

  open DecSetoid decSetoid public
    using (_≉_; setoid)

record DistributiveLattice c ℓ : Set (suc (c ⊔ ℓ)) where
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _∨_                   : Op₂ Carrier
    _∧_                   : Op₂ Carrier
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_

  open IsDistributiveLattice isDistributiveLattice public

  lattice : Lattice _ _
  lattice = record { isLattice = isLattice }

  open Lattice lattice public
    using (_≉_; setoid; decSetoid; ∨-rawMagma; ∧-rawMagma; rawLattice)

record RawBooleanAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∧_     : Op₂ Carrier
    _∨_     : Op₂ Carrier
    ¬_      : Op₁ Carrier
    ⊤       : Carrier
    ⊥       : Carrier

  rawLattice : RawLattice c ℓ
  rawLattice = record { _≈_ = _≈_; _∨_ = _∨_; _∧_ = _∧_ }

  open RawLattice rawLattice public
    using (_≉_; ∨-rawMagma; ∧-rawMagma)

record BooleanAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    _∨_              : Op₂ Carrier
    _∧_              : Op₂ Carrier
    ¬_               : Op₁ Carrier
    ⊤                : Carrier
    ⊥                : Carrier
    isBooleanAlgebra : IsBooleanAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsBooleanAlgebra isBooleanAlgebra public

  distributiveLattice : DistributiveLattice _ _
  distributiveLattice = record { isDistributiveLattice = isDistributiveLattice }

  open DistributiveLattice distributiveLattice public
    using (_≉_; setoid; decSetoid; ∨-rawMagma; ∧-rawMagma; rawLattice; lattice)
