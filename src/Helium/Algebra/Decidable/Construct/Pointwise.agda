------------------------------------------------------------------------
-- Agda Helium
--
-- Construct algebras of vectors in a pointwise manner
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Algebra.Decidable.Construct.Pointwise where

open import Algebra.Lattice.Bundles using (RawLattice)
open import Algebra.Core
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec.Functional using (replicate; map; zipWith)
open import Data.Vec.Functional.Relation.Binary.Pointwise using (Pointwise)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pwₚ
open import Function using (_$_)
open import Helium.Algebra.Decidable.Bundles
open import Helium.Algebra.Decidable.Structures
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)

module _ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} where
  private
    _≋_ = Pointwise _≈_

  module _ {∨ ∧ : Op₂ A} where
    isLattice : IsLattice _≈_ ∨ ∧ → ∀ n → IsLattice (_≋_ {n}) (zipWith ∨) (zipWith ∧)
    isLattice L n = record
      { isDecEquivalence = Pwₚ.isDecEquivalence isDecEquivalence n
      ; ∨-comm           = λ x y i → ∨-comm (x i) (y i)
      ; ∨-assoc          = λ x y z i → ∨-assoc (x i) (y i) (z i)
      ; ∨-cong           = λ x≈y u≈v i → ∨-cong (x≈y i) (u≈v i)
      ; ∧-comm           = λ x y i → ∧-comm (x i) (y i)
      ; ∧-assoc          = λ x y z i → ∧-assoc (x i) (y i) (z i)
      ; ∧-cong           = λ x≈y u≈v i → ∧-cong (x≈y i) (u≈v i)
      ; absorptive       = (λ x y i → ∨-absorbs-∧ (x i) (y i))
                         , (λ x y i → ∧-absorbs-∨ (x i) (y i))
      }
      where open IsLattice L

    isDistributiveLattice : IsDistributiveLattice _≈_ ∨ ∧ → ∀ n → IsDistributiveLattice (_≋_ {n}) (zipWith ∨) (zipWith ∧)
    isDistributiveLattice L n = record
      { isLattice = isLattice L.isLattice n
      ; ∨-distrib-∧ = (λ x y z i → L.∨-distribˡ-∧ (x i) (y i) (z i))
                    , (λ x y z i → L.∨-distribʳ-∧ (x i) (y i) (z i))
      }
      where module L = IsDistributiveLattice L

  module _ {∨ ∧ : Op₂ A} {¬ : Op₁ A} {⊤ ⊥ : A} where
    isBooleanAlgebra : IsBooleanAlgebra _≈_ ∨ ∧ ¬ ⊤ ⊥ → ∀ n → IsBooleanAlgebra (_≋_ {n}) (zipWith ∨) (zipWith ∧) (map ¬) (replicate ⊤) (replicate ⊥)
    isBooleanAlgebra B n = record
      { isDistributiveLattice = isDistributiveLattice B.isDistributiveLattice n
      ; ∨-complement = (λ x i → B.∨-complementˡ (x i))
                     , (λ x i → B.∨-complementʳ (x i))
      ; ∧-complement = (λ x i → B.∧-complementˡ (x i))
                     , (λ x i → B.∧-complementʳ (x i))
      ; ¬-cong = λ x≈y i → B.¬-cong (x≈y i)
      }
      where module B = IsBooleanAlgebra B

rawLattice : ∀ {a ℓ} → RawLattice a ℓ → ℕ → RawLattice a ℓ
rawLattice L n = record
  { _≈_ = Pointwise _≈_ {n}
  ; _∧_ = zipWith _∧_
  ; _∨_ = zipWith _∨_
  }
  where open RawLattice L

lattice : ∀ {a ℓ} → Lattice a ℓ → ℕ → Lattice a ℓ
lattice L n = record { isLattice = isLattice (Lattice.isLattice L) n }

distributiveLattice : ∀ {a ℓ} → DistributiveLattice a ℓ → ℕ → DistributiveLattice a ℓ
distributiveLattice L n = record
  { isDistributiveLattice =
    isDistributiveLattice (DistributiveLattice.isDistributiveLattice L) n
  }

rawBooleanAlgebra : ∀ {a ℓ} → RawBooleanAlgebra a ℓ → ℕ → RawBooleanAlgebra a ℓ
rawBooleanAlgebra B n = record
  { _≈_ = Pointwise _≈_ {n}
  ; _∧_ = zipWith _∧_
  ; _∨_ = zipWith _∨_
  ; ¬_  = map ¬_
  ; ⊤   = replicate ⊤
  ; ⊥   = replicate ⊥
  }
  where open RawBooleanAlgebra B

booleanAlgebra : ∀ {a ℓ} → BooleanAlgebra a ℓ → ℕ → BooleanAlgebra a ℓ
booleanAlgebra B n = record
  { isBooleanAlgebra = isBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra B) n }
