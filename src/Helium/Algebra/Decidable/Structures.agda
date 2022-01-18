------------------------------------------------------------------------
-- Agda Helium
--
-- Some decidable algebraic structures (not packed up with sets,
-- operations, etc.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Helium.Algebra.Decidable.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Core
open import Algebra.Definitions (_≈_)
open import Data.Product using (proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary.Structures using (IsDecEquivalence)

record IsLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isDecEquivalence : IsDecEquivalence _≈_
    ∨-comm           : Commutative ∨
    ∨-assoc          : Associative ∨
    ∨-cong           : Congruent₂ ∨
    ∧-comm           : Commutative ∧
    ∧-assoc          : Associative ∧
    ∧-cong           : Congruent₂ ∧
    absorptive       : Absorptive ∨ ∧

  open IsDecEquivalence isDecEquivalence public

  ∨-absorbs-∧ : ∨ Absorbs ∧
  ∨-absorbs-∧ = proj₁ absorptive

  ∧-absorbs-∨ : ∧ Absorbs ∨
  ∧-absorbs-∨ = proj₂ absorptive

  ∧-congˡ : LeftCongruent ∧
  ∧-congˡ y≈z = ∧-cong refl y≈z

  ∧-congʳ : RightCongruent ∧
  ∧-congʳ y≈z = ∧-cong y≈z refl

  ∨-congˡ : LeftCongruent ∨
  ∨-congˡ y≈z = ∨-cong refl y≈z

  ∨-congʳ : RightCongruent ∨
  ∨-congʳ y≈z = ∨-cong y≈z refl

record IsDistributiveLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isLattice   : IsLattice ∨ ∧
    ∨-distrib-∧ : ∨ DistributesOver ∧

  open IsLattice isLattice public

  ∨-distribˡ-∧ : ∨ DistributesOverˡ ∧
  ∨-distribˡ-∧ = proj₁ ∨-distrib-∧

  ∨-distribʳ-∧ : ∨ DistributesOverʳ ∧
  ∨-distribʳ-∧ = proj₂ ∨-distrib-∧

record IsBooleanAlgebra
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complement          : Inverse ⊤ ¬ ∨
    ∧-complement          : Inverse ⊥ ¬ ∧
    ¬-cong                : Congruent₁ ¬

  open IsDistributiveLattice isDistributiveLattice public

  ∨-complementˡ : LeftInverse ⊤ ¬ ∨
  ∨-complementˡ = proj₁ ∨-complement

  ∨-complementʳ : RightInverse ⊤ ¬ ∨
  ∨-complementʳ = proj₂ ∨-complement

  ∧-complementˡ : LeftInverse ⊥ ¬ ∧
  ∧-complementˡ = proj₁ ∧-complement

  ∧-complementʳ : RightInverse ⊥ ¬ ∧
  ∧-complementʳ = proj₂ ∧-complement
