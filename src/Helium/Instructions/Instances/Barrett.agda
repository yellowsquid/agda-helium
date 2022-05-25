------------------------------------------------------------------------
-- Agda Helium
--
-- Implementation of Barrett reduction.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Instructions.Instances.Barrett where

open import Data.Bool using (false)
open import Data.Integer as ℤ using (-[1+_])
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.DivMod as DivMod
open import Data.Rational.Unnormalised using (mkℚᵘ)
open import Data.Sum using (inj₁)
open import Data.Vec using ([])
open import Data.Vec.Relation.Unary.All using ([]; _∷_)
open import Helium.Instructions.Base
open import Helium.Instructions.Core
open import Relation.Binary.PropositionalEquality using (_≢_)

-- Given:
--   n
-- Computes:
--   z mod n
barrett : (n : ℕ) → ⦃ n-pos : ℕ.NonZero n ⦄ → (t z : VecReg) (im : GenReg) → Procedure State []
barrett (suc n) ⦃ n≢0 ⦄ t z im =
  *index R (lit im) ≔ call (sliceⁱ 0) (lit (ℤ.+ (4294967296 DivMod.div (2 ℕ.* suc n))) ∷ []) ∙
  invoke vqrdmulh-s32,t,z,m [] ∙
  *index R (lit im) ≔ call (sliceⁱ 0) (lit -[1+ n ] ∷ []) ∙
  invoke vmla-s32,z,t,-n [] ∙end
  where
  vqrdmulh-s32,t,z,m =
    ExecBeats (vqrdmulh (record
      { size = 32bit
      ; dest = t
      ; src₁ = z
      ; src₂ = inj₁ im
      }))
  vmla-s32,z,t,-n =
    ExecBeats (vmla (record
      { size     = 32bit
      ; unsigned = false
      ; acc      = z
      ; src₁     = t
      ; src₂     = im
      }))

open import Data.Fin.Patterns
