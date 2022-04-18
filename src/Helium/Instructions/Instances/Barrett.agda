------------------------------------------------------------------------
-- Agda Helium
--
-- Implementation of Barrett reduction.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Instructions.Instances.Barrett where

open import Data.Bool using (false)
open import Data.Sum using (inj₁)
open import Data.Vec using ([])
open import Data.Vec.Relation.Unary.All using ([])
open import Helium.Instructions.Base
open import Helium.Instructions.Core

-- Given:
--   m     = ⌊ (1 << l) * n⁻¹ ⌋
--   -n    = n
--   n     < 2 ^ 32
--   | z | < 2 ^ 31
-- Computes:
--   z mod n
barret : (m -n : Expression State [] (bits 32)) (t z : VecReg) (im : GenReg) → Procedure State []
barret m -n t z im =
  *index R (lit im) ≔ m ∙
  invoke vqrdmulh-s32,t,z,m [] ∙
  *index R (lit im) ≔ -n ∙
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
