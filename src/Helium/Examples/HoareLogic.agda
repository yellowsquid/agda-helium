{-# OPTIONS --without-K #-}

module Helium.Examples.HoareLogic where

open import Helium.Examples.ConcreteModels using (pseudocode)

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
  hiding (ℤ; module ℤ)

open import Helium.Semantics.Core rawPseudocode
open import Helium.Semantics.Axiomatic pseudocode

open import Data.Bool using (true; false)
open import Data.Fin.Patterns
open import Data.Integer as ℤ hiding (suc; pred; _≟_)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Rational.Unnormalised as ℚ
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.Vec.Relation.Unary.All using ([]; _∷_; all?)
open import Level using (lift)
open import Helium.Instructions.Base
open import Helium.Instructions.Instances.Barrett
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (True)
open import Relation.Nullary.Negation using (contradiction)

instance
  101≢0 : ℕ.NonZero 101
  101≢0 = _

Q : Assertion State [] []
Q = pred (↓ (! Q[ lit 1F , lit 0F ] ≟ call (sliceⁱ 0) (lit ℤ.1ℤ ∷ []))) ∧
    pred (↓ (! Q[ lit 1F , lit 1F ] ≟ call (sliceⁱ 0) (lit (+ 14) ∷ []))) ∧
    pred (↓ (! Q[ lit 1F , lit 2F ] ≟ call (sliceⁱ 0) (lit ℤ.1ℤ ∷ []))) ∧
    pred (↓ (! Q[ lit 1F , lit 3F ] ≟ call (sliceⁱ 0) (lit ℤ.-1ℤ ∷ [])))

do-barrett : {!!} ⊢ invoke (barrett 101 1F 0F 0F) [] ⊢ Q
do-barrett =
  invoke
    (seq
      {!!}
    (seq
      {!!}
    (seq
      {!!}

      (assign {!!})
      (invoke
        (for
          {!!}
          {!!}
          (seq
            {!!}
            {!!}
            {!!})
          {!!})))
      {!!})
      (invoke
        (for
          {!!}
          {!!}
          (seq
            {!!}
          (seq
            {!!}
          (seq
            {!!}
          (assign {!!})
          (assign {!!}))
          (invoke
            (declare
              (declare
                (declare
                  (seq
                    {!!}
                  (for
                    {!!}
                    {!!}
                    (declare
                      {!!})
                    {!!})
                  {!!}))))))
          {!!})
          {!!})))

-- zero-state : ⟦ State ⟧ₜₛ
-- zero-state = replicate (replicate (lift false))
--            , replicate (replicate (lift false))
--            , replicate (lift false)
--            , replicate (lift false)
--            , lift false
--            , lift false
--            , lift 0F

-- do-barrett : (n-1 : ℕ) →
--              (zs : Vec ℤ 4) →
--              True (suc n-1 ℕ.<? 4294967296) →
--              True (⌊ mkℚᵘ (+ 4294967296) n-1 ⌋ ℤ.<? + 4294967296) →
--              True (all? (λ z → ℤ.∣ z ∣ ℕ.<? 2147483648) zs) →
--              Statement State []
-- do-barrett n-1 zs _ _ _ =
--   for 4 (Q[ lit 0F , var 0F ] ≔ call (sliceⁱ 0) (index (lit zs) (var 0F) ∷ [])) ∙
--   invoke (barrett
--     (suc n-1)
--     1F
--     0F
--     0F)
--     []
--   where
--     instance
--       n≢0 : ℕ.NonZero (suc n-1)
--       n≢0 = _

-- barrett-101 : Statement State []
-- barrett-101 = do-barrett 100 (+ 1 ∷ + 7387 ∷ + 102 ∷ + 7473 ∷ []) _ _ _

-- test : _
-- test = Semantics.stmt barrett-101 (zero-state , _)
