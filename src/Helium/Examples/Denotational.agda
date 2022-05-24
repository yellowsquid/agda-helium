{-# OPTIONS --without-K #-}

module Helium.Examples.Denotational where

open import Helium.Examples.ConcreteModels using (pseudocode)

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
  hiding (ℤ; module ℤ)

open import Helium.Semantics.Core rawPseudocode
open import Helium.Semantics.Denotational.Core rawPseudocode renaming (module Semantics to Semantics′)

open import Data.Bool using (true; false)
open import Data.Fin.Patterns
open import Data.Integer as ℤ hiding (suc)
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

module Semantics = Semantics′ (λ { (*≡* eq) → contradiction eq (λ ()) })

zero-state : ⟦ State ⟧ₜₛ
zero-state = replicate (replicate (lift false))
           , replicate (replicate (lift false))
           , replicate (lift false)
           , replicate (lift false)
           , lift false
           , lift false
           , lift 0F

do-barrett : (n-1 : ℕ) →
             (zs : Vec ℤ 4) →
             True (suc n-1 ℕ.<? 4294967296) →
             True (⌊ mkℚᵘ (+ 4294967296) n-1 ⌋ ℤ.<? + 4294967296) →
             True (all? (λ z → ℤ.∣ z ∣ ℕ.<? 2147483648) zs) →
             Statement State []
do-barrett n-1 zs _ _ _ =
  for 4 (Q[ lit 0F , var 0F ] ≔ call (sliceⁱ 0) (index (lit zs) (var 0F) ∷ [])) ∙
  invoke (barrett
    (suc n-1)
    1F
    0F
    0F)
    []
  where
    instance
      n≢0 : ℕ.NonZero (suc n-1)
      n≢0 = _

barrett-101 : Statement State []
barrett-101 = do-barrett 100 (+ 1 ∷ + 7387 ∷ + 102 ∷ + 7473 ∷ []) _ _ _

test : _
test = Semantics.stmt barrett-101 (zero-state , _)
