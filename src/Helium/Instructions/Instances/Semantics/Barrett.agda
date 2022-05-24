------------------------------------------------------------------------
-- Agda Helium
--
-- Implementation of Barrett reduction.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Instructions.Instances.Semantics.Barrett
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; _++_; replicate)
open import Data.Vec.Relation.Unary.All as All using ([]; _∷_)
open import Function using (_∘_; id)

open import Data.Fin as Fin using (Fin; suc; fromℕ; inject₁)
open import Data.Fin.Patterns
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Helium.Instructions.Base
open import Helium.Semantics.Axiomatic pseudocode
open import Level using (lift; lower)

private
  variable
    o k m n : ℕ
    Σ Γ Δ : Vec Type n
    t t′ : Type

open import Helium.Instructions.Base
open import Helium.Instructions.Core
open import Helium.Instructions.Instances.Barrett

barrett-mod : ∀ x y t z im →
  HoareTriple {Γ = Γ} {Δ = Δ}
    false
    (invoke
      (barret (lit x) (lit y) t z im)
      [])
    true
barrett-mod x y t z im = invoke
  {!!}
  {!!}
  {!!}
  (seq {!!} (seq {!!} (seq {!!} (assign {!!}) (invoke {!!} {!!} {!!} (for {!!} {!!} (seq {!!} (seq {!!} (seq {!!} (assign {!!}) {!!}) (invoke {!!} {!!} {!!} (declare (declare (seq {!!} (assign {!!}) (declare (declare (seq {!!} (for {!!} {!!} (declare (declare (declare {!!}))) {!!}) {!!})))))) {!!})) {!!}) {!!}) {!!})) {!!}) {!!})
  {!!}
