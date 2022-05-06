------------------------------------------------------------------------
-- Agda Helium
--
-- Semantics for the Armv8-M pseudocode using Hoare triples.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (Pseudocode)

module Helium.Semantics.Axiomatic
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode

open import Data.Nat using (ℕ)
import Data.Unit
open import Function using (_∘_)
import Helium.Semantics.Core rawPseudocode as Core′
import Helium.Semantics.Axiomatic.Term rawPseudocode as Term′
import Helium.Semantics.Axiomatic.Assertion rawPseudocode as Assertion′

private
  proof-2≉0 : Core′.2≉0
  proof-2≉0 = ℝ.<⇒≉ (ℝ.n≢0∧x>0⇒n×x>0 2 (ℝ.≤∧≉⇒< ℝ.0≤1 (ℝ.1≉0 ∘ ℝ.Eq.sym))) ∘ ℝ.Eq.sym

module Core where
  open Core′ public hiding (shift)

  shift : ℤ → ℕ → ℤ
  shift = Core′.shift proof-2≉0

open Core public using (⟦_⟧ₜ; ⟦_⟧ₜ′; _≈_; _<_; Κ[_]_; 2≉0)

module Term where
  open Term′ public hiding (module Semantics)
  module Semantics {i} {j} {k} where
    open Term′.Semantics {i} {j} {k} proof-2≉0 public
  open Semantics public using (⟦_⟧)

open Term public using (Term; ↓_) hiding (module Term)
open Term.Term public

module Assertion where
  open Assertion′ public hiding (module Semantics)
  module Semantics where
    open Assertion′.Semantics proof-2≉0 public
  open Semantics public using (⟦_⟧)

open Assertion public using (Assertion) hiding (module Assertion)
open Assertion.Assertion public
open Assertion.Construct public

open import Helium.Semantics.Axiomatic.Triple rawPseudocode proof-2≉0 public
