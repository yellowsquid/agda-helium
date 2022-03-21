------------------------------------------------------------------------
-- Agda Helium
--
-- Semantics for the Armv8-M pseudocode using Hoare triples.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (Pseudocode)

module Helium.Semantics.Axiomatic
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode

open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ)
import Data.Nat.Literals as ℕₗ
import Data.Unit
open import Data.Vec using (Vec)
open import Helium.Data.Pseudocode.Core
import Helium.Semantics.Axiomatic.Core rawPseudocode as Core
import Helium.Semantics.Axiomatic.Assertion rawPseudocode as Assertion
import Helium.Semantics.Axiomatic.Term rawPseudocode as Term
import Helium.Semantics.Axiomatic.Triple rawPseudocode as Triple

open Assertion.Construct public
open Assertion.Assertion public

open Assertion public
  using (Assertion)

open Term.Term public
open Term public
  using (Term)

instance
  numberℕ : Number ℕ
  numberℕ = ℕₗ.number

2≉0 : 2 ℝ.≉ 0
2≉0 = ℝ.>⇒≉ (ℝ.n≉0⇒0<+n 2)

HoareTriple : ∀ {o} {Σ : Vec Type o} {n} {Γ : Vec Type n} {m} {Δ : Vec Type m} → Assertion Σ Γ Δ → Code.Statement Σ Γ → Assertion Σ Γ Δ → Set _
HoareTriple = Triple.HoareTriple 2≉0

ℰ : ∀ {o} {Σ : Vec Type o} {n} {Γ : Vec Type n} {m} {Δ : Vec Type m} {t : Type} → Code.Expression Σ Γ t → Term Σ Γ Δ t
ℰ = Term.ℰ 2≉0

open Triple.HoareTriple 2≉0 public
