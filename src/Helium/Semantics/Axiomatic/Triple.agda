------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of Hoare triples
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)
import Helium.Semantics.Core as Core

module Helium.Semantics.Axiomatic.Triple
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  (2≉0 : Core.2≉0 rawPseudocode)
  where

private
  open module C = RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Fin using (fromℕ; suc; inject₁)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Relation.Unary.All as All using (All)
open import Function using (_∘_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Axiomatic.Assertion rawPseudocode as Asrt
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (↓_)
open import Level using (_⊔_; lift; lower) renaming (suc to ℓsuc)
open import Relation.Nullary.Decidable.Core using (toWitness)

open Term.Term
open Semantics 2≉0

private
  variable
    i j k m n : ℕ
    t : Type
    Σ Γ Δ ts : Vec Type n
    P Q R S : Assertion Σ Γ Δ
    ref : Reference Σ Γ t
    e val : Expression Σ Γ t
    es : All (Expression Σ Γ) ts
    s s₁ s₂ : Statement Σ Γ

  ℓ = i₁ ⊔ r₁

infix 4 _⊆_
record _⊆_ (P : Assertion Σ Γ Δ) (Q : Assertion Σ Γ Δ) : Set ℓ where
  constructor arr
  field
    implies : ∀ σ γ δ → ⟦ P ⟧ σ γ δ → ⟦ Q ⟧ σ γ δ

open _⊆_ public

data HoareTriple {Σ : Vec Type i} {Γ : Vec Type j} {Δ : Vec Type k} : Assertion Σ Γ Δ → Statement Σ Γ → Assertion Σ Γ Δ → Set (ℓsuc ℓ) where
  seq     : ∀ Q → HoareTriple P s Q → HoareTriple Q s₁ R → HoareTriple P (s ∙ s₁) R
  skip    : P ⊆ Q → HoareTriple P skip Q
  assign  : P ⊆ subst Q ref (↓ val) → HoareTriple P (ref ≔ val) Q
  declare : HoareTriple (Var.weaken 0F P ∧ equal (var 0F) (Term.Var.weaken 0F (↓ e))) s (Var.weaken 0F Q) → HoareTriple P (declare e s) Q
  invoke  : let metas = All.map (Term.Meta.inject Δ) (All.tabulate meta) in
            let varsToMetas = λ P → Var.elimAll (Meta.weakenAll [] Γ P) metas in
            let termVarsToMetas = λ t → Term.Var.elimAll (Term.Meta.weakenAll [] Γ t) metas in
    HoareTriple (varsToMetas P ∧ equal (↓ tup (All.tabulate var)) (termVarsToMetas (↓ tup es))) s (varsToMetas Q) →
    HoareTriple P (invoke (s ∙end) es) Q
  if      : HoareTriple (P ∧ pred (↓ e)) s Q → P ∧ pred (↓ inv e) ⊆ Q → HoareTriple P (if e then s) Q
  if-else : HoareTriple (P ∧ pred (↓ e)) s Q → HoareTriple (P ∧ pred (↓ inv e)) s Q → HoareTriple P (if e then s) Q
  for     : ∀ (I : Assertion _ _ (fin _ ∷ _)) → P ⊆ Meta.elim 0F I (↓ lit 0F) → HoareTriple {Δ = fin _ ∷ Δ} (Var.weaken 0F (Meta.elim 1F (Meta.weaken 0F I) (fin inject₁ (cons (meta 0F) nil)))) s (Var.weaken 0F (Meta.elim 1F (Meta.weaken 0F I) (fin suc (cons (meta 0F) nil)))) → Meta.elim 0F I (↓ lit (fromℕ m)) ⊆ Q → HoareTriple P (for m s) Q
