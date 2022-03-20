------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of Hoare triples
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Axiomatic.Triple
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

import Data.Bool as Bool
import Data.Fin as Fin
open import Data.Fin.Patterns
open import Data.Nat using (suc)
open import Data.Vec using (Vec; _∷_)
open import Function using (_∘_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Axiomatic.Assertion rawPseudocode as Asrt
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (var; meta; func₀; func₁; 𝒦; ℰ; ℰ′)
open import Level using (_⊔_; lift; lower) renaming (suc to ℓsuc)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Unary using (_⊆′_)

module _ (2≉0 : Term.2≉0) {o} {Σ : Vec Type o} where
  open Code Σ
  data HoareTriple {n} {Γ : Vec Type n} {m} {Δ : Vec Type m} : Assertion Σ Γ Δ → Statement Γ → Assertion Σ Γ Δ → Set (ℓsuc (b₁ ⊔ i₁ ⊔ r₁)) where
    _∙_ : ∀ {P Q R s₁ s₂} → HoareTriple P s₁ Q → HoareTriple Q s₂ R → HoareTriple P (s₁ ∙ s₂) R
    skip : ∀ {P} → HoareTriple P skip P

    assign : ∀ {P t ref canAssign e} → HoareTriple (subst 2≉0 P (toWitness canAssign) (ℰ 2≉0 e)) (_≔_ {t = t} ref {canAssign} e) P
    declare : ∀ {t P Q e s} → HoareTriple (P ∧ equal (var 0F) (Term.wknVar (ℰ 2≉0 e))) s (Asrt.wknVar Q) → HoareTriple (Asrt.elimVar P (ℰ 2≉0 e)) (declare {t = t} e s) Q
    invoke : ∀ {m ts P Q s es} → HoareTriple P s (Asrt.addVars Q) → HoareTriple (Asrt.substVars P (ℰ′ 2≉0 es)) (invoke {m = m} {ts} (s ∙end) es) (Asrt.addVars Q)
    if : ∀ {P Q e s} → HoareTriple (P ∧ equal (ℰ 2≉0 e) (𝒦 (Bool.true ′b))) s Q → HoareTriple (P ∧ equal (ℰ 2≉0 e) (𝒦 (Bool.false ′b))) skip Q → HoareTriple P (if e then s) Q
    if-else : ∀ {P Q e s₁ s₂} → HoareTriple (P ∧ equal (ℰ 2≉0 e) (𝒦 (Bool.true ′b))) s₁ Q → HoareTriple (P ∧ equal (ℰ 2≉0 e) (𝒦 (Bool.false ′b))) s₂ Q → HoareTriple P (if e then s₁ else s₂) Q
    for : ∀ {m} {I : Assertion Σ Γ (fin (suc m) ∷ Δ)} {s} → HoareTriple (some (Asrt.wknVar (Asrt.wknMetaAt 1F I) ∧ equal (meta 1F) (var 0F) ∧ equal (meta 0F) (func₁ (lift ∘ Fin.inject₁ ∘ lower) (meta 1F)))) s (some (Asrt.wknVar (Asrt.wknMetaAt 1F I) ∧ equal (meta 0F) (func₁ (lift ∘ Fin.suc ∘ lower) (meta 1F)))) → HoareTriple (some (I ∧ equal (meta 0F) (func₀ (lift 0F)))) (for m s) (some (I ∧ equal (meta 0F) (func₀ (lift (Fin.fromℕ m)))))

    consequence : ∀ {P₁ P₂ Q₁ Q₂ s} → (∀ σ γ δ → ⟦ P₁ ⟧ σ γ δ → ⟦ P₂ ⟧ σ γ δ) → HoareTriple P₂ s Q₂ → (∀ σ γ δ → ⟦ Q₂ ⟧ σ γ δ → ⟦ Q₁ ⟧ σ γ δ) → HoareTriple P₁ s Q₁
    some : ∀ {t P Q s} → HoareTriple P s Q → HoareTriple (some {t = t} P) s (some Q)
