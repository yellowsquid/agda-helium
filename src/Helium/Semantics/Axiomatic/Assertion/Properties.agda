--------------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of the Assertion type.
--------------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Semantics.Axiomatic.Assertion.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
open import Data.Empty using (⊥-elim)
import Data.Integer as 𝕀
open import Data.Fin as Fin using (suc; punchIn)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product as × using (_,_; uncurry; map₂)
import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; insert; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function hiding (_⟶_)
open import Function.Nary.NonDependent using (congₙ)
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Level using (_⊔_; Lift; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no)

open import Helium.Semantics.Axiomatic pseudocode
import Helium.Semantics.Axiomatic.Term.Properties pseudocode
  as Termₚ
import Helium.Semantics.Core.Properties pseudocode
  as Coreₚ
open import Helium.Semantics.Denotational.Core rawPseudocode
  renaming (module Semantics to Semantics′)

private
  variable
    o k m n : ℕ
    Σ Γ Δ ts : Vec Type n
    t t′ : Type

  module Semantics = Semantics′ proof-2≉0

private
  ℓ = i₁ ⊔ r₁

pred-witness : ∀ (e₁ e₂ : Term Σ Γ Δ t) → ⦃ hasEq : HasEquality t ⦄ → ∀ σ γ δ → Term.⟦ e₁ ⟧ σ γ δ Core.≈ Term.⟦ e₂ ⟧ σ γ δ → Assertion.⟦ pred (e₁ ≟ e₂) ⟧ σ γ δ
pred-witness e₁ e₂ σ γ δ eq with Core.≈-dec (Term.⟦ e₁ ⟧ σ γ δ) (Term.⟦ e₂ ⟧ σ γ δ)
... | yes _  = _
... | no neq = ⊥-elim (neq eq)

module Construct where
  equal-refl : ∀ (e₁ e₂ : Term Σ Γ Δ t) σ γ δ  → Term.⟦ e₁ ⟧ σ γ δ ≡ Term.⟦ e₂ ⟧ σ γ δ → Assertion.⟦ equal e₁ e₂ ⟧ σ γ δ
  equal-refl {t = bool}                e₁ e₂ σ γ δ eq = pred-witness e₁ e₂ σ γ δ (Coreₚ.≈-reflexive (Term.⟦ e₁ ⟧ σ γ δ) (Term.⟦ e₂ ⟧ σ γ δ) eq)
  equal-refl {t = int}                 e₁ e₂ σ γ δ eq = pred-witness e₁ e₂ σ γ δ (Coreₚ.≈-reflexive (Term.⟦ e₁ ⟧ σ γ δ) (Term.⟦ e₂ ⟧ σ γ δ) eq)
  equal-refl {t = fin n}               e₁ e₂ σ γ δ eq = pred-witness e₁ e₂ σ γ δ (Coreₚ.≈-reflexive (Term.⟦ e₁ ⟧ σ γ δ) (Term.⟦ e₂ ⟧ σ γ δ) eq)
  equal-refl {t = real}                e₁ e₂ σ γ δ eq = pred-witness e₁ e₂ σ γ δ (Coreₚ.≈-reflexive (Term.⟦ e₁ ⟧ σ γ δ) (Term.⟦ e₂ ⟧ σ γ δ) eq)
  equal-refl {t = tuple []}            e₁ e₂ σ γ δ eq = _
  equal-refl {t = tuple (t ∷ [])}      e₁ e₂ σ γ δ eq = equal-refl (head e₁) (head e₂) σ γ δ eq
  equal-refl {t = tuple (t ∷ t₁ ∷ ts)} e₁ e₂ σ γ δ eq = equal-refl (head e₁) (head e₂) σ γ δ (cong ×.proj₁ eq) , equal-refl (tail e₁) (tail e₂) σ γ δ (cong ×.proj₂ eq)
  equal-refl {t = array t 0}           e₁ e₂ σ γ δ eq = _
  equal-refl {Δ = Δ} {t = array t (suc n)}     e₁ e₂ σ γ δ eq = λ x →
    equal-refl (Assertion.indexTerm e₁) (Assertion.indexTerm e₂) σ γ (Core.cons′ Δ x δ)
      (cong (Vec.head ∘ flip Core.sliceVec (lower (Core.fetch 0F (fin (suc n) ∷ Δ) (Core.cons′ Δ x δ))) ∘ Core.castVec (ℕₚ.+-comm 1 _)) (begin
        Term.⟦ Term.Meta.weaken 0F e₁ ⟧ σ γ (Core.cons′ Δ x δ)
          ≡⟨ Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F x) e₁ σ γ δ ⟩
        Term.⟦ e₁ ⟧ σ γ δ
          ≡⟨ eq ⟩
        Term.⟦ e₂ ⟧ σ γ δ
          ≡˘⟨ Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F x) e₂ σ γ δ ⟩
        Term.⟦ Term.Meta.weaken 0F e₂ ⟧ σ γ (Core.cons′ Δ x δ)
          ∎))
    where open ≡-Reasoning

module Var where
  weaken⇒ : ∀ i t (v : ⟦ t ⟧ₜ) (P : Assertion Σ Γ Δ) σ γ δ → Assertion.⟦ Assertion.Var.weaken {t = t} i P ⟧ σ (Core.insert′ i Γ γ v) δ → Assertion.⟦ P ⟧ σ γ δ
  weaken⇐ : ∀ i t (v : ⟦ t ⟧ₜ) (P : Assertion Σ Γ Δ) σ γ δ → Assertion.⟦ P ⟧ σ γ δ → Assertion.⟦ Assertion.Var.weaken {t = t} i P ⟧ σ (Core.insert′ i Γ γ v) δ

  weaken⇒ {Δ = Δ} i t v (all P)  σ γ δ deriv = weaken⇒ i t v P σ γ (Core.cons′ Δ _ δ) ∘ deriv
  weaken⇒ {Δ = Δ} i t v (some P) σ γ δ deriv = map₂ (weaken⇒ i t v P σ γ (Core.cons′ Δ _ δ)) deriv
  weaken⇒         i t v (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (Termₚ.RecBuilder⇒.extend (Termₚ.Var.weakenBuilder i v) p σ γ δ) deriv
  weaken⇒         i t v true     σ γ δ deriv = deriv
  weaken⇒         i t v (¬ P)    σ γ δ deriv = deriv ∘ weaken⇐ i t v P σ γ δ
  weaken⇒         i t v (P ∧ Q)  σ γ δ deriv = ×.map (weaken⇒ i t v P σ γ δ) (weaken⇒ i t v Q σ γ δ) deriv
  weaken⇒         i t v (P ∨ Q)  σ γ δ deriv = ⊎.map (weaken⇒ i t v P σ γ δ) (weaken⇒ i t v Q σ γ δ) deriv
  weaken⇒         i t v (P ⟶ Q)  σ γ δ deriv = weaken⇒ i t v Q σ γ δ ∘ deriv ∘ weaken⇐ i t v P σ γ δ

  weaken⇐ {Δ = Δ} i t v (all P)  σ γ δ deriv = weaken⇐ i t v P σ γ (Core.cons′ Δ _ δ) ∘ deriv
  weaken⇐ {Δ = Δ} i t v (some P) σ γ δ deriv = map₂ (weaken⇐ i t v P σ γ (Core.cons′ Δ _ δ)) deriv
  weaken⇐         i t v (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (sym (Termₚ.RecBuilder⇒.extend (Termₚ.Var.weakenBuilder i v) p σ γ δ)) deriv
  weaken⇐         i t v true     σ γ δ deriv = deriv
  weaken⇐         i t v (¬ P)    σ γ δ deriv = deriv ∘ weaken⇒ i t v P σ γ δ
  weaken⇐         i t v (P ∧ Q)  σ γ δ deriv = ×.map (weaken⇐ i t v P σ γ δ) (weaken⇐ i t v Q σ γ δ) deriv
  weaken⇐         i t v (P ∨ Q)  σ γ δ deriv = ⊎.map (weaken⇐ i t v P σ γ δ) (weaken⇐ i t v Q σ γ δ) deriv
  weaken⇐         i t v (P ⟶ Q)  σ γ δ deriv = weaken⇐ i t v Q σ γ δ ∘ deriv ∘ weaken⇒ i t v P σ γ δ

  elimAll⇒ : ∀ (P : Assertion Σ Γ Δ) (es : All (Term Σ ts Δ) Γ) σ γ δ → Assertion.⟦ Assertion.Var.elimAll P es ⟧ σ γ δ → Assertion.⟦ P ⟧ σ (Term.⟦ es ⟧ₛ σ γ δ) δ
  elimAll⇐ : ∀ (P : Assertion Σ Γ Δ) (es : All (Term Σ ts Δ) Γ) σ γ δ → Assertion.⟦ P ⟧ σ (Term.⟦ es ⟧ₛ σ γ δ) δ → Assertion.⟦ Assertion.Var.elimAll P es ⟧ σ γ δ

  elimAll⇒ {Δ = Δ} (all P)  es σ γ δ deriv = subst (λ γ → Assertion.⟦ P ⟧ σ γ (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extends (Termₚ.Meta.weakenBuilder 0F _) es σ γ δ) ∘ elimAll⇒ P (Term.RecBuilder.extends (Term.Meta.weakenBuilder 0F) es) σ γ (Core.cons′ Δ _ δ) ∘ deriv
  elimAll⇒ {Δ = Δ} (some P) es σ γ δ deriv = map₂ (subst (λ γ → Assertion.⟦ P ⟧ σ γ (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extends (Termₚ.Meta.weakenBuilder 0F _) es σ γ δ) ∘ elimAll⇒ P (Term.RecBuilder.extends (Term.Meta.weakenBuilder 0F) es) σ γ (Core.cons′ Δ _ δ)) deriv
  elimAll⇒         (pred p) es σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (Termₚ.RecBuilder⇐.extend (Termₚ.Var.elimAllBuilder es) p σ γ δ) deriv
  elimAll⇒         true     es σ γ δ deriv = deriv
  elimAll⇒         (¬ P)    es σ γ δ deriv = deriv ∘ elimAll⇐ P es σ γ δ
  elimAll⇒         (P ∧ Q)  es σ γ δ deriv = ×.map (elimAll⇒ P es σ γ δ) (elimAll⇒ Q es σ γ δ) deriv
  elimAll⇒         (P ∨ Q)  es σ γ δ deriv = ⊎.map (elimAll⇒ P es σ γ δ) (elimAll⇒ Q es σ γ δ) deriv
  elimAll⇒         (P ⟶ Q)  es σ γ δ deriv = elimAll⇒ Q es σ γ δ ∘ deriv ∘ elimAll⇐ P es σ γ δ

  elimAll⇐ {Δ = Δ} (all P)  es σ γ δ deriv = elimAll⇐ P (Term.RecBuilder.extends (Term.Meta.weakenBuilder 0F) es) σ γ (Core.cons′ Δ _ δ) ∘ subst (λ γ → Assertion.⟦ P ⟧ σ γ (Core.cons′ Δ _ δ)) (sym (Termₚ.RecBuilder⇒.extends (Termₚ.Meta.weakenBuilder 0F _) es σ γ δ)) ∘ deriv
  elimAll⇐ {Δ = Δ} (some P) es σ γ δ deriv = map₂ (elimAll⇐ P (Term.RecBuilder.extends (Term.Meta.weakenBuilder 0F) es) σ γ (Core.cons′ Δ _ δ) ∘ subst (λ γ → Assertion.⟦ P ⟧ σ γ (Core.cons′ Δ _ δ)) (sym (Termₚ.RecBuilder⇒.extends (Termₚ.Meta.weakenBuilder 0F _) es σ γ δ))) deriv
  elimAll⇐         (pred p) es σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (sym (Termₚ.RecBuilder⇐.extend (Termₚ.Var.elimAllBuilder es) p σ γ δ)) deriv
  elimAll⇐         true     es σ γ δ deriv = deriv
  elimAll⇐         (¬ P)    es σ γ δ deriv = deriv ∘ elimAll⇒ P es σ γ δ
  elimAll⇐         (P ∧ Q)  es σ γ δ deriv = ×.map (elimAll⇐ P es σ γ δ) (elimAll⇐ Q es σ γ δ) deriv
  elimAll⇐         (P ∨ Q)  es σ γ δ deriv = ⊎.map (elimAll⇐ P es σ γ δ) (elimAll⇐ Q es σ γ δ) deriv
  elimAll⇐         (P ⟶ Q)  es σ γ δ deriv = elimAll⇐ Q es σ γ δ ∘ deriv ∘ elimAll⇒ P es σ γ δ

module Meta where
  weaken⇒ : ∀ i t (v : ⟦ t ⟧ₜ) (P : Assertion Σ Γ Δ) σ γ δ → Assertion.⟦ Assertion.Meta.weaken {t = t} i P ⟧ σ γ (Core.insert′ i Δ δ v) → Assertion.⟦ P ⟧ σ γ δ
  weaken⇐ : ∀ i t (v : ⟦ t ⟧ₜ) (P : Assertion Σ Γ Δ) σ γ δ → Assertion.⟦ P ⟧ σ γ δ → Assertion.⟦ Assertion.Meta.weaken {t = t} i P ⟧ σ γ (Core.insert′ i Δ δ v)

  weaken⇒ {Δ = Δ} i t v (all P)  σ γ δ deriv = weaken⇒ (suc i) t v P σ γ (Core.cons′ Δ _ δ) ∘ subst (Assertion.⟦ _ ⟧ σ γ) (sym (Coreₚ.insert′-cons′ i Δ δ _ v)) ∘ deriv
  weaken⇒ {Δ = Δ} i t v (some P) σ γ δ deriv = map₂ (weaken⇒ (suc i) t v P σ γ (Core.cons′ Δ _ δ) ∘ subst (Assertion.⟦ _ ⟧ σ γ) (sym (Coreₚ.insert′-cons′ i Δ δ _ v))) deriv
  weaken⇒         i t v (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder i v) p σ γ δ) deriv
  weaken⇒         i t v true     σ γ δ deriv = deriv
  weaken⇒         i t v (¬ P)    σ γ δ deriv = deriv ∘ weaken⇐ i t v P σ γ δ
  weaken⇒         i t v (P ∧ Q)  σ γ δ deriv = ×.map (weaken⇒ i t v P σ γ δ) (weaken⇒ i t v Q σ γ δ) deriv
  weaken⇒         i t v (P ∨ Q)  σ γ δ deriv = ⊎.map (weaken⇒ i t v P σ γ δ) (weaken⇒ i t v Q σ γ δ) deriv
  weaken⇒         i t v (P ⟶ Q)  σ γ δ deriv = weaken⇒ i t v Q σ γ δ ∘ deriv ∘ weaken⇐ i t v P σ γ δ

  weaken⇐ {Δ = Δ} i t v (all P)  σ γ δ deriv = subst (Assertion.⟦ _ ⟧ σ γ) (Coreₚ.insert′-cons′ i Δ δ _ v) ∘ weaken⇐ (suc i) t v P σ γ (Core.cons′ Δ _ δ) ∘ deriv
  weaken⇐ {Δ = Δ} i t v (some P) σ γ δ deriv = map₂ (subst (Assertion.⟦ _ ⟧ σ γ) (Coreₚ.insert′-cons′ i Δ δ _ v) ∘ weaken⇐ (suc i) t v P σ γ (Core.cons′ Δ _ δ)) deriv
  weaken⇐         i t v (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (sym (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder i v) p σ γ δ)) deriv
  weaken⇐         i t v true     σ γ δ deriv = deriv
  weaken⇐         i t v (¬ P)    σ γ δ deriv = deriv ∘ weaken⇒ i t v P σ γ δ
  weaken⇐         i t v (P ∧ Q)  σ γ δ deriv = ×.map (weaken⇐ i t v P σ γ δ) (weaken⇐ i t v Q σ γ δ) deriv
  weaken⇐         i t v (P ∨ Q)  σ γ δ deriv = ⊎.map (weaken⇐ i t v P σ γ δ) (weaken⇐ i t v Q σ γ δ) deriv
  weaken⇐         i t v (P ⟶ Q)  σ γ δ deriv = weaken⇐ i t v Q σ γ δ ∘ deriv ∘ weaken⇒ i t v P σ γ δ

  elim⇒ : ∀ i (e : Term Σ Γ Δ t) (P : Assertion Σ Γ (insert Δ i t)) σ γ δ → Assertion.⟦ Assertion.Meta.elim i P e ⟧ σ γ δ → Assertion.⟦ P ⟧ σ γ (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ))
  elim⇐ : ∀ i (e : Term Σ Γ Δ t) (P : Assertion Σ Γ (insert Δ i t)) σ γ δ → Assertion.⟦ P ⟧ σ γ (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ)) → Assertion.⟦ Assertion.Meta.elim i P e ⟧ σ γ δ

  elim⇒ {Δ = Δ} i e (all P)  σ γ δ deriv = subst (Assertion.⟦ _ ⟧ σ γ) (trans (cong (Core.insert′ (suc i) (_ ∷ Δ) (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F _) e σ γ δ)) (Coreₚ.insert′-cons′ i Δ δ _ (Term.⟦ e ⟧ σ γ δ))) ∘ elim⇒ (suc i) (Term.Meta.weaken 0F e) P σ γ (Core.cons′ Δ _ δ) ∘ deriv
  elim⇒ {Δ = Δ} i e (some P) σ γ δ deriv = map₂ (subst (Assertion.⟦ _ ⟧ σ γ) (trans (cong (Core.insert′ (suc i) (_ ∷ Δ) (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F _) e σ γ δ)) (Coreₚ.insert′-cons′ i Δ δ _ (Term.⟦ e ⟧ σ γ δ))) ∘ elim⇒ (suc i) (Term.Meta.weaken 0F e) P σ γ (Core.cons′ Δ _ δ)) deriv
  elim⇒         i e (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (Termₚ.RecBuilder⇐.extend (Termₚ.Meta.elimBuilder i e) p σ γ δ) deriv
  elim⇒         i e true     σ γ δ deriv = deriv
  elim⇒         i e (¬ P)    σ γ δ deriv = deriv ∘ elim⇐ i e P σ γ δ
  elim⇒         i e (P ∧ Q)  σ γ δ deriv = ×.map (elim⇒ i e P σ γ δ) (elim⇒ i e Q σ γ δ) deriv
  elim⇒         i e (P ∨ Q)  σ γ δ deriv = ⊎.map (elim⇒ i e P σ γ δ) (elim⇒ i e Q σ γ δ) deriv
  elim⇒         i e (P ⟶ Q)  σ γ δ deriv = elim⇒ i e Q σ γ δ ∘ deriv ∘ elim⇐ i e P σ γ δ

  elim⇐ {Δ = Δ} i e (all P)  σ γ δ deriv = elim⇐ (suc i) (Term.Meta.weaken 0F e) P σ γ (Core.cons′ Δ _ δ) ∘ subst (Assertion.⟦ _ ⟧ σ γ) (sym (trans (cong (Core.insert′ (suc i) (_ ∷ Δ) (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F _) e σ γ δ)) (Coreₚ.insert′-cons′ i Δ δ _ (Term.⟦ e ⟧ σ γ δ)))) ∘ deriv
  elim⇐ {Δ = Δ} i e (some P) σ γ δ deriv = map₂ (elim⇐ (suc i) (Term.Meta.weaken 0F e) P σ γ (Core.cons′ Δ _ δ) ∘ subst (Assertion.⟦ _ ⟧ σ γ) (sym (trans (cong (Core.insert′ (suc i) (_ ∷ Δ) (Core.cons′ Δ _ δ)) (Termₚ.RecBuilder⇒.extend (Termₚ.Meta.weakenBuilder 0F _) e σ γ δ)) (Coreₚ.insert′-cons′ i Δ δ _ (Term.⟦ e ⟧ σ γ δ))))) deriv
  elim⇐         i e (pred p) σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (sym (Termₚ.RecBuilder⇐.extend (Termₚ.Meta.elimBuilder i e) p σ γ δ)) deriv
  elim⇐         i e true     σ γ δ deriv = deriv
  elim⇐         i e (¬ P)    σ γ δ deriv = deriv ∘ elim⇒ i e P σ γ δ
  elim⇐         i e (P ∧ Q)  σ γ δ deriv = ×.map (elim⇐ i e P σ γ δ) (elim⇐ i e Q σ γ δ) deriv
  elim⇐         i e (P ∨ Q)  σ γ δ deriv = ⊎.map (elim⇐ i e P σ γ δ) (elim⇐ i e Q σ γ δ) deriv
  elim⇐         i e (P ⟶ Q)  σ γ δ deriv = elim⇐ i e Q σ γ δ ∘ deriv ∘ elim⇒ i e P σ γ δ

module Soundness where
  subst⇒ : ∀ (P : Assertion Σ Γ Δ) (ref : Reference Σ Γ t) (val : Expression Σ Γ t) σ γ δ → Assertion.⟦ Assertion.subst P ref (Term.↓ val) ⟧ σ γ δ → uncurry Assertion.⟦ P ⟧ (Semantics.stmt (ref ≔ val) (σ , γ)) δ
  subst⇐ : ∀ (P : Assertion Σ Γ Δ) (ref : Reference Σ Γ t) (val : Expression Σ Γ t) σ γ δ → uncurry Assertion.⟦ P ⟧ (Semantics.stmt (ref ≔ val) (σ , γ)) δ → Assertion.⟦ Assertion.subst P ref (Term.↓ val) ⟧ σ γ δ

  subst⇒ {Δ = Δ} (all P)  ref val σ γ δ deriv = subst⇒ P ref val σ γ (Core.cons′ Δ _ δ) ∘ subst (λ t → Assertion.⟦ Assertion.subst P ref t ⟧ σ γ (Core.cons′ Δ _ δ)) (Termₚ.Meta.weaken-↓ Δ _ 0F val) ∘ deriv
  subst⇒ {Δ = Δ} (some P) ref val σ γ δ deriv = map₂ (subst⇒ P ref val σ γ (Core.cons′ Δ _ δ) ∘ subst (λ t → Assertion.⟦ Assertion.subst P ref t ⟧ σ γ (Core.cons′ Δ _ δ)) (Termₚ.Meta.weaken-↓ Δ _ 0F val)) deriv
  subst⇒ (pred p) ref val σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (Termₚ.Soundness.subst-sound p ref val σ γ δ) deriv
  subst⇒ true     ref val σ γ δ deriv = deriv
  subst⇒ (¬ P)    ref val σ γ δ deriv = deriv ∘ subst⇐ P ref val σ γ δ
  subst⇒ (P ∧ Q)  ref val σ γ δ deriv = ×.map (subst⇒ P ref val σ γ δ) (subst⇒ Q ref val σ γ δ) deriv
  subst⇒ (P ∨ Q)  ref val σ γ δ deriv = ⊎.map (subst⇒ P ref val σ γ δ) (subst⇒ Q ref val σ γ δ) deriv
  subst⇒ (P ⟶ Q)  ref val σ γ δ deriv = subst⇒ Q ref val σ γ δ ∘ deriv ∘ subst⇐ P ref val σ γ δ

  subst⇐ {Δ = Δ} (all P)  ref val σ γ δ deriv = subst (λ t → Assertion.⟦ Assertion.subst P ref t ⟧ σ γ (Core.cons′ Δ _ δ)) (sym (Termₚ.Meta.weaken-↓ Δ _ 0F val)) ∘ subst⇐ P ref val σ γ (Core.cons′ Δ _ δ) ∘ deriv
  subst⇐ {Δ = Δ} (some P) ref val σ γ δ deriv = map₂ (subst (λ t → Assertion.⟦ Assertion.subst P ref t ⟧ σ γ (Core.cons′ Δ _ δ)) (sym (Termₚ.Meta.weaken-↓ Δ _ 0F val)) ∘ subst⇐ P ref val σ γ (Core.cons′ Δ _ δ)) deriv
  subst⇐ (pred p) ref val σ γ δ deriv = subst (Lift ℓ ∘ Bool.T ∘ lower) (sym (Termₚ.Soundness.subst-sound p ref val σ γ δ)) deriv
  subst⇐ true     ref val σ γ δ deriv = deriv
  subst⇐ (¬ P)    ref val σ γ δ deriv = deriv ∘ subst⇒ P ref val σ γ δ
  subst⇐ (P ∧ Q)  ref val σ γ δ deriv = ×.map (subst⇐ P ref val σ γ δ) (subst⇐ Q ref val σ γ δ) deriv
  subst⇐ (P ∨ Q)  ref val σ γ δ deriv = ⊎.map (subst⇐ P ref val σ γ δ) (subst⇐ Q ref val σ γ δ) deriv
  subst⇐ (P ⟶ Q)  ref val σ γ δ deriv = subst⇐ Q ref val σ γ δ ∘ deriv ∘ subst⇒ P ref val σ γ δ
