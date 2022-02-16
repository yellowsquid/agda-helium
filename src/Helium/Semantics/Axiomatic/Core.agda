------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for the axiomatic semantics
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

module Helium.Semantics.Axiomatic.Core
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

open import Data.Bool using (Bool; T)
open import Data.Fin as Fin using (zero; suc)
import Data.Fin.Properties as Finₚ
-- open import Data.Nat as ℕ using (zero; suc)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; <_,_>)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; _∷_; lookup)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function using (_$_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
open import Level using (_⊔_; Lift)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable; _⊆_)

module _ {o} (Σ : Vec Type o) {n} (Γ : Vec Type n) where
  data Term {m} (Δ : Vec Type m) : Type → Set (b₁ ⊔ i₁ ⊔ r₁) where
    state : ∀ i → Term Δ (lookup Σ i)
    var   : ∀ i → Term Δ (lookup Γ i)
    meta  : ∀ i → Term Δ (lookup Δ i)
    funct : ∀ {m ts t} → (⟦ tuple m ts ⟧ₜˡ → ⟦ t ⟧ₜˡ) → All (Term Δ) ts → Term Δ t

  infixl 7 _⇒_
  infixl 6 _∧_
  infixl 5 _∨_

  data Assertion {m} (Δ : Vec Type m) : Set (b₁ ⊔ i₁ ⊔ r₁) where
    _∧_  : Assertion Δ → Assertion Δ → Assertion Δ
    _∨_  : Assertion Δ → Assertion Δ → Assertion Δ
    _⇒_  : Assertion Δ → Assertion Δ → Assertion Δ
    all  : ∀ {t} → Assertion (t ∷ Δ) → Assertion Δ
    some : ∀ {t} → Assertion (t ∷ Δ) → Assertion Δ
    pred : ∀ {m ts} → (⟦ tuple m ts ⟧ₜˡ → Bool) → All (Term Δ) ts → Assertion Δ

module _ {o} {Σ : Vec Type o} {n} {Γ : Vec Type n} {m} {Δ : Vec Type m} where
  ⟦_⟧ : ∀ {t} → Term Σ Γ Δ t → ⟦ Σ ⟧ₜˡ′ → ⟦ Γ ⟧ₜˡ′ → ⟦ Δ ⟧ₜˡ′ → ⟦ t ⟧ₜˡ
  ⟦_⟧′ : ∀ {n ts} → All (Term Σ Γ Δ) ts → ⟦ Σ ⟧ₜˡ′ → ⟦ Γ ⟧ₜˡ′ → ⟦ Δ ⟧ₜˡ′ → ⟦ tuple n ts ⟧ₜˡ
  ⟦ state i ⟧    σ γ δ = fetchˡ Σ σ i
  ⟦ var i ⟧      σ γ δ = fetchˡ Γ γ i
  ⟦ meta i ⟧     σ γ δ = fetchˡ Δ δ i
  ⟦ funct f ts ⟧ σ γ δ = f (⟦ ts ⟧′ σ γ δ)

  ⟦ [] ⟧′            σ γ δ = _
  ⟦ (t ∷ []) ⟧′      σ γ δ = ⟦ t ⟧ σ γ δ
  ⟦ (t ∷ t′ ∷ ts) ⟧′ σ γ δ = ⟦ t ⟧ σ γ δ , ⟦ t′ ∷ ts ⟧′ σ γ δ

  termSubstState : ∀ {t} → Term Σ Γ Δ t → ∀ j → Term Σ Γ Δ (lookup Σ j) → Term Σ Γ Δ t
  termSubstState (state i)    j t′ with j Fin.≟ i
  ...                                 | yes refl = t′
  ...                                 | no _     = state i
  termSubstState (var i)      j t′ = var i
  termSubstState (meta i)     j t′ = meta i
  termSubstState (funct f ts) j t′ = funct f (helper ts)
    where
    helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ Γ Δ) ts
    helper []       = []
    helper (t ∷ ts) = termSubstState t j t′ ∷ helper ts

  termSubstVar : ∀ {t} → Term Σ Γ Δ t → ∀ j → Term Σ Γ Δ (lookup Γ j) → Term Σ Γ Δ t
  termSubstVar (state i)     j t′ = state i
  termSubstVar (var i)       j t′ with j Fin.≟ i
  ...                                | yes refl = t′
  ...                                | no _     = var i
  termSubstVar (meta i)      j t′ = meta i
  termSubstVar (funct f ts)  j t′ = funct f (helper ts)
    where
    helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ Γ Δ) ts
    helper []       = []
    helper (t ∷ ts) = termSubstVar t j t′ ∷ helper ts

  termElimVar : ∀ {t t′} → Term Σ (t′ ∷ Γ) Δ t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  termElimVar (state i)     t′ = state i
  termElimVar (var zero)    t′ = t′
  termElimVar (var (suc i)) t′ = var i
  termElimVar (meta i)      t′ = meta i
  termElimVar (funct f ts)  t′ = funct f (helper ts)
    where
    helper : ∀ {n ts} → All (Term _ _ _) {n} ts → All (Term _ _ _) ts
    helper []       = []
    helper (t ∷ ts) = termElimVar t t′ ∷ helper ts

  termWknVar : ∀ {t t′} → Term Σ Γ Δ t → Term Σ (t′ ∷ Γ) Δ t
  termWknVar (state i)    = state i
  termWknVar (var i)      = var (suc i)
  termWknVar (meta i)     = meta i
  termWknVar (funct f ts) = funct f (helper ts)
    where
    helper : ∀ {n ts} → All (Term _ _ _) {n} ts → All (Term _ _ _) ts
    helper []       = []
    helper (t ∷ ts) = termWknVar t ∷ helper ts

  termWknMeta : ∀ {t t′} → Term Σ Γ Δ t → Term Σ Γ (t′ ∷ Δ) t
  termWknMeta (state i)    = state i
  termWknMeta (var i)      = var i
  termWknMeta (meta i)     = meta (suc i)
  termWknMeta (funct f ts) = funct f (helper ts)
    where
    helper : ∀ {n ts} → All (Term _ _ _) {n} ts → All (Term _ _ _) ts
    helper []       = []
    helper (t ∷ ts) = termWknMeta t ∷ helper ts

module _ {o} {Σ : Vec Type o} {n} {Γ : Vec Type n} where
  infix 4 _∋[_] _⊨_

  _∋[_] : ∀ {m Δ} → Assertion Σ Γ {m} Δ → ⟦ Σ ⟧ₜˡ′ × ⟦ Γ ⟧ₜˡ′ × ⟦ Δ ⟧ₜˡ′ → Set (b₁ ⊔ i₁ ⊔ r₁)
  P ∧ Q ∋[ s ] = P ∋[ s ] × Q ∋[ s ]
  P ∨ Q ∋[ s ] = P ∋[ s ] ⊎ Q ∋[ s ]
  P ⇒ Q ∋[ s ] = P ∋[ s ] → Q ∋[ s ]
  pred P ts ∋[ σ , γ , δ ] = Lift (b₁ ⊔ i₁ ⊔ r₁) $ T $ P (⟦ ts ⟧′ σ γ δ)
  _∋[_] {Δ = Δ} (all P)  (σ , γ , δ) = ∀ v → P ∋[ σ , γ , consˡ Δ v δ ]
  _∋[_] {Δ = Δ} (some P) (σ , γ , δ) = ∃ λ v → P ∋[ σ , γ , consˡ Δ v δ ]

  _⊨_ : ∀ {m Δ} → ⟦ Σ ⟧ₜˡ′ × ⟦ Γ ⟧ₜˡ′ × ⟦ Δ ⟧ₜˡ′ → Assertion Σ Γ {m} Δ → Set (b₁ ⊔ i₁ ⊔ r₁)
  s ⊨ P = P ∋[ s ]

  asstSubstState : ∀ {m Δ} → Assertion Σ Γ {m} Δ → ∀ j → Term Σ Γ Δ (lookup Σ j) → Assertion Σ Γ Δ
  asstSubstState (P ∧ Q)     j t = asstSubstState P j t ∧ asstSubstState Q j t
  asstSubstState (P ∨ Q)     j t = asstSubstState P j t ∨ asstSubstState Q j t
  asstSubstState (P ⇒ Q)     j t = asstSubstState P j t ⇒ asstSubstState Q j t
  asstSubstState (all P)     j t = all (asstSubstState P j (termWknMeta t))
  asstSubstState (some P)    j t = some (asstSubstState P j (termWknMeta t))
  asstSubstState (pred p ts) j t = pred p (All.map (λ t′ → termSubstState t′ j t) ts)

  asstSubstVar : ∀ {m Δ} → Assertion Σ Γ {m} Δ → ∀ j → Term Σ Γ Δ (lookup Γ j) → Assertion Σ Γ Δ
  asstSubstVar (P ∧ Q)     j t = asstSubstVar P j t ∧ asstSubstVar Q j t
  asstSubstVar (P ∨ Q)     j t = asstSubstVar P j t ∨ asstSubstVar Q j t
  asstSubstVar (P ⇒ Q)     j t = asstSubstVar P j t ⇒ asstSubstVar Q j t
  asstSubstVar (all P)     j t = all (asstSubstVar P j (termWknMeta t))
  asstSubstVar (some P)    j t = some (asstSubstVar P j (termWknMeta t))
  asstSubstVar (pred p ts) j t = pred p (All.map (λ t′ → termSubstVar t′ j t) ts)

  asstElimVar : ∀ {m Δ t′} → Assertion Σ (t′ ∷ Γ) {m} Δ → Term Σ Γ Δ t′ → Assertion Σ Γ Δ
  asstElimVar (P ∧ Q)     t = asstElimVar P t ∧ asstElimVar Q t
  asstElimVar (P ∨ Q)     t = asstElimVar P t ∨ asstElimVar Q t
  asstElimVar (P ⇒ Q)     t = asstElimVar P t ⇒ asstElimVar Q t
  asstElimVar (all P)     t = all (asstElimVar P (termWknMeta t))
  asstElimVar (some P)    t = some (asstElimVar P (termWknMeta t))
  asstElimVar (pred p ts) t = pred p (All.map (λ t′ → termElimVar t′ t) ts)

module _ {o} {Σ : Vec Type o} where
  open Code Σ

  data HoareTriple {n Γ m Δ} : Assertion Σ {n} Γ {m} Δ → Statement Γ → Assertion Σ Γ Δ → Set (b₁ ⊔ i₁ ⊔ r₁) where
    csqs : ∀ {P₁ P₂ Q₁ Q₂ : Assertion Σ Γ Δ} {s} → (_⊨ P₁) ⊆ (_⊨ P₂) → HoareTriple P₂ s Q₂ → (_⊨ Q₂) ⊆ (_⊨ Q₁) → HoareTriple P₁ s Q₁
    _∙_  : ∀ {P Q R s₁ s₂} → HoareTriple P s₁ Q → HoareTriple Q s₂ R → HoareTriple P (s₁ ∙ s₂) R
    skip : ∀ {P} → HoareTriple P skip P
