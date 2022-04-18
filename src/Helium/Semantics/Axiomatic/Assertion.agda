------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of assertions used in correctness triples
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Axiomatic.Assertion
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (suc)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; uncurry)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; insert)
open import Data.Vec.Relation.Unary.All using (All; map)
import Data.Vec.Recursive as Vecᵣ
open import Function
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (Term)
open import Level as L using (Lift; lift; lower)

private
  variable
    t t′     : Type
    i j k m n o    : ℕ
    Γ Δ Σ ts : Vec Type m

  ℓ = b₁ L.⊔ i₁ L.⊔ r₁

open Term.Term

data Assertion (Σ : Vec Type o) (Γ : Vec Type n) (Δ : Vec Type m) : Set (L.suc ℓ) where
  all    : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  some   : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  pred   : Term Σ Γ Δ bool → Assertion Σ Γ Δ
  comb   : (Set ℓ Vecᵣ.^ k → Set ℓ) → Vec (Assertion Σ Γ Δ) k → Assertion Σ Γ Δ

module Construct where
  infixl 6 _∧_
  infixl 5 _∨_

  true : Assertion Σ Γ Δ
  true = comb (λ _ → ⊤) []

  false : Assertion Σ Γ Δ
  false = comb (λ _ → ⊥) []

  _∧_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∧ Q = comb (uncurry _×_) (P ∷ Q ∷ [])

  _∨_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∨ Q = comb (uncurry _⊎_) (P ∷ Q ∷ [])

  equal : Term Σ Γ Δ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
  equal {t = bool}                x y = pred (x ≟ y)
  equal {t = int}                 x y = pred (x ≟ y)
  equal {t = fin n}               x y = pred (x ≟ y)
  equal {t = real}                x y = pred (x ≟ y)
  equal {t = bit}                 x y = pred (x ≟ y)
  equal {t = tuple []}            x y = true
  equal {t = tuple (t ∷ [])}      x y = equal (head x) (head y)
  equal {t = tuple (t ∷ t₁ ∷ ts)} x y = equal (head x) (head y) ∧ equal (tail x) (tail y)
  equal {t = array t 0}           x y = true
  equal {t = array t (suc n)}     x y = all (equal (index x) (index y))
    where
    index : Term Σ Γ Δ (array t (suc n)) → Term Σ Γ (fin (suc n) ∷ Δ) t
    index t = unbox (slice (cast (ℕₚ.+-comm 1 _) (Term.Meta.weaken 0F t)) (meta 0F))

open Construct public

module Var where
  weaken : ∀ i → Assertion Σ Γ Δ → Assertion Σ (insert Γ i t) Δ
  weaken i (all P)     = all (weaken i P)
  weaken i (some P)    = some (weaken i P)
  weaken i (pred p)    = pred (Term.Var.weaken i p)
  weaken i (comb f Ps) = comb f (helper i Ps)
    where
    helper : ∀ i → Vec (Assertion Σ Γ Δ) k → Vec (Assertion Σ (insert Γ i t) Δ) k
    helper i []       = []
    helper i (P ∷ Ps) = weaken i P ∷ helper i Ps

  weakenAll : Assertion Σ [] Δ → Assertion Σ Γ Δ
  weakenAll (all P)     = all (weakenAll P)
  weakenAll (some P)    = some (weakenAll P)
  weakenAll (pred p)    = pred (Term.Var.weakenAll p)
  weakenAll (comb f Ps) = comb f (helper Ps)
    where
    helper : Vec (Assertion Σ [] Δ) k → Vec (Assertion Σ Γ Δ) k
    helper []       = []
    helper (P ∷ Ps) = weakenAll P ∷ helper Ps

  inject : ∀ (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (Γ ++ ts) Δ
  inject ts (all P)     = all (inject ts P)
  inject ts (some P)    = some (inject ts P)
  inject ts (pred p)    = pred (Term.Var.inject ts p)
  inject ts (comb f Ps) = comb f (helper ts Ps)
    where
    helper : ∀ (ts : Vec Type n) → Vec (Assertion Σ Γ Δ) k → Vec (Assertion Σ (Γ ++ ts) Δ) k
    helper ts []       = []
    helper ts (P ∷ Ps) = inject ts P ∷ helper ts Ps

  raise : ∀ (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (ts ++ Γ) Δ
  raise ts (all P)     = all (raise ts P)
  raise ts (some P)    = some (raise ts P)
  raise ts (pred p)    = pred (Term.Var.raise ts p)
  raise ts (comb f Ps) = comb f (helper ts Ps)
    where
    helper : ∀ (ts : Vec Type n) → Vec (Assertion Σ Γ Δ) k → Vec (Assertion Σ (ts ++ Γ) Δ) k
    helper ts []       = []
    helper ts (P ∷ Ps) = raise ts P ∷ helper ts Ps

  elim : ∀ i → Assertion Σ (insert Γ i t) Δ → Term Σ Γ Δ t → Assertion Σ Γ Δ
  elim i (all P)     e = all (elim i P (Term.Meta.weaken 0F e))
  elim i (some P)    e = some (elim i P (Term.Meta.weaken 0F e))
  elim i (pred p)    e = pred (Term.Var.elim i p e)
  elim i (comb f Ps) e = comb f (helper i Ps e)
    where
    helper : ∀ i → Vec (Assertion Σ (insert Γ i t) Δ) k → Term Σ Γ Δ t → Vec (Assertion Σ Γ Δ) k
    helper i []       e = []
    helper i (P ∷ Ps) e = elim i P e ∷ helper i Ps e

  elimAll : Assertion Σ Γ Δ → All (Term Σ ts Δ) Γ → Assertion Σ ts Δ
  elimAll (all P)     es = all (elimAll P (map (Term.Meta.weaken 0F) es))
  elimAll (some P)    es = some (elimAll P (map (Term.Meta.weaken 0F) es))
  elimAll (pred p)    es = pred (Term.Var.elimAll p es)
  elimAll (comb f Ps) es = comb f (helper Ps es)
    where
    helper : Vec (Assertion Σ Γ Δ) n → All (Term Σ ts Δ) Γ → Vec (Assertion Σ ts Δ) n
    helper []       es = []
    helper (P ∷ Ps) es = elimAll P es ∷ helper Ps es

module Meta where
  weaken : ∀ i → Assertion Σ Γ Δ → Assertion Σ Γ (insert Δ i t)
  weaken i (all P)     = all (weaken (suc i) P)
  weaken i (some P)    = some (weaken (suc i) P)
  weaken i (pred p)    = pred (Term.Meta.weaken i p)
  weaken i (comb f Ps) = comb f (helper i Ps)
    where
    helper : ∀ i → Vec (Assertion Σ Γ Δ) k → Vec (Assertion Σ Γ (insert Δ i t)) k
    helper i []       = []
    helper i (P ∷ Ps) = weaken i P ∷ helper i Ps

  elim : ∀ i → Assertion Σ Γ (insert Δ i t) → Term Σ Γ Δ t → Assertion Σ Γ Δ
  elim i (all P)     e = all (elim (suc i) P (Term.Meta.weaken 0F e))
  elim i (some P)    e = some (elim (suc i) P (Term.Meta.weaken 0F e))
  elim i (pred p)    e = pred (Term.Meta.elim i p e)
  elim i (comb f Ps) e = comb f (helper i Ps e)
    where
    helper : ∀ i → Vec (Assertion Σ Γ (insert Δ i t)) k → Term Σ Γ Δ t → Vec (Assertion Σ Γ Δ) k
    helper i []       e = []
    helper i (P ∷ Ps) e = elim i P e ∷ helper i Ps e

subst : Assertion Σ Γ Δ → Reference Σ Γ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
subst (all P)     ref val = all (subst P ref (Term.Meta.weaken 0F val))
subst (some P)    ref val = some (subst P ref (Term.Meta.weaken 0F val))
subst (pred p)    ref val = pred (Term.subst p ref val)
subst (comb f Ps) ref val = comb f (helper Ps ref val)
  where
  helper : Vec (Assertion Σ Γ Δ) k → Reference Σ Γ t → Term Σ Γ Δ t → Vec (Assertion Σ Γ Δ) k
  helper []       ref val = []
  helper (P ∷ Ps) ref val = subst P ref val ∷ Ps


module Semantics (2≉0 : 2≉0) where
  module TS {i} {j} {k} = Term.Semantics {i} {j} {k} 2≉0

  ⟦_⟧ : Assertion Σ Γ Δ → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → Set ℓ
  ⟦_⟧′ : Vec (Assertion Σ Γ Δ) n → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → Vec (Set ℓ) n

  ⟦_⟧ {Δ = Δ} (all P)  σ γ δ = ∀ x → ⟦ P ⟧ σ γ (cons′ Δ x δ)
  ⟦_⟧ {Δ = Δ} (some P) σ γ δ = ∃ λ x → ⟦ P ⟧ σ γ (cons′ Δ x δ)
  ⟦ pred p ⟧           σ γ δ = Lift ℓ (Bool.T (lower (TS.⟦ p ⟧ σ γ δ)))
  ⟦ comb f Ps ⟧        σ γ δ = f (Vecᵣ.fromVec (⟦ Ps ⟧′ σ γ δ))

  ⟦ [] ⟧′     σ γ δ = []
  ⟦ P ∷ Ps ⟧′ σ γ δ = ⟦ P ⟧ σ γ δ ∷ ⟦ Ps ⟧′ σ γ δ
