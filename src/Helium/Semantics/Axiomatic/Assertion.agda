------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of assertions used in correctness triples
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Axiomatic.Assertion
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

open RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Empty using (⊥)
open import Data.Fin using (suc)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; uncurry)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; insert)
open import Data.Vec.Relation.Unary.All using (All; map)
import Data.Vec.Recursive as Vecᵣ
open import Function hiding (_⟶_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (Term)
open import Level as L using (Lift; lift; lower)

private
  variable
    t t′     : Type
    i j k m n o    : ℕ
    Γ Δ Σ ts : Vec Type m

  ℓ = i₁ L.⊔ r₁

open Term.Term

infix  7 ¬_
infixl 6 _∧_
infixl 5 _∨_
infixl 4 _⟶_

data Assertion (Σ : Vec Type o) (Γ : Vec Type n) (Δ : Vec Type m) : Set (L.suc ℓ) where
  all    : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  some   : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  pred   : Term Σ Γ Δ bool → Assertion Σ Γ Δ
  true   : Assertion Σ Γ Δ
  false  : Assertion Σ Γ Δ
  ¬_     : Assertion Σ Γ Δ → Assertion Σ Γ Δ
  _∧_    : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  _∨_    : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  _⟶_    : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ

module Construct where
  equal : Term Σ Γ Δ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
  equal {t = bool}                x y = pred (x ≟ y)
  equal {t = int}                 x y = pred (x ≟ y)
  equal {t = fin n}               x y = pred (x ≟ y)
  equal {t = real}                x y = pred (x ≟ y)
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
  weaken i true        = true
  weaken i false       = false
  weaken i (¬ P)       = ¬ (weaken i P)
  weaken i (P ∧ Q)     = weaken i P ∧ weaken i Q
  weaken i (P ∨ Q)     = weaken i P ∨ weaken i Q
  weaken i (P ⟶ Q)     = weaken i P ⟶ weaken i Q

  weakenAll : Assertion Σ [] Δ → Assertion Σ Γ Δ
  weakenAll (all P)     = all (weakenAll P)
  weakenAll (some P)    = some (weakenAll P)
  weakenAll (pred p)    = pred (Term.Var.weakenAll p)
  weakenAll true        = true
  weakenAll false       = false
  weakenAll (¬ P)       = ¬ (weakenAll P)
  weakenAll (P ∧ Q)     = weakenAll P ∧ weakenAll Q
  weakenAll (P ∨ Q)     = weakenAll P ∨ weakenAll Q
  weakenAll (P ⟶ Q)     = weakenAll P ⟶ weakenAll Q

  inject : ∀ (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (Γ ++ ts) Δ
  inject ts (all P)     = all (inject ts P)
  inject ts (some P)    = some (inject ts P)
  inject ts (pred p)    = pred (Term.Var.inject ts p)
  inject ts true        = true
  inject ts false       = false
  inject ts (¬ P)       = ¬ (inject ts P)
  inject ts (P ∧ Q)     = inject ts P ∧ inject ts Q
  inject ts (P ∨ Q)     = inject ts P ∨ inject ts Q
  inject ts (P ⟶ Q)     = inject ts P ⟶ inject ts Q

  raise : ∀ (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (ts ++ Γ) Δ
  raise ts (all P)     = all (raise ts P)
  raise ts (some P)    = some (raise ts P)
  raise ts (pred p)    = pred (Term.Var.raise ts p)
  raise ts true        = true
  raise ts false       = false
  raise ts (¬ P)       = ¬ (raise ts P)
  raise ts (P ∧ Q)     = raise ts P ∧ raise ts Q
  raise ts (P ∨ Q)     = raise ts P ∨ raise ts Q
  raise ts (P ⟶ Q)     = raise ts P ⟶ raise ts Q

  elim : ∀ i → Assertion Σ (insert Γ i t) Δ → Term Σ Γ Δ t → Assertion Σ Γ Δ
  elim i (all P)     e = all (elim i P (Term.Meta.weaken 0F e))
  elim i (some P)    e = some (elim i P (Term.Meta.weaken 0F e))
  elim i (pred p)    e = pred (Term.Var.elim i p e)
  elim i true        e = true
  elim i false       e = false
  elim i (¬ P)       e = ¬ (elim i P e)
  elim i (P ∧ Q)     e = elim i P e ∧ elim i Q e
  elim i (P ∨ Q)     e = elim i P e ∨ elim i Q e
  elim i (P ⟶ Q)     e = elim i P e ⟶ elim i Q e

  elimAll : Assertion Σ Γ Δ → All (Term Σ ts Δ) Γ → Assertion Σ ts Δ
  elimAll (all P)     es = all (elimAll P (map (Term.Meta.weaken 0F) es))
  elimAll (some P)    es = some (elimAll P (map (Term.Meta.weaken 0F) es))
  elimAll (pred p)    es = pred (Term.Var.elimAll p es)
  elimAll true        es = true
  elimAll false       es = false
  elimAll (¬ P)       es = ¬ (elimAll P es)
  elimAll (P ∧ Q)     es = elimAll P es ∧ elimAll Q es
  elimAll (P ∨ Q)     es = elimAll P es ∨ elimAll Q es
  elimAll (P ⟶ Q)     es = elimAll P es ⟶ elimAll Q es

module Meta where
  weaken : ∀ i → Assertion Σ Γ Δ → Assertion Σ Γ (insert Δ i t)
  weaken i (all P)     = all (weaken (suc i) P)
  weaken i (some P)    = some (weaken (suc i) P)
  weaken i (pred p)    = pred (Term.Meta.weaken i p)
  weaken i true        = true
  weaken i false       = false
  weaken i (¬ P)       = ¬ (weaken i P)
  weaken i (P ∧ Q)     = weaken i P ∧ weaken i Q
  weaken i (P ∨ Q)     = weaken i P ∨ weaken i Q
  weaken i (P ⟶ Q)     = weaken i P ⟶ weaken i Q

  weakenAll : ∀ (Δ′ : Vec Type k) (ts : Vec Type m) → Assertion Σ Γ (Δ′ ++ Δ) → Assertion Σ Γ (Δ′ ++ ts ++ Δ)
  weakenAll Δ′ ts (all P)     = all (weakenAll (_ ∷ Δ′) ts P)
  weakenAll Δ′ ts (some P)    = some (weakenAll (_ ∷ Δ′) ts P)
  weakenAll Δ′ ts (pred p)    = pred (Term.Meta.weakenAll Δ′ ts p)
  weakenAll Δ′ ts true        = true
  weakenAll Δ′ ts false       = false
  weakenAll Δ′ ts (¬ P)       = ¬ (weakenAll Δ′ ts P)
  weakenAll Δ′ ts (P ∧ Q)     = weakenAll Δ′ ts P ∧ weakenAll Δ′ ts Q
  weakenAll Δ′ ts (P ∨ Q)     = weakenAll Δ′ ts P ∨ weakenAll Δ′ ts Q
  weakenAll Δ′ ts (P ⟶ Q)     = weakenAll Δ′ ts P ⟶ weakenAll Δ′ ts Q

  elim : ∀ i → Assertion Σ Γ (insert Δ i t) → Term Σ Γ Δ t → Assertion Σ Γ Δ
  elim i (all P)     e = all (elim (suc i) P (Term.Meta.weaken 0F e))
  elim i (some P)    e = some (elim (suc i) P (Term.Meta.weaken 0F e))
  elim i (pred p)    e = pred (Term.Meta.elim i p e)
  elim i true        e = true
  elim i false       e = false
  elim i (¬ P)       e = ¬ (elim i P e)
  elim i (P ∧ Q)     e = elim i P e ∧ elim i Q e
  elim i (P ∨ Q)     e = elim i P e ∨ elim i Q e
  elim i (P ⟶ Q)     e = elim i P e ⟶ elim i Q e

subst : Assertion Σ Γ Δ → Reference Σ Γ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
subst (all P)     ref val = all (subst P ref (Term.Meta.weaken 0F val))
subst (some P)    ref val = some (subst P ref (Term.Meta.weaken 0F val))
subst (pred p)    ref val = pred (Term.subst p ref val)
subst true        ref val = true
subst false       ref val = false
subst (¬ P)       ref val = ¬ (subst P ref val)
subst (P ∧ Q)     ref val = subst P ref val ∧ subst Q ref val
subst (P ∨ Q)     ref val = subst P ref val ∨ subst Q ref val
subst (P ⟶ Q)     ref val = subst P ref val ⟶ subst Q ref val

module Semantics (2≉0 : 2≉0) where
  module TS {i} {j} {k} = Term.Semantics {i} {j} {k} 2≉0

  ⟦_⟧ : Assertion Σ Γ Δ → ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → Set ℓ

  ⟦_⟧ {Δ = Δ} (all P)  σ γ δ = ∀ x → ⟦ P ⟧ σ γ (cons′ Δ x δ)
  ⟦_⟧ {Δ = Δ} (some P) σ γ δ = ∃ λ x → ⟦ P ⟧ σ γ (cons′ Δ x δ)
  ⟦ pred p ⟧           σ γ δ = Lift ℓ (Bool.T (lower (TS.⟦ p ⟧ σ γ δ)))
  ⟦ true ⟧             σ γ δ = Lift ℓ ⊤
  ⟦ false ⟧            σ γ δ = Lift ℓ ⊥
  ⟦ ¬ P ⟧              σ γ δ = ⟦ P ⟧ σ γ δ → ⊥
  ⟦ P ∧ Q ⟧            σ γ δ = ⟦ P ⟧ σ γ δ × ⟦ Q ⟧ σ γ δ
  ⟦ P ∨ Q ⟧            σ γ δ = ⟦ P ⟧ σ γ δ ⊎ ⟦ Q ⟧ σ γ δ
  ⟦ P ⟶ Q ⟧            σ γ δ = ⟦ P ⟧ σ γ δ → ⟦ Q ⟧ σ γ δ
