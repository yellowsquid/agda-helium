------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of assertions used in correctness triples
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

module Helium.Semantics.Axiomatic.Assertion
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open RawPseudocode rawPseudocode

open import Data.Bool as Bool using (Bool)
open import Data.Fin as Fin using (suc)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Axiomatic.Core rawPseudocode
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (Term)
open import Level using (_⊔_; lift)
open import Relation.Nullary using (does)

private
  variable
    t t′     : Type
    m n o    : ℕ
    Γ Δ Σ ts : Vec Type m

infixl 7 _[_]↦_

open Term.Term

data Assertion (Σ : Vec Type o) (Γ : Vec Type n) (Δ : Vec Type m) : Set (b₁ ⊔ i₁ ⊔ r₁) where
  _[_]↦_ : ∀ {m t} → Term Σ Γ Δ (asType t m) → Term Σ Γ Δ (fin m) → Term Σ Γ Δ (elemType t) → Assertion Σ Γ Δ
  all    : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  some   : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  pred   : Term Σ Γ Δ bool → Assertion Σ Γ Δ
  comb   : ∀ {n} → (Vec Bool n → Bool) → Vec (Assertion Σ Γ Δ) n → Assertion Σ Γ Δ

elimVar : Assertion Σ (t ∷ Γ) Δ → Term Σ Γ Δ t → Assertion Σ Γ Δ
elimVar (ref [ i ]↦ val) t = Term.elimVar ref t [ Term.elimVar i t ]↦ Term.elimVar val t
elimVar (all P)          t = all (elimVar P (Term.wknMeta t))
elimVar (some P)         t = some (elimVar P (Term.wknMeta t))
elimVar (pred p)         t = pred (Term.elimVar p t)
elimVar (comb f Ps)      t = comb f (helper Ps t)
  where
  helper : ∀ {n} → Vec (Assertion Σ (_ ∷ Γ) Δ) n → Term Σ Γ Δ _ → Vec (Assertion Σ Γ Δ) n
  helper []       t = []
  helper (P ∷ Ps) t = elimVar P t ∷ helper Ps t

wknVar : Assertion Σ Γ Δ → Assertion Σ (t ∷ Γ) Δ
wknVar (ref [ i ]↦ val) = Term.wknVar ref [ Term.wknVar i ]↦ Term.wknVar val
wknVar (all P)          = all (wknVar P)
wknVar (some P)         = some (wknVar P)
wknVar (pred p)         = pred (Term.wknVar p)
wknVar (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ Γ Δ) n → Vec (Assertion Σ (_ ∷ Γ) Δ) n
  helper []       = []
  helper (P ∷ Ps) = wknVar P ∷ helper Ps

wknVars : (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (ts ++ Γ) Δ
wknVars τs (ref [ i ]↦ val) = Term.wknVars τs ref [ Term.wknVars τs i ]↦ Term.wknVars τs val
wknVars τs (all P)          = all (wknVars τs P)
wknVars τs (some P)         = some (wknVars τs P)
wknVars τs (pred p)         = pred (Term.wknVars τs p)
wknVars τs (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ Γ Δ) n → Vec (Assertion Σ (τs ++ Γ) Δ) n
  helper []       = []
  helper (P ∷ Ps) = wknVars τs P ∷ helper Ps

addVars : Assertion Σ [] Δ → Assertion Σ Γ Δ
addVars (ref [ i ]↦ val) = Term.addVars ref [ Term.addVars i ]↦ Term.addVars val
addVars (all P)          = all (addVars P)
addVars (some P)         = some (addVars P)
addVars (pred p)         = pred (Term.addVars p)
addVars (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ [] Δ) n → Vec (Assertion Σ Γ Δ) n
  helper []       = []
  helper (P ∷ Ps) = addVars P ∷ helper Ps

wknMetaAt : ∀ i → Assertion Σ Γ Δ → Assertion Σ Γ (Vec.insert Δ i t)
wknMetaAt i (ref [ j ]↦ val) = Term.wknMetaAt i ref [ Term.wknMetaAt i j ]↦ Term.wknMetaAt i val
wknMetaAt i (all P)          = all (wknMetaAt (suc i) P)
wknMetaAt i (some P)         = some (wknMetaAt (suc i) P)
wknMetaAt i (pred p)         = pred (Term.wknMetaAt i p)
wknMetaAt i (comb f Ps)      = comb f (helper i Ps)
  where
  helper : ∀ {n} i → Vec (Assertion Σ Γ Δ) n → Vec (Assertion Σ Γ (Vec.insert Δ i _)) n
  helper i []       = []
  helper i (P ∷ Ps) = wknMetaAt i P ∷ helper i Ps

-- NOTE: better to induct on P instead of ts?
wknMetas : (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ Γ (ts ++ Δ)
wknMetas []       P = P
wknMetas (_ ∷ ts) P = wknMetaAt 0F (wknMetas ts P)

module _ (2≉0 : Term.2≉0) where
  -- NOTE: better to induct on e here than in Term?
  subst : Assertion Σ Γ Δ → {e : Code.Expression Σ Γ t} → Code.CanAssign Σ e → Term Σ Γ Δ t → Assertion Σ Γ Δ
  subst (ref [ i ]↦ val) e t = Term.subst 2≉0 ref e t [ Term.subst 2≉0 i e t ]↦ Term.subst 2≉0 val e t
  subst (all P)          e t = all (subst P e (Term.wknMeta t))
  subst (some P)         e t = some (subst P e (Term.wknMeta t))
  subst (pred p)         e t = pred (Term.subst 2≉0 p e t)
  subst (comb f Ps)      e t = comb f (helper Ps e t)
    where
    helper : ∀ {t n} → Vec (Assertion Σ Γ Δ) n → {e : Code.Expression Σ Γ t} → Code.CanAssign Σ e → Term Σ Γ Δ t → Vec (Assertion Σ Γ Δ) n
    helper []       e t = []
    helper (P ∷ Ps) e t = subst P e t ∷ helper Ps e t

module Construct where
  infixl 6 _∧_
  infixl 5 _∨_

  true : Assertion Σ Γ Δ
  true = comb (λ _ → Bool.true) []

  false : Assertion Σ Γ Δ
  false = comb (λ _ → Bool.false) []

  _∧_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∧ Q = comb (λ { (p ∷ q ∷ []) → p Bool.∧ q }) (P ∷ Q ∷ [])

  _∨_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∨ Q = comb (λ { (p ∷ q ∷ []) → p Bool.∨ q }) (P ∷ Q ∷ [])

  equal : Term Σ Γ Δ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
  equal {t = bool} x y = pred Term.[ bool ][ x ≟ y ]
  equal {t = int} x y = pred Term.[ int ][ x ≟ y ]
  equal {t = fin n} x y = pred Term.[ fin ][ x ≟ y ]
  equal {t = real} x y = pred Term.[ real ][ x ≟ y ]
  equal {t = bit} x y = pred Term.[ bit ][ x ≟ y ]
  equal {t = bits n} x y = pred Term.[ bits n ][ x ≟ y ]
  equal {t = tuple _ []} x y = true
  equal {t = tuple _ (t ∷ ts)} x y = equal {t = t} (Term.func₁ proj₁ x) (Term.func₁ proj₁ y) ∧ equal (Term.func₁ proj₂ x) (Term.func₁ proj₂ y)
  equal {t = array t n} x y = all (some (Term.wknMeta (Term.wknMeta x) [ meta 1F ]↦ meta 0F ∧ Term.wknMeta (Term.wknMeta y) [ meta 1F ]↦ meta 0F))

open Construct public
