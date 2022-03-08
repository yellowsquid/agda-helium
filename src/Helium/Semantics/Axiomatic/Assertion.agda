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
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin as Fin using (suc)
open import Data.Fin.Patterns
open import Data.Nat using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function using (_$_)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Axiomatic.Core rawPseudocode
open import Helium.Semantics.Axiomatic.Term rawPseudocode as Term using (Term)
open import Level using (_⊔_; Lift; lift; lower) renaming (suc to ℓsuc)

private
  variable
    t t′     : Type
    m n o    : ℕ
    Γ Δ Σ ts : Vec Type m

open Term.Term

data Assertion (Σ : Vec Type o) (Γ : Vec Type n) (Δ : Vec Type m) : Set (ℓsuc (b₁ ⊔ i₁ ⊔ r₁))

data Assertion Σ Γ Δ where
  all    : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  some   : Assertion Σ Γ (t ∷ Δ) → Assertion Σ Γ Δ
  pred   : Term Σ Γ Δ bool → Assertion Σ Γ Δ
  comb   : ∀ {n} → (Vec (Set (b₁ ⊔ i₁ ⊔ r₁)) n → Set (b₁ ⊔ i₁ ⊔ r₁)) → Vec (Assertion Σ Γ Δ) n → Assertion Σ Γ Δ

elimVar : Assertion Σ (t ∷ Γ) Δ → Term Σ Γ Δ t → Assertion Σ Γ Δ
elimVar (all P)          t = all (elimVar P (Term.wknMeta t))
elimVar (some P)         t = some (elimVar P (Term.wknMeta t))
elimVar (pred p)         t = pred (Term.elimVar p t)
elimVar (comb f Ps)      t = comb f (helper Ps t)
  where
  helper : ∀ {n} → Vec (Assertion Σ (_ ∷ Γ) Δ) n → Term Σ Γ Δ _ → Vec (Assertion Σ Γ Δ) n
  helper []       t = []
  helper (P ∷ Ps) t = elimVar P t ∷ helper Ps t

wknVar : Assertion Σ Γ Δ → Assertion Σ (t ∷ Γ) Δ
wknVar (all P)          = all (wknVar P)
wknVar (some P)         = some (wknVar P)
wknVar (pred p)         = pred (Term.wknVar p)
wknVar (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ Γ Δ) n → Vec (Assertion Σ (_ ∷ Γ) Δ) n
  helper []       = []
  helper (P ∷ Ps) = wknVar P ∷ helper Ps

wknVars : (ts : Vec Type n) → Assertion Σ Γ Δ → Assertion Σ (ts ++ Γ) Δ
wknVars τs (all P)          = all (wknVars τs P)
wknVars τs (some P)         = some (wknVars τs P)
wknVars τs (pred p)         = pred (Term.wknVars τs p)
wknVars τs (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ Γ Δ) n → Vec (Assertion Σ (τs ++ Γ) Δ) n
  helper []       = []
  helper (P ∷ Ps) = wknVars τs P ∷ helper Ps

addVars : Assertion Σ [] Δ → Assertion Σ Γ Δ
addVars (all P)          = all (addVars P)
addVars (some P)         = some (addVars P)
addVars (pred p)         = pred (Term.addVars p)
addVars (comb f Ps)      = comb f (helper Ps)
  where
  helper : ∀ {n} → Vec (Assertion Σ [] Δ) n → Vec (Assertion Σ Γ Δ) n
  helper []       = []
  helper (P ∷ Ps) = addVars P ∷ helper Ps

wknMetaAt : ∀ i → Assertion Σ Γ Δ → Assertion Σ Γ (Vec.insert Δ i t)
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
  true = comb (λ _ → ⊤) []

  false : Assertion Σ Γ Δ
  false = comb (λ _ → ⊥) []

  _∧_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∧ Q = comb (λ { (P ∷ Q ∷ []) → P × Q }) (P ∷ Q ∷ [])

  _∨_ : Assertion Σ Γ Δ → Assertion Σ Γ Δ → Assertion Σ Γ Δ
  P ∨ Q = comb (λ { (P ∷ Q ∷ []) → P ⊎ Q }) (P ∷ Q ∷ [])

  equal : Term Σ Γ Δ t → Term Σ Γ Δ t → Assertion Σ Γ Δ
  equal {t = bool} x y = pred Term.[ bool ][ x ≟ y ]
  equal {t = int} x y = pred Term.[ int ][ x ≟ y ]
  equal {t = fin n} x y = pred Term.[ fin ][ x ≟ y ]
  equal {t = real} x y = pred Term.[ real ][ x ≟ y ]
  equal {t = bit} x y = pred Term.[ bit ][ x ≟ y ]
  equal {t = bits n} x y = pred Term.[ bits n ][ x ≟ y ]
  equal {t = tuple _ []} x y = true
  equal {t = tuple _ (t ∷ ts)} x y = equal {t = t} (Term.func₁ proj₁ x) (Term.func₁ proj₁ y) ∧ equal (Term.func₁ proj₂ x) (Term.func₁ proj₂ y)
  equal {t = array t 0} x y = true
  equal {t = array t (suc n)} x y = all (equal {t = t} (index x) (index y))
    where
    index = λ v → Term.unbox (array t) $
                  Term.func₁ proj₁ $
                  Term.cut (array t)
                    (Term.cast (array t) (ℕₚ.+-comm 1 n) (Term.wknMeta v))
                    (meta 0F)

open Construct public

⟦_⟧ : Assertion Σ Γ Δ → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → Set (b₁ ⊔ i₁ ⊔ r₁)
⟦_⟧′ : Vec (Assertion Σ Γ Δ) n → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → Vec (Set (b₁ ⊔ i₁ ⊔ r₁)) n

⟦ all P ⟧ σ γ δ = ∀ x → ⟦ P ⟧ σ γ (x , δ)
⟦ some P ⟧ σ γ δ = ∃ λ x → ⟦ P ⟧ σ γ (x , δ)
⟦ pred p ⟧ σ γ δ = Lift (b₁ ⊔ i₁ ⊔ r₁) (Bool.T (lower (Term.⟦ p ⟧ σ γ δ)))
⟦ comb f Ps ⟧ σ γ δ = f (⟦ Ps ⟧′ σ γ δ)

⟦ [] ⟧′     σ γ δ = []
⟦ P ∷ Ps ⟧′ σ γ δ = ⟦ P ⟧ σ γ δ ∷ ⟦ Ps ⟧′ σ γ δ
