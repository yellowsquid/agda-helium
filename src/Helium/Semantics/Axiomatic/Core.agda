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

open import Data.Bool as Bool using (Bool)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Induction as Natᵢ
import Data.Nat.Properties as ℕₚ
open import Data.Product as × using (_,_; uncurry)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function using (_on_)
open import Helium.Data.Pseudocode.Core
open import Helium.Data.Pseudocode.Properties
import Induction.WellFounded as Wf
open import Level using (_⊔_; Lift; lift)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; does; yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness; map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (_⊆_)

private
  variable
    t t′     : Type
    m n      : ℕ
    Γ Δ Σ ts : Vec Type m

sizeOf : Type → Sliced → ℕ
sizeOf bool s = 0
sizeOf int s = 0
sizeOf (fin n) s = 0
sizeOf real s = 0
sizeOf bit s = 0
sizeOf (bits n) s = Bool.if does (s ≟ˢ bits) then n else 0
sizeOf (tuple _ []) s = 0
sizeOf (tuple _ (t ∷ ts)) s = sizeOf t s ℕ.+ sizeOf (tuple _ ts) s
sizeOf (array t n) s = Bool.if does (s ≟ˢ array t) then n else sizeOf t s

allocateSpace : Vec Type n → Sliced → ℕ
allocateSpace []       s = 0
allocateSpace (t ∷ ts) s = sizeOf t s ℕ.+ allocateSpace ts s

private
  getSliced : ∀ {t} → True (sliced? t) → Sliced
  getSliced t = ×.proj₁ (toWitness t)

  getCount : ∀ {t} → True (sliced? t) → ℕ
  getCount t = ×.proj₁ (×.proj₂ (toWitness t))

data ⟦_；_⟧ₜ (counts : Sliced → ℕ) : (τ : Type) → Set (b₁ ⊔ i₁ ⊔ r₁) where
  bool   : Bool → ⟦ counts ； bool ⟧ₜ
  int    : ℤ → ⟦ counts ； int ⟧ₜ
  fin    : ∀ {n} → Fin n → ⟦ counts ； fin n ⟧ₜ
  real   : ℝ → ⟦ counts ； real ⟧ₜ
  bit    : Bit → ⟦ counts ； bit ⟧ₜ
  bits   : ∀ {n} → Vec (⟦ counts ； bit ⟧ₜ ⊎ Fin (counts bits)) n → ⟦ counts ； bits n ⟧ₜ
  array  : ∀ {t n} → Vec (⟦ counts ； t ⟧ₜ ⊎ Fin (counts (array t))) n → ⟦ counts ； array t n ⟧ₜ
  tuple  : ∀ {n ts} → All ⟦ counts ；_⟧ₜ  ts → ⟦ counts ； tuple n ts ⟧ₜ

Stack : (counts : Sliced → ℕ) → Vec Type n → Set (b₁ ⊔ i₁ ⊔ r₁)
Stack counts Γ = ⟦ counts ； tuple _ Γ ⟧ₜ

Heap : (counts : Sliced → ℕ) → Set (b₁ ⊔ i₁ ⊔ r₁)
Heap counts = ∀ t → Vec ⟦ counts ； elemType t ⟧ₜ (counts t)

record State (Γ : Vec Type n) : Set (b₁ ⊔ i₁ ⊔ r₁) where
  private
    counts = allocateSpace Γ
  field
    stack   : Stack counts Γ
    heap    : Heap counts

Transform : Vec Type m → Type → Set (b₁ ⊔ i₁ ⊔ r₁)
Transform ts t = ∀ counts → Heap counts → ⟦ counts ； tuple _ ts ⟧ₜ → ⟦ counts ； t ⟧ₜ

Predicate : Vec Type m → Set (b₁ ⊔ i₁ ⊔ r₁)
Predicate ts = ∀ counts → ⟦ counts ； tuple _ ts ⟧ₜ → Bool

-- --   ⟦_⟧ₐ : ∀ {m Δ} → Assertion Σ Γ {m} Δ → State (Σ ++ Γ ++ Δ) → Set (b₁ ⊔ i₁ ⊔ r₁)
-- --   ⟦_⟧ₐ = {!!}

-- -- module _ {o} {Σ : Vec Type o} where
-- --   open Code Σ

-- --   𝒦 : ∀ {n Γ m Δ t} → Literal t → Term Σ {n} Γ {m} Δ t
-- --   𝒦 = {!!}

-- --   ℰ : ∀ {n Γ m Δ t} → Expression {n} Γ t → Term Σ Γ {m} Δ t
-- --   ℰ = {!!}

-- --   data HoareTriple {n Γ m Δ} : Assertion Σ {n} Γ {m} Δ → Statement Γ → Assertion Σ Γ Δ → Set (b₁ ⊔ i₁ ⊔ r₁) where
-- --     _∙_ : ∀ {P Q R s₁ s₂} → HoareTriple P s₁ Q → HoareTriple Q s₂ R → HoareTriple P (s₁ ∙ s₂) R
-- --     skip : ∀ {P} → HoareTriple P skip P

-- --     assign : ∀ {P t ref canAssign e} → HoareTriple (asrtSubst P (toWitness canAssign) (ℰ e)) (_≔_ {t = t} ref {canAssign} e) P
-- --     declare : ∀ {t P Q e s} → HoareTriple (P ∧ equal (var 0F) (termWknVar (ℰ e))) s (asrtWknVar Q) → HoareTriple (asrtElimVar P (ℰ e)) (declare {t = t} e s) Q
-- --     invoke : ∀ {m ts P Q s e} → HoareTriple (assignMetas Δ ts (All.tabulate var) (asrtAddVars P)) s (asrtAddVars Q) → HoareTriple (assignMetas Δ ts (All.tabulate (λ i → ℰ (All.lookup i e))) (asrtAddVars P)) (invoke {m = m} {ts} (s ∙end) e) (asrtAddVars Q)
-- --     if : ∀ {P Q e s₁ s₂} → HoareTriple (P ∧ equal (ℰ e) (𝒦 (Bool.true ′b))) s₁ Q → HoareTriple (P ∧ equal (ℰ e) (𝒦 (Bool.false ′b))) s₂ Q → HoareTriple P (if e then s₁ else s₂) Q
-- --     for : ∀ {m} {I : Assertion Σ Γ (fin (suc m) ∷ Δ)} {s} → HoareTriple (some (asrtWknVar (asrtWknMetaAt 1F I) ∧ equal (meta 1F) (var 0F) ∧ equal (meta 0F) (func (λ { _ (lift x ∷ []) → lift (Fin.inject₁ x) }) (meta 1F ∷ [])))) s (some (asrtWknVar (asrtWknMetaAt 1F I) ∧ equal (meta 0F) (func (λ { _ (lift x ∷ []) → lift (Fin.suc x) }) (meta 1F ∷ [])))) → HoareTriple (some (I ∧ equal (meta 0F) (func (λ _ _ → lift 0F) []))) (for m s) (some (I ∧ equal (meta 0F) (func (λ _ _ → lift (Fin.fromℕ m)) [])))

-- --     consequence : ∀ {P₁ P₂ Q₁ Q₂ s} → ⟦ P₁ ⟧ₐ ⊆ ⟦ P₂ ⟧ₐ → HoareTriple P₂ s Q₂ → ⟦ Q₂ ⟧ₐ ⊆ ⟦ Q₁ ⟧ₐ → HoareTriple P₁ s Q₁
-- --     some : ∀ {t P Q s} → HoareTriple P s Q → HoareTriple (some {t = t} P) s (some Q)
-- --     frame : ∀ {P Q R s} → HoareTriple P s Q → HoareTriple (P * R) s (Q * R)
