------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of terms for use in assertions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Data.Vec using (Vec)
open import Helium.Data.Pseudocode.Core

module Helium.Data.Pseudocode.Manipulate
  {o} {Σ : Vec Type o}
  where

import Algebra.Solver.IdempotentCommutativeMonoid as ComMonoidSolver
open import Data.Fin as Fin using (Fin; suc)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; suc; _⊔_)
import Data.Nat.Induction as ℕᵢ
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Product.Relation.Binary.Lex.Strict as Lex
open import Data.Vec as Vec using ([]; _∷_)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Function using (_on_; _∘_; _∋_; case_return_of_)
open import Function.Nary.NonDependent using (congₙ)
open import Helium.Data.Pseudocode.Properties
import Induction.WellFounded as Wf
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (True; fromWitness; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)

open ComMonoidSolver (record
    { isIdempotentCommutativeMonoid = record
      { isCommutativeMonoid = ℕₚ.⊔-0-isCommutativeMonoid
      ; idem = ℕₚ.⊔-idem
      }
    })
  using (_⊕_; _⊜_)
  renaming (solve to ⊔-solve)

open Code Σ

private
  variable
    m n : ℕ
    Γ Δ : Vec Type m
    t t′ ret : Type

-- TODO: make argument irrelevant
castType : Expression Γ t → (t ≡ t′) → Expression Γ t′
castType e refl = e

cast-pres-assignable : ∀ {e : Expression Γ t} → CanAssign e → (eq : t ≡ t′) → CanAssign (castType e eq)
cast-pres-assignable e refl = e

cast-pres-stateless : ∀ {e : Expression Γ t} → (eq : t ≡ t′) → ReferencesState (castType e eq) → ReferencesState e
cast-pres-stateless refl e = e

punchOut⇒insert : ∀ {a} {A : Set a} (xs : Vec A n) {i j : Fin (suc n)} (i≢j : ¬ i ≡ j) x → Vec.lookup xs (Fin.punchOut i≢j) ≡ Vec.lookup (Vec.insert xs i x) j
punchOut⇒insert xs {i} {j} i≢j x = begin
  Vec.lookup xs (Fin.punchOut i≢j)
    ≡˘⟨ cong (λ x → Vec.lookup x _) (Vecₚ.remove-insert xs i x) ⟩
  Vec.lookup (Vec.remove (Vec.insert xs i x) i) (Fin.punchOut i≢j)
    ≡⟨  Vecₚ.remove-punchOut (Vec.insert xs i x) i≢j ⟩
  Vec.lookup (Vec.insert xs i x) j
    ∎
  where open ≡-Reasoning

elimAt : ∀ i → Expression (Vec.insert Γ i t′) t  → Expression Γ t′ → Expression Γ t
elimAt′ : ∀ i → All (Expression (Vec.insert Γ i t′)) Δ  → Expression Γ t′ → All (Expression Γ) Δ

elimAt i (lit x) e′ = lit x
elimAt i (state j) e′ = state j
elimAt i (var j) e′ with i Fin.≟ j
... | yes refl = castType e′ (sym (Vecₚ.insert-lookup _ i _))
... | no i≢j = castType (var (Fin.punchOut i≢j)) (punchOut⇒insert _ i≢j _)
elimAt i (abort e) e′ = abort (elimAt i e e′)
elimAt i (_≟_ {hasEquality = hasEq} e e₁) e′ = _≟_ {hasEquality = hasEq} (elimAt i e e′) (elimAt i e₁ e′)
elimAt i (_<?_ {isNumeric = isNum} e e₁) e′ = _<?_ {isNumeric = isNum} (elimAt i e e′) (elimAt i e₁ e′)
elimAt i (inv e) e′ = elimAt i e e′
elimAt i (e && e₁) e′ = elimAt i e e′ && elimAt i e₁ e′
elimAt i (e || e₁) e′ = elimAt i e e′ || elimAt i e₁ e′
elimAt i (not e) e′ = not (elimAt i e e′)
elimAt i (e and e₁) e′ = elimAt i e e′ and elimAt i e₁ e′
elimAt i (e or e₁) e′ = elimAt i e e′ or elimAt i e₁ e′
elimAt i [ e ] e′ = [ elimAt i e e′ ]
elimAt i (unbox e) e′ = unbox (elimAt i e e′)
elimAt i (splice e e₁ e₂) e′ = splice (elimAt i e e′) (elimAt i e₁ e′) (elimAt i e₂ e′)
elimAt i (cut e e₁) e′ = cut (elimAt i e e′) (elimAt i e₁ e′)
elimAt i (cast eq e) e′ = cast eq (elimAt i e e′)
elimAt i (-_ {isNumeric = isNum} e) e′ = -_ {isNumeric = isNum} (elimAt i e e′)
elimAt i (e + e₁) e′ = elimAt i e e′ + elimAt i e₁ e′
elimAt i (e * e₁) e′ = elimAt i e e′ * elimAt i e₁ e′
elimAt i (_^_ {isNumeric = isNum} e x) e′ = _^_ {isNumeric = isNum} (elimAt i e e′) x
elimAt i (e >> x) e′ = elimAt i e e′ >> x
elimAt i (rnd e) e′ = rnd (elimAt i e e′)
elimAt i (fin x e) e′ = fin x (elimAt i e e′)
elimAt i (asInt e) e′ = asInt (elimAt i e e′)
elimAt i nil e′ = nil
elimAt i (cons e e₁) e′ = cons (elimAt i e e′) (elimAt i e₁ e′)
elimAt i (head e) e′ = head (elimAt i e e′)
elimAt i (tail e) e′ = tail (elimAt i e e′)
elimAt i (call f es) e′ = call f (elimAt′ i es e′)
elimAt i (if e then e₁ else e₂) e′ = if elimAt i e e′ then elimAt i e₁ e′ else elimAt i e₂ e′

elimAt′ i []       e′ = []
elimAt′ i (e ∷ es) e′ = elimAt i e e′ ∷ elimAt′ i es e′

wknAt  : ∀ i → Expression Γ t → Expression (Vec.insert Γ i t′) t
wknAt′ : ∀ i → All (Expression Γ) Δ  → All (Expression (Vec.insert Γ i t′)) Δ

wknAt i (lit x) = lit x
wknAt i (state j) = state j
wknAt i (var j) = castType (var (Fin.punchIn i j)) (Vecₚ.insert-punchIn _ i _ j)
wknAt i (abort e) = abort (wknAt i e)
wknAt i (_≟_ {hasEquality = hasEq} e e₁) = _≟_ {hasEquality = hasEq} (wknAt i e) (wknAt i e₁)
wknAt i (_<?_ {isNumeric = isNum} e e₁) = _<?_ {isNumeric = isNum} (wknAt i e) (wknAt i e₁)
wknAt i (inv e) = inv (wknAt i e)
wknAt i (e && e₁) = wknAt i e && wknAt i e₁
wknAt i (e || e₁) = wknAt i e && wknAt i e₁
wknAt i (not e) = not (wknAt i e)
wknAt i (e and e₁) = wknAt i e and wknAt i e₁
wknAt i (e or e₁) = wknAt i e or wknAt i e₁
wknAt i [ e ] = [ wknAt i e ]
wknAt i (unbox e) = unbox (wknAt i e)
wknAt i (splice e e₁ e₂) = splice (wknAt i e) (wknAt i e₁) (wknAt i e₂)
wknAt i (cut e e₁) = cut (wknAt i e) (wknAt i e₁)
wknAt i (cast eq e) = cast eq (wknAt i e)
wknAt i (-_ {isNumeric = isNum} e) = -_ {isNumeric = isNum} (wknAt i e)
wknAt i (e + e₁) = wknAt i e + wknAt i e₁
wknAt i (e * e₁) = wknAt i e * wknAt i e₁
wknAt i (_^_ {isNumeric = isNum} e x) = _^_ {isNumeric = isNum} (wknAt i e) x
wknAt i (e >> x) = wknAt i e >> x
wknAt i (rnd e) = rnd (wknAt i e)
wknAt i (fin x e) = fin x (wknAt i e)
wknAt i (asInt e) = asInt (wknAt i e)
wknAt i nil = nil
wknAt i (cons e e₁) = cons (wknAt i e) (wknAt i e₁)
wknAt i (head e) = head (wknAt i e)
wknAt i (tail e) = tail (wknAt i e)
wknAt i (call f es) = call f (wknAt′ i es)
wknAt i (if e then e₁ else e₂) = if wknAt i e then wknAt i e₁ else wknAt i e₂

wknAt′ i []       = []
wknAt′ i (e ∷ es) = wknAt i e ∷ wknAt′ i es

substAt : ∀ i → Expression Γ t → Expression Γ (Vec.lookup Γ i) → Expression Γ t
substAt′ : ∀ i → All (Expression Γ) Δ → Expression Γ (Vec.lookup Γ i) → All (Expression Γ) Δ
substAt i (lit x) e′ = lit x
substAt i (state j) e′ = state j
substAt i (var j) e′ with i Fin.≟ j
... | yes refl = e′
... | no _     = var j
substAt i (abort e) e′ = abort (substAt i e e′)
substAt i (_≟_ {hasEquality = hasEq} e e₁) e′ = _≟_ {hasEquality = hasEq} (substAt i e e′) (substAt i e₁ e′)
substAt i (_<?_ {isNumeric = isNum} e e₁) e′ = _<?_ {isNumeric = isNum} (substAt i e e′) (substAt i e₁ e′)
substAt i (inv e) e′ = inv (substAt i e e′)
substAt i (e && e₁) e′ = substAt i e e′ && substAt i e₁ e′
substAt i (e || e₁) e′ = substAt i e e′ || substAt i e₁ e′
substAt i (not e) e′ = not (substAt i e e′)
substAt i (e and e₁) e′ = substAt i e e′ and substAt i e₁ e′
substAt i (e or e₁) e′ = substAt i e e′ or substAt i e₁ e′
substAt i [ e ] e′ = [ substAt i e e′ ]
substAt i (unbox e) e′ = unbox (substAt i e e′)
substAt i (splice e e₁ e₂) e′ = splice (substAt i e e′) (substAt i e₁ e′) (substAt i e₂ e′)
substAt i (cut e e₁) e′ = cut (substAt i e e′) (substAt i e₁ e′)
substAt i (cast eq e) e′ = cast eq (substAt i e e′)
substAt i (-_ {isNumeric = isNum} e) e′ = -_ {isNumeric = isNum} (substAt i e e′)
substAt i (e + e₁) e′ = substAt i e e′ + substAt i e₁ e′
substAt i (e * e₁) e′ = substAt i e e′ * substAt i e₁ e′
substAt i (_^_ {isNumeric = isNum} e x) e′ = _^_ {isNumeric = isNum} (substAt i e e′) x
substAt i (e >> x) e′ = substAt i e e′ >> x
substAt i (rnd e) e′ = rnd (substAt i e e′)
substAt i (fin x e) e′ = fin x (substAt i e e′)
substAt i (asInt e) e′ = asInt (substAt i e e′)
substAt i nil e′ = nil
substAt i (cons e e₁) e′ = cons (substAt i e e′) (substAt i e₁ e′)
substAt i (head e) e′ = head (substAt i e e′)
substAt i (tail e) e′ = tail (substAt i e e′)
substAt i (call f es) e′ = call f (substAt′ i es e′)
substAt i (if e then e₁ else e₂) e′ = if substAt i e e′ then substAt i e₁ e′ else substAt i e₂ e′

substAt′ i []       e′ = []
substAt′ i (e ∷ es) e′ = substAt i e e′ ∷ substAt′ i es e′

updateRef : ∀ {e : Expression Γ t} (ref : CanAssign e) → ¬ ReferencesState e → Expression Γ t → Expression Γ t′ → Expression Γ t′
updateRef (state i) stateless val e = contradiction (state i) stateless
updateRef (var i) stateless val e = substAt i e val
updateRef (abort _) stateless val e = e
updateRef [ ref ] stateless val e = updateRef ref (stateless ∘ [_]) (unbox val) e
updateRef (unbox ref) stateless val e = updateRef ref (stateless ∘ unbox) [ val ] e
updateRef (splice ref ref₁ e₂) stateless val e = updateRef ref₁ (stateless ∘ (λ x → spliceʳ _ x _)) (head (tail (cut val e₂))) (updateRef ref (stateless ∘ (λ x → spliceˡ x _ _)) (head (cut val e₂)) e)
updateRef (cut ref e₁) stateless val e = updateRef ref (stateless ∘ (λ x → cut x _)) (splice (head val) (head (tail val)) e₁) e
updateRef (cast eq ref) stateless val e = updateRef ref (stateless ∘ cast eq) (cast (sym eq) val) e
updateRef nil stateless val e = e
updateRef (cons ref ref₁) stateless val e = updateRef ref₁ (stateless ∘ (λ x → consʳ _ x)) (tail val) (updateRef ref (stateless ∘ (λ x → consˡ x _)) (head val) e)
updateRef (head {e = e′} ref) stateless val e = updateRef ref (stateless ∘ head) (cons val (tail e′)) e
updateRef (tail {e = e′} ref) stateless val e = updateRef ref (stateless ∘ tail) (cons (head e′) val) e

wknAt-pres-assignable : ∀ i {e} → CanAssign e → CanAssign (wknAt {Γ = Γ} {t} {t′} i e)
wknAt-pres-assignable i (state j) = state j
wknAt-pres-assignable i (var j) = cast-pres-assignable (var (Fin.punchIn i j)) (Vecₚ.insert-punchIn _ i _ j)
wknAt-pres-assignable i (abort e) = abort (wknAt i e)
wknAt-pres-assignable i [ ref ] = [ wknAt-pres-assignable i ref ]
wknAt-pres-assignable i (unbox ref) = unbox (wknAt-pres-assignable i ref)
wknAt-pres-assignable i (splice ref ref₁ e₂) = splice (wknAt-pres-assignable i ref) (wknAt-pres-assignable i ref₁) (wknAt i e₂)
wknAt-pres-assignable i (cut ref e₁) = cut (wknAt-pres-assignable i ref) (wknAt i e₁)
wknAt-pres-assignable i (cast eq ref) = cast eq (wknAt-pres-assignable i ref)
wknAt-pres-assignable i nil = nil
wknAt-pres-assignable i (cons ref ref₁) = cons (wknAt-pres-assignable i ref) (wknAt-pres-assignable i ref₁)
wknAt-pres-assignable i (head ref) = head (wknAt-pres-assignable i ref)
wknAt-pres-assignable i (tail ref) = tail (wknAt-pres-assignable i ref)

wknAt-pres-stateless : ∀ i {e} → ReferencesState (wknAt {Γ = Γ} {t} {t′} i e) → ReferencesState e
wknAt-pres-stateless i {state _} (state j) = state j
wknAt-pres-stateless i {var j} e = contradiction (cast-pres-stateless {e = var (Fin.punchIn i j)} (Vecₚ.insert-punchIn _ i _ j) e) (λ ())
wknAt-pres-stateless i {[ _ ]} [ e ] = [ wknAt-pres-stateless i e  ]
wknAt-pres-stateless i {unbox _} (unbox e) = unbox (wknAt-pres-stateless i e)
wknAt-pres-stateless i {splice _ _ _} (spliceˡ e e₁ e₂) = spliceˡ (wknAt-pres-stateless i e) _ _
wknAt-pres-stateless i {splice _ _ _} (spliceʳ e e₁ e₂) = spliceʳ _ (wknAt-pres-stateless i e₁) _
wknAt-pres-stateless i {cut _ _} (cut e e₁) = cut (wknAt-pres-stateless i e) _
wknAt-pres-stateless i {cast _ _} (cast eq e) = cast eq (wknAt-pres-stateless i e)
wknAt-pres-stateless i {cons _ _} (consˡ e e₁) = consˡ (wknAt-pres-stateless i e) _
wknAt-pres-stateless i {cons _ _} (consʳ e e₁) = consʳ _ (wknAt-pres-stateless i e₁)
wknAt-pres-stateless i {head _} (head e) = head (wknAt-pres-stateless i e)
wknAt-pres-stateless i {tail _} (tail e) = tail (wknAt-pres-stateless i e)

wknStatementAt : ∀ t i → Statement Γ → Statement (Vec.insert Γ i t)
wknStatementAt t i (s ∙ s₁) = wknStatementAt t i s ∙ wknStatementAt t i s₁
wknStatementAt t i skip = skip
wknStatementAt t i (_≔_ ref {assignable} x) = _≔_ (wknAt i ref) {fromWitness (wknAt-pres-assignable i (toWitness assignable))} (wknAt i x)
wknStatementAt t i (declare x s) = declare (wknAt i x) (wknStatementAt t (suc i) s)
wknStatementAt t i (invoke p es) = invoke p (wknAt′ i es)
wknStatementAt t i (if x then s) = if wknAt i x then wknStatementAt t i s
wknStatementAt t i (if x then s else s₁) = if wknAt i x then wknStatementAt t i s else wknStatementAt t i s₁
wknStatementAt t i (for m s) = for m (wknStatementAt t (suc i) s)

subst : Expression Γ t → All (Expression Δ) Γ → Expression Δ t
subst′ : ∀ {n ts} → All (Expression Γ) {n} ts → All (Expression Δ) Γ → All (Expression Δ) ts

subst (lit x) xs = lit x
subst (state i) xs = state i
subst (var i) xs = All.lookup i xs
subst (abort e) xs = abort (subst e xs)
subst (_≟_ {hasEquality = hasEq} e e₁) xs = _≟_ {hasEquality = hasEq} (subst e xs) (subst e₁ xs)
subst (_<?_ {isNumeric = isNum} e e₁) xs = _<?_ {isNumeric = isNum} (subst e xs) (subst e₁ xs)
subst (inv e) xs = inv (subst e xs)
subst (e && e₁) xs = subst e xs && subst e₁ xs
subst (e || e₁) xs = subst e xs || subst e₁ xs
subst (not e) xs = not (subst e xs)
subst (e and e₁) xs = subst e xs and subst e₁ xs
subst (e or e₁) xs = subst e xs or subst e₁ xs
subst [ e ] xs = [ subst e xs ]
subst (unbox e) xs = unbox (subst e xs)
subst (splice e e₁ e₂) xs = splice (subst e xs) (subst e₁ xs) (subst e₂ xs)
subst (cut e e₁) xs = cut (subst e xs) (subst e₁ xs)
subst (cast eq e) xs = cast eq (subst e xs)
subst (-_ {isNumeric = isNum} e) xs = -_ {isNumeric = isNum} (subst e xs)
subst (e + e₁) xs = subst e xs + subst e₁ xs
subst (e * e₁) xs = subst e xs * subst e₁ xs
subst (_^_ {isNumeric = isNum} e x) xs = _^_ {isNumeric = isNum} (subst e xs) x
subst (e >> x) xs = subst e xs >> x
subst (rnd e) xs = rnd (subst e xs)
subst (fin x e) xs = fin x (subst e xs)
subst (asInt e) xs = asInt (subst e xs)
subst nil xs = nil
subst (cons e e₁) xs = cons (subst e xs) (subst e₁ xs)
subst (head e) xs = head (subst e xs)
subst (tail e) xs = tail (subst e xs)
subst (call f es) xs = call f (subst′ es xs)
subst (if e then e₁ else e₂) xs = if subst e xs then subst e₁ xs else subst e₂ xs

subst′ []       xs = []
subst′ (e ∷ es) xs = subst e xs ∷ subst′ es xs

callDepth     : Expression Γ t → ℕ
callDepth′  : All (Expression Γ) Δ → ℕ
stmtCallDepth : Statement Γ → ℕ
funCallDepth  : Function Γ ret → ℕ
procCallDepth : Procedure Γ → ℕ

callDepth (lit x) = 0
callDepth (state i) = 0
callDepth (var i) = 0
callDepth (abort e) = callDepth e
callDepth (e ≟ e₁) = callDepth e ⊔ callDepth e₁
callDepth (e <? e₁) = callDepth e ⊔ callDepth e₁
callDepth (inv e) = callDepth e
callDepth (e && e₁) = callDepth e ⊔ callDepth e₁
callDepth (e || e₁) = callDepth e ⊔ callDepth e₁
callDepth (not e) = callDepth e
callDepth (e and e₁) = callDepth e ⊔ callDepth e₁
callDepth (e or e₁) = callDepth e ⊔ callDepth e₁
callDepth [ e ] = callDepth e
callDepth (unbox e) = callDepth e
callDepth (splice e e₁ e₂) = callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂
callDepth (cut e e₁) = callDepth e ⊔ callDepth e₁
callDepth (cast eq e) = callDepth e
callDepth (- e) = callDepth e
callDepth (e + e₁) = callDepth e ⊔ callDepth e₁
callDepth (e * e₁) = callDepth e ⊔ callDepth e₁
callDepth (e ^ x) = callDepth e
callDepth (e >> x) = callDepth e
callDepth (rnd e) = callDepth e
callDepth (fin x e) = callDepth e
callDepth (asInt e) = callDepth e
callDepth nil = 0
callDepth (cons e e₁) = callDepth e ⊔ callDepth e₁
callDepth (head e) = callDepth e
callDepth (tail e) = callDepth e
callDepth (call f es) = suc (funCallDepth f) ⊔ callDepth′ es
callDepth (if e then e₁ else e₂) = callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂

callDepth′ [] = 0
callDepth′ (e ∷ es) = callDepth e ⊔ callDepth′ es

stmtCallDepth (s ∙ s₁) = stmtCallDepth s ⊔ stmtCallDepth s₁
stmtCallDepth skip = 0
stmtCallDepth (ref ≔ x) = callDepth ref ⊔ callDepth x
stmtCallDepth (declare x s) = callDepth x ⊔ stmtCallDepth s
stmtCallDepth (invoke p es) = procCallDepth p ⊔ callDepth′ es
stmtCallDepth (if x then s) = callDepth x ⊔ stmtCallDepth s
stmtCallDepth (if x then s else s₁) = callDepth x ⊔ stmtCallDepth s ⊔ stmtCallDepth s₁
stmtCallDepth (for m s) = stmtCallDepth s

funCallDepth (s ∙return x) = stmtCallDepth s ⊔ callDepth x
funCallDepth (declare x f) = funCallDepth f ⊔ callDepth x

procCallDepth (x ∙end) = stmtCallDepth x

open ℕₚ.≤-Reasoning

castType-pres-callDepth : ∀ (e : Expression Γ t) (eq : t ≡ t′) → callDepth (castType e eq) ≡ callDepth e
castType-pres-callDepth e refl = refl

elimAt-pres-callDepth : ∀ i (e : Expression (Vec.insert Γ i t′) t) (e′ : Expression Γ t′) → callDepth (elimAt i e e′) ℕ.≤ callDepth e′ ⊔ callDepth e
elimAt′-pres-callDepth : ∀ i (es : All (Expression (Vec.insert Γ i t′)) Δ) (e′ : Expression Γ t′) → callDepth′ (elimAt′ i es e′) ℕ.≤ callDepth e′ ⊔ callDepth′ es

elimAt-pres-callDepth i (lit x) e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
elimAt-pres-callDepth i (state j) e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
elimAt-pres-callDepth i (var j) e′ with i Fin.≟ j
... | yes refl = begin
  callDepth (castType e′ (sym (Vecₚ.insert-lookup _ i _)))
    ≡⟨ castType-pres-callDepth e′ (sym (Vecₚ.insert-lookup _ i _)) ⟩
  callDepth e′
    ≤⟨ ℕₚ.m≤m⊔n (callDepth e′) 0 ⟩
  callDepth e′ ⊔ 0
    ∎
elimAt-pres-callDepth {Γ = Γ} i (var j) e′ | no i≢j   = begin
    callDepth (castType (var {Γ = Γ} (Fin.punchOut i≢j)) (punchOut⇒insert Γ i≢j _))
      ≡⟨ castType-pres-callDepth (var {Γ = Γ} (Fin.punchOut i≢j)) (punchOut⇒insert Γ i≢j _) ⟩
    0
      ≤⟨ ℕ.z≤n ⟩
    callDepth e′ ⊔ 0
      ∎
elimAt-pres-callDepth i (abort e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (e ≟ e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (e <? e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (inv e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (e && e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (e || e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (not e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (e and e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (e or e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i [ e ] e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (unbox e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (splice e e₁ e₂) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′) ⊔ callDepth (elimAt i e₂ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′)) (elimAt-pres-callDepth i e₂ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁) ⊔ (callDepth e′ ⊔ callDepth e₂)
    ≡⟨ ⊔-solve 4 (λ m n o p → (((m ⊕ n) ⊕ (m ⊕ o)) ⊕ (m ⊕ p)) ⊜ (m ⊕ ((n ⊕ o) ⊕ p))) refl (callDepth e′) (callDepth e) (callDepth e₁) (callDepth e₂) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂)
    ∎
elimAt-pres-callDepth i (cut e e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (cast eq e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (- e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (e + e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (e * e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (e ^ x) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (e >> x) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (rnd e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (fin x e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (asInt e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i nil e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
elimAt-pres-callDepth i (cons e e₁) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ m n o → (m ⊕ n) ⊕ (m ⊕ o) ⊜ m ⊕ (n ⊕ o)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
elimAt-pres-callDepth i (head e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (tail e) e′ = elimAt-pres-callDepth i e e′
elimAt-pres-callDepth i (call f es) e′ = begin
  suc (funCallDepth f) ⊔ callDepth′ (elimAt′ i es e′)
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (suc (funCallDepth f)) (elimAt′-pres-callDepth i es e′) ⟩
  suc (funCallDepth f) ⊔ (callDepth e′ ⊔ callDepth′ es)
    ≡⟨ ⊔-solve 3 (λ a b c → b ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (suc (funCallDepth f)) (callDepth′ es) ⟩
  callDepth e′ ⊔ (suc (funCallDepth f) ⊔ callDepth′ es)
    ∎
elimAt-pres-callDepth i (if e then e₁ else e₂) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth (elimAt i e₁ e′) ⊔ callDepth (elimAt i e₂ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt-pres-callDepth i e₁ e′)) (elimAt-pres-callDepth i e₂ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁) ⊔ (callDepth e′ ⊔ callDepth e₂)
    ≡⟨ ⊔-solve 4 (λ m n o p → (((m ⊕ n) ⊕ (m ⊕ o)) ⊕ (m ⊕ p)) ⊜ (m ⊕ ((n ⊕ o) ⊕ p))) refl (callDepth e′) (callDepth e) (callDepth e₁) (callDepth e₂) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂)
    ∎

elimAt′-pres-callDepth i []       e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
elimAt′-pres-callDepth i (e ∷ es) e′ = begin
  callDepth (elimAt i e e′) ⊔ callDepth′ (elimAt′ i es e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (elimAt-pres-callDepth i e e′) (elimAt′-pres-callDepth i es e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth′ es)
    ≡⟨ ⊔-solve 3 (λ a b c → ((a ⊕ b) ⊕ (a ⊕ c)) ⊜ (a ⊕ (b ⊕ c))) refl (callDepth e′) (callDepth e) (callDepth′ es) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth′ es)
    ∎

wknAt-pres-callDepth : ∀ i (e : Expression Γ t) → callDepth (wknAt {t′ = t′} i e) ≡ callDepth e
wknAt′-pres-callDepth : ∀ i (es : All (Expression Γ) Δ) → callDepth′ (wknAt′ {t′ = t′} i es) ≡ callDepth′ es

wknAt-pres-callDepth i (Code.lit x) = refl
wknAt-pres-callDepth i (Code.state j) = refl
wknAt-pres-callDepth {Γ = Γ} i (Code.var j) = castType-pres-callDepth (var {Γ = Vec.insert Γ i _} (Fin.punchIn i j)) (Vecₚ.insert-punchIn Γ i _ j)
wknAt-pres-callDepth i (Code.abort e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (e Code.≟ e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (e Code.<? e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (Code.inv e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (e Code.&& e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (e Code.|| e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (Code.not e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (e Code.and e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (e Code.or e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i Code.[ e ] = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.unbox e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.splice e e₁ e₂) = congₙ 3 (λ m n o → m ⊔ n ⊔ o) (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁) (wknAt-pres-callDepth i e₂)
wknAt-pres-callDepth i (Code.cut e e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (Code.cast eq e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.- e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (e Code.+ e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (e Code.* e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (e Code.^ x) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (e Code.>> x) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.rnd e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.fin x e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.asInt e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i Code.nil = refl
wknAt-pres-callDepth i (Code.cons e e₁) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁)
wknAt-pres-callDepth i (Code.head e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.tail e) = wknAt-pres-callDepth i e
wknAt-pres-callDepth i (Code.call f es) = cong (suc (funCallDepth f) ⊔_) (wknAt′-pres-callDepth i es)
wknAt-pres-callDepth i (Code.if e then e₁ else e₂) = congₙ 3 (λ m n o → m ⊔ n ⊔ o) (wknAt-pres-callDepth i e) (wknAt-pres-callDepth i e₁) (wknAt-pres-callDepth i e₂)

wknAt′-pres-callDepth i []       = refl
wknAt′-pres-callDepth i (e ∷ es) = cong₂ _⊔_ (wknAt-pres-callDepth i e) (wknAt′-pres-callDepth i es)

substAt-pres-callDepth : ∀ i (e : Expression Γ t) e′ → callDepth (substAt i e e′) ℕ.≤ callDepth e′ ⊔ callDepth e
substAt-pres-callDepth i (Code.lit x) e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
substAt-pres-callDepth i (Code.state j) e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
substAt-pres-callDepth i (Code.var j) e′ with i Fin.≟ j
... | yes refl = ℕₚ.m≤m⊔n (callDepth e′) 0
... | no _     = ℕₚ.m≤n⊔m (callDepth e′) 0
substAt-pres-callDepth i (Code.abort e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (e Code.≟ e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (e Code.<? e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (Code.inv e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (e Code.&& e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (e Code.|| e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (Code.not e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (e Code.and e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (e Code.or e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i Code.[ e ] e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.unbox e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.splice e e₁ e₂) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′) ⊔ callDepth (substAt i e₂ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′)) (substAt-pres-callDepth i e₂ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁) ⊔ (callDepth e′ ⊔ callDepth e₂)
    ≡⟨ ⊔-solve 4 (λ a b c d → ((a ⊕ b) ⊕ (a ⊕ c)) ⊕ (a ⊕ d) ⊜ a ⊕ ((b ⊕ c) ⊕ d)) refl (callDepth e′) (callDepth e) (callDepth e₁) (callDepth e₂) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂)
    ∎
substAt-pres-callDepth i (Code.cut e e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (Code.cast eq e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.- e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (e Code.+ e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (e Code.* e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (e Code.^ x) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (e Code.>> x) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.rnd e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.fin x e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.asInt e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i Code.nil e′ = ℕₚ.m≤n⊔m (callDepth e′) 0
substAt-pres-callDepth i (Code.cons e e₁) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ b) ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (callDepth e) (callDepth e₁) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁)
    ∎
substAt-pres-callDepth i (Code.head e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.tail e) e′ = substAt-pres-callDepth i e e′
substAt-pres-callDepth i (Code.call f es) e′ = begin
  suc (funCallDepth f) ⊔ callDepth′ (substAt′ i es e′)
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (suc (funCallDepth f)) (helper es) ⟩
  suc (funCallDepth f) ⊔ (callDepth e′ ⊔ callDepth′ es)
    ≡⟨ ⊔-solve 3 (λ a b c → b ⊕ (a ⊕ c) ⊜ a ⊕ (b ⊕ c)) refl (callDepth e′) (suc (funCallDepth f)) (callDepth′ es) ⟩
  callDepth e′ ⊔ (suc (funCallDepth f) ⊔ callDepth′ es)
    ∎
  where
  helper : ∀ {n ts} (es : All _ {n} ts) → callDepth′ (substAt′ i es e′) ℕ.≤ callDepth e′ ⊔ callDepth′ es
  helper []       = ℕₚ.m≤n⊔m (callDepth e′) 0
  helper (e ∷ es) = begin
    callDepth (substAt i e e′) ⊔ callDepth′ (substAt′ i es e′)
      ≤⟨ ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (helper es) ⟩
    callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth′ es)
      ≡⟨ ⊔-solve 3 (λ a b c → ((a ⊕ b) ⊕ (a ⊕ c)) ⊜ (a ⊕ (b ⊕ c))) refl (callDepth e′) (callDepth e) (callDepth′ es) ⟩
    callDepth e′ ⊔ (callDepth e ⊔ callDepth′ es)
      ∎
substAt-pres-callDepth i (Code.if e then e₁ else e₂) e′ = begin
  callDepth (substAt i e e′) ⊔ callDepth (substAt i e₁ e′) ⊔ callDepth (substAt i e₂ e′)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (substAt-pres-callDepth i e e′) (substAt-pres-callDepth i e₁ e′)) (substAt-pres-callDepth i e₂ e′) ⟩
  callDepth e′ ⊔ callDepth e ⊔ (callDepth e′ ⊔ callDepth e₁) ⊔ (callDepth e′ ⊔ callDepth e₂)
    ≡⟨ ⊔-solve 4 (λ a b c d → ((a ⊕ b) ⊕ (a ⊕ c)) ⊕ (a ⊕ d) ⊜ a ⊕ ((b ⊕ c) ⊕ d)) refl (callDepth e′) (callDepth e) (callDepth e₁) (callDepth e₂) ⟩
  callDepth e′ ⊔ (callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂)
    ∎

updateRef-pres-callDepth : ∀ {e : Expression Γ t} ref stateless val (e′ : Expression Γ t′) →
                           callDepth (updateRef {e = e} ref stateless val e′) ℕ.≤ callDepth e ⊔ callDepth val ⊔ callDepth e′
updateRef-pres-callDepth (state i) stateless val e′ = contradiction (state i) stateless
updateRef-pres-callDepth (var i) stateless val e′ = substAt-pres-callDepth i e′ val
updateRef-pres-callDepth (abort e) stateless val e′ = ℕₚ.m≤n⊔m (callDepth e ⊔ callDepth val) (callDepth e′)
updateRef-pres-callDepth [ ref ] stateless val e′ = updateRef-pres-callDepth ref (stateless ∘ [_]) (unbox val) e′
updateRef-pres-callDepth (unbox ref) stateless val e′ = updateRef-pres-callDepth ref (stateless ∘ unbox) [ val ] e′
updateRef-pres-callDepth (splice {e₁ = e₁} {e₂ = e₂} ref ref₁ e₃) stateless val e′ = begin
  callDepth outer
    ≤⟨ updateRef-pres-callDepth ref₁ (stateless ∘ (λ x → spliceʳ _ x e₃)) (head (tail (cut val e₃))) inner ⟩
  callDepth e₂ ⊔ (callDepth val ⊔ callDepth e₃) ⊔ callDepth inner
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (callDepth e₂ ⊔ (callDepth val ⊔ callDepth e₃)) (updateRef-pres-callDepth ref (stateless ∘ (λ x → spliceˡ x _ e₃)) (head (cut val e₃)) e′) ⟩
  callDepth e₂ ⊔ (callDepth val ⊔ callDepth e₃) ⊔ (callDepth e₁ ⊔ (callDepth val ⊔ callDepth e₃) ⊔ callDepth e′)
    ≡⟨ ⊔-solve 5 (λ a b c d e → ((b ⊕ (d ⊕ c)) ⊕ ((a ⊕ (d ⊕ c)) ⊕ e)) ⊜ ((((a ⊕ b) ⊕ c) ⊕ d) ⊕ e)) refl (callDepth e₁) (callDepth e₂) (callDepth e₃) (callDepth val) (callDepth e′) ⟩
  callDepth e₁ ⊔ callDepth e₂ ⊔ callDepth e₃ ⊔ callDepth val ⊔ callDepth e′
    ∎
  where
  inner = updateRef ref (stateless ∘ (λ x → spliceˡ x _ e₃)) (head (cut val e₃)) e′
  outer = updateRef ref₁ (stateless ∘ (λ x → spliceʳ _ x e₃)) (head (tail (cut val e₃))) inner
updateRef-pres-callDepth (cut {e₁ = e₁} ref e₂) stateless val e′ = begin
  callDepth (updateRef ref (stateless ∘ (λ x → (cut x e₂))) (splice (head val) (head (tail val)) e₂) e′)
    ≤⟨ updateRef-pres-callDepth ref (stateless ∘ (λ x → (cut x e₂))) (splice (head val) (head (tail val)) e₂) e′ ⟩
  callDepth e₁ ⊔ (callDepth val ⊔ callDepth val ⊔ callDepth e₂) ⊔ callDepth e′
    ≡⟨ ⊔-solve 4 (λ a b c d → (a ⊕ ((c ⊕ c) ⊕ b)) ⊕ d ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (callDepth e₁) (callDepth e₂) (callDepth val) (callDepth e′) ⟩
  callDepth e₁ ⊔ callDepth e₂ ⊔ callDepth val ⊔ callDepth e′
    ∎
updateRef-pres-callDepth (cast eq ref) stateless val e′ = updateRef-pres-callDepth ref (stateless ∘ cast eq) (cast (sym eq) val) e′
updateRef-pres-callDepth nil stateless val e′ = ℕₚ.m≤n⊔m (callDepth val) (callDepth e′)
updateRef-pres-callDepth (cons {e₁ = e₁} {e₂ = e₂} ref ref₁) stateless val e′ = begin
  callDepth outer
    ≤⟨ updateRef-pres-callDepth ref₁ (stateless ∘ consʳ e₁) (tail val) inner ⟩
  callDepth e₂ ⊔ callDepth val ⊔ callDepth inner
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (callDepth e₂ ⊔ callDepth val) (updateRef-pres-callDepth ref (stateless ∘ (λ x → consˡ x e₂)) (head val) e′) ⟩
  callDepth e₂ ⊔ callDepth val ⊔ (callDepth e₁ ⊔ callDepth val ⊔ callDepth e′)
    ≡⟨ ⊔-solve 4 (λ a b c d → (b ⊕ c) ⊕ ((a ⊕ c) ⊕ d) ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (callDepth e₁) (callDepth e₂) (callDepth val) (callDepth e′) ⟩
  callDepth e₁ ⊔ callDepth e₂ ⊔ callDepth val ⊔ callDepth e′
    ∎
  where
  inner = updateRef ref (stateless ∘ (λ x → consˡ x e₂)) (head val) e′
  outer = updateRef ref₁ (stateless ∘ consʳ e₁) (tail val) inner
updateRef-pres-callDepth (head {e = e} ref) stateless val e′ = begin
  callDepth (updateRef ref (stateless ∘ head) (cons val (tail e)) e′)
    ≤⟨ updateRef-pres-callDepth ref (stateless ∘ head) (cons val (tail e)) e′ ⟩
  callDepth e ⊔ (callDepth val ⊔ callDepth e) ⊔ callDepth e′
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ (b ⊕ a)) ⊕ c ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth val) (callDepth e′) ⟩
  callDepth e ⊔ callDepth val ⊔ callDepth e′
    ∎
updateRef-pres-callDepth (tail {e = e} ref) stateless val e′ = begin
  callDepth (updateRef ref (stateless ∘ tail) (cons (head e) val) e′)
    ≤⟨ updateRef-pres-callDepth ref (stateless ∘ tail) (cons (head e) val) e′ ⟩
  callDepth e ⊔ (callDepth e ⊔ callDepth val) ⊔ callDepth e′
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ (a ⊕ b)) ⊕ c ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth val) (callDepth e′) ⟩
  callDepth e ⊔ callDepth val ⊔ callDepth e′
    ∎

subst-pres-callDepth : ∀ (e : Expression Γ t) (args : All (Expression Δ) Γ) → callDepth (subst e args) ℕ.≤ callDepth e ⊔ callDepth′ args
subst-pres-callDepth (lit x) args = ℕ.z≤n
subst-pres-callDepth (state i) args = ℕ.z≤n
subst-pres-callDepth (var i) args = helper i args
  where
  helper : ∀ i (es : All (Expression Γ) Δ) → callDepth (All.lookup i es) ℕ.≤ callDepth′ es
  helper 0F (e ∷ es) = ℕₚ.m≤m⊔n (callDepth e) (callDepth′ es)
  helper (suc i) (e ∷ es) = ℕₚ.m≤n⇒m≤o⊔n (callDepth e) (helper i es)
subst-pres-callDepth (abort e) args = subst-pres-callDepth e args
subst-pres-callDepth (e ≟ e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (e <? e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (inv e) args = subst-pres-callDepth e args
subst-pres-callDepth (e && e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (e || e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (not e) args = subst-pres-callDepth e args
subst-pres-callDepth (e and e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (e or e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth [ e ] args = subst-pres-callDepth e args
subst-pres-callDepth (unbox e) args = subst-pres-callDepth e args
subst-pres-callDepth (splice e e₁ e₂) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args) ⊔ callDepth (subst e₂ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args)) (subst-pres-callDepth e₂ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args) ⊔ (callDepth e₂ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 4 (λ a b c d → ((a ⊕ d) ⊕ (b ⊕ d)) ⊕ (c ⊕ d) ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (callDepth e) (callDepth e₁) (callDepth e₂) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (cut e e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (cast eq e) args = subst-pres-callDepth e args
subst-pres-callDepth (- e) args = subst-pres-callDepth e args
subst-pres-callDepth (e + e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (e * e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (e ^ x) args = subst-pres-callDepth e args
subst-pres-callDepth (e >> x) args = subst-pres-callDepth e args
subst-pres-callDepth (rnd e) args = subst-pres-callDepth e args
subst-pres-callDepth (fin x e) args = subst-pres-callDepth e args
subst-pres-callDepth (asInt e) args = subst-pres-callDepth e args
subst-pres-callDepth nil args = ℕ.z≤n
subst-pres-callDepth (cons e e₁) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth e₁) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth′ args
    ∎
subst-pres-callDepth (head e) args = subst-pres-callDepth e args
subst-pres-callDepth (tail e) args = subst-pres-callDepth e args
subst-pres-callDepth (call f es) args = begin
  suc (funCallDepth f) ⊔ callDepth′ (subst′ es args)
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (suc (funCallDepth f)) (helper es args) ⟩
  suc (funCallDepth f) ⊔ (callDepth′ es ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → a ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (suc (funCallDepth f)) (callDepth′ es) (callDepth′ args) ⟩
  suc (funCallDepth f) ⊔ callDepth′ es ⊔ callDepth′ args
    ∎
  where
  helper : ∀ {n ts} (es : All (Expression Γ) {n} ts) (args : All (Expression Δ) Γ) → callDepth′ (subst′ es args) ℕ.≤ callDepth′ es ℕ.⊔ callDepth′ args
  helper []       args = ℕ.z≤n
  helper (e ∷ es) args = begin
    callDepth (subst e args) ⊔ callDepth′ (subst′ es args)
      ≤⟨ ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (helper es args) ⟩
    callDepth e ⊔ callDepth′ args ⊔ (callDepth′ es ⊔ callDepth′ args)
      ≡⟨ ⊔-solve 3 (λ a b c → (a ⊕ c) ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth e) (callDepth′ es) (callDepth′ args) ⟩
    callDepth e ⊔ callDepth′ es ⊔ callDepth′ args
      ∎
subst-pres-callDepth (if e then e₁ else e₂) args = begin
  callDepth (subst e args) ⊔ callDepth (subst e₁ args) ⊔ callDepth (subst e₂ args)
    ≤⟨ ℕₚ.⊔-mono-≤ (ℕₚ.⊔-mono-≤ (subst-pres-callDepth e args) (subst-pres-callDepth e₁ args)) (subst-pres-callDepth e₂ args) ⟩
  callDepth e ⊔ callDepth′ args ⊔ (callDepth e₁ ⊔ callDepth′ args) ⊔ (callDepth e₂ ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 4 (λ a b c d → ((a ⊕ d) ⊕ (b ⊕ d)) ⊕ (c ⊕ d) ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (callDepth e) (callDepth e₁) (callDepth e₂) (callDepth′ args) ⟩
  callDepth e ⊔ callDepth e₁ ⊔ callDepth e₂ ⊔ callDepth′ args
    ∎

wkn-pres-callDepth : ∀ t i (s : Statement Γ) → stmtCallDepth (wknStatementAt t i s) ≡ stmtCallDepth s
wkn-pres-callDepth t i (s Code.∙ s₁) = cong₂ _⊔_ (wkn-pres-callDepth t i s) (wkn-pres-callDepth t i s₁)
wkn-pres-callDepth t i Code.skip = refl
wkn-pres-callDepth t i (ref Code.≔ x) = cong₂ _⊔_ (wknAt-pres-callDepth i ref) (wknAt-pres-callDepth i x)
wkn-pres-callDepth t i (Code.declare x s) = cong₂ _⊔_ (wknAt-pres-callDepth i x) (wkn-pres-callDepth t (suc i) s)
wkn-pres-callDepth t i (Code.invoke p es) = cong (procCallDepth p ⊔_) (wknAt′-pres-callDepth i es)
wkn-pres-callDepth t i (Code.if x then s) = cong₂ _⊔_ (wknAt-pres-callDepth i x) (wkn-pres-callDepth t i s)
wkn-pres-callDepth t i (Code.if x then s else s₁) = congₙ 3 (λ m n o → m ⊔ n ⊔ o) (wknAt-pres-callDepth i x) (wkn-pres-callDepth t i s) (wkn-pres-callDepth t i s₁)
wkn-pres-callDepth t i (Code.for m s) = wkn-pres-callDepth t (suc i) s

private
  index₀ : Statement Γ → ℕ
  index₀ (s ∙ s₁)                                     = index₀ s ℕ.+ index₀ s₁
  index₀ skip                                         = 0
  index₀ (ref ≔ x)                                    = 0
  index₀ (declare x s)                                = index₀ s
  index₀ (invoke p es)                                = 0
  index₀ (if x then s)                                = index₀ s
  index₀ (if x then s else s₁)                        = suc (index₀ s ℕ.+ index₀ s₁)
  index₀ (for m s)                                    = index₀ s

  index₁ : Statement Γ → ℕ
  index₁ (s ∙ s₁)              = suc (index₁ s ℕ.+ index₁ s₁)
  index₁ skip                  = 0
  index₁ (ref ≔ x)             = 0
  index₁ (declare x s)         = index₁ s
  index₁ (invoke x x₁)         = 0
  index₁ (if x then s)         = suc (3 ℕ.* index₁ s)
  index₁ (if x then s else s₁) = suc (3 ℕ.* index₁ s ℕ.+ index₁ s₁)
  index₁ (for m s)             = suc (index₁ s)

  index₂ : Statement Γ → ℕ
  index₂ (s ∙ s₁)              = 0
  index₂ skip                  = 0
  index₂ (ref ≔ x)             = 0
  index₂ (declare x s)         = suc (index₂ s)
  index₂ (invoke _ _)          = 0
  index₂ (if x then s)         = 2 ℕ.* index₂ s
  index₂ (if x then s else s₁) = 0
  index₂ (for m s)             = 0

  wkn-pres-index₀ : ∀ t i s → index₀ (wknStatementAt {Γ = Γ} t i s) ≡ index₀ s
  wkn-pres-index₀ _ i (s ∙ s₁) = cong₂ ℕ._+_ (wkn-pres-index₀ _ i s) (wkn-pres-index₀ _ i s₁)
  wkn-pres-index₀ _ i skip = refl
  wkn-pres-index₀ _ i (ref ≔ x) = refl
  wkn-pres-index₀ _ i (declare x s) = wkn-pres-index₀ _ (suc i) s
  wkn-pres-index₀ _ i (invoke x x₁) = refl
  wkn-pres-index₀ _ i (if x then s) = wkn-pres-index₀ _ i s
  wkn-pres-index₀ _ i (if x then s else s₁) = cong₂ (λ m n → suc (m ℕ.+ n)) (wkn-pres-index₀ _ i s) (wkn-pres-index₀ _ i s₁)
  wkn-pres-index₀ _ i (for m s) = wkn-pres-index₀ _ (suc i) s

  wkn-pres-index₁ : ∀ t i s → index₁ (wknStatementAt {Γ = Γ} t i s) ≡ index₁ s
  wkn-pres-index₁ _ i (s ∙ s₁) = cong₂ (λ m n → suc (m ℕ.+ n)) (wkn-pres-index₁ _ i s) (wkn-pres-index₁ _ i s₁)
  wkn-pres-index₁ _ i skip = refl
  wkn-pres-index₁ _ i (ref ≔ x) = refl
  wkn-pres-index₁ _ i (declare x s) = wkn-pres-index₁ _ (suc i) s
  wkn-pres-index₁ _ i (invoke x x₁) = refl
  wkn-pres-index₁ _ i (if x then s) = cong (λ m → suc (3 ℕ.* m)) (wkn-pres-index₁ _ i s)
  wkn-pres-index₁ _ i (if x then s else s₁) = cong₂ (λ m n → suc (3 ℕ.* m ℕ.+ n)) (wkn-pres-index₁ _ i s) (wkn-pres-index₁ _ i s₁)
  wkn-pres-index₁ _ i (for m s) = cong suc (wkn-pres-index₁ _ (suc i) s)

  wkn-pres-changes : ∀ t i {s} → ChangesState (wknStatementAt {Γ = Γ} t i s) → ChangesState s
  wkn-pres-changes t i {_ ∙ _} (s ∙ˡ s₁) = wkn-pres-changes t i s ∙ˡ _
  wkn-pres-changes t i {_ ∙ _} (s ∙ʳ s₁) = _ ∙ʳ wkn-pres-changes t i s₁
  wkn-pres-changes t i {_ ≔ _} (_≔_ ref {canAssign} {refsState} e) = _≔_ _ {refsState = fromWitness (wknAt-pres-stateless i (toWitness refsState))} _
  wkn-pres-changes t i {declare _ _} (declare e s) = declare _ (wkn-pres-changes t (suc i) s)
  wkn-pres-changes t i {invoke _ _} (invoke p es) = invoke _ _
  wkn-pres-changes t i {if _ then _} (if e then s) = if _ then wkn-pres-changes t i s
  wkn-pres-changes t i {if _ then _ else _} (if e then′ s else s₁) = if _ then′ wkn-pres-changes t i s else _
  wkn-pres-changes t i {if _ then _ else _} (if e then s else′ s₁) = if _ then _ else′ wkn-pres-changes t i s₁
  wkn-pres-changes t i {for _ _} (for m s) = for m (wkn-pres-changes t (suc i) s)

  RecItem : Set
  RecItem = ∃ λ n → ∃ (Statement {n})

  inlinePredicate : RecItem → Set
  inlinePredicate (_ , Γ , s) = ¬ ChangesState s → ∀ {ret} → (e : Expression Γ ret) → ∃ λ (e′ : Expression Γ ret) → callDepth e′ ℕ.≤ stmtCallDepth s ⊔ callDepth e

  inlineRel : RecItem → RecItem → Set
  inlineRel = Lex.×-Lex _≡_ ℕ._<_ (Lex.×-Lex _≡_ ℕ._<_ ℕ._<_) on < (index₀ ∘ proj₂ ∘ proj₂) , < (index₁ ∘ proj₂ ∘ proj₂) , (index₂ ∘ proj₂ ∘ proj₂) > >

  inlineRelWf : Wf.WellFounded inlineRel
  inlineRelWf =
    On.wellFounded
      < (index₀ ∘ proj₂ ∘ proj₂) , < (index₁ ∘ proj₂ ∘ proj₂) , (index₂ ∘ proj₂ ∘ proj₂) > >
      (Lex.×-wellFounded ℕᵢ.<-wellFounded (Lex.×-wellFounded ℕᵢ.<-wellFounded ℕᵢ.<-wellFounded))

  s<s∙s₁ : ∀ (s s₁ : Statement Γ) → inlineRel (_ , _ , s) (_ , _ , (s ∙ s₁))
  s<s∙s₁ s s₁ = case index₀ s₁ return (λ x → index₀ s ℕ.< index₀ s ℕ.+ x ⊎ index₀ s ≡ index₀ s ℕ.+ x × (index₁ s ℕ.< suc (index₁ s ℕ.+ index₁ s₁) ⊎ (index₁ s ≡ suc (index₁ s ℕ.+ index₁ s₁) × index₂ s ℕ.< 0))) of λ
    { 0       → inj₂ (sym (ℕₚ.+-identityʳ (index₀ s)) , inj₁ (ℕₚ.m≤m+n (suc (index₁ s)) (index₁ s₁)))
    ; (suc n) → inj₁ (ℕₚ.m<m+n (index₀ s) ℕₚ.0<1+n)
    }

  s₁<s∙s₁ : ∀ (s s₁ : Statement Γ) → inlineRel (_ , _ , s₁) (_ , _ , (s ∙ s₁))
  s₁<s∙s₁ s s₁ = case index₀ s return (λ x → index₀ s₁ ℕ.< x ℕ.+ index₀ s₁ ⊎ index₀ s₁ ≡ x ℕ.+ index₀ s₁ × (index₁ s₁ ℕ.< suc (index₁ s ℕ.+ index₁ s₁) ⊎ (index₁ s₁ ≡ suc (index₁ s ℕ.+ index₁ s₁) × index₂ s₁ ℕ.< 0))) of λ
    { 0       → inj₂ (refl , inj₁ (ℕ.s≤s (ℕₚ.m≤n+m (index₁ s₁) (index₁ s))))
    ; (suc n) → inj₁ (ℕₚ.m<n+m (index₀ s₁) ℕₚ.0<1+n)
    }

  s<declare‿s : ∀ (s : Statement _) (e : Expression Γ t) → inlineRel (_ , _ , s) (_ , _ , declare e s)
  s<declare‿s s _ = inj₂ (refl , inj₂ (refl , ℕₚ.n<1+n (index₂ s)))

  splitIf : ∀ (x : Expression Γ bool) (s s₁ : Statement Γ) → Statement Γ
  splitIf x s s₁ = declare x (if var 0F then wknStatementAt bool 0F s ∙ if var 0F then wknStatementAt bool 0F s₁)

  splitIf<if‿s∙s₁ : ∀ (x : Expression Γ bool) (s s₁ : Statement Γ) → inlineRel (_ , _ , splitIf x s s₁) (_ , _ , (if x then (s ∙ s₁)))
  splitIf<if‿s∙s₁ x s s₁ = inj₂ (s≡₀s′ , inj₁ s<₁s′)
    where
    open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
    s≡₀s′ = cong₂ ℕ._+_ (wkn-pres-index₀ bool 0F s) (wkn-pres-index₀ bool 0F s₁)
    s<₁s′ = begin-strict
      suc (suc (3 ℕ.* index₁ (wknStatementAt bool 0F s)) ℕ.+ suc (3 ℕ.* index₁ (wknStatementAt bool 0F s₁)))
        ≡⟨ cong₂ (λ m n → suc (suc (3 ℕ.* m) ℕ.+ suc (3 ℕ.* n))) (wkn-pres-index₁ bool 0F s) (wkn-pres-index₁ bool 0F s₁) ⟩
      suc (suc (3 ℕ.* index₁ s) ℕ.+ suc (3 ℕ.* index₁ s₁))
        <⟨ ℕₚ.m<n+m (suc (suc (3 ℕ.* index₁ s) ℕ.+ suc (3 ℕ.* index₁ s₁))) (ℕₚ.0<1+n {n = 0}) ⟩
      suc (suc (suc (3 ℕ.* index₁ s) ℕ.+ suc (3 ℕ.* index₁ s₁)))
        ≡⟨ solve 2 (λ m n → con 2 :+ (con 1 :+ (con 3 :* m) :+ (con 1 :+ (con 3 :* n))) := con 1 :+ (con 3 :* (con 1 :+ m :+ n))) refl (index₁ s) (index₁ s₁) ⟩
      suc (3 ℕ.* (suc (index₁ s ℕ.+ index₁ s₁)))
        ∎

  splitIf-stateless : ∀ {x : Expression Γ bool} {s s₁ : Statement Γ} → ¬ ChangesState (if x then (s ∙ s₁)) → ¬ ChangesState (splitIf x s s₁)
  splitIf-stateless stateless (declare _ ((if _ then s) ∙ˡ _))  = stateless (if _ then (wkn-pres-changes bool 0F s ∙ˡ _))
  splitIf-stateless stateless (declare _ (_ ∙ʳ (if _ then s₁))) = stateless (if _ then (_ ∙ʳ wkn-pres-changes bool 0F s₁))

  pushRef-stateless : ∀ {e} {ref : Expression Γ t} {canAssign val} → ¬ ChangesState (if e then _≔_ ref {canAssign} val) → ¬ ChangesState (_≔_ ref {canAssign} (if e then val else ref))
  pushRef-stateless stateless (_≔_ ref {refsState = refsState} _) = stateless (if _ then _≔_ ref {refsState = refsState} _)

  declare∘if<if∘declare : ∀ e (e′ : Expression Γ t) s → inlineRel (_ , _ , declare e′ (if wknAt 0F e then s)) (_ , _ , (if e then declare e′ s))
  declare∘if<if∘declare e e′ s = inj₂ (refl , inj₂ (refl , (begin-strict
    suc (2 ℕ.* index₂ s)
      <⟨ ℕₚ.n<1+n _ ⟩
    suc (suc (2 ℕ.* index₂ s))
      ≡⟨ solve 1 (λ m → con 2 :+ con 2 :* m := con 2 :* (con 1 :+ m)) refl (index₂ s) ⟩
    2 ℕ.* suc (index₂ s)
      ∎)))
    where
    open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

  declare∘if-stateless : ∀ {e} {e′ : Expression Γ t} {s} → ¬ ChangesState (if e then declare e′ s) → ¬ ChangesState (declare e′ (if wknAt 0F e then s))
  declare∘if-stateless stateless (declare _ (if _ then s)) = stateless (if _ then (declare _ s))

  if<if∘if : ∀ (e e′ : Expression Γ bool) s → inlineRel (_ , _ , (if e && e′ then s)) (_ , _ , (if e then if e′ then s))
  if<if∘if e e′ s = inj₂ (refl , inj₁ (begin-strict
    suc (3 ℕ.* index₁ s)
      <⟨ ℕₚ.m<n+m (suc (3 ℕ.* index₁ s)) (ℕₚ.0<1+n {n = 2}) ⟩
    4 ℕ.+ 3 ℕ.* index₁ s
      ≤⟨ ℕₚ.m≤n+m (4 ℕ.+ 3 ℕ.* index₁ s) (6 ℕ.* index₁ s) ⟩
    6 ℕ.* index₁ s ℕ.+ (4 ℕ.+ 3 ℕ.* index₁ s)
      ≡⟨ solve 1 (λ m → con 6 :* m :+ (con 4 :+ con 3 :* m) := con 1 :+ con 3 :* (con 1 :+ con 3 :* m)) refl (index₁ s) ⟩
    suc (3 ℕ.* suc (3 ℕ.* index₁ s))
      ∎))
    where
    open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

  if-stateless : ∀ {e e′ : Expression Γ bool} {s} → ¬ ChangesState (if e then if e′ then s) → ¬ ChangesState (if e && e′ then s)
  if-stateless stateless (if _ then s) = stateless (if _ then if _ then s)

  if∙if : ∀ (e e′ : Expression Γ bool) (s s₁ : Statement Γ) → Statement Γ
  if∙if e e′ s s₁ =
    declare e (
    declare (wknAt 0F e′) (
      if var 1F && var 0F then wknStatementAt bool 0F (wknStatementAt bool 0F s) ∙
      if var 1F && inv (var 0F) then wknStatementAt bool 0F (wknStatementAt bool 0F s₁)))

  if∙if<if‿if‿else : ∀ (e e′ : Expression Γ bool) s s₁ → inlineRel (_ , _ , if∙if e e′ s s₁) (_ , _ , (if e then (if e′ then s else s₁)))
  if∙if<if‿if‿else e e′ s s₁ = inj₁ (begin-strict
    index₀ (wknStatementAt bool 0F (wknStatementAt bool 0F s)) ℕ.+ index₀ (wknStatementAt bool 0F (wknStatementAt bool 0F s₁))
      ≡⟨ cong₂ ℕ._+_ (wkn-pres-index₀ bool 0F (wknStatementAt bool 0F s)) (wkn-pres-index₀ bool 0F (wknStatementAt bool 0F s₁)) ⟩
    index₀ (wknStatementAt bool 0F s) ℕ.+ index₀ (wknStatementAt bool 0F s₁)
      ≡⟨ cong₂ ℕ._+_ (wkn-pres-index₀ bool 0F s) (wkn-pres-index₀ bool 0F s₁) ⟩
    index₀ s ℕ.+ index₀ s₁
      <⟨ ℕₚ.n<1+n (index₀ s ℕ.+ index₀ s₁) ⟩
    suc (index₀ s ℕ.+ index₀ s₁)
      ∎)

  if∙if-stateless : ∀ {e e′ : Expression Γ bool} {s s₁} → ¬ ChangesState (if e then (if e′ then s else s₁)) → ¬ ChangesState (if∙if e e′ s s₁)
  if∙if-stateless stateless (declare _ (declare _ ((if _ then s) ∙ˡ _))) = stateless (if _ then (if _ then′ wkn-pres-changes bool 0F (wkn-pres-changes bool 0F s) else _))
  if∙if-stateless stateless (declare _ (declare _ (_ ∙ʳ (if _ then s₁)))) = stateless (if _ then (if _ then _ else′ wkn-pres-changes bool 0F (wkn-pres-changes bool 0F s₁)))

  declare-stateless : ∀ {i : Fin m} {s : Statement (fin m ∷ Γ)} → ¬ ChangesState (for m s) → ¬ ChangesState (declare (lit (i ′f)) s)
  declare-stateless stateless (declare _ s) = stateless (for _ s)

  for‿if : ∀ (e : Expression Γ bool) m (s : Statement (fin m ∷ Γ)) → Statement Γ
  for‿if e m s = declare e (for m (if var 1F then wknStatementAt bool 1F s))

  for‿if<if‿for : ∀ (e : Expression Γ bool) m s → inlineRel (_ , _ , for‿if e m s) (_ , _ , (if e then for m s))
  for‿if<if‿for e m s = inj₂ (s≡₀s′ , inj₁ s<₁s′)
    where
    open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
    s≡₀s′ = wkn-pres-index₀ bool 1F s
    s<₁s′ = begin-strict
      suc (suc (3 ℕ.* index₁ (wknStatementAt bool 1F s)))
        ≡⟨ cong (λ m → suc (suc (3 ℕ.* m))) (wkn-pres-index₁ bool 1F s) ⟩
      suc (suc (3 ℕ.* index₁ s))
        <⟨ ℕₚ.m<n+m (suc (suc (3 ℕ.* index₁ s))) (ℕₚ.0<1+n {n = 1}) ⟩
      4 ℕ.+ 3 ℕ.* index₁ s
        ≡⟨ solve 1 (λ m → con 4 :+ con 3 :* m := con 1 :+ con 3 :* (con 1 :+ m)) refl (index₁ s) ⟩
      suc (3 ℕ.* suc (index₁ s))
        ∎

  for‿if-stateless : ∀ {e : Expression Γ bool} {m s} → ¬ ChangesState (if e then for m s) → ¬ ChangesState (for‿if e m s)
  for‿if-stateless stateless (declare _ (for _ (if _ then s))) = stateless (if _ then (for _ (wkn-pres-changes bool 1F s)))

  if∙if′ : ∀ (e : Expression Γ bool) (s s₁ : Statement Γ) → Statement Γ
  if∙if′ e s s₁ = declare e (
    if var 0F then wknStatementAt bool 0F s ∙
    if inv (var 0F) then wknStatementAt bool 0F s₁)

  if∙if′<if‿else : ∀ (e : Expression Γ bool) s s₁ → inlineRel (_ , _ , if∙if′ e s s₁) (_ , _ , (if e then s else s₁))
  if∙if′<if‿else e s s₁ = inj₁ (begin-strict
    index₀ (wknStatementAt bool 0F s) ℕ.+ index₀ (wknStatementAt bool 0F s₁)
      ≡⟨ cong₂ ℕ._+_ (wkn-pres-index₀ bool 0F s) (wkn-pres-index₀ bool 0F s₁) ⟩
    index₀ s ℕ.+ index₀ s₁
      <⟨ ℕₚ.n<1+n (index₀ s ℕ.+ index₀ s₁) ⟩
    suc (index₀ s ℕ.+ index₀ s₁)
      ∎)

  if∙if′-stateless : ∀ {e : Expression Γ bool} {s s₁} → ¬ ChangesState (if e then s else s₁) → ¬ ChangesState (if∙if′ e s s₁)
  if∙if′-stateless stateless (declare _ ((if _ then s) ∙ˡ _)) = stateless (if _ then′ wkn-pres-changes bool 0F s else _)
  if∙if′-stateless stateless (declare _ (_ ∙ʳ (if _ then s₁))) = stateless (if _ then _ else′ wkn-pres-changes bool 0F s₁)

  inlineHelper : ∀ n,Γ,s → Wf.WfRec inlineRel inlinePredicate n,Γ,s → inlinePredicate n,Γ,s
  proj₁ (inlineHelper (_ , _ , (s ∙ s₁)) rec stateless e) =
    proj₁ (rec
      (_ , _ , s₁)
      (s₁<s∙s₁ s s₁)
      (stateless ∘ (s ∙ʳ_))
      (proj₁ (rec
        (_ , _ , s)
        (s<s∙s₁ s s₁)
        (stateless ∘ (_∙ˡ s₁))
        e)))
  proj₁ (inlineHelper (_ , _ , skip) rec stateless e) = e
  proj₁ (inlineHelper (_ , _ , (_≔_ ref {canAssign} val)) rec stateless e) =
    updateRef
      (toWitness canAssign)
      (stateless ∘ λ x → _≔_ ref {refsState = fromWitness x} val)
      val
      e
  proj₁ (inlineHelper (_ , _ , declare x s) rec stateless e) =
    elimAt 0F
      (proj₁ (rec
        (_ , _ , s)
        (s<declare‿s s x)
        (stateless ∘ declare x)
        (wknAt 0F e)))
      x
  proj₁ (inlineHelper (_ , _ , invoke p es) rec stateless e) = contradiction (invoke p es) stateless
  proj₁ (inlineHelper (_ , _ , (if x then (s ∙ s₁))) rec stateless e) =
    proj₁ (rec
      (_ , _ , splitIf x s s₁)
      (splitIf<if‿s∙s₁ x s s₁)
      (splitIf-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then skip)) rec stateless e) = e
  proj₁ (inlineHelper (_ , _ , (if x then (_≔_ ref {canAssign} val))) rec stateless e) =
    proj₁ (rec
      (_ , _ , (_≔_ ref {canAssign} (if x then val else ref)))
      (inj₂ (refl , inj₁ ℕₚ.0<1+n))
      (pushRef-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then declare x₁ s)) rec stateless e) =
    proj₁ (rec
      (_ , _ , declare x₁ (if wknAt 0F x then s))
      (declare∘if<if∘declare x x₁ s)
      (declare∘if-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then invoke p es)) rec stateless e) = contradiction (if x then invoke p es) stateless
  proj₁ (inlineHelper (_ , _ , (if x then if x₁ then s)) rec stateless e) =
    proj₁ (rec
      (_ , _ , (if (x && x₁) then s))
      (if<if∘if x x₁ s)
      (if-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then (if x₁ then s else s₁))) rec stateless e) =
    proj₁ (rec
      (_ , _ , if∙if x x₁ s s₁)
      (if∙if<if‿if‿else x x₁ s s₁)
      (if∙if-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then for m s)) rec stateless e) =
    proj₁ (rec
      (_ , _ , for‿if x m s)
      (for‿if<if‿for x m s)
      (for‿if-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , (if x then s else s₁)) rec stateless e) =
    proj₁ (rec
      (_ , _ , if∙if′ x s s₁)
      (if∙if′<if‿else x s s₁)
      (if∙if′-stateless stateless)
      e)
  proj₁ (inlineHelper (_ , _ , for m s) rec stateless e) =
    Vec.foldl
      (λ _ → Expression _ _)
      (λ e i →
        proj₁ (rec
          (_ , _ , declare (lit (i ′f)) s)
          (inj₂ (refl , inj₁ (ℕₚ.n<1+n (index₁ s))))
          (declare-stateless stateless)
          e))
      e
      (Vec.allFin _)
  proj₂ (inlineHelper (_ , _ , (s ∙ s₁)) rec stateless e) = begin
    callDepth (proj₁ outer)
      ≤⟨ proj₂ outer ⟩
    stmtCallDepth s₁ ⊔ callDepth (proj₁ inner)
      ≤⟨ ℕₚ.⊔-monoʳ-≤ (stmtCallDepth s₁) (proj₂ inner) ⟩
    stmtCallDepth s₁ ⊔ (stmtCallDepth s ⊔ callDepth e)
      ≡⟨ ⊔-solve 3 (λ a b c → b ⊕ (a ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (stmtCallDepth s) (stmtCallDepth s₁) (callDepth e) ⟩
    stmtCallDepth s ⊔ stmtCallDepth s₁ ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , s) (s<s∙s₁ s s₁) (stateless ∘ (_∙ˡ s₁)) e
    outer = rec (_ , _ , s₁) (s₁<s∙s₁ s s₁) (stateless ∘ (s ∙ʳ_)) (proj₁ inner)
  -- with rec (_ , _ , s) (s<s∙s₁ s s₁) (stateless ∘ (_∙ˡ s₁)) e
  -- ... | inner , eq with inner | eq | rec (_ , _ , s₁) (s₁<s∙s₁ s s₁) (stateless ∘ (s ∙ʳ_)) inner
  -- ... | inner | inj₁ inner≤s | outer , inj₁ outer≤s₁ = inj₁ (ℕₚ.m≤n⇒m≤o⊔n (stmtCallDepth s) outer≤s₁)
  -- ... | inner | inj₁ inner≤s | outer , inj₂ outer≡inner = inj₁ (begin
  --   callDepth outer ≡⟨ outer≡inner ⟩
  --   callDepth inner ≤⟨ ℕₚ.m≤n⇒m≤n⊔o (stmtCallDepth s₁) inner≤s ⟩
  --   stmtCallDepth s ⊔ stmtCallDepth s₁ ∎)
  -- ... | inner | inj₂ inner≡e | outer , inj₁ outer≤s₁ = inj₁ (ℕₚ.m≤n⇒m≤o⊔n (stmtCallDepth s) outer≤s₁)
  -- ... | inner | inj₂ inner≡e | outer , inj₂ outer≡inner = inj₂ (trans outer≡inner inner≡e)
  proj₂ (inlineHelper (_ , _ , skip) rec stateless e) = ℕₚ.≤-refl
  proj₂ (inlineHelper (_ , _ , (_≔_ ref {canAssign} x)) rec stateless e) = updateRef-pres-callDepth (toWitness canAssign) (λ x → stateless (_≔_ _ {refsState = fromWitness x} _)) x e
  proj₂ (inlineHelper (_ , _ , declare x s) rec stateless e) = begin
    callDepth (elimAt 0F (proj₁ inner) x)
      ≤⟨ elimAt-pres-callDepth 0F (proj₁ inner) x ⟩
    callDepth x ⊔ callDepth (proj₁ inner)
      ≤⟨ ℕₚ.⊔-monoʳ-≤ (callDepth x) (proj₂ inner) ⟩
    callDepth x ⊔ (stmtCallDepth s ⊔ callDepth (wknAt 0F e))
      ≡⟨ cong (λ m → callDepth x ⊔ (stmtCallDepth s ⊔ m)) (wknAt-pres-callDepth 0F e) ⟩
    callDepth x ⊔ (stmtCallDepth s ⊔ callDepth e)
      ≡⟨ ⊔-solve 3 (λ a b c → a ⊕ (b ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (callDepth x) (stmtCallDepth s) (callDepth e) ⟩
    callDepth x ⊔ stmtCallDepth s ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , s) (s<declare‿s s x) (λ x → stateless (declare _ x)) (wknAt 0F e)
  proj₂ (inlineHelper (_ , _ , invoke p es) rec stateless e) = contradiction (invoke p es) stateless
  proj₂ (inlineHelper (_ , _ , (if x then (s ∙ s₁))) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x ⊔ (stmtCallDepth (wknStatementAt bool 0F s) ⊔ stmtCallDepth (wknStatementAt bool 0F s₁)) ⊔ callDepth e
      ≡⟨ cong₂ (λ m n → callDepth x ⊔ (m ⊔ n) ⊔ callDepth e) (wkn-pres-callDepth bool 0F s) (wkn-pres-callDepth bool 0F s₁) ⟩
    callDepth x ⊔ (stmtCallDepth s ⊔ stmtCallDepth s₁) ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , splitIf x s s₁) (splitIf<if‿s∙s₁ x s s₁) (splitIf-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then skip)) rec stateless e) = ℕₚ.m≤n⊔m (callDepth x ⊔ 0) (callDepth e)
  proj₂ (inlineHelper (_ , _ , (if x then (_≔_ ref {canAssign} val))) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth ref ⊔ (callDepth x ⊔ callDepth val ⊔ callDepth ref) ⊔ callDepth e
      ≡⟨ ⊔-solve 4 (λ a b c d → (b ⊕ ((a ⊕ c) ⊕ b)) ⊕ d ⊜ (a ⊕ (b ⊕ c)) ⊕ d) refl (callDepth x) (callDepth ref) (callDepth val) (callDepth e) ⟩
    callDepth x ⊔ (callDepth ref ⊔ callDepth val) ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , (_≔_ ref {canAssign} (if x then val else ref))) (inj₂ (refl , inj₁ ℕₚ.0<1+n)) (pushRef-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then declare x₁ s)) rec stateless e) = begin
    callDepth(proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x₁ ⊔ (callDepth (wknAt 0F x) ⊔ stmtCallDepth s) ⊔ callDepth e
      ≡⟨ cong (λ m → callDepth x₁ ⊔ (m ⊔ stmtCallDepth s) ⊔ callDepth e) (wknAt-pres-callDepth 0F x) ⟩
    callDepth x₁ ⊔ (callDepth x ⊔ stmtCallDepth s) ⊔ callDepth e
      ≡⟨ ⊔-solve 4 (λ a b c d → (b ⊕ (a ⊕ c)) ⊕ d ⊜ (a ⊕ (b ⊕ c)) ⊕ d) refl (callDepth x) (callDepth x₁) (stmtCallDepth s) (callDepth e) ⟩
    callDepth x ⊔ (callDepth x₁ ⊔ stmtCallDepth s) ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , declare x₁ (if wknAt 0F x then s)) (declare∘if<if∘declare x x₁ s) (declare∘if-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then invoke p es)) rec stateless e) = contradiction (if _ then invoke p es) stateless
  proj₂ (inlineHelper (_ , _ , (if x then (if x₁ then s))) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x ⊔ callDepth x₁ ⊔ stmtCallDepth s ⊔ callDepth e
      ≡⟨ ⊔-solve 4 (λ a b c d → ((a ⊕ b) ⊕ c) ⊕ d ⊜ (a ⊕ (b ⊕ c)) ⊕ d) refl (callDepth x) (callDepth x₁) (stmtCallDepth s) (callDepth e) ⟩
    callDepth x ⊔ (callDepth x₁ ⊔ stmtCallDepth s) ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , (if x && x₁ then s)) (if<if∘if x x₁ s) (if-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then (if x₁ then s else s₁))) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x ⊔ (callDepth (wknAt 0F x₁) ⊔ (stmtCallDepth (wknStatementAt bool 0F (wknStatementAt bool 0F s)) ⊔ stmtCallDepth (wknStatementAt bool 0F (wknStatementAt bool 0F s₁)))) ⊔ callDepth e
      ≡⟨ congₙ 3 (λ m n o → callDepth x ⊔ (m ⊔ (n ⊔ o)) ⊔ callDepth e) (wknAt-pres-callDepth 0F x₁) (trans (wkn-pres-callDepth bool 0F (wknStatementAt bool 0F s)) (wkn-pres-callDepth bool 0F s)) (trans (wkn-pres-callDepth bool 0F (wknStatementAt bool 0F s₁)) (wkn-pres-callDepth bool 0F s₁)) ⟩
    callDepth x ⊔ (callDepth x₁ ⊔ (stmtCallDepth s ⊔ stmtCallDepth s₁)) ⊔ callDepth e
      ≡⟨ ⊔-solve 5 (λ a b c d e → (a ⊕ (b ⊕ (c ⊕ d))) ⊕ e ⊜ (a ⊕ ((b ⊕ c) ⊕ d)) ⊕ e) refl (callDepth x) (callDepth x₁) (stmtCallDepth s) (stmtCallDepth s₁) (callDepth e) ⟩
    callDepth x ⊔ (callDepth x₁ ⊔ stmtCallDepth s ⊔ stmtCallDepth s₁) ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , if∙if x x₁ s s₁) (if∙if<if‿if‿else x x₁ s s₁) (if∙if-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then for m s)) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x ⊔ stmtCallDepth (wknStatementAt bool 1F s) ⊔ callDepth e
      ≡⟨ cong (λ m → callDepth x ⊔ m ⊔ callDepth e) (wkn-pres-callDepth bool 1F s) ⟩
    callDepth x ⊔ stmtCallDepth s ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , for‿if x m s) (for‿if<if‿for x m s) (for‿if-stateless stateless) e
  proj₂ (inlineHelper (_ , _ , (if x then s else s₁)) rec stateless e) = begin
    callDepth (proj₁ inner)
      ≤⟨ proj₂ inner ⟩
    callDepth x ⊔ (stmtCallDepth (wknStatementAt bool 0F s) ⊔ stmtCallDepth (wknStatementAt bool 0F s₁)) ⊔ callDepth e
      ≡⟨ cong₂ (λ m n → callDepth x ⊔ (m ⊔ n) ⊔ callDepth e) (wkn-pres-callDepth bool 0F s) (wkn-pres-callDepth bool 0F s₁) ⟩
    callDepth x ⊔ (stmtCallDepth s ⊔ stmtCallDepth s₁) ⊔ callDepth e
      ≡⟨ ⊔-solve 4 (λ a b c d → (a ⊕ (b ⊕ c)) ⊕ d ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (callDepth x) (stmtCallDepth s) (stmtCallDepth s₁) (callDepth e) ⟩
    callDepth x ⊔ stmtCallDepth s ⊔ stmtCallDepth s₁ ⊔ callDepth e
      ∎
    where
    inner = rec (_ , _ , if∙if′ x s s₁) (if∙if′<if‿else x s s₁) (if∙if′-stateless stateless) e
  proj₂ (inlineHelper (n , Γ , for m s) rec stateless {ret} e) = helper
    (stmtCallDepth s)
    (λ e i →
      rec
      (_ , _ , declare (lit (i ′f)) s)
      (inj₂ (refl , inj₁ (ℕₚ.n<1+n (index₁ s))))
      (declare-stateless stateless)
      e)
    e
    (Vec.allFin m)
    where
    helper : ∀ {n m} k (f : ∀ {n : ℕ} e (i : Fin m) → ∃ λ e′ → callDepth e′ ℕ.≤ k ⊔ callDepth e) → ∀ e xs → callDepth (Vec.foldl (λ _ → Expression Γ ret) {n} (λ {n} e i → proj₁ (f {n} e i)) e xs) ℕ.≤ k ⊔ callDepth e
    helper k f e []       = ℕₚ.m≤n⊔m k (callDepth e)
    helper k f e (x ∷ xs) = begin
      callDepth (Vec.foldl _ (λ e i → proj₁ (f e i)) (proj₁ (f e x)) xs)
        ≤⟨ helper k f (proj₁ (f e x)) xs ⟩
      k ⊔ callDepth (proj₁ (f e x))
        ≤⟨ ℕₚ.⊔-monoʳ-≤ k (proj₂ (f e x)) ⟩
      k ⊔ (k ⊔ callDepth e)
        ≡⟨ ⊔-solve 2 (λ a b → a ⊕ (a ⊕ b) ⊜ a ⊕ b) refl k (callDepth e) ⟩
      k ⊔ callDepth e
        ∎

inlineFunction : Function Γ ret → All (Expression Δ) Γ → Expression Δ ret
inlineFunction (declare e f) args = inlineFunction f (subst e args ∷ args)
inlineFunction (_∙return_ s {stateless} e) args =
  subst
    (proj₁ (Wf.All.wfRec
      inlineRelWf
      _
      inlinePredicate
      inlineHelper
      (_ , _ , s)
      (toWitnessFalse stateless)
      e))
    args

inlineFunction-lowers-callDepth : ∀ (f : Function Δ ret) (args : All (Expression Γ) Δ) → callDepth (inlineFunction f args) ℕ.≤ funCallDepth f ⊔ callDepth′ args
inlineFunction-lowers-callDepth (declare e f) args = begin
  callDepth (inlineFunction f (subst e args ∷ args))
    ≤⟨ inlineFunction-lowers-callDepth f (subst e args ∷ args) ⟩
  funCallDepth f ⊔ (callDepth (subst e args) ⊔ callDepth′ args)
    ≤⟨ ℕₚ.⊔-monoʳ-≤ (funCallDepth f) (ℕₚ.⊔-monoˡ-≤ (callDepth′ args) (subst-pres-callDepth e args)) ⟩
  funCallDepth f ⊔ (callDepth e ⊔ callDepth′ args ⊔ callDepth′ args)
    ≡⟨ ⊔-solve 3 (λ a b c → a ⊕ ((b ⊕ c) ⊕ c) ⊜ (a ⊕ b) ⊕ c) refl (funCallDepth f) (callDepth e) (callDepth′ args) ⟩
  funCallDepth f ⊔ callDepth e ⊔ callDepth′ args
    ∎
inlineFunction-lowers-callDepth (_∙return_ s {stateless} e) args = begin
  callDepth (subst (proj₁ theCall) args)          ≤⟨ subst-pres-callDepth (proj₁ theCall) args ⟩
  callDepth (proj₁ theCall) ⊔ callDepth′ args     ≤⟨ ℕₚ.⊔-monoˡ-≤ (callDepth′ args) (proj₂ theCall) ⟩
  stmtCallDepth s ⊔ callDepth e ⊔ callDepth′ args ∎
  where
  theCall = Wf.All.wfRec
    inlineRelWf
    _
    inlinePredicate
    inlineHelper
    (_ , _ , s)
    (toWitnessFalse stateless)
    e
