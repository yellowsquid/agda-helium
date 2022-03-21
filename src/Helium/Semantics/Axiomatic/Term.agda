------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of terms for use in assertions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Axiomatic.Term
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Fin as Fin using (Fin; suc)
import Data.Fin.Properties as Finₚ
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; uncurry; dmap)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup)
import Data.Vec.Functional as VecF
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function using (_∘_; _∘₂_; id; flip)
open import Helium.Data.Pseudocode.Core
import Helium.Data.Pseudocode.Manipulate as M
open import Helium.Semantics.Axiomatic.Core rawPseudocode
open import Level using (_⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality hiding ([_]) renaming (subst to ≡-subst)
open import Relation.Nullary using (does; yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Relation.Nullary.Negation using (contradiction)

private
  variable
    t t′ t₁ t₂ : Type
    m n o      : ℕ
    Γ Δ Σ ts   : Vec Type m

data Term (Σ : Vec Type o) (Γ : Vec Type n) (Δ : Vec Type m) : Type → Set (b₁ ⊔ i₁ ⊔ r₁) where
  state : ∀ i → Term Σ Γ Δ (lookup Σ i)
  var   : ∀ i → Term Σ Γ Δ (lookup Γ i)
  meta  : ∀ i → Term Σ Γ Δ (lookup Δ i)
  func  : Transform ts t → All (Term Σ Γ Δ) ts → Term Σ Γ Δ t

castType : Term Σ Γ Δ t → t ≡ t′ → Term Σ Γ Δ t′
castType (state i)   refl = state i
castType (var i)     refl = var i
castType (meta i)    refl = meta i
castType (func f ts) eq   = func (≡-subst (Transform _) eq f) ts

substState : Term Σ Γ Δ t → ∀ i → Term Σ Γ Δ (lookup Σ i) → Term Σ Γ Δ t
substState (state i) j t′ with i Fin.≟ j
... | yes refl = t′
... | no _     = state i
substState (var i) j t′ = var i
substState (meta i) j t′ = meta i
substState (func f ts) j t′ = func f (helper ts j t′)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → ∀ i → Term Σ Γ Δ (lookup Σ i) → All (Term Σ Γ Δ) ts
  helper []       i t′ = []
  helper (t ∷ ts) i t′ = substState t i t′ ∷ helper ts i t′

substVar : Term Σ Γ Δ t → ∀ i → Term Σ Γ Δ (lookup Γ i) → Term Σ Γ Δ t
substVar (state i) j t′ = state i
substVar (var i) j t′ with i Fin.≟ j
... | yes refl = t′
... | no _     = var i
substVar (meta i) j t′ = meta i
substVar (func f ts) j t′ = func f (helper ts j t′)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → ∀ i → Term Σ Γ Δ (lookup Γ i) → All (Term Σ Γ Δ) ts
  helper []       i t′ = []
  helper (t ∷ ts) i t′ = substVar t i t′ ∷ helper ts i t′

substVars : Term Σ Γ Δ t → All (Term Σ ts Δ) Γ → Term Σ ts Δ t
substVars (state i)    ts = state i
substVars (var i)      ts = All.lookup i ts
substVars (meta i)     ts = meta i
substVars (func f ts′) ts = func f (helper ts′ ts)
  where
  helper : ∀ {ts ts′} → All (Term Σ Γ Δ) {n} ts → All (Term {n = m} Σ ts′ Δ) Γ → All (Term Σ ts′ Δ) ts
  helper []        ts = []
  helper (t ∷ ts′) ts = substVars t ts ∷ helper ts′ ts

elimVar : Term Σ (t′ ∷ Γ) Δ t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
elimVar (state i)     t′ = state i
elimVar (var 0F)      t′ = t′
elimVar (var (suc i)) t′ = var i
elimVar (meta i)      t′ = meta i
elimVar (func f ts)   t′ = func f (helper ts t′)
  where
  helper : ∀ {n ts} → All (Term Σ (_ ∷ Γ) Δ) {n} ts → Term Σ Γ Δ _ → All (Term Σ Γ Δ) ts
  helper []       t′ = []
  helper (t ∷ ts) t′ = elimVar t t′ ∷ helper ts t′

wknVar : Term Σ Γ Δ t → Term Σ (t′ ∷ Γ) Δ t
wknVar (state i)   = state i
wknVar (var i)     = var (suc i)
wknVar (meta i)    = meta i
wknVar (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ (_ ∷ Γ) Δ) ts
  helper []       = []
  helper (t ∷ ts) = wknVar t ∷ helper ts

wknVars : (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ (ts ++ Γ) Δ t
wknVars τs (state i)   = state i
wknVars τs (var i)     = castType (var (Fin.raise (Vec.length τs) i)) (Vecₚ.lookup-++ʳ τs _ i)
wknVars τs (meta i)    = meta i
wknVars τs (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ (τs ++ Γ) Δ) ts
  helper []       = []
  helper (t ∷ ts) = wknVars τs t ∷ helper ts

addVars : Term Σ [] Δ t → Term Σ Γ Δ t
addVars (state i)   = state i
addVars (meta i)    = meta i
addVars (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ [] Δ) {n} ts → All (Term Σ Γ Δ) ts
  helper []       = []
  helper (t ∷ ts) = addVars t ∷ helper ts

wknMetaAt : ∀ i → Term Σ Γ Δ t → Term Σ Γ (Vec.insert Δ i t′) t
wknMetaAt′ : ∀ i → All (Term Σ Γ Δ) ts → All (Term Σ Γ (Vec.insert Δ i t′)) ts

wknMetaAt i (state j)   = state j
wknMetaAt i (var j)     = var j
wknMetaAt i (meta j)    = castType (meta (Fin.punchIn i j)) (Vecₚ.insert-punchIn _ i _ j)
wknMetaAt i (func f ts) = func f (wknMetaAt′ i ts)

wknMetaAt′ i []       = []
wknMetaAt′ i (t ∷ ts) = wknMetaAt i t ∷ wknMetaAt′ i ts

wknMeta : Term Σ Γ Δ t → Term Σ Γ (t′ ∷ Δ) t
wknMeta = wknMetaAt 0F

wknMeta′ : All (Term Σ Γ Δ) ts → All (Term Σ Γ (t′ ∷ Δ)) ts
wknMeta′ = wknMetaAt′ 0F

wknMetas : (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ Γ (ts ++ Δ) t
wknMetas τs (state i)   = state i
wknMetas τs (var i)     = var i
wknMetas τs (meta i)    = castType (meta (Fin.raise (Vec.length τs) i)) (Vecₚ.lookup-++ʳ τs _ i)
wknMetas τs (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ Γ (τs ++ Δ)) ts
  helper []       = []
  helper (t ∷ ts) = wknMetas τs t ∷ helper ts

func₀ : ⟦ t ⟧ₜ → Term Σ Γ Δ t
func₀ f = func (λ _ → f) []

func₁ : (⟦ t ⟧ₜ → ⟦ t′ ⟧ₜ) → Term Σ Γ Δ t → Term Σ Γ Δ t′
func₁ f t = func (λ (x , _) → f x) (t ∷ [])

func₂ : (⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ t′ ⟧ₜ) → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ t′
func₂ f t₁ t₂ = func (λ (x , y , _) → f x y) (t₁ ∷ t₂ ∷ [])

[_][_≟_] : HasEquality t → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
[ bool ][ t ≟ t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x Bool.≟ y))) t t′
[ int ][ t ≟ t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x ≟ᶻ y))) t t′
[ fin ][ t ≟ t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x Fin.≟ y))) t t′
[ real ][ t ≟ t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x ≟ʳ y))) t t′
[ bit ][ t ≟ t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x ≟ᵇ₁ y))) t t′
[ bits ][ t ≟ t′ ] = func₂ (λ xs ys → lift (does (VecF.fromVec (Vec.map lower xs) ≟ᵇ VecF.fromVec (Vec.map lower ys)))) t t′

[_][_<?_] : IsNumeric t → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
[ int ][ t <? t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x <ᶻ? y))) t t′
[ real ][ t <? t′ ] = func₂ (λ (lift x) (lift y) → lift (does (x <ʳ? y))) t t′

[_][_] : ∀ t → Term Σ Γ Δ (elemType t) → Term Σ Γ Δ (asType t 1)
[ bits ][ t ] = func₁ (_∷ []) t
[ array τ ][ t ] = func₁ (_∷ []) t

unbox : ∀ t → Term Σ Γ Δ (asType t 1) → Term Σ Γ Δ (elemType t)
unbox bits = func₁ Vec.head
unbox (array t) = func₁ Vec.head

castV : ∀ {a} {A : Set a} {m n} → .(eq : m ≡ n) → Vec A m → Vec A n
castV {n = 0}     eq []       = []
castV {n = suc n} eq (x ∷ xs) = x ∷ castV (ℕₚ.suc-injective eq) xs

cast′ : ∀ t → .(eq : m ≡ n) → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ
cast′ bits      eq = castV eq
cast′ (array τ) eq = castV eq

cast : ∀ t → .(eq : m ≡ n) → Term Σ Γ Δ (asType t m) → Term Σ Γ Δ (asType t n)
cast τ eq = func₁ (cast′ τ eq)

[_][-_] : IsNumeric t → Term Σ Γ Δ t → Term Σ Γ Δ t
[ int ][- t ] = func₁ (lift ∘ ℤ.-_ ∘ lower) t
[ real ][- t ] = func₁ (lift ∘ ℝ.-_ ∘ lower) t

[_,_,_,_][_+_] : ∀ t₁ t₂ → (isNum₁ : True (isNumeric? t₁)) → (isNum₂ : True (isNumeric? t₂)) → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (combineNumeric t₁ t₂ isNum₁ isNum₂)
[ int , int , _ , _ ][ t + t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℤ.+ y)) t t′
[ int , real , _ , _ ][ t + t′ ] = func₂ (λ (lift x) (lift y) → lift (x /1 ℝ.+ y)) t t′
[ real , int , _ , _ ][ t + t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℝ.+ y /1)) t t′
[ real , real , _ , _ ][ t + t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℝ.+ y)) t t′

[_,_,_,_][_*_] : ∀ t₁ t₂ → (isNum₁ : True (isNumeric? t₁)) → (isNum₂ : True (isNumeric? t₂)) → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (combineNumeric t₁ t₂ isNum₁ isNum₂)
[ int , int , _ , _ ][ t * t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℤ.* y)) t t′
[ int , real , _ , _ ][ t * t′ ] = func₂ (λ (lift x) (lift y) → lift (x /1 ℝ.* y)) t t′
[ real , int , _ , _ ][ t * t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℝ.* y /1)) t t′
[ real , real , _ , _ ][ t * t′ ] = func₂ (λ (lift x) (lift y) → lift (x ℝ.* y)) t t′

[_][_^_] : IsNumeric t → Term Σ Γ Δ t → ℕ → Term Σ Γ Δ t
[ int ][ t ^ n ] = func₁ (lift ∘ (ℤ′._^′ n) ∘ lower) t
[ real ][ t ^ n ] = func₁ (lift ∘ (ℝ′._^′ n) ∘ lower) t

2≉0 : Set _
2≉0 = 2 ℝ′.×′ 1ℝ ℝ.≉ 0ℝ

[_][_>>_] : 2≉0 → Term Σ Γ Δ int → ℕ → Term Σ Γ Δ int
[ 2≉0 ][ t >> n ] = func₁ (lift ∘ ⌊_⌋ ∘ (ℝ._* 2≉0 ℝ.⁻¹ ℝ′.^′ n) ∘ _/1 ∘ lower) t

-- 0 of y is 0 of result
join′ : ∀ t → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ → ⟦ asType t (n ℕ.+ m) ⟧ₜ
join′ bits      = flip _++_
join′ (array t) = flip _++_

take′ : ∀ t m {n} → ⟦ asType t (m ℕ.+ n) ⟧ₜ → ⟦ asType t m ⟧ₜ
take′ bits      m = Vec.take m
take′ (array t) m = Vec.take m

drop′ : ∀ t m {n} → ⟦ asType t (m ℕ.+ n) ⟧ₜ → ⟦ asType t n ⟧ₜ
drop′ bits      m = Vec.drop m
drop′ (array t) m = Vec.drop m

private
  m≤n⇒m+k≡n : ∀ {m n} → m ℕ.≤ n → ∃ λ k → m ℕ.+ k ≡ n
  m≤n⇒m+k≡n ℕ.z≤n       = _ , refl
  m≤n⇒m+k≡n (ℕ.s≤s m≤n) = dmap id (cong suc) (m≤n⇒m+k≡n m≤n)

  slicedSize : ∀ n m (i : Fin (suc n)) → ∃ λ k → n ℕ.+ m ≡ Fin.toℕ i ℕ.+ (m ℕ.+ k) × Fin.toℕ i ℕ.+ k ≡ n
  slicedSize n m i = k , (begin
    n ℕ.+ m                 ≡˘⟨ cong (ℕ._+ m) (proj₂ i+k≡n) ⟩
    (Fin.toℕ i ℕ.+ k) ℕ.+ m ≡⟨  ℕₚ.+-assoc (Fin.toℕ i) k m ⟩
    Fin.toℕ i ℕ.+ (k ℕ.+ m) ≡⟨  cong (Fin.toℕ i ℕ.+_) (ℕₚ.+-comm k m) ⟩
    Fin.toℕ i ℕ.+ (m ℕ.+ k) ∎) ,
    proj₂ i+k≡n
    where
    open ≡-Reasoning
    i+k≡n = m≤n⇒m+k≡n (ℕₚ.≤-pred (Finₚ.toℕ<n i))
    k = proj₁ i+k≡n

-- 0 of x is i of result
splice′ : ∀ t → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ → ⟦ fin (suc n) ⟧ₜ → ⟦ asType t (n ℕ.+ m) ⟧ₜ
splice′ {m = m} t x y (lift i) = cast′ t eq (join′ t (join′ t high x) low)
  where
  reasoning = slicedSize _ m i
  k = proj₁ reasoning
  n≡i+k = sym (proj₂ (proj₂ reasoning))
  low = take′ t (Fin.toℕ i) (cast′ t n≡i+k y)
  high = drop′ t (Fin.toℕ i) (cast′ t n≡i+k y)
  eq = sym (proj₁ (proj₂ reasoning))

splice : ∀ t → Term Σ Γ Δ (asType t m) → Term Σ Γ Δ (asType t n) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (asType t (n ℕ.+ m))
splice τ t₁ t₂ t′ = func (λ (x , y , i , _) → splice′ τ x y i) (t₁ ∷ t₂ ∷ t′ ∷ [])

-- i of x is 0 of first
cut′ : ∀ t → ⟦ asType t (n ℕ.+ m) ⟧ₜ → ⟦ fin (suc n) ⟧ₜ → ⟦ asType t m ∷ asType t n ∷ [] ⟧ₜ′
cut′ {m = m} t x (lift i) = middle , cast′ t i+k≡n (join′ t high low) , _
  where
  reasoning = slicedSize _ m i
  k = proj₁ reasoning
  i+k≡n = proj₂ (proj₂ reasoning)
  eq = proj₁ (proj₂ reasoning)
  low = take′ t (Fin.toℕ i) (cast′ t eq x)
  middle = take′ t m (drop′ t (Fin.toℕ i) (cast′ t eq x))
  high = drop′ t m (drop′ t (Fin.toℕ i) (cast′ t eq x))

cut : ∀ t → Term Σ Γ Δ (asType t (n ℕ.+ m)) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (tuple _ (asType t m ∷ asType t n ∷ []))
cut τ t t′ = func₂ (cut′ τ) t t′

flatten : ∀ {ms : Vec ℕ n} → ⟦ Vec.map fin ms ⟧ₜ′ → All Fin ms
flatten {ms = []}     _             = []
flatten {ms = _ ∷ ms} (lift x , xs) = x ∷ flatten xs

𝒦 : Literal t → Term Σ Γ Δ t
𝒦 (x ′b) = func₀ (lift x)
𝒦 (x ′i) = func₀ (lift (x ℤ′.×′ 1ℤ))
𝒦 (x ′f) = func₀ (lift x)
𝒦 (x ′r) = func₀ (lift (x ℝ′.×′ 1ℝ))
𝒦 (x ′x) = func₀ (lift (Bool.if x then 1𝔹 else 0𝔹))
𝒦 ([] ′xs) = func₀ []
𝒦 ((x ∷ xs) ′xs) = func₂ (flip Vec._∷ʳ_) (𝒦 (x ′x)) (𝒦 (xs ′xs))
𝒦 (x ′a) = func₁ Vec.replicate (𝒦 x)

module _ (2≉0 : 2≉0) where
  ℰ : Code.Expression Σ Γ t → Term Σ Γ Δ t
  ℰ e = (uncurry helper) (M.elimFunctions e)
    where
    1+m⊔n≡1+k : ∀ m n → ∃ λ k → suc m ℕ.⊔ n ≡ suc k
    1+m⊔n≡1+k m 0       = m , refl
    1+m⊔n≡1+k m (suc n) = m ℕ.⊔ n , refl

    pull-0₂ : ∀ {x y} → x ℕ.⊔ y ≡ 0 → x ≡ 0
    pull-0₂ {0} {0}     refl = refl
    pull-0₂ {0} {suc y} ()

    pull-0₃ : ∀ {x y z} → x ℕ.⊔ y ℕ.⊔ z ≡ 0 → x ≡ 0
    pull-0₃ {0}     {0}     {0} refl = refl
    pull-0₃ {0}     {suc y} {0}     ()
    pull-0₃ {suc x} {0}     {0}     ()
    pull-0₃ {suc x} {0}     {suc z} ()

    pull-1₃ : ∀ x {y z} → x ℕ.⊔ y ℕ.⊔ z ≡ 0 → y ≡ 0
    pull-1₃ 0       {0}     {0}     refl = refl
    pull-1₃ 0       {suc y} {0}     ()
    pull-1₃ (suc x) {0}     {0}     ()
    pull-1₃ (suc x) {0}     {suc z} ()

    pull-last : ∀ {x y} → x ℕ.⊔ y ≡ 0 → y ≡ 0
    pull-last {0}     {0} refl = refl
    pull-last {suc x} {0} ()

    helper : ∀ (e : Code.Expression Σ Γ t) → M.callDepth e ≡ 0 → Term Σ Γ Δ t
    helper (Code.lit x) eq = 𝒦 x
    helper (Code.state i) eq = state i
    helper (Code.var i) eq = var i
    helper (Code.abort e) eq = func₁ (λ ()) (helper e eq)
    helper (Code._≟_ {hasEquality = hasEq} e e₁) eq = [ toWitness hasEq ][ helper e (pull-0₂ eq) ≟ helper e₁ (pull-last eq) ]
    helper (Code._<?_ {isNumeric = isNum} e e₁) eq = [ toWitness isNum ][ helper e (pull-0₂ eq) <? helper e₁ (pull-last eq) ]
    helper (Code.inv e) eq = func₁ (lift ∘ Bool.not ∘ lower) (helper e eq)
    helper (e Code.&& e₁) eq = func₂ (λ (lift x) (lift y) → lift (x Bool.∧ y)) (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (e Code.|| e₁) eq = func₂ (λ (lift x) (lift y) → lift (x Bool.∨ y)) (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (Code.not e) eq = func₁ (Vec.map (lift ∘ 𝔹.¬_ ∘ lower)) (helper e eq)
    helper (e Code.and e₁) eq = func₂ (λ xs ys → Vec.zipWith (λ (lift x) (lift y) → lift (x 𝔹.∧ y)) xs ys) (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (e Code.or e₁) eq = func₂ (λ xs ys → Vec.zipWith (λ (lift x) (lift y) → lift (x 𝔹.∨ y)) xs ys) (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (Code.[_] {t = t} e) eq = [ t ][ helper e eq ]
    helper (Code.unbox {t = t} e) eq = unbox t (helper e eq)
    helper (Code.splice {t = t} e e₁ e₂) eq = splice t (helper e (pull-0₃ eq)) (helper e₁ (pull-1₃ (M.callDepth e) eq)) (helper e₂ (pull-last eq))
    helper (Code.cut {t = t} e e₁) eq = cut t (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (Code.cast {t = t} i≡j e) eq = cast t i≡j (helper e eq)
    helper (Code.-_ {isNumeric = isNum} e) eq = [ toWitness isNum ][- helper e eq ]
    helper (Code._+_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁) eq = [ _ , _ , isNum₁ , isNum₂ ][ helper e (pull-0₂ eq) + helper e₁ (pull-last eq) ]
    helper (Code._*_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁) eq = [ _ , _ , isNum₁ , isNum₂ ][ helper e (pull-0₂ eq) * helper e₁ (pull-last eq) ]
    helper (Code._^_ {isNumeric = isNum} e y) eq = [ toWitness isNum ][ helper e eq ^ y ]
    helper (e Code.>> n) eq = [ 2≉0 ][ helper e eq >> n ]
    helper (Code.rnd e) eq = func₁ (lift ∘ ⌊_⌋ ∘ lower) (helper e eq)
    helper (Code.fin f e) eq = func₁ (lift ∘ f ∘ flatten) (helper e eq)
    helper (Code.asInt e) eq = func₁ (lift ∘ (ℤ′._×′ 1ℤ) ∘ Fin.toℕ ∘ lower) (helper e eq)
    helper Code.nil eq = func₀ _
    helper (Code.cons e e₁) eq = func₂ _,_ (helper e (pull-0₂ eq)) (helper e₁ (pull-last eq))
    helper (Code.head e) eq = func₁ proj₁ (helper e eq)
    helper (Code.tail e) eq = func₁ proj₂ (helper e eq)
    helper (Code.call f es) eq = contradiction (trans (sym eq) (proj₂ (1+m⊔n≡1+k (M.funCallDepth f) (M.callDepth′ es)))) ℕₚ.0≢1+n
    helper (Code.if e then e₁ else e₂) eq = func (λ (lift b , x , x₁ , _) → Bool.if b then x else x₁) (helper e (pull-0₃ eq) ∷ helper e₁ (pull-1₃ (M.callDepth e) eq) ∷ helper e₂ (pull-last eq) ∷ [])

  ℰ′ : All (Code.Expression Σ Γ) ts → All (Term Σ Γ Δ) ts
  ℰ′ []       = []
  ℰ′ (e ∷ es) = ℰ e ∷ ℰ′ es

  subst : Term Σ Γ Δ t → {e : Code.Expression Σ Γ t′} → Code.CanAssign Σ e → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  subst t (Code.state i) t′ = substState t i t′
  subst t (Code.var i) t′ = substVar t i t′
  subst t (Code.abort e) t′ = func₁ (λ ()) (ℰ e)
  subst t (Code.[_] {t = τ} ref) t′ = subst t ref (unbox τ t′)
  subst t (Code.unbox {t = τ} ref) t′ = subst t ref [ τ ][ t′ ]
  subst t (Code.splice {t = τ} ref ref₁ e₃) t′ = subst (subst t ref (func₁ proj₁ (cut τ t′ (ℰ e₃)))) ref₁ (func₁ (proj₁ ∘ proj₂) (cut τ t′ (ℰ e₃)))
  subst t (Code.cut {t = τ} ref e₂) t′ = subst t ref (splice τ (func₁ proj₁ t′) (func₁ (proj₁ ∘ proj₂) t′) (ℰ e₂))
  subst t (Code.cast {t = τ} eq ref) t′ = subst t ref (cast τ (sym eq) t′)
  subst t Code.nil t′ = t
  subst t (Code.cons ref ref₁) t′ = subst (subst t ref (func₁ proj₁ t′)) ref₁ (func₁ proj₂ t′)
  subst t (Code.head {e = e} ref) t′ = subst t ref (func₂ _,_ t′ (func₁ proj₂ (ℰ e)))
  subst t (Code.tail {t = τ} {e = e} ref) t′ = subst t ref (func₂ {t₁ = τ} _,_ (func₁ proj₁ (ℰ e)) t′)

⟦_⟧ : Term Σ Γ Δ t → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → ⟦ t ⟧ₜ
⟦_⟧′ : ∀ {ts} → All (Term Σ Γ Δ) {n} ts → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → ⟦ ts ⟧ₜ′

⟦ state i ⟧ σ γ δ = fetch i σ
⟦ var i ⟧ σ γ δ = fetch i γ
⟦ meta i ⟧ σ γ δ = fetch i δ
⟦ func f ts ⟧ σ γ δ = f (⟦ ts ⟧′ σ γ δ)

⟦ [] ⟧′     σ γ δ = _
⟦ t ∷ ts ⟧′ σ γ δ = ⟦ t ⟧ σ γ δ , ⟦ ts ⟧′ σ γ δ
