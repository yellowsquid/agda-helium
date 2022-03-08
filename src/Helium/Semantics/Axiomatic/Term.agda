------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of terms for use in assertions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

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
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Function using (_∘_; _∘₂_; id)
open import Helium.Data.Pseudocode.Core
import Helium.Data.Pseudocode.Manipulate as M
open import Helium.Semantics.Axiomatic.Core rawPseudocode
open import Level using (_⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no; ¬_)
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
castType (func f ts) eq   = func (subst (Transform _) eq f) ts

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
wknMetaAt i (state j)   = state j
wknMetaAt i (var j)     = var j
wknMetaAt i (meta j)    = castType (meta (Fin.punchIn i j)) (Vecₚ.insert-punchIn _ i _ j)
wknMetaAt i (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ Γ (Vec.insert Δ i _)) ts
  helper []       = []
  helper (t ∷ ts) = wknMetaAt i t ∷ helper ts

wknMeta : Term Σ Γ Δ t → Term Σ Γ (t′ ∷ Δ) t
wknMeta = wknMetaAt 0F

wknMetas : (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ Γ (ts ++ Δ) t
wknMetas τs (state i)   = state i
wknMetas τs (var i)     = var i
wknMetas τs (meta i)    = castType (meta (Fin.raise (Vec.length τs) i)) (Vecₚ.lookup-++ʳ τs _ i)
wknMetas τs (func f ts) = func f (helper ts)
  where
  helper : ∀ {n ts} → All (Term Σ Γ Δ) {n} ts → All (Term Σ Γ (τs ++ Δ)) ts
  helper []       = []
  helper (t ∷ ts) = wknMetas τs t ∷ helper ts

module _ {Σ : Vec Type o} (2≉0 : ¬ 2 ℝ′.×′ 1ℝ ℝ.≈ 0ℝ) where
  open Code Σ

  𝒦 : Literal t → Term Σ Γ Δ t
  𝒦 (x ′b) = func (λ _ → lift x) []
  𝒦 (x ′i) = func (λ _ → lift (x ℤ′.×′ 1ℤ)) []
  𝒦 (x ′f) = func (λ _ → lift x) []
  𝒦 (x ′r) = func (λ _ → lift (x ℝ′.×′ 1ℝ)) []
  𝒦 (x ′x) = func (λ _ → lift (Bool.if x then 1𝔹 else 0𝔹)) []
  𝒦 ([] ′xs) = func (λ _ → []) []
  𝒦 ((x ∷ xs) ′xs) = func (λ (x , xs , _) → xs Vec.∷ʳ x) (𝒦 (x ′x) ∷ 𝒦 (xs ′xs) ∷ [])
  𝒦 (x ′a) = func (λ (x , _) → Vec.replicate x) (𝒦 x ∷ [])

  ℰ : Expression Γ t → Term Σ Γ Δ t
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

    equal : HasEquality t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ → ⟦ bool ⟧ₜ
    equal bool (lift x) (lift y) = lift (does (x Bool.≟ y))
    equal int (lift x) (lift y) = lift (does (x ≟ᶻ y))
    equal fin (lift x) (lift y) = lift (does (x Fin.≟ y))
    equal real (lift x) (lift y) = lift (does (x ≟ʳ y))
    equal bit (lift x) (lift y) = lift (does (x ≟ᵇ₁ y))
    equal bits []       []       = lift (Bool.true)
    equal bits (x ∷ xs) (y ∷ ys) = lift (lower (equal bit x y) Bool.∧ lower (equal bits xs ys))

    less : IsNumeric t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ → ⟦ bool ⟧ₜ
    less int (lift x) (lift y) = lift (does (x <ᶻ? y))
    less real (lift x) (lift y) = lift (does (x <ʳ? y))

    box : ∀ t → ⟦ elemType t ⟧ₜ → ⟦ asType t 1 ⟧ₜ
    box bits x = x ∷ []
    box (array t) x = x ∷ []

    unboxed : ∀ t → ⟦ asType t 1 ⟧ₜ → ⟦ elemType t ⟧ₜ
    unboxed bits (x ∷ []) = x
    unboxed (array t) (x ∷ []) = x

    casted : ∀ t {i j} → .(eq : i ≡ j) → ⟦ asType t i ⟧ₜ → ⟦ asType t j ⟧ₜ
    casted bits      {j = 0}     eq []       = []
    casted bits      {j = suc j} eq (x ∷ xs) = x ∷ casted bits (ℕₚ.suc-injective eq) xs
    casted (array t) {j = 0}     eq []       = []
    casted (array t) {j = suc j} eq (x ∷ xs) = x ∷ casted (array t) (ℕₚ.suc-injective eq) xs

    neg : IsNumeric t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ
    neg int (lift x) = lift (ℤ.- x)
    neg real (lift x) = lift (ℝ.- x)

    add : (isNum₁ : True (isNumeric? t₁)) → (isNum₂ : True (isNumeric? t₂)) → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ combineNumeric t₁ t₂ {isNum₁} {isNum₂} ⟧ₜ
    add {int} {int} _ _ (lift x) (lift y) = lift (x ℤ.+ y)
    add {int} {real} _ _ (lift x) (lift y) = lift (x /1 ℝ.+ y)
    add {real} {int} _ _ (lift x) (lift y) = lift (x ℝ.+ y /1)
    add {real} {real} _ _ (lift x) (lift y) = lift (x ℝ.+ y)

    mul : (isNum₁ : True (isNumeric? t₁)) → (isNum₂ : True (isNumeric? t₂)) → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ combineNumeric t₁ t₂ {isNum₁} {isNum₂} ⟧ₜ
    mul {int} {int} _ _ (lift x) (lift y) = lift (x ℤ.* y)
    mul {int} {real} _ _ (lift x) (lift y) = lift (x /1 ℝ.* y)
    mul {real} {int} _ _ (lift x) (lift y) = lift (x ℝ.* y /1)
    mul {real} {real} _ _ (lift x) (lift y) = lift (x ℝ.* y)

    pow : IsNumeric t → ⟦ t ⟧ₜ → ℕ → ⟦ t ⟧ₜ
    pow int (lift x) y = lift (x ℤ′.^′ y)
    pow real (lift x) y = lift (x ℝ′.^′ y)

    shift : ⟦ int ⟧ₜ → ℕ → ⟦ int ⟧ₜ
    shift (lift x) n = lift (⌊ x /1 ℝ.* 2≉0 ℝ.⁻¹ ℝ′.^′ n ⌋)

    flatten : ∀ {ms : Vec ℕ n} → ⟦ Vec.map fin ms ⟧ₜ′ → All Fin ms
    flatten {ms = []}     _             = []
    flatten {ms = _ ∷ ms} (lift x , xs) = x ∷ flatten xs

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

    -- 0 of y is 0 of result
    join : ∀ t → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ → ⟦ asType t (n ℕ.+ m) ⟧ₜ
    join bits      xs ys = ys ++ xs
    join (array t) xs ys = ys ++ xs

    take : ∀ t i {j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ asType t i ⟧ₜ
    take bits      i xs = Vec.take i xs
    take (array t) i xs = Vec.take i xs

    drop : ∀ t i {j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ asType t j ⟧ₜ
    drop bits      i xs = Vec.drop i xs
    drop (array t) i xs = Vec.drop i xs

    -- 0 of x is i of result
    spliced : ∀ t {m n} → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ → ⟦ fin (suc n) ⟧ₜ → ⟦ asType t (n ℕ.+ m) ⟧ₜ
    spliced t {m} x y (lift i) = casted t eq (join t (join t high x) low)
      where
      reasoning = slicedSize _ m i
      k = proj₁ reasoning
      n≡i+k = sym (proj₂ (proj₂ reasoning))
      low = take t (Fin.toℕ i) (casted t n≡i+k y)
      high = drop t (Fin.toℕ i) (casted t n≡i+k y)
      eq = sym (proj₁ (proj₂ reasoning))

    -- i of x is 0 of first
    sliced : ∀ t {m n} → ⟦ asType t (n ℕ.+ m) ⟧ₜ → ⟦ fin (suc n) ⟧ₜ → ⟦ asType t m ∷ asType t n ∷ [] ⟧ₜ′
    sliced t {m} x (lift i) = middle , casted t i+k≡n (join t high low) , _
      where
      reasoning = slicedSize _ m i
      k = proj₁ reasoning
      i+k≡n = proj₂ (proj₂ reasoning)
      eq = proj₁ (proj₂ reasoning)
      low = take t (Fin.toℕ i) (casted t eq x)
      middle = take t m (drop t (Fin.toℕ i) (casted t eq x))
      high = drop t m (drop t (Fin.toℕ i) (casted t eq x))

    helper : ∀ (e : Expression Γ t) → M.callDepth e ≡ 0 → Term Σ Γ Δ t
    helper (Code.lit x) eq = 𝒦 x
    helper (Code.state i) eq = state i
    helper (Code.var i) eq = var i
    helper (Code.abort e) eq = func (λ ()) (helper e eq ∷ [])
    helper (_≟_ {hasEquality = hasEq} e e₁) eq = func (λ (x , y , _) → equal (toWitness hasEq) x y) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (_<?_ {isNumeric = isNum} e e₁) eq = func (λ (x , y , _) → less (toWitness isNum) x y) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (Code.inv e) eq = func (λ (lift b , _) → lift (Bool.not b)) (helper e eq ∷ [])
    helper (e Code.&& e₁) eq = func (λ (lift b , lift b₁ , _) → lift (b Bool.∧ b₁)) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (e Code.|| e₁) eq = func (λ (lift b , lift b₁ , _) → lift (b Bool.∨ b₁)) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (Code.not e) eq = func (λ (xs , _) → Vec.map (lift ∘ 𝔹.¬_ ∘ lower) xs) (helper e eq ∷ [])
    helper (e Code.and e₁) eq = func (λ (xs , ys , _) → Vec.zipWith (lift ∘₂ 𝔹._∧_ ) (Vec.map lower xs) (Vec.map lower ys)) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (e Code.or e₁) eq = func (λ (xs , ys , _) → Vec.zipWith (lift ∘₂ 𝔹._∨_ ) (Vec.map lower xs) (Vec.map lower ys)) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper ([_] {t = t} e) eq = func (λ (x , _) → box t x) (helper e eq ∷ [])
    helper (Code.unbox {t = t} e) eq = func (λ (x , _) → unboxed t x) (helper e eq ∷ [])
    helper (Code.splice {t = t} e e₁ e₂) eq = func (λ (x , y , i , _) → spliced t x y i) (helper e (pull-0₃ eq) ∷ helper e₁ (pull-1₃ (M.callDepth e) eq) ∷ helper e₂ (pull-last eq) ∷ [])
    helper (Code.cut {t = t} e e₁) eq = func (λ (x , i , _) → sliced t x i) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (Code.cast {t = t} i≡j e) eq = func (λ (x , _) → casted t i≡j x) (helper e eq ∷ [])
    helper (-_ {isNumeric = isNum} e) eq = func (λ (x , _) → neg (toWitness isNum) x) (helper e eq ∷ [])
    helper (_+_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁) eq = func (λ (x , y , _) → add isNum₁ isNum₂ x y) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (_*_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁) eq = func (λ (x , y , _) → mul isNum₁ isNum₂ x y) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (_^_ {isNumeric = isNum} e y) eq = func (λ (x , _) → pow (toWitness isNum) x y) (helper e eq ∷ [])
    helper (e >> n) eq = func (λ (x , _) → shift x n) (helper e eq ∷ [])
    helper (Code.rnd e) eq = func (λ (lift x , _) → lift ⌊ x ⌋) (helper e eq ∷ [])
    helper (Code.fin f e) eq = func (λ (xs , _) → lift (f (flatten xs))) (helper e eq ∷ [])
    helper (Code.asInt e) eq = func (λ (lift x , _) → lift (Fin.toℕ x ℤ′.×′ 1ℤ)) (helper e eq ∷ [])
    helper Code.nil eq = func (λ args → _) []
    helper (Code.cons e e₁) eq = func (λ (x , xs , _) → x , xs) (helper e (pull-0₂ eq) ∷ helper e₁ (pull-last eq) ∷ [])
    helper (Code.head e) eq = func (λ ((x , _) , _) → x) (helper e eq ∷ [])
    helper (Code.tail e) eq = func (λ ((_ , xs) , _) → xs) (helper e eq ∷ [])
    helper (Code.call f es) eq = contradiction (trans (sym eq) (proj₂ (1+m⊔n≡1+k (M.funCallDepth f) (M.callDepth′ es)))) ℕₚ.0≢1+n
    helper (Code.if e then e₁ else e₂) eq = func (λ (lift b , x , x₁ , _) → Bool.if b then x else x₁) (helper e (pull-0₃ eq) ∷ helper e₁ (pull-1₃ (M.callDepth e) eq) ∷ helper e₂ (pull-last eq) ∷ [])
