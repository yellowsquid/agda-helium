------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for the denotational semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

module Helium.Semantics.Denotational.Core
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

open import Data.Bool as Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin; zero; suc; #_)
import Data.Fin.Properties as Finₚ
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product as P using (_×_; _,_)
open import Data.Sum as S using (_⊎_) renaming (inj₁ to next; inj₂ to ret)
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
import Data.Vec.Functional as VecF
open import Function using (case_of_; _∘′_; id)
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
import Induction as I
import Induction.WellFounded as Wf
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable.Core using (True; False; toWitness; fromWitness)

-- The case for bitvectors looks odd so that the right-most bit is bit 0.
𝒦 : ∀ {t} → Literal t → ⟦ t ⟧ₜ
𝒦 (x ′b)  = x
𝒦 (x ′i)  = x ℤ′.×′ 1ℤ
𝒦 (x ′f)  = x
𝒦 (x ′r)  = x ℝ′.×′ 1ℝ
𝒦 (xs ′x) = Vec.foldl Bits (λ bs b → (Bool.if b then 1𝔹 else 0𝔹) VecF.∷ bs) VecF.[] xs
𝒦 (x ′a)  = Vec.replicate (𝒦 x)

updateAt : ∀ {n} ts i → ⟦ Vec.lookup ts i ⟧ₜ → ⟦ tuple n ts ⟧ₜ → ⟦ tuple n ts ⟧ₜ
updateAt (_ ∷ [])     zero    v _        = v
updateAt (_ ∷ _ ∷ _)  zero    v (_ , xs) = v , xs
updateAt (_ ∷ t ∷ ts) (suc i) v (x , xs) = x , updateAt (t ∷ ts) i v xs

tupCons : ∀ {n t} ts → ⟦ t ⟧ₜ → ⟦ tuple n ts ⟧ₜ → ⟦ tuple _ (t ∷ ts) ⟧ₜ
tupCons []       x xs = x
tupCons (t ∷ ts) x xs = x , xs

tupHead : ∀ {n t} ts → ⟦ tuple (suc n) (t ∷ ts) ⟧ₜ → ⟦ t ⟧ₜ
tupHead {t = t} ts xs = fetch (t ∷ ts) xs zero

tupTail : ∀ {n t} ts → ⟦ tuple _ (t ∷ ts) ⟧ₜ → ⟦ tuple n ts ⟧ₜ
tupTail []      x        = _
tupTail (_ ∷ _) (x , xs) = xs

equal : ∀ {t} → HasEquality t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ → Bool
equal bool x y = does (x Bool.≟ y)
equal int  x y = does (x ≟ᶻ y)
equal fin  x y = does (x Fin.≟ y)
equal real x y = does (x ≟ʳ y)
equal bits x y = does (x ≟ᵇ y)

comp : ∀ {t} → IsNumeric t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ → Bool
comp int  x y = does (x <ᶻ? y)
comp real x y = does (x <ʳ? y)

-- 0 of y is 0 of result
join : ∀ t {m n} → ⟦ asType t m ⟧ₜ → ⟦ asType t n ⟧ₜ → ⟦ asType t (n ℕ.+ m) ⟧ₜ
join bits      {m} x y = y VecF.++ x
join (array _) {m} x y = y Vec.++ x

-- take from 0
take : ∀ t i {j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ asType t i ⟧ₜ
take bits      i x = VecF.take i x
take (array _) i x = Vec.take i x

-- drop from 0
drop : ∀ t i {j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ asType t j ⟧ₜ
drop bits      i x = VecF.drop i x
drop (array _) i x = Vec.drop i x

casted : ∀ t {i j} → .(eq : i ≡ j) → ⟦ asType t i ⟧ₜ → ⟦ asType t j ⟧ₜ
casted bits                  eq x       = x ∘′ Fin.cast (≡.sym eq)
casted (array _) {j = zero}  eq []      = []
casted (array t) {j = suc _} eq (x ∷ y) = x ∷ casted (array t) (ℕₚ.suc-injective eq) y

module _ where
  m≤n⇒m+k≡n : ∀ {m n} → m ℕ.≤ n → P.∃ λ k → m ℕ.+ k ≡ n
  m≤n⇒m+k≡n ℕ.z≤n       = _ , ≡.refl
  m≤n⇒m+k≡n (ℕ.s≤s m≤n) = P.dmap id (≡.cong suc) (m≤n⇒m+k≡n m≤n)

  slicedSize : ∀ i j (off : Fin (suc i)) → P.∃ λ k → i ℕ.+ j ≡ Fin.toℕ off ℕ.+ (j ℕ.+ k)
  slicedSize i j off = k , (begin
    i ℕ.+ j                   ≡˘⟨ ≡.cong (ℕ._+ j) (P.proj₂ off+k≤i) ⟩
    (Fin.toℕ off ℕ.+ k) ℕ.+ j ≡⟨  ℕₚ.+-assoc (Fin.toℕ off) k j ⟩
    Fin.toℕ off ℕ.+ (k ℕ.+ j) ≡⟨  ≡.cong (Fin.toℕ off ℕ.+_) (ℕₚ.+-comm k j) ⟩
    Fin.toℕ off ℕ.+ (j ℕ.+ k) ∎)
    where
    open ≡-Reasoning
    off+k≤i = m≤n⇒m+k≡n (ℕₚ.≤-pred (Finₚ.toℕ<n off))
    k = P.proj₁ off+k≤i

  sliced : ∀ t {i j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ fin (suc i) ⟧ₜ → ⟦ asType t j ⟧ₜ
  sliced t {i} {j} x off = take t j (drop t (Fin.toℕ off) (casted t (P.proj₂ (slicedSize i j off)) x))

updateSliced : ∀ {a} {A : Set a} t {i j} → ⟦ asType t (i ℕ.+ j) ⟧ₜ → ⟦ fin (suc i) ⟧ₜ → ⟦ asType t j ⟧ₜ → (⟦ asType t (i ℕ.+ j) ⟧ₜ → A) → A
updateSliced t {i} {j} orig off v f = f (casted t (≡.sym eq) (join t (join t untaken v) dropped))
  where
  eq = P.proj₂ (slicedSize i j off)
  dropped = take t (Fin.toℕ off) (casted t eq orig)
  untaken = drop t j (drop t (Fin.toℕ off) (casted t eq orig))

neg : ∀ {t} → IsNumeric t → ⟦ t ⟧ₜ → ⟦ t ⟧ₜ
neg int  x = ℤ.- x
neg real x = ℝ.- x

add : ∀ {t₁ t₂} (isNum₁ : True (isNumeric? t₁)) (isNum₂ : True (isNumeric? t₂)) → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ combineNumeric t₁ t₂ {isNum₁} {isNum₂} ⟧ₜ
add {t₁ = int}  {t₂ = int}  _ _ x y = x ℤ.+ y
add {t₁ = int}  {t₂ = real} _ _ x y = x /1 ℝ.+ y
add {t₁ = real} {t₂ = int}  _ _ x y = x ℝ.+ y /1
add {t₁ = real} {t₂ = real} _ _ x y = x ℝ.+ y

mul : ∀ {t₁ t₂} (isNum₁ : True (isNumeric? t₁)) (isNum₂ : True (isNumeric? t₂)) → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ combineNumeric t₁ t₂ {isNum₁} {isNum₂} ⟧ₜ
mul {t₁ = int}  {t₂ = int}  _ _ x y = x ℤ.* y
mul {t₁ = int}  {t₂ = real} _ _ x y = x /1 ℝ.* y
mul {t₁ = real} {t₂ = int}  _ _ x y = x ℝ.* y /1
mul {t₁ = real} {t₂ = real} _ _ x y = x ℝ.* y

pow : ∀ {t} → IsNumeric t → ⟦ t ⟧ₜ → ℕ → ⟦ t ⟧ₜ
pow int  x n = x ℤ′.^′ n
pow real x n = x ℝ′.^′ n

shiftr : 2 ℝ′.×′ 1ℝ ℝ.≉ 0ℝ → ⟦ int ⟧ₜ → ℕ → ⟦ int ⟧ₜ
shiftr 2≉0 x n = ⌊ x /1 ℝ.* 2≉0 ℝ.⁻¹ ℝ′.^′ n ⌋

module Expression
  {o} {Σ : Vec Type o}
  (2≉0 : 2 ℝ′.×′ 1ℝ ℝ.≉ 0ℝ)
  where

  open Code Σ

  ⟦_⟧ᵉ : ∀ {n} {Γ : Vec Type n} {t} → Expression Γ t → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ t ⟧ₜ
  ⟦_⟧ˢ : ∀ {n} {Γ : Vec Type n} → Statement Γ → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′ × ⟦ Γ ⟧ₜ′
  ⟦_⟧ᶠ : ∀ {n} {Γ : Vec Type n} {ret} → Function Γ ret → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ ret ⟧ₜ
  ⟦_⟧ᵖ : ∀ {n} {Γ : Vec Type n} → Procedure Γ → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′
  ⟦_⟧ᵉ′ : ∀ {n} {Γ : Vec Type n} {m ts} → All (Expression Γ) ts → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ tuple m ts ⟧ₜ
  update : ∀ {n Γ t e} → CanAssign {n} {Γ} {t} e → ⟦ t ⟧ₜ → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′ × ⟦ Γ ⟧ₜ′

  ⟦ lit x ⟧ᵉ σ γ = 𝒦 x
  ⟦ state i ⟧ᵉ σ γ = fetch Σ σ (# i)
  ⟦_⟧ᵉ {Γ = Γ} (var i) σ γ = fetch Γ γ (# i)
  ⟦ abort e ⟧ᵉ σ γ = case ⟦ e ⟧ᵉ σ γ of λ ()
  ⟦ _≟_ {hasEquality = hasEq} e e₁ ⟧ᵉ σ γ = equal (toWitness hasEq) (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  ⟦ _<?_ {isNumeric = isNum} e e₁ ⟧ᵉ σ γ = comp (toWitness isNum) (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  ⟦ inv e ⟧ᵉ σ γ = Bool.not (⟦ e ⟧ᵉ σ γ)
  ⟦ e && e₁ ⟧ᵉ σ γ = Bool.if ⟦ e ⟧ᵉ σ γ then ⟦ e₁ ⟧ᵉ σ γ else false
  ⟦ e || e₁ ⟧ᵉ σ γ = Bool.if ⟦ e ⟧ᵉ σ γ then true else ⟦ e₁ ⟧ᵉ σ γ
  ⟦ not e ⟧ᵉ σ γ = Bits.¬_ (⟦ e ⟧ᵉ σ γ)
  ⟦ e and e₁ ⟧ᵉ σ γ = ⟦ e ⟧ᵉ σ γ Bits.∧ ⟦ e₁ ⟧ᵉ σ γ
  ⟦ e or e₁ ⟧ᵉ σ γ = ⟦ e ⟧ᵉ σ γ Bits.∨ ⟦ e₁ ⟧ᵉ σ γ
  ⟦ [ e ] ⟧ᵉ σ γ = ⟦ e ⟧ᵉ σ γ Vec.∷ []
  ⟦ unbox e ⟧ᵉ σ γ = Vec.head (⟦ e ⟧ᵉ σ γ)
  ⟦ _∶_ {t = t} e e₁ ⟧ᵉ σ γ = join t (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  ⟦ slice {t = t} e e₁ ⟧ᵉ σ γ = sliced t (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  ⟦ cast {t = t} eq e ⟧ᵉ σ γ = casted t eq (⟦ e ⟧ᵉ σ γ)
  ⟦ -_ {isNumeric = isNum} e ⟧ᵉ σ γ = neg (toWitness isNum) (⟦ e ⟧ᵉ σ γ)
  ⟦ _+_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁ ⟧ᵉ σ γ = add isNum₁ isNum₂ (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  ⟦ _*_ {isNumeric₁ = isNum₁} {isNumeric₂ = isNum₂} e e₁ ⟧ᵉ σ γ = mul isNum₁ isNum₂ (⟦ e ⟧ᵉ σ γ) (⟦ e₁ ⟧ᵉ σ γ)
  -- ⟦ e / e₁ ⟧ᵉ σ γ = {!!}
  ⟦ _^_ {isNumeric = isNum} e n ⟧ᵉ σ γ = pow (toWitness isNum) (⟦ e ⟧ᵉ σ γ) n
  ⟦ _>>_ e n ⟧ᵉ σ γ = shiftr 2≉0 (⟦ e ⟧ᵉ σ γ) n
  ⟦ rnd e ⟧ᵉ σ γ = ⌊ ⟦ e ⟧ᵉ σ γ ⌋
  ⟦ fin x e ⟧ᵉ σ γ = apply x (⟦ e ⟧ᵉ σ γ)
    where
    apply : ∀ {k ms n} → (All Fin ms → Fin n) → ⟦ Vec.map {n = k} fin ms ⟧ₜ′ → ⟦ fin n ⟧ₜ
    apply {zero}  {[]}     f xs = f []
    apply {suc k} {_ ∷ ms} f xs =
      apply (λ x → f (tupHead (Vec.map fin ms) xs ∷ x)) (tupTail (Vec.map fin ms) xs)
  ⟦ asInt e ⟧ᵉ σ γ = Fin.toℕ (⟦ e ⟧ᵉ σ γ) ℤ′.×′ 1ℤ
  ⟦ tup [] ⟧ᵉ σ γ = _
  ⟦ tup (e ∷ []) ⟧ᵉ σ γ = ⟦ e ⟧ᵉ σ γ
  ⟦ tup (e ∷ e′ ∷ es) ⟧ᵉ σ γ = ⟦ e ⟧ᵉ σ γ , ⟦ tup (e′ ∷ es) ⟧ᵉ σ γ
  ⟦ call f e ⟧ᵉ σ γ = ⟦ f ⟧ᶠ σ (⟦ e ⟧ᵉ′ σ γ)
  ⟦ if e then e₁ else e₂ ⟧ᵉ σ γ = Bool.if ⟦ e ⟧ᵉ σ γ then ⟦ e₁ ⟧ᵉ σ γ else ⟦ e₂ ⟧ᵉ σ γ

  ⟦ [] ⟧ᵉ′          σ γ = _
  ⟦ e ∷ [] ⟧ᵉ′      σ γ = ⟦ e ⟧ᵉ σ γ
  ⟦ e ∷ e′ ∷ es ⟧ᵉ′ σ γ = ⟦ e ⟧ᵉ σ γ , ⟦ e′ ∷ es ⟧ᵉ′ σ γ

  ⟦ s ∙ s₁ ⟧ˢ σ γ = P.uncurry ⟦ s ⟧ˢ (⟦ s ⟧ˢ σ γ)
  ⟦ skip ⟧ˢ σ γ = σ , γ
  ⟦ _≔_ ref {canAssign = canAssign} e ⟧ˢ σ γ = update (toWitness canAssign) (⟦ e ⟧ᵉ σ γ) σ γ
  ⟦_⟧ˢ {Γ = Γ} (declare e s) σ γ = P.map₂ (tupTail Γ) (⟦ s ⟧ˢ σ (tupCons Γ (⟦ e ⟧ᵉ σ γ) γ))
  ⟦ invoke p e ⟧ˢ σ γ = ⟦ p ⟧ᵖ σ (⟦ e ⟧ᵉ′ σ γ) , γ
  ⟦ if e then s₁ else s₂ ⟧ˢ σ γ = Bool.if ⟦ e ⟧ᵉ σ γ then ⟦ s₁ ⟧ˢ σ γ else ⟦ s₂ ⟧ˢ σ γ
  ⟦_⟧ˢ {Γ = Γ} (for m s) σ γ = helper m ⟦ s ⟧ˢ σ γ
    where
    helper : ∀ m → (⟦ Σ ⟧ₜ′ → ⟦ fin m ∷ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′ × ⟦ fin m ∷ Γ ⟧ₜ′) → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′ × ⟦ Γ ⟧ₜ′
    helper zero    s σ γ = σ , γ
    helper (suc m) s σ γ = P.uncurry (helper m s′) (P.map₂ (tupTail Γ) (s σ (tupCons Γ zero γ)))
      where
      s′ : ⟦ Σ ⟧ₜ′ → ⟦ fin m ∷ Γ ⟧ₜ′ → ⟦ Σ ⟧ₜ′ × ⟦ fin m ∷ Γ ⟧ₜ′
      s′ σ γ =
        P.map₂ (tupCons Γ (tupHead Γ γ) ∘′ (tupTail Γ))
               (s σ (tupCons Γ (suc (tupHead Γ γ)) (tupTail Γ γ)))

  ⟦ s ∙return e ⟧ᶠ σ γ = P.uncurry ⟦ e ⟧ᵉ (⟦ s ⟧ˢ σ γ)
  ⟦_⟧ᶠ {Γ = Γ} (declare e f) σ γ = ⟦ f ⟧ᶠ σ (tupCons Γ (⟦ e ⟧ᵉ σ γ) γ)

  ⟦ s ∙end ⟧ᵖ σ γ = P.proj₁ (⟦ s ⟧ˢ σ γ)

  update (state i {i<o}) v σ γ = updateAt Σ (#_ i {m<n = i<o}) v σ , γ
  update {Γ = Γ} (var i {i<n}) v σ γ = σ , updateAt Γ (#_ i {m<n = i<n}) v γ
  update abort v σ γ = σ , γ
  update (_∶_ {m = m} {t = t} e e₁) v σ γ = do
    let σ′ , γ′ = update e (sliced t v (Fin.fromℕ _)) σ γ
    update e₁ (sliced t (casted t (ℕₚ.+-comm _ m) v) zero) σ′ γ′
  update [ e ] v σ γ = update e (Vec.head v) σ γ
  update (unbox e) v σ γ = update e (v ∷ []) σ γ
  update (slice {t = t} {e₁ = e₁} a e₂) v σ γ = updateSliced t (⟦ e₁ ⟧ᵉ σ γ) (⟦ e₂ ⟧ᵉ σ γ) v (λ v → update a v σ γ)
  update (cast {t = t} eq e) v σ γ = update e (casted t (≡.sym eq) v) σ γ
  update (tup {es = []} x) v σ γ = σ , γ
  update (tup {es = _ ∷ []} (x ∷ [])) v σ γ = update x v σ γ
  update (tup {es = _ ∷ _ ∷ _} (x ∷ xs)) (v , vs) σ γ = do
    let σ′ , γ′ = update x v σ γ
    update (tup xs) vs σ′ γ′
