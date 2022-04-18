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
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; suc; punchOut)
open import Data.Fin.Patterns
import Data.Integer as 𝕀
import Data.Fin.Properties as Finₚ
open import Data.Nat as ℕ using (ℕ; suc; _≤_; z≤n; s≤s; _⊔_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _,_; dmap)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup; insert; remove; map; zipWith; take; drop)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Recursive as Vecᵣ using (2+_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Helium.Data.Pseudocode.Core
open import Helium.Data.Pseudocode.Manipulate hiding (module Cast)
open import Helium.Semantics.Core rawPseudocode
open import Level as L using (lift; lower)
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Relation.Nullary using (does; yes; no)

private
  variable
    t t′ t₁ t₂  : Type
    i j k m n o : ℕ
    Γ Δ Σ ts    : Vec Type m

  ℓ = b₁ L.⊔ i₁ L.⊔ r₁

  punchOut-insert : ∀ {a} {A : Set a} (xs : Vec A n) {i j} (i≢j : i ≢ j) x → lookup xs (punchOut i≢j) ≡ lookup (insert xs i x) j
  punchOut-insert xs {i} {j} i≢j x = begin
    lookup xs (punchOut i≢j)                         ≡˘⟨ cong (flip lookup (punchOut i≢j)) (Vecₚ.remove-insert xs i x) ⟩
    lookup (remove (insert xs i x) i) (punchOut i≢j) ≡⟨  Vecₚ.remove-punchOut (insert xs i x) i≢j ⟩
    lookup (insert xs i x) j                         ∎
    where open ≡-Reasoning

  open ℕₚ.≤-Reasoning

  ⨆[_]_ : ∀ n → ℕ Vecᵣ.^ n → ℕ
  ⨆[_]_ = Vecᵣ.foldl (const ℕ) 0 id (const (flip ℕ._⊔_))

  ⨆-step : ∀ m x xs → ⨆[ 2+ m ] (x , xs) ≡ x ⊔ ⨆[ suc m ] xs
  ⨆-step 0       x xs       = refl
  ⨆-step (suc m) x (y , xs) = begin-equality
    ⨆[ 2+ suc m ] (x , y , xs) ≡⟨  ⨆-step m (x ⊔ y) xs ⟩
    x ⊔ y ⊔ ⨆[ suc m ] xs      ≡⟨  ℕₚ.⊔-assoc x y _ ⟩
    x ⊔ (y ⊔ ⨆[ suc m ] xs)    ≡˘⟨ cong (_ ⊔_) (⨆-step m y xs) ⟩
    x ⊔ ⨆[ 2+ m ] (y , xs)     ∎

  lookup-⨆-≤ : ∀ i (xs : ℕ Vecᵣ.^ n) → Vecᵣ.lookup i xs ≤ ⨆[ n ] xs
  lookup-⨆-≤ {1}    0F      x        = ℕₚ.≤-refl
  lookup-⨆-≤ {2+ n} 0F      (x , xs) = begin
    x                  ≤⟨  ℕₚ.m≤m⊔n x _ ⟩
    x ⊔ ⨆[ suc n ] xs  ≡˘⟨ ⨆-step n x xs ⟩
    ⨆[ 2+ n ] (x , xs) ∎
  lookup-⨆-≤ {2+ n} (suc i) (x , xs) = begin
    Vecᵣ.lookup i xs   ≤⟨  lookup-⨆-≤ i xs ⟩
    ⨆[ suc n ] xs      ≤⟨  ℕₚ.m≤n⊔m x _ ⟩
    x ⊔ ⨆[ suc n ] xs  ≡˘⟨ ⨆-step n x xs ⟩
    ⨆[ 2+ n ] (x , xs) ∎

data Term (Σ : Vec Type i) (Γ : Vec Type j) (Δ : Vec Type k) : Type → Set ℓ where
  lit           : ⟦ t ⟧ₜ → Term Σ Γ Δ t
  state         : ∀ i → Term Σ Γ Δ (lookup Σ i)
  var           : ∀ i → Term Σ Γ Δ (lookup Γ i)
  meta          : ∀ i → Term Σ Γ Δ (lookup Δ i)
  _≟_           : ⦃ HasEquality t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
  _<?_          : ⦃ Ordered t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
  inv           : Term Σ Γ Δ bool → Term Σ Γ Δ bool
  _&&_          : Term Σ Γ Δ bool → Term Σ Γ Δ bool → Term Σ Γ Δ bool
  _||_          : Term Σ Γ Δ bool → Term Σ Γ Δ bool → Term Σ Γ Δ bool
  not           : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  _and_         : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  _or_          : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  [_]           : Term Σ Γ Δ t → Term Σ Γ Δ (array t 1)
  unbox         : Term Σ Γ Δ (array t 1) → Term Σ Γ Δ t
  merge         : Term Σ Γ Δ (array t m) → Term Σ Γ Δ (array t n) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t (n ℕ.+ m))
  slice         : Term Σ Γ Δ (array t (n ℕ.+ m)) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t m)
  cut           : Term Σ Γ Δ (array t (n ℕ.+ m)) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t n)
  cast          : .(eq : m ≡ n) → Term Σ Γ Δ (array t m) → Term Σ Γ Δ (array t n)
  -_            : ⦃ IsNumeric t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t
  _+_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (isNum₁ +ᵗ isNum₂)
  _*_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (isNum₁ +ᵗ isNum₂)
  _^_           : ⦃ IsNumeric t ⦄ → Term Σ Γ Δ t → ℕ → Term Σ Γ Δ t
  _>>_          : Term Σ Γ Δ int → (n : ℕ) → Term Σ Γ Δ int
  rnd           : Term Σ Γ Δ real → Term Σ Γ Δ int
  fin           : ∀ {ms} (f : literalTypes (map fin ms) → Fin n) → Term Σ Γ Δ (tuple {n = o} (map fin ms)) → Term Σ Γ Δ (fin n)
  asInt         : Term Σ Γ Δ (fin n) → Term Σ Γ Δ int
  nil           : Term Σ Γ Δ (tuple [])
  cons          : Term Σ Γ Δ t → Term Σ Γ Δ (tuple ts) → Term Σ Γ Δ (tuple (t ∷ ts))
  head          : Term Σ Γ Δ (tuple (t ∷ ts)) → Term Σ Γ Δ t
  tail          : Term Σ Γ Δ (tuple (t ∷ ts)) → Term Σ Γ Δ (tuple ts)
  if_then_else_ : Term Σ Γ Δ bool → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ t

↓_ : Expression Σ Γ t → Term Σ Γ Δ t
↓ e = go (Flatten.expr e) (Flatten.expr-depth e)
  where
  ⊔-inj : ∀ i xs → ⨆[ n ] xs ≡ 0 → Vecᵣ.lookup i xs ≡ 0
  ⊔-inj i xs eq = ℕₚ.n≤0⇒n≡0 (ℕₚ.≤-trans (lookup-⨆-≤ i xs) (ℕₚ.≤-reflexive eq))

  go : ∀ (e : Expression Σ Γ t) → CallDepth.expr e ≡ 0 → Term Σ Γ Δ t
  go (lit {t} x)            ≡0 = lit (Κ[ t ] x)
  go (state i)              ≡0 = state i
  go (var i)                ≡0 = var i
  go (e ≟ e₁)               ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) ≟ go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (e <? e₁)              ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) <? go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (inv e)                ≡0 = inv (go e ≡0)
  go (e && e₁)              ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) && go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (e || e₁)              ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) || go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (not e)                ≡0 = not (go e ≡0)
  go (e and e₁)             ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) and go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (e or e₁)              ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) or go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go [ e ]                  ≡0 = [ go e ≡0 ]
  go (unbox e)              ≡0 = unbox (go e ≡0)
  go (merge e e₁ e₂)        ≡0 = merge (go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0)) (go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0)) (go e₂ (⊔-inj 2F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0))
  go (slice e e₁)           ≡0 = slice (go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0)) (go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0))
  go (cut e e₁)             ≡0 = cut (go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0)) (go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0))
  go (cast eq e)            ≡0 = cast eq (go e ≡0)
  go (- e)                  ≡0 = - go e ≡0
  go (e + e₁)               ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) + go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (e * e₁)               ≡0 = go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0) * go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0)
  go (e ^ x)                ≡0 = go e ≡0 ^ x
  go (e >> n)               ≡0 = go e ≡0 >> n
  go (rnd e)                ≡0 = rnd (go e ≡0)
  go (fin f e)              ≡0 = fin f (go e ≡0)
  go (asInt e)              ≡0 = asInt (go e ≡0)
  go nil                    ≡0 = nil
  go (cons e e₁)            ≡0 = cons (go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁) ≡0)) (go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁) ≡0))
  go (head e)               ≡0 = head (go e ≡0)
  go (tail e)               ≡0 = tail (go e ≡0)
  go (call f es)            ≡0 = ⊥-elim (ℕₚ.>⇒≢ (CallDepth.call>0 f es) ≡0)
  go (if e then e₁ else e₂) ≡0 = if go e (⊔-inj 0F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0) then go e₁ (⊔-inj 1F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0) else go e₂ (⊔-inj 2F (CallDepth.expr e , CallDepth.expr e₁ , CallDepth.expr e₂) ≡0)

module Cast where
  type : t ≡ t′ → Term Σ Γ Δ t → Term Σ Γ Δ t′
  type refl = id

module State where
  subst : ∀ i → Term Σ Γ Δ t → Term Σ Γ Δ (lookup Σ i) → Term Σ Γ Δ t
  subst i (lit x)                e′ = lit x
  subst i (state j)              e′ with i Fin.≟ j
  ...                              | yes refl = e′
  ...                              | no i≢j   = state j
  subst i (var j)                e′ = var j
  subst i (meta j)               e′ = meta j
  subst i (e ≟ e₁)               e′ = subst i e e′ ≟ subst i e₁ e′
  subst i (e <? e₁)              e′ = subst i e e′ <? subst i e₁ e′
  subst i (inv e)                e′ = inv (subst i e e′)
  subst i (e && e₁)              e′ = subst i e e′ && subst i e₁ e′
  subst i (e || e₁)              e′ = subst i e e′ || subst i e₁ e′
  subst i (not e)                e′ = not (subst i e e′)
  subst i (e and e₁)             e′ = subst i e e′ and subst i e₁ e′
  subst i (e or e₁)              e′ = subst i e e′ or subst i e₁ e′
  subst i [ e ]                  e′ = [ subst i e e′ ]
  subst i (unbox e)              e′ = unbox (subst i e e′)
  subst i (merge e e₁ e₂)        e′ = merge (subst i e e′) (subst i e₁ e′) (subst i e₂ e′)
  subst i (slice e e₁)           e′ = slice (subst i e e′) (subst i e₁ e′)
  subst i (cut e e₁)             e′ = cut (subst i e e′) (subst i e₁ e′)
  subst i (cast eq e)            e′ = cast eq (subst i e e′)
  subst i (- e)                  e′ = - subst i e e′
  subst i (e + e₁)               e′ = subst i e e′ + subst i e₁ e′
  subst i (e * e₁)               e′ = subst i e e′ * subst i e₁ e′
  subst i (e ^ x)                e′ = subst i e e′ ^ x
  subst i (e >> n)               e′ = subst i e e′ >> n
  subst i (rnd e)                e′ = rnd (subst i e e′)
  subst i (fin f e)              e′ = fin f (subst i e e′)
  subst i (asInt e)              e′ = asInt (subst i e e′)
  subst i nil                    e′ = nil
  subst i (cons e e₁)            e′ = cons (subst i e e′) (subst i e₁ e′)
  subst i (head e)               e′ = head (subst i e e′)
  subst i (tail e)               e′ = tail (subst i e e′)
  subst i (if e then e₁ else e₂) e′ = if subst i e e′ then subst i e₁ e′ else subst i e₂ e′

module Var {Γ : Vec Type o} where
  weaken : ∀ i → Term Σ Γ Δ t → Term Σ (insert Γ i t′) Δ t
  weaken i (lit x)                = lit x
  weaken i (state j)              = state j
  weaken i (var j)                = Cast.type (Vecₚ.insert-punchIn _ i _ j) (var (Fin.punchIn i j))
  weaken i (meta j)               = meta j
  weaken i (e ≟ e₁)               = weaken i e ≟ weaken i e₁
  weaken i (e <? e₁)              = weaken i e <? weaken i e₁
  weaken i (inv e)                = inv (weaken i e)
  weaken i (e && e₁)              = weaken i e && weaken i e₁
  weaken i (e || e₁)              = weaken i e || weaken i e₁
  weaken i (not e)                = not (weaken i e)
  weaken i (e and e₁)             = weaken i e and weaken i e₁
  weaken i (e or e₁)              = weaken i e or weaken i e₁
  weaken i [ e ]                  = [ weaken i e ]
  weaken i (unbox e)              = unbox (weaken i e)
  weaken i (merge e e₁ e₂)        = merge (weaken i e) (weaken i e₁) (weaken i e₂)
  weaken i (slice e e₁)           = slice (weaken i e) (weaken i e₁)
  weaken i (cut e e₁)             = cut (weaken i e) (weaken i e₁)
  weaken i (cast eq e)            = cast eq (weaken i e)
  weaken i (- e)                  = - weaken i e
  weaken i (e + e₁)               = weaken i e + weaken i e₁
  weaken i (e * e₁)               = weaken i e * weaken i e₁
  weaken i (e ^ x)                = weaken i e ^ x
  weaken i (e >> n)               = weaken i e >> n
  weaken i (rnd e)                = rnd (weaken i e)
  weaken i (fin f e)              = fin f (weaken i e)
  weaken i (asInt e)              = asInt (weaken i e)
  weaken i nil                    = nil
  weaken i (cons e e₁)            = cons (weaken i e) (weaken i e₁)
  weaken i (head e)               = head (weaken i e)
  weaken i (tail e)               = tail (weaken i e)
  weaken i (if e then e₁ else e₂) = if weaken i e then weaken i e₁ else weaken i e₂

  weakenAll : Term Σ [] Δ t → Term Σ Γ Δ t
  weakenAll (lit x)                = lit x
  weakenAll (state j)              = state j
  weakenAll (meta j)               = meta j
  weakenAll (e ≟ e₁)               = weakenAll e ≟ weakenAll e₁
  weakenAll (e <? e₁)              = weakenAll e <? weakenAll e₁
  weakenAll (inv e)                = inv (weakenAll e)
  weakenAll (e && e₁)              = weakenAll e && weakenAll e₁
  weakenAll (e || e₁)              = weakenAll e || weakenAll e₁
  weakenAll (not e)                = not (weakenAll e)
  weakenAll (e and e₁)             = weakenAll e and weakenAll e₁
  weakenAll (e or e₁)              = weakenAll e or weakenAll e₁
  weakenAll [ e ]                  = [ weakenAll e ]
  weakenAll (unbox e)              = unbox (weakenAll e)
  weakenAll (merge e e₁ e₂)        = merge (weakenAll e) (weakenAll e₁) (weakenAll e₂)
  weakenAll (slice e e₁)           = slice (weakenAll e) (weakenAll e₁)
  weakenAll (cut e e₁)             = cut (weakenAll e) (weakenAll e₁)
  weakenAll (cast eq e)            = cast eq (weakenAll e)
  weakenAll (- e)                  = - weakenAll e
  weakenAll (e + e₁)               = weakenAll e + weakenAll e₁
  weakenAll (e * e₁)               = weakenAll e * weakenAll e₁
  weakenAll (e ^ x)                = weakenAll e ^ x
  weakenAll (e >> n)               = weakenAll e >> n
  weakenAll (rnd e)                = rnd (weakenAll e)
  weakenAll (fin f e)              = fin f (weakenAll e)
  weakenAll (asInt e)              = asInt (weakenAll e)
  weakenAll nil                    = nil
  weakenAll (cons e e₁)            = cons (weakenAll e) (weakenAll e₁)
  weakenAll (head e)               = head (weakenAll e)
  weakenAll (tail e)               = tail (weakenAll e)
  weakenAll (if e then e₁ else e₂) = if weakenAll e then weakenAll e₁ else weakenAll e₂

  inject : ∀ (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ (Γ ++ ts) Δ t
  inject ts (lit x)                = lit x
  inject ts (state j)              = state j
  inject ts (var j)                = Cast.type (Vecₚ.lookup-++ˡ Γ ts j) (var (Fin.inject+ _ j))
  inject ts (meta j)               = meta j
  inject ts (e ≟ e₁)               = inject ts e ≟ inject ts e₁
  inject ts (e <? e₁)              = inject ts e <? inject ts e₁
  inject ts (inv e)                = inv (inject ts e)
  inject ts (e && e₁)              = inject ts e && inject ts e₁
  inject ts (e || e₁)              = inject ts e || inject ts e₁
  inject ts (not e)                = not (inject ts e)
  inject ts (e and e₁)             = inject ts e and inject ts e₁
  inject ts (e or e₁)              = inject ts e or inject ts e₁
  inject ts [ e ]                  = [ inject ts e ]
  inject ts (unbox e)              = unbox (inject ts e)
  inject ts (merge e e₁ e₂)        = merge (inject ts e) (inject ts e₁) (inject ts e₂)
  inject ts (slice e e₁)           = slice (inject ts e) (inject ts e₁)
  inject ts (cut e e₁)             = cut (inject ts e) (inject ts e₁)
  inject ts (cast eq e)            = cast eq (inject ts e)
  inject ts (- e)                  = - inject ts e
  inject ts (e + e₁)               = inject ts e + inject ts e₁
  inject ts (e * e₁)               = inject ts e * inject ts e₁
  inject ts (e ^ x)                = inject ts e ^ x
  inject ts (e >> n)               = inject ts e >> n
  inject ts (rnd e)                = rnd (inject ts e)
  inject ts (fin f e)              = fin f (inject ts e)
  inject ts (asInt e)              = asInt (inject ts e)
  inject ts nil                    = nil
  inject ts (cons e e₁)            = cons (inject ts e) (inject ts e₁)
  inject ts (head e)               = head (inject ts e)
  inject ts (tail e)               = tail (inject ts e)
  inject ts (if e then e₁ else e₂) = if inject ts e then inject ts e₁ else inject ts e₂

  raise : ∀ (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ (ts ++ Γ) Δ t
  raise ts (lit x)                = lit x
  raise ts (state j)              = state j
  raise ts (var j)                = Cast.type (Vecₚ.lookup-++ʳ ts Γ j) (var (Fin.raise _ j))
  raise ts (meta j)               = meta j
  raise ts (e ≟ e₁)               = raise ts e ≟ raise ts e₁
  raise ts (e <? e₁)              = raise ts e <? raise ts e₁
  raise ts (inv e)                = inv (raise ts e)
  raise ts (e && e₁)              = raise ts e && raise ts e₁
  raise ts (e || e₁)              = raise ts e || raise ts e₁
  raise ts (not e)                = not (raise ts e)
  raise ts (e and e₁)             = raise ts e and raise ts e₁
  raise ts (e or e₁)              = raise ts e or raise ts e₁
  raise ts [ e ]                  = [ raise ts e ]
  raise ts (unbox e)              = unbox (raise ts e)
  raise ts (merge e e₁ e₂)        = merge (raise ts e) (raise ts e₁) (raise ts e₂)
  raise ts (slice e e₁)           = slice (raise ts e) (raise ts e₁)
  raise ts (cut e e₁)             = cut (raise ts e) (raise ts e₁)
  raise ts (cast eq e)            = cast eq (raise ts e)
  raise ts (- e)                  = - raise ts e
  raise ts (e + e₁)               = raise ts e + raise ts e₁
  raise ts (e * e₁)               = raise ts e * raise ts e₁
  raise ts (e ^ x)                = raise ts e ^ x
  raise ts (e >> n)               = raise ts e >> n
  raise ts (rnd e)                = rnd (raise ts e)
  raise ts (fin f e)              = fin f (raise ts e)
  raise ts (asInt e)              = asInt (raise ts e)
  raise ts nil                    = nil
  raise ts (cons e e₁)            = cons (raise ts e) (raise ts e₁)
  raise ts (head e)               = head (raise ts e)
  raise ts (tail e)               = tail (raise ts e)
  raise ts (if e then e₁ else e₂) = if raise ts e then raise ts e₁ else raise ts e₂

  elim : ∀ i → Term Σ (insert Γ i t′) Δ t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  elim i (lit x)                e′ = lit x
  elim i (state j)              e′ = state j
  elim i (var j)                e′ with i Fin.≟ j
  ...                              | yes refl = Cast.type (sym (Vecₚ.insert-lookup Γ i _)) e′
  ...                              | no i≢j   = Cast.type (punchOut-insert Γ i≢j _) (var (Fin.punchOut i≢j))
  elim i (meta j)               e′ = meta j
  elim i (e ≟ e₁)               e′ = elim i e e′ ≟ elim i e₁ e′
  elim i (e <? e₁)              e′ = elim i e e′ <? elim i e₁ e′
  elim i (inv e)                e′ = inv (elim i e e′)
  elim i (e && e₁)              e′ = elim i e e′ && elim i e₁ e′
  elim i (e || e₁)              e′ = elim i e e′ || elim i e₁ e′
  elim i (not e)                e′ = not (elim i e e′)
  elim i (e and e₁)             e′ = elim i e e′ and elim i e₁ e′
  elim i (e or e₁)              e′ = elim i e e′ or elim i e₁ e′
  elim i [ e ]                  e′ = [ elim i e e′ ]
  elim i (unbox e)              e′ = unbox (elim i e e′)
  elim i (merge e e₁ e₂)        e′ = merge (elim i e e′) (elim i e₁ e′) (elim i e₂ e′)
  elim i (slice e e₁)           e′ = slice (elim i e e′) (elim i e₁ e′)
  elim i (cut e e₁)             e′ = cut (elim i e e′) (elim i e₁ e′)
  elim i (cast eq e)            e′ = cast eq (elim i e e′)
  elim i (- e)                  e′ = - elim i e e′
  elim i (e + e₁)               e′ = elim i e e′ + elim i e₁ e′
  elim i (e * e₁)               e′ = elim i e e′ * elim i e₁ e′
  elim i (e ^ x)                e′ = elim i e e′ ^ x
  elim i (e >> n)               e′ = elim i e e′ >> n
  elim i (rnd e)                e′ = rnd (elim i e e′)
  elim i (fin f e)              e′ = fin f (elim i e e′)
  elim i (asInt e)              e′ = asInt (elim i e e′)
  elim i nil                    e′ = nil
  elim i (cons e e₁)            e′ = cons (elim i e e′) (elim i e₁ e′)
  elim i (head e)               e′ = head (elim i e e′)
  elim i (tail e)               e′ = tail (elim i e e′)
  elim i (if e then e₁ else e₂) e′ = if elim i e e′ then elim i e₁ e′ else elim i e₂ e′

  elimAll : Term Σ Γ Δ t → All (Term Σ ts Δ) Γ → Term Σ ts Δ t
  elimAll (lit x)                es = lit x
  elimAll (state j)              es = state j
  elimAll (var j)                es = All.lookup j es
  elimAll (meta j)               es = meta j
  elimAll (e ≟ e₁)               es = elimAll e es ≟ elimAll e₁ es
  elimAll (e <? e₁)              es = elimAll e es <? elimAll e₁ es
  elimAll (inv e)                es = inv (elimAll e es)
  elimAll (e && e₁)              es = elimAll e es && elimAll e₁ es
  elimAll (e || e₁)              es = elimAll e es || elimAll e₁ es
  elimAll (not e)                es = not (elimAll e es)
  elimAll (e and e₁)             es = elimAll e es and elimAll e₁ es
  elimAll (e or e₁)              es = elimAll e es or elimAll e₁ es
  elimAll [ e ]                  es = [ elimAll e es ]
  elimAll (unbox e)              es = unbox (elimAll e es)
  elimAll (merge e e₁ e₂)        es = merge (elimAll e es) (elimAll e₁ es) (elimAll e₂ es)
  elimAll (slice e e₁)           es = slice (elimAll e es) (elimAll e₁ es)
  elimAll (cut e e₁)             es = cut (elimAll e es) (elimAll e₁ es)
  elimAll (cast eq e)            es = cast eq (elimAll e es)
  elimAll (- e)                  es = - elimAll e es
  elimAll (e + e₁)               es = elimAll e es + elimAll e₁ es
  elimAll (e * e₁)               es = elimAll e es * elimAll e₁ es
  elimAll (e ^ x)                es = elimAll e es ^ x
  elimAll (e >> n)               es = elimAll e es >> n
  elimAll (rnd e)                es = rnd (elimAll e es)
  elimAll (fin f e)              es = fin f (elimAll e es)
  elimAll (asInt e)              es = asInt (elimAll e es)
  elimAll nil                    es = nil
  elimAll (cons e e₁)            es = cons (elimAll e es) (elimAll e₁ es)
  elimAll (head e)               es = head (elimAll e es)
  elimAll (tail e)               es = tail (elimAll e es)
  elimAll (if e then e₁ else e₂) es = if elimAll e es then elimAll e₁ es else elimAll e₂ es

  subst : ∀ i → Term Σ Γ Δ t → Term Σ Γ Δ (lookup Γ i) → Term Σ Γ Δ t
  subst i (lit x)                e′ = lit x
  subst i (state j)              e′ = state j
  subst i (var j)                e′ with i Fin.≟ j
  ...                              | yes refl = e′
  ...                              | no i≢j   = var j
  subst i (meta j)               e′ = meta j
  subst i (e ≟ e₁)               e′ = subst i e e′ ≟ subst i e₁ e′
  subst i (e <? e₁)              e′ = subst i e e′ <? subst i e₁ e′
  subst i (inv e)                e′ = inv (subst i e e′)
  subst i (e && e₁)              e′ = subst i e e′ && subst i e₁ e′
  subst i (e || e₁)              e′ = subst i e e′ || subst i e₁ e′
  subst i (not e)                e′ = not (subst i e e′)
  subst i (e and e₁)             e′ = subst i e e′ and subst i e₁ e′
  subst i (e or e₁)              e′ = subst i e e′ or subst i e₁ e′
  subst i [ e ]                  e′ = [ subst i e e′ ]
  subst i (unbox e)              e′ = unbox (subst i e e′)
  subst i (merge e e₁ e₂)        e′ = merge (subst i e e′) (subst i e₁ e′) (subst i e₂ e′)
  subst i (slice e e₁)           e′ = slice (subst i e e′) (subst i e₁ e′)
  subst i (cut e e₁)             e′ = cut (subst i e e′) (subst i e₁ e′)
  subst i (cast eq e)            e′ = cast eq (subst i e e′)
  subst i (- e)                  e′ = - subst i e e′
  subst i (e + e₁)               e′ = subst i e e′ + subst i e₁ e′
  subst i (e * e₁)               e′ = subst i e e′ * subst i e₁ e′
  subst i (e ^ x)                e′ = subst i e e′ ^ x
  subst i (e >> n)               e′ = subst i e e′ >> n
  subst i (rnd e)                e′ = rnd (subst i e e′)
  subst i (fin f e)              e′ = fin f (subst i e e′)
  subst i (asInt e)              e′ = asInt (subst i e e′)
  subst i nil                    e′ = nil
  subst i (cons e e₁)            e′ = cons (subst i e e′) (subst i e₁ e′)
  subst i (head e)               e′ = head (subst i e e′)
  subst i (tail e)               e′ = tail (subst i e e′)
  subst i (if e then e₁ else e₂) e′ = if subst i e e′ then subst i e₁ e′ else subst i e₂ e′

module Meta {Δ : Vec Type o} where
  weaken : ∀ i → Term Σ Γ Δ t → Term Σ Γ (insert Δ i t′) t
  weaken i (lit x)                = lit x
  weaken i (state j)              = state j
  weaken i (var j)                = var j
  weaken i (meta j)               = Cast.type (Vecₚ.insert-punchIn _ i _ j) (meta (Fin.punchIn i j))
  weaken i (e ≟ e₁)               = weaken i e ≟ weaken i e₁
  weaken i (e <? e₁)              = weaken i e <? weaken i e₁
  weaken i (inv e)                = inv (weaken i e)
  weaken i (e && e₁)              = weaken i e && weaken i e₁
  weaken i (e || e₁)              = weaken i e || weaken i e₁
  weaken i (not e)                = not (weaken i e)
  weaken i (e and e₁)             = weaken i e and weaken i e₁
  weaken i (e or e₁)              = weaken i e or weaken i e₁
  weaken i [ e ]                  = [ weaken i e ]
  weaken i (unbox e)              = unbox (weaken i e)
  weaken i (merge e e₁ e₂)        = merge (weaken i e) (weaken i e₁) (weaken i e₂)
  weaken i (slice e e₁)           = slice (weaken i e) (weaken i e₁)
  weaken i (cut e e₁)             = cut (weaken i e) (weaken i e₁)
  weaken i (cast eq e)            = cast eq (weaken i e)
  weaken i (- e)                  = - weaken i e
  weaken i (e + e₁)               = weaken i e + weaken i e₁
  weaken i (e * e₁)               = weaken i e * weaken i e₁
  weaken i (e ^ x)                = weaken i e ^ x
  weaken i (e >> n)               = weaken i e >> n
  weaken i (rnd e)                = rnd (weaken i e)
  weaken i (fin f e)              = fin f (weaken i e)
  weaken i (asInt e)              = asInt (weaken i e)
  weaken i nil                    = nil
  weaken i (cons e e₁)            = cons (weaken i e) (weaken i e₁)
  weaken i (head e)               = head (weaken i e)
  weaken i (tail e)               = tail (weaken i e)
  weaken i (if e then e₁ else e₂) = if weaken i e then weaken i e₁ else weaken i e₂

  elim : ∀ i → Term Σ Γ (insert Δ i t′) t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  elim i (lit x)                e′ = lit x
  elim i (state j)              e′ = state j
  elim i (var j)                e′ = var j
  elim i (meta j)               e′ with i Fin.≟ j
  ...                              | yes refl = Cast.type (sym (Vecₚ.insert-lookup Δ i _)) e′
  ...                              | no i≢j   = Cast.type (punchOut-insert Δ i≢j _) (meta (Fin.punchOut i≢j))
  elim i (e ≟ e₁)               e′ = elim i e e′ ≟ elim i e₁ e′
  elim i (e <? e₁)              e′ = elim i e e′ <? elim i e₁ e′
  elim i (inv e)                e′ = inv (elim i e e′)
  elim i (e && e₁)              e′ = elim i e e′ && elim i e₁ e′
  elim i (e || e₁)              e′ = elim i e e′ || elim i e₁ e′
  elim i (not e)                e′ = not (elim i e e′)
  elim i (e and e₁)             e′ = elim i e e′ and elim i e₁ e′
  elim i (e or e₁)              e′ = elim i e e′ or elim i e₁ e′
  elim i [ e ]                  e′ = [ elim i e e′ ]
  elim i (unbox e)              e′ = unbox (elim i e e′)
  elim i (merge e e₁ e₂)        e′ = merge (elim i e e′) (elim i e₁ e′) (elim i e₂ e′)
  elim i (slice e e₁)           e′ = slice (elim i e e′) (elim i e₁ e′)
  elim i (cut e e₁)             e′ = cut (elim i e e′) (elim i e₁ e′)
  elim i (cast eq e)            e′ = cast eq (elim i e e′)
  elim i (- e)                  e′ = - elim i e e′
  elim i (e + e₁)               e′ = elim i e e′ + elim i e₁ e′
  elim i (e * e₁)               e′ = elim i e e′ * elim i e₁ e′
  elim i (e ^ x)                e′ = elim i e e′ ^ x
  elim i (e >> n)               e′ = elim i e e′ >> n
  elim i (rnd e)                e′ = rnd (elim i e e′)
  elim i (fin f e)              e′ = fin f (elim i e e′)
  elim i (asInt e)              e′ = asInt (elim i e e′)
  elim i nil                    e′ = nil
  elim i (cons e e₁)            e′ = cons (elim i e e′) (elim i e₁ e′)
  elim i (head e)               e′ = head (elim i e e′)
  elim i (tail e)               e′ = tail (elim i e e′)
  elim i (if e then e₁ else e₂) e′ = if elim i e e′ then elim i e₁ e′ else elim i e₂ e′

subst : Term Σ Γ Δ t → Reference Σ Γ t′ → Term Σ Γ Δ t′ → Term Σ Γ Δ t
subst e (state i)          val = State.subst i e val
subst e (var i)            val = Var.subst i e val
subst e [ ref ]            val = subst e ref (unbox val)
subst e (unbox ref)        val = subst e ref [ val ]
subst e (merge ref ref₁ x) val = subst (subst e ref (slice val (↓ x))) ref₁ (cut val (↓ x))
subst e (slice ref x)      val = subst e ref (merge val (↓ ! cut ref x) (↓ x))
subst e (cut ref x)        val = subst e ref (merge (↓ ! slice ref x) val (↓ x))
subst e (cast eq ref)      val = subst e ref (cast (sym eq) val)
subst e nil                val = e
subst e (cons ref ref₁)    val = subst (subst e ref (head val)) ref₁ (tail val)
subst e (head ref)         val = subst e ref (cons val (↓ ! tail ref))
subst e (tail ref)         val = subst e ref (cons (↓ ! head ref) val)

module Semantics (2≉0 : 2≉0) {Σ : Vec Type i} {Γ : Vec Type j} {Δ : Vec Type k} where
  ⟦_⟧ : Term Σ Γ Δ t → ⟦ Σ ⟧ₜ′ → ⟦ Γ ⟧ₜ′ → ⟦ Δ ⟧ₜ′ → ⟦ t ⟧ₜ
  ⟦ lit x ⟧                σ γ δ = x
  ⟦ state i ⟧              σ γ δ = fetch i Σ σ
  ⟦ var i ⟧                σ γ δ = fetch i Γ γ
  ⟦ meta i ⟧               σ γ δ = fetch i Δ δ
  ⟦ e ≟ e₁ ⟧               σ γ δ = (lift ∘₂ does ∘₂ ≈-dec) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e <? e₁ ⟧              σ γ δ = (lift ∘₂ does ∘₂ <-dec) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ inv e ⟧                σ γ δ = lift ∘ Bool.not ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ e && e₁ ⟧              σ γ δ = (lift ∘₂ Bool._∧_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e || e₁ ⟧              σ γ δ = (lift ∘₂ Bool._∨_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ not e ⟧                σ γ δ = map (lift ∘ 𝔹.¬_ ∘ lower) (⟦ e ⟧ σ γ δ)
  ⟦ e and e₁ ⟧             σ γ δ = zipWith (lift ∘₂ 𝔹._∧_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e or e₁ ⟧              σ γ δ = zipWith (lift ∘₂ 𝔹._∨_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ [ e ] ⟧                σ γ δ = ⟦ e ⟧ σ γ δ ∷ []
  ⟦ unbox e ⟧              σ γ δ = Vec.head (⟦ e ⟧ σ γ δ)
  ⟦ merge e e₁ e₂ ⟧        σ γ δ = mergeVec (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ) (lower (⟦ e₂ ⟧ σ γ δ))
  ⟦ slice e e₁ ⟧           σ γ δ = sliceVec (⟦ e ⟧ σ γ δ) (lower (⟦ e₁ ⟧ σ γ δ))
  ⟦ cut e e₁ ⟧             σ γ δ = cutVec (⟦ e ⟧ σ γ δ) (lower (⟦ e₁ ⟧ σ γ δ))
  ⟦ cast eq e ⟧            σ γ δ = castVec eq (⟦ e ⟧ σ γ δ)
  ⟦ - e ⟧                  σ γ δ = neg (⟦ e ⟧ σ γ δ)
  ⟦ e + e₁ ⟧               σ γ δ = add (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e * e₁ ⟧               σ γ δ = mul (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e ^ x ⟧                σ γ δ = pow (⟦ e ⟧ σ γ δ) x
  ⟦ e >> n ⟧               σ γ δ = lift ∘ flip (shift 2≉0) n ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ rnd e ⟧                σ γ δ = lift ∘ ⌊_⌋ ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ fin {ms = ms} f e ⟧    σ γ δ = lift ∘ f ∘ lowerFin ms $ ⟦ e ⟧ σ γ δ
  ⟦ asInt e ⟧              σ γ δ = lift ∘ 𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ nil ⟧                  σ γ δ = _
  ⟦ cons {ts = ts} e e₁ ⟧  σ γ δ = cons′ ts (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ head {ts = ts} e ⟧     σ γ δ = head′ ts (⟦ e ⟧ σ γ δ)
  ⟦ tail {ts = ts} e ⟧     σ γ δ = tail′ ts (⟦ e ⟧ σ γ δ)
  ⟦ if e then e₁ else e₂ ⟧ σ γ δ = Bool.if lower (⟦ e ⟧ σ γ δ) then ⟦ e₁ ⟧ σ γ δ else ⟦ e₂ ⟧ σ γ δ
