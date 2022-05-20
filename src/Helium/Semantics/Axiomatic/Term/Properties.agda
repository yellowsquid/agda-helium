--------------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of the Term type.
--------------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Semantics.Axiomatic.Term.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
import Data.Integer as 𝕀
open import Data.Fin as Fin using (suc; punchIn)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup; insert; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Function.Nary.NonDependent using (congₙ)
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Level using (Level; _⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no)

open import Helium.Semantics.Axiomatic pseudocode
import Helium.Semantics.Core.Properties pseudocode
  as Coreₚ
open import Helium.Semantics.Denotational.Core rawPseudocode
  renaming (module Semantics to Semantics′)
import Helium.Semantics.Denotational.Properties pseudocode
  as Denₚ

private
  variable
    o k m n : ℕ
    Σ Γ Δ Σ′ Γ′ Δ′ ts : Vec Type n
    t t′ : Type

  module Semantics = Semantics′ proof-2≉0

private
  ℓ = i₁ ⊔ r₁

record RecBuilder⇒ (f : Term.RecBuilder Σ Γ Δ Σ′ Γ′ Δ′) : Set ℓ where
  private
    module f = Term.RecBuilder f
  field
    onState⇒  : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Σ′ ⟧ₜₛ
    onVar⇒    : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ
    onMeta⇒   : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ
    onState-iso : ∀ i σ γ δ → Term.⟦ f.onState i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Σ σ
    onVar-iso   : ∀ i σ γ δ → Term.⟦ f.onVar i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Γ γ
    onMeta-iso  : ∀ i σ γ δ → Term.⟦ f.onMeta i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Δ δ

  extend : ∀ {t} (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ f.extend e ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Term.⟦ e ⟧ σ γ δ
  extends : ∀ {ts : Vec Type n} (es : All (Term Σ Γ Δ) ts) σ γ δ → Term.⟦ f.extends es ⟧ₛ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Term.⟦ es ⟧ₛ σ γ δ

  extend (lit x) σ γ δ = refl
  extend (state i) σ γ δ = onState-iso i σ γ δ
  extend (var i) σ γ δ = onVar-iso i σ γ δ
  extend (meta i) σ γ δ = onMeta-iso i σ γ δ
  extend (e ≟ e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.≈-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e <? e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.<-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (inv e) σ γ δ = cong (lift ∘ Bool.not ∘ lower) (extend e σ γ δ)
  extend (e && e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∧_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e || e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∨_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (not e) σ γ δ = cong (map (lift ∘ Bool.not ∘ lower)) (extend e σ γ δ)
  extend (e and e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∧_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e or e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∨_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend [ e ] σ γ δ = cong (_∷ []) (extend e σ γ δ)
  extend (unbox e) σ γ δ = cong Vec.head (extend e σ γ δ)
  extend (merge e e₁ e₂) σ γ δ = congₙ 3 Core.mergeVec (extend e σ γ δ) (extend e₁ σ γ δ) (cong lower (extend e₂ σ γ δ))
  extend (slice e e₁) σ γ δ = cong₂ Core.sliceVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cut e e₁) σ γ δ = cong₂ Core.cutVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cast eq e) σ γ δ = cong (Core.castVec eq) (extend e σ γ δ)
  extend (- e) σ γ δ = cong Core.neg (extend e σ γ δ)
  extend (e + e₁) σ γ δ = cong₂ Core.add (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e * e₁) σ γ δ = cong₂ Core.mul (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e ^ x) σ γ δ = cong (flip Core.pow x) (extend e σ γ δ)
  extend (e >> n) σ γ δ = cong (lift ∘ flip Core.shift n ∘ lower) (extend e σ γ δ)
  extend (rnd e) σ γ δ = cong (lift ∘ ⌊_⌋ ∘ lower) (extend e σ γ δ)
  extend (fin {ms = ms} f e) σ γ δ = cong (lift ∘ f ∘ Core.lowerFin ms) (extend e σ γ δ)
  extend (asInt e) σ γ δ = cong (lift ∘ Core.𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower) (extend e σ γ δ)
  extend nil σ γ δ = refl
  extend (cons {ts = ts} e e₁) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (head {ts = ts} e) σ γ δ = cong (Core.head′ ts) (extend e σ γ δ)
  extend (tail {ts = ts} e) σ γ δ = cong (Core.tail′ ts) (extend e σ γ δ)
  extend (call f es es₁) σ γ δ = cong₂ (Semantics.fun f ∘₂ _,_) (extends es σ γ δ) (extends es₁ σ γ δ)
  extend (if e then e₁ else e₂) σ γ δ = congₙ 3 Bool.if_then_else_ (cong lower (extend e σ γ δ)) (extend e₁ σ γ δ) (extend e₂ σ γ δ)

  extends               []       σ γ δ = refl
  extends {ts = _ ∷ ts} (e ∷ es) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extends es σ γ δ)

record RecBuilder⇐ (f : Term.RecBuilder Σ Γ Δ Σ′ Γ′ Δ′) : Set ℓ where
  private
    module f = Term.RecBuilder f
  field
    onState⇐  : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ
    onVar⇐    : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ
    onMeta⇐   : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ
    onState-iso : ∀ i σ γ δ → Term.⟦ f.onState i ⟧ σ γ δ ≡ Core.fetch i Σ (onState⇐ σ γ δ)
    onVar-iso   : ∀ i σ γ δ → Term.⟦ f.onVar i ⟧ σ γ δ ≡ Core.fetch i Γ (onVar⇐ σ γ δ)
    onMeta-iso  : ∀ i σ γ δ → Term.⟦ f.onMeta i ⟧ σ γ δ ≡ Core.fetch i Δ (onMeta⇐ σ γ δ)

  extend : ∀ {t} (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ f.extend e ⟧ σ γ δ ≡ Term.⟦ e ⟧ (onState⇐ σ γ δ) (onVar⇐ σ γ δ) (onMeta⇐ σ γ δ)
  extends : ∀ {ts : Vec Type n} (es : All (Term Σ Γ Δ) ts) σ γ δ → Term.⟦ f.extends es ⟧ₛ σ γ δ ≡ Term.⟦ es ⟧ₛ (onState⇐ σ γ δ) (onVar⇐ σ γ δ) (onMeta⇐ σ γ δ)

  extend (lit x) σ γ δ = refl
  extend (state i) σ γ δ = onState-iso i σ γ δ
  extend (var i) σ γ δ = onVar-iso i σ γ δ
  extend (meta i) σ γ δ = onMeta-iso i σ γ δ
  extend (e ≟ e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.≈-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e <? e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.<-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (inv e) σ γ δ = cong (lift ∘ Bool.not ∘ lower) (extend e σ γ δ)
  extend (e && e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∧_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e || e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∨_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (not e) σ γ δ = cong (map (lift ∘ Bool.not ∘ lower)) (extend e σ γ δ)
  extend (e and e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∧_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e or e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∨_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend [ e ] σ γ δ = cong (_∷ []) (extend e σ γ δ)
  extend (unbox e) σ γ δ = cong Vec.head (extend e σ γ δ)
  extend (merge e e₁ e₂) σ γ δ = congₙ 3 Core.mergeVec (extend e σ γ δ) (extend e₁ σ γ δ) (cong lower (extend e₂ σ γ δ))
  extend (slice e e₁) σ γ δ = cong₂ Core.sliceVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cut e e₁) σ γ δ = cong₂ Core.cutVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cast eq e) σ γ δ = cong (Core.castVec eq) (extend e σ γ δ)
  extend (- e) σ γ δ = cong Core.neg (extend e σ γ δ)
  extend (e + e₁) σ γ δ = cong₂ Core.add (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e * e₁) σ γ δ = cong₂ Core.mul (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e ^ x) σ γ δ = cong (flip Core.pow x) (extend e σ γ δ)
  extend (e >> n) σ γ δ = cong (lift ∘ flip Core.shift n ∘ lower) (extend e σ γ δ)
  extend (rnd e) σ γ δ = cong (lift ∘ ⌊_⌋ ∘ lower) (extend e σ γ δ)
  extend (fin {ms = ms} f e) σ γ δ = cong (lift ∘ f ∘ Core.lowerFin ms) (extend e σ γ δ)
  extend (asInt e) σ γ δ = cong (lift ∘ Core.𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower) (extend e σ γ δ)
  extend nil σ γ δ = refl
  extend (cons {ts = ts} e e₁) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (head {ts = ts} e) σ γ δ = cong (Core.head′ ts) (extend e σ γ δ)
  extend (tail {ts = ts} e) σ γ δ = cong (Core.tail′ ts) (extend e σ γ δ)
  extend (call f es es₁) σ γ δ = cong₂ (Semantics.fun f ∘₂ _,_) (extends es σ γ δ) (extends es₁ σ γ δ)
  extend (if e then e₁ else e₂) σ γ δ = congₙ 3 Bool.if_then_else_ (cong lower (extend e σ γ δ)) (extend e₁ σ γ δ) (extend e₂ σ γ δ)

  extends               []       σ γ δ = refl
  extends {ts = _ ∷ ts} (e ∷ es) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extends es σ γ δ)

private
  module Allₚ where
    variable
      a b : Level
      A : Set a
      xs : Vec A n

    module _ {P : A → Set a} where
      lookup∘tabulate : ∀ i (f : ∀ i → P (lookup xs i)) → All.lookup i (All.tabulate {P = P} {xs = xs} f) ≡ f i
      lookup∘tabulate {xs = _ ∷ _} 0F      f = refl
      lookup∘tabulate {xs = _ ∷ _} (suc i) f = lookup∘tabulate i (f ∘ suc)

      tabulate-cong : ∀ {f g : ∀ i → P (lookup xs i)} → (∀ i → f i ≡ g i) → All.tabulate {P = P} {xs = xs} f ≡ All.tabulate g
      tabulate-cong {xs = []}     f≗g = refl
      tabulate-cong {xs = x ∷ xs} f≗g = cong₂ _∷_ (f≗g 0F) (tabulate-cong (f≗g ∘ suc))

    module _ {P : A → Set a} {Q : A → Set b} where
      tabulate-∘ : ∀ (f : ∀ {x} → P x → Q x) (g : ∀ i → P (lookup xs i)) → All.tabulate {P = Q} {xs = xs} (f ∘ g) ≡ All.map {P = P} {Q = Q} f (All.tabulate g)
      tabulate-∘ {xs = []}     f g = refl
      tabulate-∘ {xs = x ∷ xs} f g = cong (f (g 0F) ∷_) (tabulate-∘ f (g ∘ suc))

module RecBuilder where
  open Term.RecBuilder
  extends≗map : (f : Term.RecBuilder Σ Γ Δ Σ′ Γ′ Δ′) → extends f {ts = ts} ≗ All.map (extend f)
  extends≗map f []       = refl
  extends≗map f (e ∷ es) = cong (extend f e ∷_) (extends≗map f es)

module Cast where
  type : (eq : t ≡ t′) → ∀ (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ Term.Cast.type eq e ⟧ σ γ δ ≡ subst ⟦_⟧ₜ eq (Term.⟦ e ⟧ σ γ δ)
  type refl e σ γ δ = refl

module State where
  substBuilder : ∀ i (e : Term Σ Γ Δ (lookup Σ i)) → RecBuilder⇐ (Term.State.substBuilder i e)
  substBuilder {Σ = Σ} i e = record
    { onState⇐ = λ σ γ δ → Core.updateAt i Σ (Term.⟦ e ⟧ σ γ δ) σ
    ; onVar⇐   = λ σ γ δ → γ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = onState-iso
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
    open ≡-Reasoning

    onState-iso : ∀ j σ γ δ → Term.⟦ Term.RecBuilder.onState (Term.State.substBuilder i e) j ⟧ σ γ δ ≡ _
    onState-iso j σ γ δ with i Fin.≟ j
    ...                 | yes refl = sym (Coreₚ.fetch-updateAt-≡ j Σ (Term.⟦ e ⟧ σ γ δ) σ)
    ...                 | no i≢j   = sym (Coreₚ.fetch-updateAt-≢ i≢j Σ (Term.⟦ e ⟧ σ γ δ) σ)

module Var where
  weakenBuilder : ∀ i → ⟦ t ⟧ₜ → RecBuilder⇒ (Term.Var.weakenBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} {t = t} i)
  weakenBuilder {t = t} {Γ = Γ} i v = record
    { onState⇒ = λ σ γ δ → σ
    ; onVar⇒   = λ σ γ δ → Core.insert′ i Γ γ v
    ; onMeta⇒  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar⇒
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where

    onVar⇒ : ∀ j σ γ δ → _
    onVar⇒ j σ γ δ = begin
      Term.⟦ Term.Cast.type eq (var (punchIn i j)) ⟧ σ γ′ δ
        ≡⟨ Cast.type eq (var (punchIn i j)) σ γ′ δ ⟩
      subst ⟦_⟧ₜ eq (Core.fetch (punchIn i j) (insert Γ i t) γ′)
        ≡⟨ Coreₚ.fetch-punchIn Γ i t j γ v ⟩
      Core.fetch j Γ γ
        ∎
      where
      open ≡-Reasoning
      γ′ = Core.insert′ i Γ γ v
      eq = Vecₚ.insert-punchIn Γ i t j

  weakenAllBuilder : ⟦ Γ ⟧ₜₛ → RecBuilder⇒ (Term.Var.weakenAllBuilder {Σ = Σ} {Δ = Δ} {Γ = Γ})
  weakenAllBuilder γ = record
    { onState⇒ = λ σ _ δ → σ
    ; onVar⇒   = λ σ _ δ → γ
    ; onMeta⇒  = λ σ _ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ ()
    ; onMeta-iso  = λ _ _ _ _ → refl
    }

  elimAllBuilder : (es : All (Term Σ ts Δ) Γ) → RecBuilder⇐ (Term.Var.elimAllBuilder es)
  elimAllBuilder es = record
    { onState⇐ = λ σ γ δ → σ
    ; onVar⇐   = Term.⟦ es ⟧ₛ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar-iso es
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
      onVar-iso : ∀ (es : All (Term _ _ _) ts) i σ γ δ → Term.⟦ All.lookup i es ⟧ σ γ δ ≡ Core.fetch i ts (Term.⟦ es ⟧ₛ σ γ δ)
      onVar-iso {ts = _ ∷ ts} (e ∷ es) 0F      σ γ δ = sym (Coreₚ.head′-cons′ ts (Term.⟦ e ⟧ σ γ δ) (Term.⟦ es ⟧ₛ σ γ δ))
      onVar-iso {ts = _ ∷ ts} (e ∷ es) (suc i) σ γ δ = begin
        Term.⟦ All.lookup i es ⟧ σ γ δ
          ≡⟨ onVar-iso es i σ γ δ ⟩
        Core.fetch i ts (Term.⟦ es ⟧ₛ σ γ δ)
          ≡˘⟨ cong (Core.fetch i ts) (Coreₚ.tail′-cons′ ts _ _) ⟩
        Core.fetch (suc i) (_ ∷ ts) (Term.⟦ e ∷ es ⟧ₛ σ γ δ)
          ∎
        where open ≡-Reasoning

  substBuilder : ∀ i (e : Term Σ Γ Δ (lookup Γ i)) → RecBuilder⇐ (Term.Var.substBuilder i e)
  substBuilder {Γ = Γ} i e = record
    { onState⇐ = λ σ γ δ → σ
    ; onVar⇐   = λ σ γ δ → Core.updateAt i Γ (Term.⟦ e ⟧ σ γ δ) γ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar-iso
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
    open ≡-Reasoning

    onVar-iso : ∀ j σ γ δ → Term.⟦ Term.RecBuilder.onVar (Term.Var.substBuilder i e) j ⟧ σ γ δ ≡ _
    onVar-iso j σ γ δ with i Fin.≟ j
    ...               | yes refl = sym (Coreₚ.fetch-updateAt-≡ j Γ (Term.⟦ e ⟧ σ γ δ) γ)
    ...               | no i≢j   = sym (Coreₚ.fetch-updateAt-≢ i≢j Γ (Term.⟦ e ⟧ σ γ δ) γ)

module Meta where
  weakenBuilder : ∀ i → ⟦ t ⟧ₜ → RecBuilder⇒ (Term.Meta.weakenBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} {t = t} i)
  weakenBuilder {t = t} {Δ = Δ} i v = record
    { onState⇒ = λ σ γ δ → σ
    ; onVar⇒   = λ σ γ δ → γ
    ; onMeta⇒  = λ σ γ δ → Core.insert′ i Δ δ v
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = onMeta⇒
    }
    where
    onMeta⇒ : ∀ j σ γ δ → _
    onMeta⇒ j σ γ δ = begin
      Term.⟦ Term.Cast.type eq (meta (punchIn i j)) ⟧ σ γ δ′
        ≡⟨ Cast.type eq (meta (punchIn i j)) σ γ δ′ ⟩
      subst ⟦_⟧ₜ eq (Core.fetch (punchIn i j) (insert Δ i t) δ′)
        ≡⟨ Coreₚ.fetch-punchIn Δ i t j δ v ⟩
      Core.fetch j Δ δ
        ∎
      where
      open ≡-Reasoning
      δ′ = Core.insert′ i Δ δ v
      eq = Vecₚ.insert-punchIn Δ i t j

  weakenAllBuilder : ∀ (Δ′ : Vec Type k) (ts : Vec Type m) → ⟦ ts ⟧ₜₛ → RecBuilder⇒ (Term.Meta.weakenAllBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} Δ′ ts)
  weakenAllBuilder {Δ = Δ} Δ′ ts vs = record
    { onState⇒ = λ σ γ δ → σ
    ; onVar⇒   = λ σ γ δ → γ
    ; onMeta⇒  = λ σ γ δ →
      let δ′,δ = Core.split Δ′ Δ δ in
      Core.append Δ′ (ts ++ Δ) (proj₁ δ′,δ) (Core.append ts Δ vs (proj₂ δ′,δ))
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = {!!}
    }

  weaken-↓ : ∀ (Δ : Vec Type n) t′ i (e : Expression Σ Γ t) → Term.Meta.weaken {t′ = t′} i (Term.↓_ {Δ = Δ} e) ≡ Term.↓_ {Δ = insert Δ i t′} e
  weaken-↓s : ∀ (Δ : Vec Type n) t′ i (es : All (Expression Σ Γ) ts) → Term.RecBuilder.extends (Term.Meta.weakenBuilder {t = t′} i) (Term.↓s_ {Δ = Δ} es) ≡ Term.↓s_ {Δ = insert Δ i t′} es

  weaken-↓ Δ t i (lit x) = refl
  weaken-↓ Δ t i (state j) = refl
  weaken-↓ Δ t i (var j) = refl
  weaken-↓ Δ t i (e ≟ e₁) = cong₂ _≟_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (e <? e₁) = cong₂ _<?_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (inv e) = cong inv (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (e && e₁) = cong₂ _&&_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (e || e₁) = cong₂ _||_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (not e) = cong not (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (e and e₁) = cong₂ _and_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (e or e₁) = cong₂ _or_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i [ e ] = cong [_] (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (unbox e) = cong unbox (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (merge e e₁ e₂) = congₙ 3 merge (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁) (weaken-↓ Δ t i e₂)
  weaken-↓ Δ t i (slice e e₁) = cong₂ slice (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (cut e e₁) = cong₂ cut (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (cast eq e) = cong (cast eq) (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (- e) = cong -_ (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (e + e₁) = cong₂ _+_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (e * e₁) = cong₂ _*_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (e ^ x) = cong (_^ x) (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (e >> n) = cong (_>> n) (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (rnd e) = cong rnd (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (fin f e) = cong (fin f) (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (asInt e) = cong asInt (weaken-↓ Δ t i e)
  weaken-↓ Δ t i nil = refl
  weaken-↓ Δ t i (cons e e₁) = cong₂ cons (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁)
  weaken-↓ Δ t i (head e) = cong head (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (tail e) = cong tail (weaken-↓ Δ t i e)
  weaken-↓ Δ t i (call f x) = cong₂ (call f) eq (weaken-↓s Δ t i x)
    where
    open ≡-Reasoning
    wb = Term.Meta.weakenBuilder i
    eq = begin
      Term.RecBuilder.extends wb (All.tabulate state)
        ≡⟨  RecBuilder.extends≗map wb (All.tabulate state) ⟩
      All.map (Term.RecBuilder.extend wb) (All.tabulate state)
        ≡˘⟨ Allₚ.tabulate-∘ (Term.RecBuilder.extend wb) state ⟩
      All.tabulate (Term.RecBuilder.extend wb ∘ state)
        ≡⟨  Allₚ.tabulate-cong (λ _ → refl) ⟩
      All.tabulate state
        ∎
  weaken-↓ Δ t i (if e then e₁ else e₂) = congₙ 3 if_then_else_ (weaken-↓ Δ t i e) (weaken-↓ Δ t i e₁) (weaken-↓ Δ t i e₂)

  weaken-↓s Δ t i []       = refl
  weaken-↓s Δ t i (e ∷ es) = cong₂ _∷_ (weaken-↓ Δ t i e) (weaken-↓s Δ t i es)

  elimBuilder : ∀ i (e : Term Σ Γ Δ t) → RecBuilder⇐ (Term.Meta.elimBuilder i e)
  elimBuilder {Δ = Δ} {t = t} i e = record
    { onState⇐ = λ σ γ δ → σ
    ; onVar⇐   = λ σ γ δ → γ
    ; onMeta⇐  = λ σ γ δ → Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ)
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = onMeta-iso
    }
    where
    open ≡-Reasoning
    onMeta-iso : ∀ j σ γ δ → Term.⟦ Term.RecBuilder.onMeta (Term.Meta.elimBuilder i e) j ⟧ σ γ δ ≡ Core.fetch j (insert Δ i t) (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ))
    onMeta-iso j σ γ δ with i Fin.≟ j
    ... | yes refl = begin
      Term.⟦ Term.Cast.type (sym (Vecₚ.insert-lookup Δ i t)) e ⟧ σ γ δ
        ≡⟨  Cast.type (sym (Vecₚ.insert-lookup Δ i t)) e σ γ δ ⟩
      subst ⟦_⟧ₜ (sym (Vecₚ.insert-lookup Δ i t)) (Term.⟦ e ⟧ σ γ δ)
        ≡˘⟨ cong (subst ⟦_⟧ₜ (sym (Vecₚ.insert-lookup Δ i t))) (Coreₚ.fetch-insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ)) ⟩
      subst ⟦_⟧ₜ (sym (Vecₚ.insert-lookup Δ i t)) (subst ⟦_⟧ₜ (Vecₚ.insert-lookup Δ i t) (Core.fetch i (insert Δ i t) (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ))))
        ≡⟨  subst-sym-subst (Vecₚ.insert-lookup Δ i t) ⟩
      Core.fetch i (insert Δ i t) (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ))
        ∎
    ... | no i≢j   = begin
      Term.⟦ Term.Cast.type (Core.punchOut-insert Δ i≢j t) (meta _) ⟧ σ γ δ
        ≡⟨  Cast.type (Core.punchOut-insert Δ i≢j t) (meta _) σ γ δ ⟩
      subst ⟦_⟧ₜ (Core.punchOut-insert Δ i≢j t) (Core.fetch (Fin.punchOut i≢j) Δ δ)
        ≡˘⟨ Coreₚ.fetch-punchOut i≢j Δ δ (Term.⟦ e ⟧ σ γ δ) ⟩
      Core.fetch j (insert Δ i t) (Core.insert′ i Δ δ (Term.⟦ e ⟧ σ γ δ))
        ∎

import Helium.Semantics.Denotational.Core rawPseudocode as Den′
  renaming (module Semantics to Semantics′)

private
  module Den where
    open Den′ hiding (module Semantics′)
    module Sem = Den′.Semantics′ proof-2≉0

⟦⟧ₛ-pointwise : ∀ (es : All (Term Σ Γ Δ) ts) (vs : ⟦ ts ⟧ₜₛ) σ γ δ → (∀ i → Term.⟦ All.lookup i es ⟧ σ γ δ ≡ Core.fetch i ts vs) → Term.⟦ es ⟧ₛ σ γ δ ≡ vs
⟦⟧ₛ-pointwise               []       vs σ γ δ point-≡ = refl
⟦⟧ₛ-pointwise {ts = _ ∷ ts} (e ∷ es) vs σ γ δ point-≡ = begin
  Core.cons′ ts (Term.⟦ e ⟧ σ γ δ) (Term.⟦ es ⟧ₛ σ γ δ) ≡⟨ cong₂ (Core.cons′ ts) (point-≡ 0F) (⟦⟧ₛ-pointwise es (Core.tail′ ts vs) σ γ δ (point-≡ ∘ suc)) ⟩
  Core.cons′ ts (Core.head′ ts vs) (Core.tail′ ts vs)   ≡⟨ Coreₚ.cons′-head′-tail′ ts vs ⟩
  vs                                                    ∎
  where open ≡-Reasoning

module Soundness where
  ↓-homo : ∀ (e : Expression Σ Γ t) σ γ (δ : ⟦ Δ ⟧ₜₛ) → Term.⟦ ↓_ {Δ = Δ} e ⟧ σ γ δ ≡ Semantics.expr e (σ , γ)
  ↓s-homo : ∀ (es : All (Expression Σ Γ) ts) σ γ (δ : ⟦ Δ ⟧ₜₛ) → Term.⟦ ↓s_ {Δ = Δ} es ⟧ₛ σ γ δ ≡ Semantics.exprs es (σ , γ)

  ↓-homo (lit x)                σ γ δ = refl
  ↓-homo (state i)              σ γ δ = refl
  ↓-homo (var i)                σ γ δ = refl
  ↓-homo (_≟_ e e₁)             σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.≈-dec) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (e <? e₁)              σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.<-dec) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (inv e)                σ γ δ = cong (lift ∘ Bool.not ∘ lower) (↓-homo e σ γ δ)
  ↓-homo (e && e₁)              σ γ δ = cong₂ (lift ∘₂ Bool._∧_ on lower) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (e || e₁)              σ γ δ = cong₂ (lift ∘₂ Bool._∨_ on lower) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (not e)                σ γ δ = cong (map (lift ∘ Bool.not ∘ lower)) (↓-homo e σ γ δ)
  ↓-homo (e and e₁)             σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∧_ on lower)) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (e or e₁)              σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∨_ on lower)) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo [ e ]                  σ γ δ = cong (_∷ []) (↓-homo e σ γ δ)
  ↓-homo (unbox e)              σ γ δ = cong Vec.head (↓-homo e σ γ δ)
  ↓-homo (merge e e₁ e₂)        σ γ δ = congₙ 3 Core.mergeVec (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ) (cong lower (↓-homo e₂ σ γ δ))
  ↓-homo (slice e e₁)           σ γ δ = cong₂ Core.sliceVec (↓-homo e σ γ δ) (cong lower (↓-homo e₁ σ γ δ))
  ↓-homo (cut e e₁)             σ γ δ = cong₂ Core.cutVec (↓-homo e σ γ δ) (cong lower (↓-homo e₁ σ γ δ))
  ↓-homo (cast eq e)            σ γ δ = cong (Core.castVec eq) (↓-homo e σ γ δ)
  ↓-homo (- e)                  σ γ δ = cong Core.neg (↓-homo e σ γ δ)
  ↓-homo (e + e₁)               σ γ δ = cong₂ Core.add (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (e * e₁)               σ γ δ = cong₂ Core.mul (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (e ^ x)                σ γ δ = cong (flip Core.pow x) (↓-homo e σ γ δ)
  ↓-homo (e >> n)               σ γ δ = cong (lift ∘ flip Core.shift n ∘ lower) (↓-homo e σ γ δ)
  ↓-homo (rnd e)                σ γ δ = cong (lift ∘ ⌊_⌋ ∘ lower) (↓-homo e σ γ δ)
  ↓-homo (fin {ms = ms} f e)    σ γ δ = cong (lift ∘ f ∘ Core.lowerFin ms) (↓-homo e σ γ δ)
  ↓-homo (asInt e)              σ γ δ = cong (lift ∘ Core.𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower) (↓-homo e σ γ δ)
  ↓-homo nil                    σ γ δ = refl
  ↓-homo (cons {ts = ts} e e₁)  σ γ δ = cong₂ (Core.cons′ ts) (↓-homo e σ γ δ) (↓-homo e₁ σ γ δ)
  ↓-homo (head {ts = ts} e)     σ γ δ = cong (Core.head′ ts) (↓-homo e σ γ δ)
  ↓-homo (tail {ts = ts} e)     σ γ δ = cong (Core.tail′ ts) (↓-homo e σ γ δ)
  ↓-homo {Σ = Σ} (call f es)    σ γ δ = cong₂ (Semantics.fun f ∘₂ _,_) (⟦⟧ₛ-pointwise (All.tabulate {xs = Σ} state) σ σ γ δ (λ i → cong (λ t → Term.⟦ t ⟧ σ γ δ) (Allₚ.lookup∘tabulate i state))) (↓s-homo es σ γ δ)
  ↓-homo (if e then e₁ else e₂) σ γ δ = congₙ 3 Bool.if_then_else_ (cong lower (↓-homo e σ γ δ)) (↓-homo e₁ σ γ δ) (↓-homo e₂ σ γ δ)

  ↓s-homo []            σ γ δ = refl
  ↓s-homo (e ∷ [])      σ γ δ = ↓-homo e σ γ δ
  ↓s-homo (e ∷ e₁ ∷ es) σ γ δ = cong₂ _,_ (↓-homo e σ γ δ) (↓s-homo (e₁ ∷ es) σ γ δ)

  subst-sound : ∀ (t : Term Σ Γ Δ t) (ref : Reference Σ Γ t′) val σ γ δ → Term.⟦ Term.subst t ref (Term.↓ val) ⟧ σ γ δ ≡ uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Den.Sem.expr val (σ , γ)) (σ , γ)) δ
  subst-sound {Σ = Σ} t (state i)    val σ γ δ = subst (λ v → Term.⟦ Term.State.subst i t (Term.↓ val) ⟧ σ γ δ ≡ Term.⟦ t ⟧ (Core.updateAt i Σ v σ) γ δ) (↓-homo val σ γ δ) (RecBuilder⇐.extend (State.substBuilder i (↓ val)) t σ γ δ)
  subst-sound {Γ = Γ} t (var i)      val σ γ δ = subst (λ v → Term.⟦ Term.Var.subst i t (Term.↓ val) ⟧ σ γ δ ≡ Term.⟦ t ⟧ σ (Core.updateAt i Γ v γ) δ) (↓-homo val σ γ δ) (RecBuilder⇐.extend (Var.substBuilder i (↓ val)) t σ γ δ)
  subst-sound t [ ref ]              val σ γ δ = subst-sound t ref (unbox val) σ γ δ
  subst-sound t (unbox ref)          val σ γ δ = subst-sound t ref [ val ] σ γ δ
  subst-sound t (slice ref e)        val σ γ δ = begin
    Term.⟦ Term.subst t ref (↓ merge val (! cut ref e) e) ⟧ σ γ δ
      ≡⟨ subst-sound t ref (merge val (! cut ref e) e) σ γ δ ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec (Den.Sem.expr val (σ , γ)) (Den.Sem.expr (! cut ref e) (σ , γ)) (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ
      ≡⟨ cong (λ v → uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec (Den.Sem.expr val (σ , γ)) v (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ)
           (Denₚ.!-homo-⟦⟧ (cut ref e) (σ , γ)) ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec (Den.Sem.expr val (σ , γ)) (Den.Sem.ref (cut ref e) (σ , γ)) (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ
      ∎
    where open ≡-Reasoning
  subst-sound t (cut ref e)          val σ γ δ = begin
    Term.⟦ Term.subst t ref (↓ merge (! slice ref e) val e) ⟧ σ γ δ
      ≡⟨ subst-sound t ref (merge (! slice ref e) val e) σ γ δ ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec (Den.Sem.expr (! slice ref e) (σ , γ)) (Den.Sem.expr val (σ , γ)) (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ
      ≡⟨ cong (λ v → uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec v (Den.Sem.expr val (σ , γ)) (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ)
           (Denₚ.!-homo-⟦⟧ (slice ref e) (σ , γ)) ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.mergeVec (Den.Sem.ref (slice ref e) (σ , γ)) (Den.Sem.expr val (σ , γ)) (lower (Den.Sem.expr e (σ , γ)))) (σ , γ)) δ
      ∎
    where open ≡-Reasoning
  subst-sound t (cast eq ref)        val σ γ δ = subst-sound t ref (cast (sym eq) val) σ γ δ
  subst-sound t (head {ts = ts} ref) val σ γ δ = begin
    Term.⟦ Term.subst t ref (↓ cons val (! tail ref)) ⟧ σ γ δ
      ≡⟨ subst-sound t ref (cons val (! tail ref)) σ γ δ ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Den.Sem.expr (cons val (! tail ref)) (σ , γ)) (σ , γ)) δ
      ≡⟨ cong (λ v → uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.cons′ ts _ v) (σ , γ)) δ)
           (Denₚ.!-homo-⟦⟧ (tail ref) (σ , γ)) ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.cons′ ts (Den.Sem.expr val (σ , γ)) (Den.Sem.ref (tail ref) (σ , γ))) (σ , γ)) δ
      ∎
    where open ≡-Reasoning
  subst-sound t (tail {ts = ts} ref) val σ γ δ = begin
    Term.⟦ Term.subst t ref (↓ cons (! head ref) val) ⟧ σ γ δ
      ≡⟨ subst-sound t ref (cons (! head ref) val) σ γ δ ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Den.Sem.expr (cons (! head ref) val) (σ , γ)) (σ , γ)) δ
      ≡⟨ cong (λ v → uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.cons′ ts v _) (σ , γ)) δ)
           (Denₚ.!-homo-⟦⟧ (head ref) (σ , γ)) ⟩
    uncurry Term.⟦ t ⟧ (Den.Sem.assign ref (Core.cons′ ts (Den.Sem.ref (head ref) (σ , γ)) (Den.Sem.expr val (σ , γ))) (σ , γ)) δ
      ∎
    where open ≡-Reasoning
