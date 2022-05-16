------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of the Hoare logic semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Semantics.Axiomatic.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
import Data.Fin.Properties as Finₚ
import Data.Integer as 𝕀
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; map; zipWith; replicate)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
import Data.Vec.Properties as Vecₚ
open import Function using (_∘_; _∘₂_; _$_; id; flip; _on_)
open import Function.Nary.NonDependent using (congₙ)

open import Data.Fin as Fin using (Fin; suc; fromℕ; inject₁)
open import Data.Fin.Patterns
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; uncurry; map₂; <_,_>)
import Data.Sum as ⊎
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core hiding (_∶_)
open import Helium.Semantics.Axiomatic pseudocode
import Helium.Semantics.Axiomatic.Assertion.Properties pseudocode as Assertionₚ
import Helium.Semantics.Axiomatic.Term.Properties pseudocode as Termₚ
import Helium.Semantics.Core.Properties pseudocode as Coreₚ
open import Helium.Semantics.Denotational.Core rawPseudocode
  renaming (module Semantics to Semantics′)
open import Level using (_⊔_; Lift; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)

private
  variable
    o k m n : ℕ
    Σ Γ Δ Σ′ Γ′ Δ′ ts : Vec Type n
    t t′ : Type
    P Q : Assertion Σ Γ Δ
    s : Statement Σ Γ

  module Semantics = Semantics′ proof-2≉0
  ℓ = i₁ ⊔ r₁

sound : ∀ {P Q : Assertion Σ Γ Δ} → P ⊢ s ⊢ Q → ∀ σ γ δ → Assertion.⟦ P ⟧ σ γ δ → uncurry Assertion.⟦ Q ⟧ (Semantics.stmt s (σ , γ)) δ
sound (seq {s = s} Q p p₁) σ γ δ inP = uncurry (sound p₁) (Semantics.stmt s (σ , γ)) δ (sound p σ γ δ inP)
sound (skip (arr imp))     σ γ δ inP = imp σ γ δ inP
sound {Q = Q} (assign {ref = ref} {val = val} (arr imp))   σ γ δ inP = Assertionₚ.Soundness.subst⇒ Q ref val σ γ δ $ imp σ γ δ inP
sound {Γ = Γ} {Δ = Δ} {P = P} {Q} (declare {e = e} {s = s} p) σ γ δ inP =
  Assertionₚ.Var.weaken⇒ 0F _ (Core.head′ Γ γ′) Q σ′ (Core.tail′ Γ γ′) δ $
  subst
    (λ γ′ → Assertion.⟦ Assertion.Var.weaken 0F Q ⟧ σ′ γ′ δ)
    (sym (Coreₚ.cons′-head′-tail′ Γ γ′)) $
  sound p σ (Core.cons′ Γ ⟦e⟧ γ) δ
    ( Assertionₚ.Var.weaken⇐ 0F _ ⟦e⟧ P σ γ δ inP
    , Assertionₚ.Construct.equal-refl
        (var 0F) (Term.Var.weaken 0F (↓ e))
        σ (Core.cons′ Γ ⟦e⟧ γ) δ
        eq
    )
  where
  open ≡-Reasoning
  ⟦e⟧ = Semantics.expr e (σ , γ)
  σ′,γ′ = Semantics.stmt s (σ , Core.cons′ Γ ⟦e⟧ γ)

  σ′ = ×.proj₁ σ′,γ′
  γ′ = ×.proj₂ σ′,γ′

  eq = begin
    Core.head′ Γ (Core.cons′ Γ ⟦e⟧ γ)
      ≡⟨  Coreₚ.head′-cons′ Γ ⟦e⟧ γ ⟩
    Semantics.expr e (σ , γ)
      ≡˘⟨ Termₚ.Soundness.↓-homo e σ γ δ ⟩
    Term.⟦ ↓_ {Δ = Δ} e ⟧ σ γ δ
      ≡˘⟨ Termₚ.RecBuilder⇒.extend (Termₚ.Var.weakenBuilder 0F ⟦e⟧) (↓ e) σ γ δ ⟩
    Term.⟦ Term.Var.weaken 0F (↓ e) ⟧ σ (Core.cons′ Γ ⟦e⟧ γ) δ
      ∎
sound (invoke p)           σ γ δ inP = {!!}
sound {Δ = Δ} (if {e = e} p (arr imp)) σ γ δ inP with Term.⟦ ↓_ {Δ = Δ} e ⟧ σ γ δ | Semantics.expr e (σ , γ) | Termₚ.Soundness.↓-homo {Δ = Δ} e σ γ δ | sound p σ γ δ  | imp σ γ δ
... | lift Bool.true  | .(lift Bool.true)  | refl | f | g = f (inP , _)
... | lift Bool.false | .(lift Bool.false) | refl | f | g = g (inP , _)
sound {Δ = Δ} (if-else {e = e} p p₁) σ γ δ inP with Term.⟦ ↓_ {Δ = Δ} e ⟧ σ γ δ | Semantics.expr e (σ , γ) | Termₚ.Soundness.↓-homo {Δ = Δ} e σ γ δ | sound p σ γ δ  | sound p₁ σ γ δ
... | lift Bool.true  | .(lift Bool.true)  | refl | f | g = f (inP , _)
... | lift Bool.false | .(lift Bool.false) | refl | f | g = g (inP , _)
sound {Σ = Σ} {Γ = Γ} {Δ = Δ} (for {m = m} {s = s} I (arr imp) p (arr imp₁)) σ γ δ inP =
  imp₁ σᶠ γᶠ δ $
  Assertionₚ.Meta.elim⇐ 0F (Term.↓ lit (fromℕ m)) I σᶠ γᶠ δ $
  subst (λ (f : _ → _) → uncurry Assertion.⟦ I ⟧ (f (σ , γ)) (Core.insert′ 0F Δ δ (lift (fromℕ m)))) (subst-independent (sym (Finₚ.toℕ-fromℕ m))) $
  loop $
  Assertionₚ.Meta.elim⇒ 0F (Term.↓ lit 0F) I σ γ δ $
  imp σ γ δ inP
  where
  σᶠ,γᶠ = Semantics.stmt (for m s) (σ , γ)
  σᶠ = ×.proj₁ σᶠ,γᶠ
  γᶠ = ×.proj₂ σᶠ,γᶠ

  foldl⁺ : ∀ {a b c} {A : Set a} (B : ℕ → Set b) {m} →
           (P : ∀ {i : Fin (suc m)} → B (Fin.toℕ i) → Set c) →
           (f : ∀ {n} → B n → A → B (suc n)) →
           (y : B 0) →
           (xs : Vec A m) →
           (∀ {i} {x} → P {Fin.inject₁ i} x → P {suc i} (subst B (Finₚ.toℕ-inject₁ (suc i)) (f x (Vec.lookup xs i)))) →
           P {0F} y →
           P {Fin.fromℕ m} (subst B (sym (Finₚ.toℕ-fromℕ m)) (Vec.foldl B f y xs))
  foldl⁺ B             P f y []       step base = base
  foldl⁺ B {m = suc m} P f y (x ∷ xs) step base = subst P eq₁ (foldl⁺ (B ∘ suc) (λ {i} → P {suc i}) f (f y x) xs (λ {i} {x} Px → subst (P {suc (suc i)}) eq₂ (step Px)) (step base))
    where
    eq₁ = begin
      subst (B ∘ suc) (sym (Finₚ.toℕ-fromℕ m)) v    ≡⟨  subst-∘ (sym (Finₚ.toℕ-fromℕ m)) ⟩
      subst B (cong suc (sym (Finₚ.toℕ-fromℕ m))) v ≡˘⟨ cong (flip (subst B) v) (sym-cong (Finₚ.toℕ-fromℕ m)) ⟩
      subst B (sym (Finₚ.toℕ-fromℕ (suc m))) v      ∎
      where
      open ≡-Reasoning
      v = Vec.foldl (B ∘ suc) f (f y x) xs
      sym-cong : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {x y : A} → (x≡y : x ≡ y) → sym (cong f x≡y) ≡ cong f (sym x≡y)
      sym-cong refl = refl

    eq₂ : ∀ {i : Fin _} {x : B (suc (Fin.toℕ (Fin.inject₁ i)))} → subst B (cong suc (cong suc (Finₚ.toℕ-inject₁ i))) (f x (Vec.lookup xs i)) ≡ subst (B ∘ suc) (cong suc (Finₚ.toℕ-inject₁ i)) (f x (Vec.lookup xs i))
    eq₂ {i} = sym (subst-∘ (Finₚ.toℕ-inject₁ (suc i)))

  subst-independent : ∀ {a b} {A : Set a} {B : Set b} {x y : A} → (x≡y : x ≡ y) {v : B} → subst (λ _ → B) x≡y v ≡ v
  subst-independent refl = refl

  step : (⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ) → Fin m → (⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ)
  step = flip λ i → (< proj₁ , Core.tail′ Γ ∘ proj₂ > ∘ Semantics.stmt s ∘ < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ >) ∘_

  loop-pred : ∀ {i : Fin (suc m)} (f : ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ) → Set _
  loop-pred {i} f = uncurry Assertion.⟦ I ⟧ (f (σ , γ)) (Core.cons′ Δ (lift i) δ)

  step-deriv : ∀ {i : Fin m} {f} → loop-pred f → loop-pred (subst {A = ℕ} (λ _ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ) (Finₚ.toℕ-inject₁ (suc i)) (step f (Vec.lookup (Vec.allFin m) i)))
  step-deriv {i} {f} inI =
       inI  ∶ uncurry Assertion.⟦ I ⟧ (f (σ , γ)) (Core.cons′ Δ (lift (inject₁ i)) δ)
    |> uncurry
         (Assertionₚ.Meta.weaken⇐ 0F (fin m) (lift i) I)
         (f (σ , γ))
         (Core.cons′ Δ (lift (inject₁ i)) δ)
       ∶ uncurry
           Assertion.⟦ Assertion.Meta.weaken 0F I ⟧
           (f (σ , γ))
           (Core.cons′ {t = fin m} (fin (suc m) ∷ Δ) (lift i) (Core.cons′ Δ (lift (inject₁ i)) δ))
    |> subst
         (uncurry Assertion.⟦ Assertion.Meta.weaken 0F I ⟧ (f (σ , γ)))
         (sym $ trans
           (cong
             (Core.insert′ 1F (fin m ∷ Δ) (Core.cons′ Δ (lift i) δ) ∘
              lift ∘
              inject₁ ∘
              lower)
             (Coreₚ.head′-cons′ Δ (lift i) δ))
           (insert-1-cons Δ (lift i) (lift (inject₁ i)) δ))
       ∶ uncurry
           Assertion.⟦ Assertion.Meta.weaken 0F I ⟧
           (f (σ , γ))
           (Core.insert′ 1F (fin m ∷ Δ)
             (Core.cons′ Δ (lift i) δ)
             (lift ∘ inject₁ ∘ lower ∘ Core.fetch 0F (fin m ∷ Δ) $
              Core.cons′ Δ (lift i) δ))
    |> uncurry
         (Assertionₚ.Meta.elim⇐ 1F (fin inject₁ (cons (meta 0F) nil)) ∘
          Assertion.Meta.weaken 0F $
          I)
         (f (σ , γ))
         (Core.cons′ Δ (lift i) δ)
       ∶ uncurry
           Assertion.⟦ flip (Assertion.Meta.elim {Δ = fin m ∷ Δ} 1F) (fin inject₁ (cons (meta 0F) nil)) ∘
                       Assertion.Meta.weaken 0F $
                       I
                     ⟧
           (f (σ , γ))
           (Core.cons′ Δ (lift i) δ)
    |> uncurry
         (Assertionₚ.Var.weaken⇐ 0F (fin m) (lift i) ∘
          flip (Assertion.Meta.elim 1F) (fin inject₁ (cons (meta 0F) nil)) ∘
          Assertion.Meta.weaken 0F $
          I)
         (f (σ , γ))
         (Core.cons′ Δ (lift i) δ)
       ∶ uncurry
           Assertion.⟦ Assertion.Var.weaken 0F ∘
                       flip (Assertion.Meta.elim {Δ = fin m ∷ Δ} 1F) (fin inject₁ (cons (meta 0F) nil)) ∘
                       Assertion.Meta.weaken 0F $
                       I ⟧
           (< proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $ (f (σ , γ)))
           (Core.cons′ Δ (lift i) δ)
    |> _, uncurry
          (Assertionₚ.Construct.equal-refl {Σ = Σ} {Γ = fin m ∷ Γ} {Δ = fin m ∷ Δ} {t = fin m} (meta 0F) (var 0F))
          (< proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $ (f (σ , γ)))
          (Core.cons′ Δ (lift i) δ)
          (trans (Coreₚ.head′-cons′ Δ (lift i) δ) (sym $ Coreₚ.head′-cons′ Γ (lift i) (proj₂ (f (σ , γ)))))
       ∶ uncurry
           Assertion.⟦
             ( Assertion.Var.weaken 0F ∘
               flip (Assertion.Meta.elim {Δ = fin m ∷ Δ} 1F) (fin inject₁ (cons (meta 0F) nil)) ∘
               Assertion.Meta.weaken 0F $
               I
             ) ∧ equal (meta 0F) (var 0F) ⟧
           (< proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $ (f (σ , γ)))
           (Core.cons′ Δ (lift i) δ)
    |> uncurry
         (sound p)
         (< proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $ (f (σ , γ)))
         (Core.cons′ Δ (lift i) δ)
        ∶ uncurry
            Assertion.⟦ Assertion.Var.weaken 0F ∘
                        flip (Assertion.Meta.elim 1F) (fin suc (cons (meta 0F) nil)) ∘
                        Assertion.Meta.weaken 0F $
                        I ⟧
            (Semantics.stmt s ∘ < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $ (f (σ , γ)))
            (Core.cons′ Δ (lift i) δ)
    |> subst
         (flip
           (uncurry
              Assertion.⟦ Assertion.Var.weaken 0F ∘
                          flip (Assertion.Meta.elim 1F) (fin suc (cons (meta 0F) nil)) ∘
                          Assertion.Meta.weaken 0F $
                          I ⟧ )
           (Core.cons′ Δ (lift i) δ))
         (cong
            ((proj₁ ∘
              Semantics.stmt s ∘
              < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $
              (f (σ , γ)))
             ,_) ∘
          sym ∘
          Coreₚ.cons′-head′-tail′ Γ $
          (proj₂ ∘
           Semantics.stmt s ∘
           < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $
           (f (σ , γ))))
       ∶ uncurry
           Assertion.⟦ Assertion.Var.weaken 0F ∘
                       flip (Assertion.Meta.elim 1F) (fin suc (cons (meta 0F) nil)) ∘
                       Assertion.Meta.weaken 0F $
                       I ⟧
           ( < proj₁ , uncurry (Core.cons′ Γ) ∘ < Core.head′ Γ , Core.tail′ Γ > ∘ proj₂ > ∘
             Semantics.stmt s ∘
             < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $
             (f (σ , γ)) )
           (Core.cons′ Δ (lift i) δ)
    |> uncurry
         (Assertionₚ.Var.weaken⇒ 0F (fin m)
            (Core.head′ Γ ∘
             proj₂ ∘
             Semantics.stmt s ∘
             < proj₁ , Core.cons′ Γ (lift i) ∘ proj₂ > $
             (f (σ , γ))) ∘
          flip (Assertion.Meta.elim 1F) (fin suc (cons (meta 0F) nil)) ∘
          Assertion.Meta.weaken 0F $
          I)
         (step f i (σ , γ))
         (Core.cons′ Δ (lift i) δ)
       ∶ uncurry
           Assertion.⟦ flip (Assertion.Meta.elim 1F) (fin suc (cons (meta 0F) nil)) ∘
                       Assertion.Meta.weaken 0F $
                       I ⟧
           (step f i (σ , γ))
           (Core.cons′ Δ (lift i) δ)
    |> uncurry
         (Assertionₚ.Meta.elim⇒ 1F (fin suc (cons (meta 0F) nil)) ∘
          Assertion.Meta.weaken 0F
          $ I)
         (step f i (σ , γ))
         (Core.cons′ Δ (lift i) δ)
       ∶ uncurry
           Assertion.⟦ Assertion.Meta.weaken 0F I ⟧
           (step f i (σ , γ))
           (Core.insert′ 1F (fin m ∷ Δ) (Core.cons′ Δ (lift i) δ) (lift ∘ Fin.suc ∘ lower ∘ Core.head′ {t = fin m} Δ $ (Core.cons′ Δ (lift i) δ)))
    |> subst
         (uncurry
            Assertion.⟦ Assertion.Meta.weaken 0F I ⟧
            (step f i (σ , γ)))
         (trans
           (cong
             (Core.insert′ 1F (fin m ∷ Δ) (Core.cons′ Δ (lift i) δ) ∘ lift ∘ suc ∘ lower)
             (Coreₚ.head′-cons′ Δ (lift i) δ))
           (insert-1-cons Δ (lift i) (lift (suc i)) δ))
       ∶ uncurry
           Assertion.⟦ Assertion.Meta.weaken 0F I ⟧
           (step f i (σ , γ))
           (Core.cons′ {t = fin m} (fin (suc m) ∷ Δ) (lift i) (Core.cons′ Δ (lift (suc i)) δ))
    |> uncurry
         (Assertionₚ.Meta.weaken⇒ 0F (fin m) (lift i) I)
         (step f i (σ , γ))
         (Core.cons′ Δ (lift (suc i)) δ)
       ∶ uncurry
           Assertion.⟦ I ⟧
           (step f i (σ , γ))
           (Core.cons′ Δ (lift (suc i)) δ)
    |> subst
         (flip (uncurry Assertion.⟦ I ⟧) (Core.cons′ Δ (lift (suc i)) δ) ∘ (σ , γ |>_))
         (trans
           (cong (step f) (sym (Vecₚ.lookup-allFin i)))
           (sym (subst-independent (Finₚ.toℕ-inject₁ (suc i)))))
       ∶ uncurry
           Assertion.⟦ I ⟧
           ((subst {A = ℕ} (λ _ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ) (Finₚ.toℕ-inject₁ (suc i)) (step f (Vec.lookup (Vec.allFin m) i))) (σ , γ))
           (Core.cons′ Δ (lift (suc i)) δ)
    where
    open import Function.Reasoning
    insert-1-cons : ∀ (ts : Vec Type n) (v : ⟦ t ⟧ₜ) (v′ : ⟦ t′ ⟧ₜ) (vs : ⟦ ts ⟧ₜₛ) →
                    Core.insert′ 1F (t ∷ ts) (Core.cons′ ts v vs) v′ ≡
                    Core.cons′ {t = t} (t′ ∷ ts) v (Core.cons′ ts v′ vs)
    insert-1-cons ts v v′ vs = cong₂ _,_ (Coreₚ.head′-cons′ ts v vs) (cong (Core.cons′ ts v′) (Coreₚ.tail′-cons′ ts v vs))

  loop : Assertion.⟦ I ⟧ σ γ (Core.insert′ 0F Δ δ (lift 0F)) → uncurry Assertion.⟦ I ⟧ ((subst (λ _ → _ → _) (sym (Finₚ.toℕ-fromℕ m)) (Semantics.stmt (for m s))) (σ , γ)) (Core.insert′ 0F Δ δ (lift (fromℕ m)))
  loop = foldl⁺ _ (λ {i} → loop-pred {i}) step id (Vec.allFin m) (λ {i x} → step-deriv {i} {x})
