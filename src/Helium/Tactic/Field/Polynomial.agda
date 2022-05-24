open import Helium.Algebra.Bundles using (RawField)

module Helium.Tactic.Field.Polynomial
  {ℓ₁ ℓ₂}
  (F : RawField ℓ₁ ℓ₂)
  where

open import Algebra
open import Data.Bool
open import Data.Empty using (⊥-elim)
open import Data.Integer hiding (_⊔_)
import Data.Integer.Properties as ℤₚ
open import Data.List as List hiding ([_]; merge; head; last)
open import Data.List.NonEmpty hiding (concatMap; flatten)
import Data.List.Properties as Listₚ
import Data.List.Relation.Binary.Pointwise as ListPw
open import Data.List.Relation.Unary.All hiding (toList; head)
open import Data.List.Relation.Unary.Linked as Linked hiding (head)
open import Data.List.Relation.Unary.Sorted.TotalOrder renaming (Sorted to Sorted′) hiding (head)
open import Data.Nat hiding (_⊔_)
open import Data.Product
import Data.Product.Properties as Productₚ
open import Data.Product.Relation.Binary.Pointwise.NonDependent renaming (Pointwise to ×-Pw)
import Data.Vec.Relation.Binary.Lex.Strict as Lex
open import Data.Vec using (Vec)
import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPw
open import Function
open import Helium.Tactic.Field.Sorted hiding (head)
open import Level
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

private
  module F = RawField F
  open F using () renaming (Carrier to A)

  variable
    n : ℕ

Term : ℕ → Set ℓ₁
Term n = Vec ℤ n × A

SortedTerms : List (Term n) → Set ℓ₁
SortedTerms = Sorted (On.strictTotalOrder (Lex.<-strictTotalOrder ℤₚ.<-strictTotalOrder _) proj₁)

NearlySortedTerms : List (Term n) → Set ℓ₁
NearlySortedTerms = Sorted′ (On.totalOrder (Lex.≤-totalOrder ℤₚ.<-strictTotalOrder _) proj₁)

record Polynomial (n : ℕ) : Set ℓ₁ where
  constructor _,_
  field
    terms  : List (Term n)
    sorted : SortedTerms terms

open Polynomial

record NearPolynomial (n : ℕ) : Set ℓ₁ where
  constructor _,_
  field
    terms  : List (Term n)
    sorted : NearlySortedTerms terms

private
  module Term {n} where
    strictTotalOrder = On.strictTotalOrder (Lex.<-strictTotalOrder ℤₚ.<-strictTotalOrder n) (proj₁ {B = λ _ → A})
    open StrictTotalOrder strictTotalOrder public

_≋_ : Rel (Polynomial n) (ℓ₁ ⊔ ℓ₂)
_≋_ = ListPw.Pointwise (×-Pw (VecPw.Pointwise _≡_) F._≈_) on terms

-- Collects terms with equal coefficients
group : List (Term n) → List (List⁺ (Term n))
group []           = []
group (x ∷ [])     = [ x ] ∷ []
group (x ∷ y ∷ xs) with does (x Term.≟ y) | group (y ∷ xs)
... | true  | []          = []             -- impossible
... | true  | ys ∷ groups = (x ∷⁺ ys) ∷ groups
... | false | groups      = [ x ] ∷ groups

group-concat : ∀ (xs : List (Term n)) → concatMap toList (group xs) ≡ xs
group-concat []       = refl
group-concat (x ∷ []) = refl
group-concat (x ∷ y ∷ xs) with does (x Term.≟ y) | group (y ∷ xs) | group-concat (y ∷ xs)
... | true  | ys ∷ groups | eq rewrite eq = refl
... | false | group       | eq rewrite eq = refl

group-runs : ∀ (xs : List (Term n)) → All (Linked Term._≈_ ∘ toList) (group xs)
group-runs []           = []
group-runs (x ∷ [])     = [-] ∷ []
group-runs (x ∷ y ∷ xs) with x Term.≟ y | group (y ∷ xs) | group-runs (y ∷ xs) | group-concat (y ∷ xs)
... | yes x≡y | ys ∷ groups | pys ∷ all | eq = ((VecPw.trans trans x≡y ∘ VecPw.≡⇒Pointwise-≡ ∘ cong proj₁ ∘ Listₚ.∷-injectiveˡ ∘ sym) eq ∷ pys) ∷ all
... | no x≢y  | groups      | all       | eq = [-] ∷ all

group-distinct : ∀ (xs : List (Term n)) → Linked (λ xs ys → ¬ last xs Term.≈ head ys) (group xs)
group-distinct []           = []
group-distinct (x ∷ [])     = [-]
group-distinct (x ∷ y ∷ xs) with x Term.≟ y | group (y ∷ xs) | group-distinct (y ∷ xs) | group-concat (y ∷ xs)
... | no x≢y  | ys ∷ groups | distinct | eq = x≢y ∘ flip (VecPw.trans trans) (VecPw.≡⇒Pointwise-≡ (cong proj₁ (Listₚ.∷-injectiveˡ eq))) ∷ distinct
... | yes x≡y | ys ∷ groups | distinct | eq = my-map (λ {y} → f {_} {x} {ys} {y}) (head′ distinct) ∷′ Linked.tail distinct
  where
  open import Data.Maybe
  open import Data.Maybe.Relation.Binary.Connected hiding (refl; sym)
  my-map : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} {x x′} → (∀ {y} → R x y → R x′ y) → ∀ {y} → Connected R (just x) y → Connected R (just x′) y
  my-map f (just r)     = just (f r)
  my-map f just-nothing = just-nothing

  last-∷ : ∀ {a} {A : Set a} (x : A) xs → last (x ∷⁺ xs) ≡ last xs
  last-∷ x (y ∷ xs) with initLast xs
  ... | []       = refl
  ... | xs ∷ʳ′ z = refl

  f : ∀ {x : Term n} {xs y} → ¬ last xs Term.≈ head y → ¬ last (x ∷⁺ xs) Term.≈ head y
  f {x = x} {xs} {y} neq = neq ∘ Term.Eq.trans {_} {last xs} {last (x ∷⁺ xs)} {head y} (Term.Eq.reflexive (sym (last-∷ x xs)))

flatten : Op₂ A → List (List⁺ (Term n)) → List (Term n)
flatten _∙_ = List.map (foldl₁ (λ x y → proj₁ x , proj₂ x ∙ proj₂ y))

-- flatten : Op₂ A → NearPolynomial n → Polynomial n
-- terms (flatten _∙_ ([] , xs↗))               = []
-- terms (flatten _∙_ (x ∷ [] , xs↗))           = x ∷ []
-- terms (flatten _∙_ (x ∷ y ∷ xs , x≤y ∷ xs↗)) with x On′.≟ y
-- ... | yes x≡y = terms (flatten _∙_ ((proj₁ y , proj₂ x ∙ proj₂ y) ∷ xs , {!!}))
-- ... | no x≢y  = {!a!}
-- sorted (flatten _∙_ xs) = {!!}

-- merge : Op₂ A → Op₂ (Polynomial n)
-- merge _∙_ ([] , [])        (ys , ys↗)       = ys , ys↗
-- merge _∙_ ((x ∷ xs) , xs↗) ([] , [])        = x ∷ xs , xs↗
-- merge _∙_ ((x ∷ xs) , xs↗) ((y ∷ ys) , ys↗) with pair-cmp x y
-- ... |

-- _⊕_ : Op₂ (Polynomial n)
-- xs ⊕ ys = {!!}
