------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Core where

open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (∃; _,_; proj₂; uncurry)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_; reduce)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Function as F using (_∘_; _∘′_; _∋_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (True; False; toWitness; fromWitness; map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary using (Decidable)

--- The set of types and boolean properties of them
data Type : Set where
  bool  : Type
  int   : Type
  fin   : (n : ℕ) → Type
  real  : Type
  bit   : Type
  bits  : (n : ℕ) → Type
  tuple : ∀ n → Vec Type n → Type
  array : Type → (n : ℕ) → Type

data HasEquality : Type → Set where
  bool : HasEquality bool
  int  : HasEquality int
  fin  : ∀ {n} → HasEquality (fin n)
  real : HasEquality real
  bit  : HasEquality bit
  bits : ∀ n → HasEquality (bits n)

hasEquality? : Decidable HasEquality
hasEquality? bool        = yes bool
hasEquality? int         = yes int
hasEquality? (fin n)     = yes fin
hasEquality? real        = yes real
hasEquality? bit         = yes bit
hasEquality? (bits n)    = yes (bits n)
hasEquality? (tuple n x) = no (λ ())
hasEquality? (array t n) = no (λ ())

data IsNumeric : Type → Set where
  int  : IsNumeric int
  real : IsNumeric real

isNumeric? : Decidable IsNumeric
isNumeric? bool        = no (λ ())
isNumeric? int         = yes int
isNumeric? (fin n)     = no (λ ())
isNumeric? real        = yes real
isNumeric? bit         = no (λ ())
isNumeric? (bits n)    = no (λ ())
isNumeric? (tuple n x) = no (λ ())
isNumeric? (array t n) = no (λ ())

combineNumeric : ∀ t₁ t₂ → (isNumeric₁ : True (isNumeric? t₁)) → (isNumeric₂ : True (isNumeric? t₂)) → Type
combineNumeric int  int  _ _ = int
combineNumeric int  real _ _ = real
combineNumeric real _    _ _ = real

data Sliced : Set where
  bits  : Sliced
  array : Type → Sliced

asType : Sliced → ℕ → Type
asType bits      n = bits n
asType (array t) n = array t n

sliced? : ∀ t → Dec (∃ λ t′ → ∃ λ n → asType t′ n ≡ t)
sliced? bool = no (λ { (bits , ()) ; (array _ , ()) })
sliced? int = no (λ { (bits , ()) ; (array _ , ()) })
sliced? (fin n) = no (λ { (bits , ()) ; (array _ , ()) })
sliced? real = no (λ { (bits , ()) ; (array _ , ()) })
sliced? bit = no (λ { (bits , ()) ; (array _ , ()) })
sliced? (bits n) = yes (bits , n , refl)
sliced? (tuple n x) = no (λ { (bits , ()) ; (array _ , ()) })
sliced? (array t n) = yes (array t , n , refl)

elemType : Sliced → Type
elemType bits      = bit
elemType (array t) = t

--- Literals

data Literal : Type → Set where
  _′b  : Bool → Literal bool
  _′i  : ℕ → Literal int
  _′f  : ∀ {n} → Fin n → Literal (fin n)
  _′r  : ℕ → Literal real
  _′x  : Bool → Literal bit
  _′xs : ∀ {n} → Vec Bool n → Literal (bits n)
  _′a  : ∀ {n t} → Literal t → Literal (array t n)

--- Expressions, references, statements, functions and procedures

module Code {o} (Σ : Vec Type o) where
  data Expression {n} (Γ : Vec Type n) : Type → Set
  data CanAssign {n Γ} : ∀ {t} → Expression {n} Γ t → Set
  canAssign? : ∀ {n Γ t} → Decidable (CanAssign {n} {Γ} {t})
  data ReferencesState {n Γ} : ∀ {t} → Expression {n} Γ t → Set
  referencesState? : ∀ {n Γ t} → Decidable (ReferencesState {n} {Γ} {t})
  data Statement {n} (Γ : Vec Type n) : Set
  data ChangesState {n Γ} : Statement {n} Γ → Set
  changesState? : ∀ {n Γ} → Decidable (ChangesState {n} {Γ})
  data Function {n} (Γ : Vec Type n) (ret : Type) : Set
  data Procedure {n} (Γ : Vec Type n) : Set

  infix  8 -_
  infixr 7 _^_
  infixl 6 _*_ _and_ _>>_
  -- infixl 6 _/_
  infixl 5 _+_ _or_ _&&_ _||_
  infix  4 _≟_ _<?_

  data Expression {n} Γ where
    lit    : ∀ {t} → Literal t → Expression Γ t
    state  : ∀ i → Expression Γ (lookup Σ i)
    var    : ∀ i → Expression Γ (lookup Γ i)
    abort  : ∀ {t} → Expression Γ (fin 0) → Expression Γ t
    _≟_    : ∀ {t} {hasEquality : True (hasEquality? t)} → Expression Γ t → Expression Γ t → Expression Γ bool
    _<?_   : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → Expression Γ t → Expression Γ bool
    inv    : Expression Γ bool → Expression Γ bool
    _&&_   : Expression Γ bool → Expression Γ bool → Expression Γ bool
    _||_   : Expression Γ bool → Expression Γ bool → Expression Γ bool
    not    : ∀ {m} → Expression Γ (bits m) → Expression Γ (bits m)
    _and_  : ∀ {m} → Expression Γ (bits m) → Expression Γ (bits m) → Expression Γ (bits m)
    _or_   : ∀ {m} → Expression Γ (bits m) → Expression Γ (bits m) → Expression Γ (bits m)
    [_]    : ∀ {t} → Expression Γ (elemType t) → Expression Γ (asType t 1)
    unbox  : ∀ {t} → Expression Γ (asType t 1) → Expression Γ (elemType t)
    splice : ∀ {m n t} → Expression Γ (asType t m) → Expression Γ (asType t n) → Expression Γ (fin (suc n)) → Expression Γ (asType t (n ℕ.+ m))
    cut    : ∀ {m n t} → Expression Γ (asType t (n ℕ.+ m)) → Expression Γ (fin (suc n)) → Expression Γ (tuple 2 (asType t m ∷ asType t n ∷ []))
    cast   : ∀ {i j t} → .(eq : i ≡ j) → Expression Γ (asType t i) → Expression Γ (asType t j)
    -_     : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → Expression Γ t
    _+_    : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ isNumeric₁ isNumeric₂)
    _*_    : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ isNumeric₁ isNumeric₂)
    -- _/_   : Expression Γ real → Expression Γ real → Expression Γ real
    _^_    : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → ℕ → Expression Γ t
    _>>_   : Expression Γ int → ℕ → Expression Γ int
    rnd    : Expression Γ real → Expression Γ int
    fin    : ∀ {k ms n} → (All (Fin) ms → Fin n) → Expression Γ (tuple k (map fin ms)) → Expression Γ (fin n)
    asInt  : ∀ {m} → Expression Γ (fin m) → Expression Γ int
    nil    : Expression Γ (tuple 0 [])
    cons   : ∀ {m t ts} → Expression Γ t → Expression Γ (tuple m ts) → Expression Γ (tuple (suc m) (t ∷ ts))
    head   : ∀ {m t ts} → Expression Γ (tuple (suc m) (t ∷ ts)) → Expression Γ t
    tail   : ∀ {m t ts} → Expression Γ (tuple (suc m) (t ∷ ts)) → Expression Γ (tuple m ts)
    call   : ∀ {t m Δ} → Function Δ t → All (Expression Γ) {m} Δ → Expression Γ t
    if_then_else_ : ∀ {t} → Expression Γ bool → Expression Γ t → Expression Γ t → Expression Γ t

  data CanAssign {n} {Γ} where
    state : ∀ i → CanAssign (state i)
    var   : ∀ i → CanAssign (var i)
    abort : ∀ {t} e → CanAssign (abort {t = t} e)
    [_]   : ∀ {t e} → CanAssign e → CanAssign ([_] {t = t} e)
    unbox : ∀ {t e} → CanAssign e → CanAssign (unbox {t = t} e)
    splice : ∀ {m n t e₁ e₂} → CanAssign e₁ → CanAssign e₂ → ∀ e₃ → CanAssign (splice {m = m} {n} {t} e₁ e₂ e₃)
    cut    : ∀ {m n t e₁} → CanAssign e₁ → ∀ e₂ → CanAssign (cut {m = m} {n} {t} e₁ e₂)
    cast  : ∀ {i j t e} .(eq : i ≡ j) → CanAssign e → CanAssign (cast {t = t} eq e)
    nil   : CanAssign nil
    cons  : ∀ {m t ts e₁ e₂} → CanAssign e₁ → CanAssign e₂ → CanAssign (cons {m = m} {t} {ts} e₁ e₂)
    head  : ∀ {m t ts e} → CanAssign e → CanAssign (head {m = m} {t} {ts} e)
    tail  : ∀ {m t ts e} → CanAssign e → CanAssign (tail {m = m} {t} {ts} e)

  canAssign? (lit x)      = no λ ()
  canAssign? (state i)    = yes (state i)
  canAssign? (var i)      = yes (var i)
  canAssign? (abort e)    = yes (abort e)
  canAssign? (e ≟ e₁)     = no λ ()
  canAssign? (e <? e₁)    = no λ ()
  canAssign? (inv e)      = no λ ()
  canAssign? (e && e₁)    = no λ ()
  canAssign? (e || e₁)    = no λ ()
  canAssign? (not e)      = no λ ()
  canAssign? (e and e₁)   = no λ ()
  canAssign? (e or e₁)    = no λ ()
  canAssign? [ e ]        = map′ [_] (λ { [ e ] → e }) (canAssign? e)
  canAssign? (unbox e)    = map′ unbox (λ { (unbox e) → e }) (canAssign? e)
  canAssign? (splice e e₁ e₂) = map′ (λ (e , e₁) → splice e e₁ e₂) (λ { (splice e e₁ _) → e , e₁ }) (canAssign? e ×-dec canAssign? e₁)
  canAssign? (cut e e₁)       = map′ (λ e → cut e e₁) (λ { (cut e e₁) → e }) (canAssign? e)
  canAssign? (cast eq e)  = map′ (cast eq) (λ { (cast eq e) → e }) (canAssign? e)
  canAssign? (- e)        = no λ ()
  canAssign? (e + e₁)     = no λ ()
  canAssign? (e * e₁)     = no λ ()
  -- canAssign? (e / e₁)     = no λ ()
  canAssign? (e ^ e₁)     = no λ ()
  canAssign? (e >> e₁)    = no λ ()
  canAssign? (rnd e)      = no λ ()
  canAssign? (fin x e)    = no λ ()
  canAssign? (asInt e)    = no λ ()
  canAssign? nil          = yes nil
  canAssign? (cons e e₁)  = map′ (uncurry cons) (λ { (cons e e₁) → e , e₁ }) (canAssign? e ×-dec canAssign? e₁)
  canAssign? (head e)     = map′ head (λ { (head e) → e }) (canAssign? e)
  canAssign? (tail e)     = map′ tail (λ { (tail e) → e }) (canAssign? e)
  canAssign? (call x e)   = no λ ()
  canAssign? (if e then e₁ else e₂) = no λ ()

  data ReferencesState where
    state : ∀ i → ReferencesState (state i)
    [_] : ∀ {t e} → ReferencesState e → ReferencesState ([_] {t = t} e)
    unbox : ∀ {t e} → ReferencesState e → ReferencesState (unbox {t = t} e)
    spliceˡ : ∀ {m n t e} → ReferencesState e → ∀ e₁ e₂ → ReferencesState (splice {m = m} {n} {t} e e₁ e₂)
    spliceʳ : ∀ {m n t} e {e₁} → ReferencesState e₁ → ∀ e₂ → ReferencesState (splice {m = m} {n} {t} e e₁ e₂)
    cut : ∀ {m n t e} → ReferencesState e → ∀ e₁ → ReferencesState (cut {m = m} {n} {t} e e₁)
    cast : ∀ {i j t} .(eq : i ≡ j) {e} → ReferencesState e → ReferencesState (cast {t = t} eq e)
    consˡ : ∀ {m t ts e} → ReferencesState e → ∀ e₁ → ReferencesState (cons {m = m} {t} {ts} e e₁)
    consʳ : ∀ {m t ts} e {e₁} → ReferencesState e₁ → ReferencesState (cons {m = m} {t} {ts} e e₁)
    head : ∀ {m t ts e} → ReferencesState e → ReferencesState (head {m = m} {t} {ts} e)
    tail : ∀ {m t ts e} → ReferencesState e → ReferencesState (tail {m = m} {t} {ts} e)

  referencesState? (lit x) = no λ ()
  referencesState? (state i) = yes (state i)
  referencesState? (var i) = no λ ()
  referencesState? (abort e) = no λ ()
  referencesState? (e ≟ e₁) = no λ ()
  referencesState? (e <? e₁) = no λ ()
  referencesState? (inv e) = no λ ()
  referencesState? (e && e₁) = no λ ()
  referencesState? (e || e₁) = no λ ()
  referencesState? (not e) = no λ ()
  referencesState? (e and e₁) = no λ ()
  referencesState? (e or e₁) = no λ ()
  referencesState? [ e ] = map′ [_] (λ { [ e ] → e }) (referencesState? e)
  referencesState? (unbox e) = map′ unbox (λ { (unbox e) → e }) (referencesState? e)
  referencesState? (splice e e₁ e₂) = map′ [ (λ e → spliceˡ e e₁ e₂) , (λ e₁ → spliceʳ e e₁ e₂) ]′ (λ { (spliceˡ e e₁ e₂) → inj₁ e ; (spliceʳ e e₁ e₂) → inj₂ e₁ }) (referencesState? e ⊎-dec referencesState? e₁)
  referencesState? (cut e e₁) = map′ (λ e → cut e e₁) (λ { (cut e e₁) → e }) (referencesState? e)
  referencesState? (cast eq e) = map′ (cast eq) (λ { (cast eq e) → e }) (referencesState? e)
  referencesState? (- e) = no λ ()
  referencesState? (e + e₁) = no λ ()
  referencesState? (e * e₁) = no λ ()
  referencesState? (e ^ x) = no λ ()
  referencesState? (e >> x) = no λ ()
  referencesState? (rnd e) = no λ ()
  referencesState? (fin x e) = no λ ()
  referencesState? (asInt e) = no λ ()
  referencesState? nil = no λ ()
  referencesState? (cons e e₁) = map′ [ (λ e → consˡ e e₁) , (λ e₁ → consʳ e e₁) ]′ (λ { (consˡ e e₁) → inj₁ e ; (consʳ e e₁) → inj₂ e₁ }) (referencesState? e ⊎-dec referencesState? e₁)
  referencesState? (head e) = map′ head (λ { (head e) → e }) (referencesState? e)
  referencesState? (tail e) = map′ tail (λ { (tail e) → e }) (referencesState? e)
  referencesState? (call f es) = no λ ()
  referencesState? (if e then e₁ else e₂) = no λ ()

  infix  4 _≔_
  infixl 2 if_then_else_ if_then_
  infixl 1 _∙_ _∙return_
  infix  1 _∙end

  data Statement Γ where
    _∙_           : Statement Γ → Statement Γ → Statement Γ
    skip          : Statement Γ
    _≔_           : ∀ {t} → (ref : Expression Γ t) → {canAssign : True (canAssign? ref)} → Expression Γ t → Statement Γ
    declare       : ∀ {t} → Expression Γ t → Statement (t ∷ Γ) → Statement Γ
    invoke        : ∀ {m Δ} → Procedure Δ → All (Expression Γ) {m} Δ → Statement Γ
    if_then_      : Expression Γ bool → Statement Γ → Statement Γ
    if_then_else_ : Expression Γ bool → Statement Γ → Statement Γ → Statement Γ
    for           : ∀ m → Statement (fin m ∷ Γ) → Statement Γ

  data ChangesState where
    _∙ˡ_           : ∀ {s} → ChangesState s → ∀ s₁ → ChangesState (s ∙ s₁)
    _∙ʳ_           : ∀ s {s₁} → ChangesState s₁ → ChangesState (s ∙ s₁)
    _≔_            : ∀ {t} ref {canAssign : True (canAssign? ref)} {refsState : True (referencesState? ref)} e₂ → ChangesState (_≔_ {t = t} ref {canAssign} e₂)
    declare        : ∀ {t} e {s} → ChangesState s → ChangesState (declare {t = t} e s)
    invoke         : ∀ {m Δ} p es → ChangesState (invoke {m = m} {Δ} p es)
    if_then_       : ∀ e {s} → ChangesState s → ChangesState (if e then s)
    if_then′_else_ : ∀ e {s} → ChangesState s → ∀ s₁ → ChangesState (if e then s else s₁)
    if_then_else′_ : ∀ e s {s₁} → ChangesState s₁ → ChangesState (if e then s else s₁)
    for            : ∀ m {s} → ChangesState s → ChangesState (for m s)

  changesState? (s ∙ s₁)              = map′ [ _∙ˡ s₁ , s ∙ʳ_ ]′ (λ { (s ∙ˡ s₁) → inj₁ s ; (s ∙ʳ s₁) → inj₂ s₁ }) (changesState? s ⊎-dec changesState? s₁)
  changesState? skip                  = no λ ()
  changesState? (_≔_ ref e)           = map′ (λ refsState → _≔_ ref {refsState = fromWitness refsState} e) (λ { (_≔_ ref {refsState = refsState} e) → toWitness refsState }) (referencesState? ref)
  changesState? (declare e s)         = map′ (declare e) (λ { (declare e s) → s }) (changesState? s)
  changesState? (invoke p e)          = yes (invoke p e)
  changesState? (if e then s)         = map′ (if e then_) (λ { (if e then s) → s }) (changesState? s)
  changesState? (if e then s else s₁) = map′ [ if e then′_else s₁ , if e then s else′_ ]′ (λ { (if e then′ s else s₁) → inj₁ s ; (if e then s else′ s₁) → inj₂ s₁ }) (changesState? s ⊎-dec changesState? s₁)
  changesState? (for m s)             = map′ (for m) (λ { (for m s) → s }) (changesState? s)

  data Function Γ ret where
    _∙return_ : (s : Statement Γ) → {False (changesState? s)} → Expression Γ ret → Function Γ ret
    declare   : ∀ {t} → Expression Γ t → Function (t ∷ Γ) ret → Function Γ ret

  data Procedure Γ where
    _∙end   : Statement Γ → Procedure Γ

  infixl  6 _<<_
  infixl 5 _-_ _∶_

  tup : ∀ {n Γ m ts} → All (Expression {n} Γ) ts → Expression Γ (tuple m ts)
  tup []       = nil
  tup (e ∷ es) = cons e (tup es)

  _∶_ : ∀ {n Γ i j t} → Expression {n} Γ (asType t j) → Expression Γ (asType t i) → Expression Γ (asType t (i ℕ.+ j))
  e₁ ∶ e₂ = splice e₁ e₂ (lit (Fin.fromℕ _ ′f))

  slice : ∀ {n Γ i j t} → Expression {n} Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc i)) → Expression Γ (asType t j)
  slice e₁ e₂ = head (cut e₁ e₂)

  slice′ : ∀ {n Γ i j t} → Expression {n} Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc j)) → Expression Γ (asType t i)
  slice′ {i = i} e₁ e₂ = slice (cast (+-comm i _) e₁) e₂

  _-_   : ∀ {n Γ t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression {n} Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ isNumeric₁ isNumeric₂)
  _-_ {isNumeric₂ = isNumeric₂} x y = x + (-_ {isNumeric = isNumeric₂} y)

  _<<_ : ∀ {n Γ} → Expression {n} Γ int → ℕ → Expression Γ int
  x << n = rnd (x * lit (2 ′r) ^ n)

  get : ∀ {n Γ} → ℕ → Expression {n} Γ int → Expression Γ bit
  get i x = if x - x >> suc i << suc i <? lit (2 ′i) ^ i then lit (false ′x) else lit (true ′x)

  uint : ∀ {n Γ m} → Expression {n} Γ (bits m) → Expression Γ int
  uint {m = zero}  x = lit (0 ′i)
  uint {m = suc m} x =
    lit (2 ′i) * uint {m = m} (slice x (lit (1F ′f))) +
    ( if slice′ x (lit (0F ′f)) ≟ lit ((true ∷ []) ′xs)
      then lit (1 ′i)
      else lit (0 ′i))

  sint : ∀ {n Γ m} → Expression {n} Γ (bits m) → Expression Γ int
  sint {m = zero}        x = lit (0 ′i)
  sint {m = suc zero}    x = if x ≟ lit ((true ∷ []) ′xs) then - lit (1 ′i) else lit (0 ′i)
  sint {m = suc (suc m)} x =
    lit (2 ′i) * sint (slice {i = 1} x (lit (1F ′f))) +
    ( if slice′ x (lit (0F ′f)) ≟ lit ((true ∷ []) ′xs)
      then lit (1 ′i)
      else lit (0 ′i))
