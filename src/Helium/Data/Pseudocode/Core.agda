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
  bits : ∀ {n} → HasEquality (bits n)

hasEquality? : Decidable HasEquality
hasEquality? bool        = yes bool
hasEquality? int         = yes int
hasEquality? (fin n)     = yes fin
hasEquality? real        = yes real
hasEquality? bit         = yes bit
hasEquality? (bits n)    = yes bits
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

combineNumeric : ∀ t₁ t₂ → {isNumeric₁ : True (isNumeric? t₁)} → {isNumeric₂ : True (isNumeric? t₂)} → Type
combineNumeric int  int  = int
combineNumeric int  real = real
combineNumeric real _    = real

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
  data AssignsState {n Γ} : ∀ {t e} → CanAssign {n} {Γ} {t} e → Set
  assignsState? : ∀ {n Γ t e} → Decidable (AssignsState {n} {Γ} {t} {e})
  assignsStateAny? : ∀ {n Γ m ts es} → Decidable {A = All (CanAssign ∘ proj₂) (reduce {P = Expression {n} Γ} (λ {x} e → x , e) {m} {ts} es)} (Any (AssignsState ∘ proj₂) ∘ reduce (λ {x} a → x , a))
  data Statement {n} (Γ : Vec Type n) : Set
  data ChangesState {n Γ} : Statement {n} Γ → Set
  changesState? : ∀ {n Γ} → Decidable (ChangesState {n} {Γ})
  data Function {n} (Γ : Vec Type n) (ret : Type) : Set
  data Procedure {n} (Γ : Vec Type n) : Set

  infix  8 -_
  infixr 7 _^_
  infixl 6 _*_ _and_ _>>_
  -- infixl 6 _/_
  infixl 5 _+_ _or_ _&&_ _||_ _∶_
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
    _+_    : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
    _*_    : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
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

  data AssignsState where
    state : ∀ i → AssignsState (state i)
    [_] : ∀ {t e a} → AssignsState a → AssignsState ([_] {t = t} {e} a)
    unbox : ∀ {t e a} → AssignsState a → AssignsState (unbox {t = t} {e} a)
    spliceˡ : ∀ {m n t e₁ e₂ a₁} → AssignsState a₁ → ∀ a₂ e₃ → AssignsState (splice {m = m} {n} {t} {e₁} {e₂} a₁ a₂ e₃)
    spliceʳ : ∀ {m n t e₁ e₂} a₁ {a₂} → AssignsState a₂ → ∀ e₃ → AssignsState (splice {m = m} {n} {t} {e₁} {e₂} a₁ a₂ e₃)
    cut : ∀ {m n t e₁ a₁} → AssignsState a₁ → ∀ e₂ → AssignsState (cut {m = m} {n} {t} {e₁} a₁ e₂)
    cast : ∀ {i j t e} .(eq : i ≡ j) {a} → AssignsState a → AssignsState (cast {t = t} {e} eq a)
    consˡ : ∀ {m t ts e₁ e₂ a₁} → AssignsState a₁ → ∀ a₂ → AssignsState (cons {m = m} {t} {ts} {e₁} {e₂} a₁ a₂)
    consʳ : ∀ {m t ts e₁ e₂} a₁ {a₂} → AssignsState a₂ → AssignsState (cons {m = m} {t} {ts} {e₁} {e₂} a₁ a₂)
    head : ∀ {m t ts e a} → AssignsState a → AssignsState (head {m = m} {t} {ts} {e} a)
    tail : ∀ {m t ts e a} → AssignsState a → AssignsState (tail {m = m} {t} {ts} {e} a)

  assignsState? (state i)    = yes (state i)
  assignsState? (var i)      = no λ ()
  assignsState? (abort e)    = no λ ()
  assignsState? [ a ]        = map′ [_] (λ { [ s ] → s }) (assignsState? a)
  assignsState? (unbox a)    = map′ unbox (λ { (unbox s) → s }) (assignsState? a)
  assignsState? (splice a₁ a₂ e₃) = map′ [ (λ a₁ → spliceˡ a₁ a₂ e₃) , (λ a₂ → spliceʳ a₁ a₂ e₃) ]′ (λ { (spliceˡ a₁ _ _) → inj₁ a₁ ; (spliceʳ _ a₂ _) → inj₂ a₂ }) (assignsState? a₁ ⊎-dec assignsState? a₂)
  assignsState? (cut a e₂) = map′ (λ s → cut s e₂ ) (λ { (cut s _) → s }) (assignsState? a)
  assignsState? (cast eq a)  = map′ (cast eq) (λ { (cast _ s) → s }) (assignsState? a)
  assignsState? nil          = no λ ()
  assignsState? (cons a₁ a₂) = map′ [ (λ a₁ → consˡ a₁ a₂) , (λ a₂ → consʳ a₁ a₂) ]′ (λ { (consˡ a₁ _) → inj₁ a₁ ; (consʳ _ a₂) → inj₂ a₂ }) (assignsState? a₁ ⊎-dec assignsState? a₂)
  assignsState? (head a)     = map′ head (λ { (head s) → s }) (assignsState? a)
  assignsState? (tail a)     = map′ tail (λ { (tail s) → s }) (assignsState? a)

  assignsStateAny? {es = []}     []       = no λ ()
  assignsStateAny? {es = e ∷ es} (a ∷ as) = map′ [ here , there ]′ (λ { (here s) → inj₁ s ; (there ss) → inj₂ ss }) (assignsState? a ⊎-dec assignsStateAny? as)

  infix  4 _≔_
  infixl 2 if_then_else_
  infixl 1 _∙_ _∙return_
  infix  1 _∙end

  data Statement Γ where
    _∙_           : Statement Γ → Statement Γ → Statement Γ
    skip          : Statement Γ
    _≔_           : ∀ {t} → (ref : Expression Γ t) → {canAssign : True (canAssign? ref)} → Expression Γ t → Statement Γ
    declare       : ∀ {t} → Expression Γ t → Statement (t ∷ Γ) → Statement Γ
    invoke        : ∀ {m Δ} → Procedure Δ → All (Expression Γ) {m} Δ → Statement Γ
    if_then_else_ : Expression Γ bool → Statement Γ → Statement Γ → Statement Γ
    for           : ∀ m → Statement (fin m ∷ Γ) → Statement Γ

  data ChangesState where
    _∙ˡ_           : ∀ {s₁} → ChangesState s₁ → ∀ s₂ → ChangesState (s₁ ∙ s₂)
    _∙ʳ_           : ∀ s₁ {s₂} → ChangesState s₂ → ChangesState (s₁ ∙ s₂)
    _≔_            : ∀ {t ref} canAssign {assignsState : True (assignsState? (toWitness canAssign))} e₂ → ChangesState (_≔_ {t = t} ref {canAssign} e₂)
    declare        : ∀ {t} e {s} → ChangesState s → ChangesState (declare {t = t} e s)
    invoke         : ∀ {m Δ} p e → ChangesState (invoke {m = m} {Δ} p e)
    if_then′_else_ : ∀ e {s₁} → ChangesState s₁ → ∀ s₂ → ChangesState (if e then s₁ else s₂)
    if_then_else′_ : ∀ e s₁ {s₂} → ChangesState s₂ → ChangesState (if e then s₁ else s₂)
    for            : ∀ m {s} → ChangesState s → ChangesState (for m s)

  changesState? (s₁ ∙ s₂)              = map′ [ _∙ˡ s₂ , s₁ ∙ʳ_ ]′ (λ { (s ∙ˡ _) → inj₁ s ; (_ ∙ʳ s) → inj₂ s }) (changesState? s₁ ⊎-dec changesState? s₂)
  changesState? skip                   = no λ ()
  changesState? (_≔_ ref {a} e)        = map′ (λ s → _≔_ a {fromWitness s} e) (λ { (_≔_ _ {s} _) → toWitness s }) (assignsState? (toWitness a))
  changesState? (declare e s)          = map′ (declare e) (λ { (declare e s) → s }) (changesState? s)
  changesState? (invoke p e)           = yes (invoke p e)
  changesState? (if e then s₁ else s₂) = map′ [ if e then′_else s₂ , if e then s₁ else′_ ]′ (λ { (if _ then′ s else _) → inj₁ s ; (if _ then _ else′ s) → inj₂ s }) (changesState? s₁ ⊎-dec changesState? s₂)
  changesState? (for m s)              = map′ (for m) (λ { (for m s) → s }) (changesState? s)

  data Function Γ ret where
    _∙return_ : (s : Statement Γ) → {False (changesState? s)} → Expression Γ ret → Function Γ ret
    declare   : ∀ {t} → Expression Γ t → Function (t ∷ Γ) ret → Function Γ ret

  data Procedure Γ where
    _∙end   : Statement Γ → Procedure Γ

  infixl  6 _<<_
  infixl 5 _-_

  tup : ∀ {n Γ m ts} → All (Expression {n} Γ) ts → Expression Γ (tuple m ts)
  tup []       = nil
  tup (e ∷ es) = cons e (tup es)

  _∶_ : ∀ {n Γ i j t} → Expression {n} Γ (asType t j) → Expression Γ (asType t i) → Expression Γ (asType t (i ℕ.+ j))
  e₁ ∶ e₂ = splice e₁ e₂ (lit (Fin.fromℕ _ ′f))

  slice : ∀ {n Γ i j t} → Expression {n} Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc i)) → Expression Γ (asType t j)
  slice e₁ e₂ = head (cut e₁ e₂)

  slice′ : ∀ {n Γ i j t} → Expression {n} Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc j)) → Expression Γ (asType t i)
  slice′ {i = i} e₁ e₂ = slice (cast (+-comm i _) e₁) e₂

  _-_   : ∀ {n Γ t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression {n} Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
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
