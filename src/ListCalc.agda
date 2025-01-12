module ListCalc where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary.Decidable using (True; toWitness)

data Context : Set
data Term : Set 
-- data Type : Set


data Context where
    [] : Context
    _,_ : (Γ : Context) → Term → Context

data _∋_ : (Γ : Context) → Term → Set where
  Z : ∀ {A} {Γ : Context}
    →  (Γ , A) ∋ A

  S : ∀ {A} {B} {Γ : Context}
    -- Ensure there is a lookup judgement in submodule
    → Γ ∋ A
    →  (Γ , B) ∋ A


private variable 
    Γ : Context
    A B C D : Term
    a b c d e f g h l m n  : Term

data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ∶_♭_ : Term → Term → Term
    _·_ : Term → Term → Term

    -- data cons
    ---- Nats
    z : Term
    s : Term → Term 
    -- list 
    nill : Term 
    _∷l_ : Term → Term → Term 
    -- vec
    nilv : Term 
    _∷v_ : Term → Term → Term 

    ---- elims 
    -- Nat
    elimnat : (nat : Term) → Term → Term → Term
    -- List
    -- For now annotate parametrized type
    eliml : (list : Term) → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    -- vec
    -- For now annotate length
    elimv : (vec : Term) → (length : Term) → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    
    -- Types
    Nat : Term
    List : Term → Term
    Vec : Term → Term → Term
    ∶_⟶_ : Term → Term → Term -- Pi type
    Sett : Term -- Universe 
    El : Term → Term
    
{- 
data Type where 
    ∶_⟶_ : Type → Type → Type -- Pi type
    U : Type -- Universe 
    El : Term → Type
    
    -- Base type
    Nat : Type 
    List : Type → Type
    Vec : Type → Term → Type -- Cant stick the Nat in here directly
-}

-- Could reflection make this more efficient?
_[_/_]  : ∀ {Γ A} →  Term → Term → Γ ∋ A → Term
var 0 [ a / Z ] = a
var b [ a / i ] = var b
_[_/_] (ƛ∶ bₜ ♭ b) a i = ƛ∶ bₜ [ a / i ] ♭ (b [ a / S {B = bₜ} i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b ⟶ c) [ a / i ] = ∶ b [ a / i ] ⟶ (c [ a / i ])
Sett [ a / i ] = Sett
El b [ a / i ] = El (b [ a / i ])
z [ a / i ] = z
s b [ a / i ] = s (b [ a / i ]) 
nill [ a / i ] = nill
(h ∷l t) [ a / i ] = (h [ a / i ]) ∷l (t [ a / i ])
nilv [ a / i ] = nilv
(h ∷v t) [ a / i ] = (h [ a / i ]) ∷v (t [ a / i ])
-- Eliminations should introduce relevant variables into context
elimnat b bz bs [ a / i ] = elimnat (b [ a / i ]) (bz [ a / i ]) (bs [ a / S {B = Nat} i ])
eliml b biₜ b[] b∷ [ a / i ] = eliml (b [ a / i ]) (biₜ [ a / i ]) (b[] [ a / i ]) (b∷ [ a / S {B = biₜ} (S {B = List biₜ} i) ]) 
-- potential bug from mapping 0 to 0 for subtraction
elimv b biₜ bl b[] b∷ [ a / i ] = elimv (b [ a / i ]) bis bls (b[] [ a / i ]) (b∷ [ a / S {B = biₜ} (S {B = Vec (elimnat bls z (var 0)) biₜ} i) ]) 
    where
    bls = bl [ a / i ]
    bis = biₜ [ a / i ]
Nat [ a / i ] = Nat
List b [ a / i ] = List (b [ a / i ])
Vec n b [ a / i ] = Vec (n [ a / i ]) (b [ a / i ])

∋→ℕ : Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

data _⊢_＝_ : Context → Term → Term → Set

data _⊢_∶_ : Context → Term → Term → Set where
    ⊢var : ∀ {Γ A}
        (i : Γ ∋ A) →
        Γ ⊢ var (∋→ℕ i) ∶ A
    
    -- functions
    ⊢pi :
        Γ ⊢ A ∶ Sett →
        (Γ , A) ⊢ B ∶ Sett →
        Γ ⊢ ∶ A ⟶ B ∶ Sett
    ⊢lam : 
        (Γ , A) ⊢ b ∶ B →
        Γ ⊢ A ∶ Sett →
        Γ ⊢ ƛ∶ A ♭ b ∶ (∶ A ⟶ B)
    ⊢app : 
        Γ ⊢ a ∶ (∶ A ⟶ B) →
        Γ ⊢ b ∶ A →
        Γ ⊢ a · b ∶  (_[_/_] {A = A} B b (Z {Γ = Γ}))
    -- Nats
    ⊢Nat : 
        Γ ⊢ Nat ∶ Sett
    ⊢z : 
        Γ ⊢ z ∶ Sett
    ⊢s : 
        Γ ⊢ a ∶ Nat →
        Γ ⊢ s a ∶ Nat
    -- might be nice to have flow sensitivity but that could be good for when pat match/ gen elim
    ⊢natel :   
        Γ ⊢ a ∶ Nat →
        Γ ⊢ b ∶ A →
        (Γ , Nat) ⊢ c ∶ A →
        Γ ⊢ elimnat a b c ∶ A
    
    -- Lists
    ⊢List : 
        Γ ⊢ List A ∶ Sett
    ⊢nill :
        Γ ⊢ nill ∶ List A -- may need to add annotations later
    ⊢∷l :
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ List A →
        Γ ⊢ a ∷l b ∶ List A
    ⊢listel : 
        Γ ⊢ a ∶ List A → 
        Γ ⊢ c ∶ B →
        ((Γ , A) , List A  ) ⊢ d ∶ B → 
        Γ ⊢ eliml a A c d ∶ B

    -- Vecs
    ⊢Vec : 
        Γ ⊢ Vec b A ∶ Sett
    ⊢nilv : 
        Γ ⊢ nilv ∶ Vec z A
    ⊢∷v :
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ Vec c A →
        Γ ⊢ a ∷v b ∶ Vec (s c) A
    ⊢vecel : 
        Γ ⊢ a ∶ Vec n A →
        Γ ⊢ d ∶ B →
        ((Γ , A) , Vec {!   !} A) ⊢ e ∶ B → -- What if length is 0 lol
        Γ ⊢ elimv a n A d e ∶ B

    ⊢Sett : 
        Γ ⊢ Sett ∶ Sett
    ⊢conv : 
        Γ ⊢ a ∶ A →
        Γ ⊢ A ＝ B →
        Γ ⊢ a ∶ B

data _⊢ : Context → Set where
    ⊢nil : Γ ⊢
    ⊢cons : 
        Γ ⊢ A ∶ Sett →
        (Γ , A) ⊢

data _⊢_＝_ where
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ a

    ＝pi : 
        Γ ⊢ A ＝ C → 
        (Γ , A) ⊢ B ＝ D →
        Γ ⊢ ∶ A ⟶ B ＝ (∶ C ⟶ D)
    ＝lam :
        (Γ , A) ⊢ b ＝ c →
        Γ ⊢ ƛ∶ A ♭ b  ＝ (ƛ∶ A ♭ c)
    ＝app : 
        Γ ⊢ b ＝ d →
        Γ ⊢ a ＝ c →
        Γ ⊢ b · a ＝ (d · c)

    ＝beta : Γ ⊢ (ƛ∶ A ♭ b) · a ＝ (b [ a / Z {A} {Γ} ])

    =lift : 
        (Γ , A) ⊢ b ∶ B →
        Γ ⊢ a ＝ c →
        Γ ⊢ b [ a / Z {A} {Γ} ] ＝ ( b [ c / Z {A} {Γ} ]) 
    
    -- equiv properties
    ＝refl : Γ ⊢ A ＝ A
    ＝sym : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ A 
    ＝trans : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ C →
        Γ ⊢ A ＝ C
       
-- Id example

idTy : Term 
idTy = ∶ Sett ⟶ (∶ var 0 ⟶ (var 0))

idDef : Term
idDef = ƛ∶ Sett ♭ (ƛ∶ var 0 ♭ (var 0))

idTyped : Γ ⊢ idDef ∶ idTy
idTyped {Γ} = ⊢lam (⊢lam (⊢var Z) (⊢var Z)) ⊢Sett
