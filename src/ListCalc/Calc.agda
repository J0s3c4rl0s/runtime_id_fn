module Calc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
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
    A B C D P : Term
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term

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
    elimnat_P∶_zb∶_sb∶_ : Term → Term → Term → Term → Term
    -- List
    -- For now annotate parametrized type
    eliml_P∶_ty∶_nb∶_cb∶_ : (list : Term) → Term → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    -- vec
    -- For now annotate length
    elimv_P∶_l∶_ty∶_nb∶_cb∶_ : (vec : Term) → Term → (length : Term) → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    
    -- Types
    Nat : Term
    List : Term → Term
    Vec : Term → Term → Term
    ∶_⟶_ : Term → Term → Term -- Pi type
    Sett : Term -- Universe 
    El : Term → Term

∋→ℕ : Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ∶ t ♭ t₁) i l = ƛ∶ shiftindices t i l ♭ shiftindices t₁ i (suc l)
shiftindices (t · t₁) i l = shiftindices t i l · shiftindices t₁ i l
shiftindices z i l = z
shiftindices (s t) i l = s (shiftindices t i l) 
shiftindices nill i l = nill
shiftindices (t ∷l t₁) i l = shiftindices t i l ∷l shiftindices t₁ i l
shiftindices nilv i l = nilv
shiftindices (t ∷v t₁) i l = shiftindices t i l ∷v shiftindices t₁ i l
shiftindices (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) i l = 
    elimnat_P∶_zb∶_sb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l)
shiftindices (eliml t P∶ t₁ ty∶ t₂ nb∶ t₃ cb∶ t₄) i l = 
    eliml_P∶_ty∶_nb∶_cb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l) (shiftindices t₄ i l)
shiftindices (elimv t P∶ t₁ l∶ t₂ ty∶ t₃ nb∶ t₄ cb∶ t₅) i l = 
    elimv_P∶_l∶_ty∶_nb∶_cb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l) (shiftindices t₄ i l) (shiftindices t₅ i l)
shiftindices Nat i l = Nat
shiftindices (List t) i l = List (shiftindices t i l)
shiftindices (Vec t t₁) i l = Vec (shiftindices t i l) (shiftindices t₁ i l)
shiftindices (∶ t ⟶ t₁) i l = ∶ shiftindices t i l ⟶ shiftindices t₁ i (suc l)
shiftindices Sett i l = Sett
shiftindices (El t) i l = El (shiftindices t i l)

-- Consider parallel subtitutions to deal with free variable capture

-- Could reflection make this more efficient?
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ∶ bₜ ♭ b) [ a / i ] = ƛ∶ bₜ [ a / i ] ♭ (b [ shiftindices a 1 0 / suc i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b ⟶ c) [ a / i ] = ∶ bs ⟶ (c [ shiftindices a 1 0 / suc i ]) 
    where 
        bs = b [ a / i ]
Sett [ a / i ] = Sett
El b [ a / i ] = El (b [ a / i ])
z [ a / i ] = z
s b [ a / i ] = s (b [ a / i ]) 
nill [ a / i ] = nill
(h ∷l t) [ a / i ] = (h [ a / i ]) ∷l (t [ a / i ])
nilv [ a / i ] = nilv
(h ∷v t) [ a / i ] = (h [ a / i ]) ∷v (t [ a / i ])
(elimnat b P∶ P zb∶ zb sb∶ sb) [ a / i ] = 
    elimnat b [ a / i ] P∶ P [ a / i ] 
        zb∶ zb [ a / i ] 
        sb∶ (sb [ a / suc i ])
(eliml b P∶ P ty∶ bty nb∶ nb cb∶ cb) [ a / i ] = 
    eliml b [ a / i ] P∶ P [ a / i ] ty∶ bty [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ a / i ])
(elimv b P∶ P l∶ n ty∶ ty nb∶ nb cb∶ cb) [ a / i ] = 
    elimv b [ a / i ] P∶ P [ a / i ] l∶ n [ a / i ] ty∶ ty [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ a / i ])
Nat [ a / i ] = Nat
List b [ a / i ] = List (b [ a / i ])
Vec n b [ a / i ] = Vec (n [ a / i ]) (b [ a / i ])


data _⊢_＝_ : Context → Term → Term → Set

data _⊢_∶_ : Context → Term → Term → Set where
    ⊢var : ∀ {Γ A}
        (i : Γ ∋ A) →
        Γ ⊢ var (∋→ℕ i) ∶ shiftindices A (suc (∋→ℕ i)) 0
    
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
        Γ ⊢ a · b ∶  (B [ b / 0 ])
    -- Nats
    ⊢Nat : 
        Γ ⊢ Nat ∶ Sett
    ⊢z : 
        Γ ⊢ z ∶ Nat
    ⊢s : 
        Γ ⊢ a ∶ Nat →
        Γ ⊢ s a ∶ Nat
    ⊢natel : ∀ {zb sb} →
        Γ ⊢ n ∶ Nat →
        Γ ⊢ P ∶ (∶ Nat ⟶ Sett) →
        Γ ⊢ zb ∶ (P · z) →
        Γ ⊢ sb ∶ (∶ Nat ⟶ (∶ P · var 0 ⟶ (P · s (var 1)))) →
        Γ ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            ∶ (P · n) -- Not convinced about this type signature, maybe shoulda made eliminators just special functions instead

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
        Γ ⊢ l ∶ List A →
        Γ ⊢ P ∶ (∶ List A ⟶ Sett) → 
        Γ ⊢ nb ∶ (P · nill) → -- Could put things in the context
        Γ ⊢ cb ∶ (∶ A ⟶ (∶ List A ⟶ (∶ P · var 0 ⟶ (P · (var 2 ∷l var 1))))) → 
        Γ ⊢ eliml l P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ∶ (P · l)

    -- Vecs
    ⊢Vec : 
        Γ ⊢ Vec n A ∶ Sett
    ⊢nilv : 
        Γ ⊢ nilv ∶ Vec z A
    ⊢∷v :
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ Vec c A →
        Γ ⊢ a ∷v b ∶ Vec (s c) A
    ⊢vecel : 
        Γ ⊢ b ∶ Vec n A →
        Γ ⊢ P ∶ (∶ Nat ⟶ Vec (var 0) A) →
        Γ ⊢ nb ∶ ((P · z) · nilv) →
        Γ ⊢ cb ∶ (∶ Nat ⟶ (∶ A ⟶ (∶ Vec (var 1) A ⟶ (∶ P · var 0 ⟶ (P · (var 2 ∷v var 1)))))) → 
        Γ ⊢ elimv b P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ∶ (P · b)

    ⊢Sett : 
        Γ ⊢ Sett ∶ Sett
    ⊢conv : 
        Γ ⊢ a ∶ A →
        Γ ⊢ A ＝ B →
        Γ ⊢ a ∶ B
{-
data _⊢ : Context → Set where
    ⊢nil : Γ ⊢
    ⊢cons : 
        Γ ⊢ A ∶ Sett →
        (Γ , A) ⊢
-}

data _⊢_＝_ where
    {-
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ shiftindices a (suc (∋→ℕ i)) 0
    -}
    
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

    ＝beta : Γ ⊢ (ƛ∶ A ♭ b) · a ＝ (b [ a / 0 ])

    ＝lift : 
        (Γ , A) ⊢ b ∶ B →
        Γ ⊢ a ＝ c →
        Γ ⊢ b [ a / 0 ] ＝ ( b [ c / 0 ]) 
    
    -- equiv properties
    ＝refl : Γ ⊢ A ＝ A
    ＝sym : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ A 
    ＝trans : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ C →
        Γ ⊢ A ＝ C
    
    ---- eliminators 
    -- nats
    ＝natelz :
        Γ ⊢ m ＝ z →
        Γ ⊢ elimnat m P∶ P 
            zb∶ zb 
            sb∶ sb 
            ＝ 
            zb
    ＝natels :
        Γ ⊢ n ＝ s n →
        Γ ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            a →
        Γ ⊢ elimnat m P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            ((sb · n) · a)
    -- list
    ＝listeln :
        Γ ⊢ cs ＝ nill →
        Γ ⊢ eliml cs P∶ P ty∶ A  
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝listelc : 
        Γ ⊢ cs ＝ (a ∷l as) →
        Γ ⊢ eliml as P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        Γ ⊢ eliml cs P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            (((cb · a) · as) ·  b)
    -- vec
    ＝veceln :
        Γ ⊢ cs ＝ nilv →
        Γ ⊢ elimv cs P∶ P l∶ z ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝vecelc :
        Γ ⊢ cs ＝ (a ∷v as) → 
        Γ ⊢ elimv nilv P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        Γ ⊢ elimv cs P∶ P l∶ s n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            ((((cb · n) · a) · as) · b)
    
    ---- Cong rules for datatypes 
    -- Nat
    ＝s : 
        Γ ⊢ n ＝ m →
        Γ ⊢ s n ＝ s m
    -- List
    ＝list : 
        Γ ⊢ A ＝ B →
        Γ ⊢ List A ＝ List B
    ＝∷l :
        Γ ⊢ a ＝ c →
        Γ ⊢ as ＝ cs →
        Γ ⊢ a ∷l as ＝ (c ∷l cs)
    -- Vec
    ＝vec : 
        Γ ⊢ n ＝ m →
        Γ ⊢ A ＝ B →
        Γ ⊢ Vec n A ＝ Vec m B
    ＝∷v :
        Γ ⊢ a ＝ c →
        Γ ⊢ as ＝ cs →
        Γ ⊢ a ∷v as ＝ (c ∷v cs)
