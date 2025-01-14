module ListCalc where

open import Data.Nat using (ℕ; zero; suc; _+_)
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



-- Could reflection make this more efficient?
_[_/_]  : ∀ {Γ A} →  Term → Term → Γ ∋ A → Term
var 0 [ a / Z ] = a
var b [ a / i ] = var b
_[_/_] (ƛ∶ bₜ ♭ b) a i = ƛ∶ bs ♭ (b [ a / S {B = bs} i ])
    where 
        bs = bₜ [ a / i ]
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b ⟶ c) [ a / i ] = ∶ bs ⟶ (c [ a / S {B = bs} i ]) -- Propagate substitution here (telescoping?)
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
        sb∶ (sb [ a / S {B = Nat} i ])
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

∋→ℕ : Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

liftindices : Term → Γ ∋ A → Term
liftindices (var x) i = var (x + (1 + ∋→ℕ i)) 
liftindices (ƛ∶ t ♭ t₁) i = ƛ∶ liftindices t i ♭ liftindices t₁ i
liftindices (t · t₁) i = liftindices t i · liftindices t₁ i
liftindices z i = z
liftindices (s t) i = s (liftindices t i) 
liftindices nill i = nill
liftindices (t ∷l t₁) i = liftindices t i ∷l liftindices t₁ i
liftindices nilv i = nilv
liftindices (t ∷v t₁) i = liftindices t i ∷v liftindices t₁ i
liftindices (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) i = 
    elimnat_P∶_zb∶_sb∶_ (liftindices t i) (liftindices t₁ i) (liftindices t₂ i) (liftindices t₃ i)
liftindices (eliml t P∶ t₁ ty∶ t₂ nb∶ t₃ cb∶ t₄) i = 
    eliml_P∶_ty∶_nb∶_cb∶_ (liftindices t i) (liftindices t i) (liftindices t₂ i) (liftindices t₃ i) (liftindices t₃ i)
liftindices (elimv t P∶ t₁ l∶ t₂ ty∶ t₃ nb∶ t₄ cb∶ t₅) i = 
    elimv_P∶_l∶_ty∶_nb∶_cb∶_ (liftindices t i) (liftindices t i) (liftindices t₂ i) (liftindices t₃ i) (liftindices t₃ i) (liftindices t₄ i)
liftindices Nat i = Nat
liftindices (List t) i = List (liftindices t i)
liftindices (Vec t t₁) i = Vec (liftindices t i) (liftindices t₁ i)
liftindices (∶ t ⟶ t₁) i = ∶ liftindices t i ⟶ liftindices t₁ i
liftindices Sett i = Sett
liftindices (El t) i = El (liftindices t i)

data _⊢_＝_ : Context → Term → Term → Set

data _⊢_∶_ : Context → Term → Term → Set where
    ⊢var : ∀ {Γ A}
        (i : Γ ∋ A) →
        Γ ⊢ var (∋→ℕ i) ∶ liftindices A i
    
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
        Γ ⊢ nb ∶ (P · nill) →
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
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ liftindices a i

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

    ＝lift : 
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
    
    -- For easier comparison of Data types 
    ＝list : 
        Γ ⊢ A ＝ B →
        Γ ⊢ List A ＝ List B
    ＝vec : 
        Γ ⊢ n ＝ m →
        Γ ⊢ A ＝ B →
        Γ ⊢ Vec n A ＝ Vec m B
       
-- Id example

idTy : Term 
idTy = ∶ Sett ⟶ (∶ var 0 ⟶ (var 0))

idDef : Term
idDef = ƛ∶ Sett ♭ (ƛ∶ var 0 ♭ (var 0))

idTyped : Γ ⊢ idDef ∶ idTy
idTyped {Γ} = ⊢lam (⊢lam (⊢conv (⊢var Z) (＝sym (＝var Z))) (⊢var Z)) ⊢Sett

listLengthTy : Term 
listLengthTy = ∶ Sett ⟶ (∶ List (var 0) ⟶ Nat)

listLengthDef : Term
listLengthDef = 
    ƛ∶ Sett ♭ 
        (ƛ∶ List (var 0) ♭ 
            (eliml var 0 P∶ ƛ∶ List (var 1) ♭ Nat ty∶ var 1 
                nb∶ z 
                cb∶ (ƛ∶ var 1 ♭ (ƛ∶ List (var 1) ♭ (ƛ∶ Nat ♭ s (var 0))))))
 
listLengthTyped : [] ⊢ listLengthDef ∶ listLengthTy
listLengthTyped = 
    ⊢lam 
        (⊢lam 
            (⊢conv 
            (⊢listel 
                (⊢conv (⊢var Z) ＝refl) 
                (⊢lam ⊢Nat ⊢List) 
                (⊢conv ⊢z (＝sym ＝beta)) 
                (⊢lam 
                    (⊢lam 
                        (⊢conv (⊢lam (⊢s (⊢var Z)) ⊢Nat) (＝sym (＝pi ＝beta ＝beta))) 
                        ⊢List) 
                    (⊢var (S Z))) 
                ) 
                ＝beta) 
            ⊢List) 
        ⊢Sett

-- Assume A in context
listToVecTy : Term 
listToVecTy = ∶ List Nat ⟶ Vec ((listLengthDef · Nat) · var 0) Nat

listToVecDef : Term
listToVecDef = 
    ƛ∶ List Nat ♭ 
        (eliml var 0 P∶ ƛ∶ List Nat ♭ Vec ((listLengthDef · Nat) · var 0) Nat ty∶ Nat 
            nb∶ nilv 
            cb∶ (ƛ∶ Nat ♭ 
                    (ƛ∶ List Nat ♭ 
                        (ƛ∶ Vec ((listLengthDef · Nat) · var 0) Nat ♭ (var 2 ∷v var 0)))))

listToVecTyped : [] ⊢ listToVecDef ∶ listToVecTy
listToVecTyped = 
    ⊢lam 
        (⊢conv 
            (⊢listel 
                (⊢var Z) 
                (⊢lam ⊢Vec ⊢List) 
                (⊢conv 
                    (⊢nilv {A = Nat}) 
                    (＝sym (＝trans 
                        ＝beta 
                        (＝vec 
                            (＝trans 
                                (＝app 
                                    ＝beta 
                                    ＝refl) 
                                (＝trans 
                                    ＝beta 
                                    (＝listeln ＝refl))) 
                            ＝refl)))) 
                (⊢lam 
                    (⊢lam 
                        (⊢conv 
                            (⊢lam 
                                (⊢∷v (⊢var (S (S Z))) (⊢var Z)) 
                                ⊢Vec) 
                            (＝sym (＝pi 
                                ＝beta 
                                (＝trans 
                                    ＝beta 
                                    (＝vec 
                                        (＝trans 
                                            (＝app 
                                                ＝beta 
                                                ＝refl) 
                                            (＝trans 
                                                ＝beta 
                                                (＝trans 
                                                    {!   !}
                                                    {!   !}))) 
                                        ＝refl)))))
                        ⊢List) 
                    ⊢Nat)) 
            ＝beta) 
        ⊢List  