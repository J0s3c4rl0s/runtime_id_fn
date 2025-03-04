module ListCalc.Calc.TypeRules where

open import ListCalc.Calc.Syntax
open import ListCalc.Calc.Utils

open import Data.Nat using (ℕ; suc)


private variable 
    Γ : Context
    A B C D P : Term
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term

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
        Γ ⊢ A ∶ Sett →
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
        Γ ⊢ A ∶ Sett →
        Γ ⊢ A ∶ Sett →
        Γ ⊢ Vec n A ∶ Sett
    ⊢nilv : 
        Γ ⊢ A ∶ Sett → 
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
