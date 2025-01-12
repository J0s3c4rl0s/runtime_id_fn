module CalcPre where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

data PreContext : Set
data PreTerm : Set
data PreType : Set

data PreContext where
    [] : PreContext
    _,_ : (Γ : PreContext) → PreType → PreContext

data PreType where
    ∶_⟶_ : PreType → PreType → PreType
    Nat : PreType
    El : PreTerm → PreType
    Sett : PreType

data PreTerm where
    var : ℕ → PreTerm 

    -- function stuff
    ƛ∶_♭_ : PreTerm → PreTerm → PreTerm
    _·_ : PreTerm → PreTerm → PreTerm

    -- Numbers
    z : PreTerm
    s : PreTerm → PreTerm
    elimNat : PreTerm → PreTerm → PreTerm → PreTerm

private variable   
    Γ : PreContext
    A B C : PreType
    a b c : PreTerm

data _⊢ : PreContext → Set
data _⊢_ : PreContext → PreType → Set
data _⊢_∶_ : PreContext → PreTerm → PreType → Set

data _⊢ where
    [] : [] ⊢
    _,_ :
        Γ ⊢ → 
        (Γ , A) ⊢ -- Later gotta add wellformedness check to A

data _⊢_  where
    Pi : 
        Γ ⊢ A →
        (Γ , A) ⊢ B →
        Γ ⊢ ((∶ A ⟶ B))
    
    

data _⊢_∶_ where