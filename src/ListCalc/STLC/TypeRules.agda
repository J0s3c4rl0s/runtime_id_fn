module ListCalc.STLC.TypeRules where

open import ListCalc.STLC.Syntax
open import ListCalc.STLC.Utils

-- re-export Syntax constructs
open ListCalc.STLC.Syntax public

private variable 
    Γ : Context
    A B C D P : Type
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term


data _⊢_∶_ : Context → Term → Type → Set where
    ⊢var : ∀ {Γ A}
        (i : Γ ∋ A) →
        Γ ⊢ var (∋→ℕ i) ∶ A

    ⊢lam : 
        (Γ , A) ⊢ b ∶ B →
        Γ ⊢ ƛ b ∶ (A ⟶ B)
    ⊢app : 
        Γ ⊢ a ∶ (A ⟶ B) →
        Γ ⊢ b ∶ A →
        Γ ⊢ a · b ∶ B
    -- Nats
    ⊢z : 
        Γ ⊢ z ∶ Nat
    ⊢s : 
        Γ ⊢ a ∶ Nat →
        Γ ⊢ s a ∶ Nat
    ⊢natel : ∀ {zb sb} →
        Γ ⊢ n ∶ Nat →
        Γ ⊢ zb ∶ P →
        Γ ⊢ sb ∶ P →
        Γ ⊢ elimnat n 
                zb∶ zb 
                sb∶ sb 
            ∶ P 
    -- Lists
    ⊢nill :
        Γ ⊢ nill ∶ List A -- may need to add annotations later
    ⊢∷l :
        Γ ⊢ a ∶ A →
        Γ ⊢ b ∶ List A →
        Γ ⊢ a ∷l b ∶ List A
    ⊢listel : 
        Γ ⊢ l ∶ List A →
        Γ ⊢ nb ∶ P → -- !!!! put things in the context
        Γ ⊢ cb ∶ P → 
        Γ ⊢ eliml l 
                nb∶ nb 
                cb∶ cb 
            ∶ P 
    -- Vecs
    ⊢nilv :  
        Γ ⊢ nilv ∶ Vec A
    ⊢∷v :
        Γ ⊢ a ∶ A →
        Γ ⊢ n ∶ Nat →
        Γ ⊢ b ∶ Vec A →
        Γ ⊢ a ∷v b 𝕟 n ∶ Vec A
    ⊢vecel : 
        Γ ⊢ b ∶ Vec A →
        -- should pi = delta?
        -- is it really 0 usage mode?
        Γ ⊢ nb ∶ P →
        -- assuming that the constructors are not heterogenous, I think they might need to be rho
        ((((Γ , Nat) , A) , Vec A) , P) ⊢ cb ∶ P →
        Γ ⊢ elimv b 
                nb∶ nb 
                cb∶ cb 
            ∶ P