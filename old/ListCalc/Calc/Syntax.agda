module ListCalc.Calc.Syntax where

open import Data.Nat using (ℕ)
    
data Term : Set  where
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


data Context : Set where
    [] : Context
    _,_ : (Γ : Context) → Term → Context

data _∋_ : (Γ : Context) → Term → Set where
  Z : ∀ {A} {Γ : Context}
    →  (Γ , A) ∋ A

  S : ∀ {A} {B} {Γ : Context}
    -- Ensure there is a lookup judgement in submodule
    → Γ ∋ A
    →  (Γ , B) ∋ A