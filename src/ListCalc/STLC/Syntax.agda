module ListCalc.STLC.Syntax where

open import Data.Nat using (ℕ)

data Context : Set
data Term : Set 
data Type : Set


data Context where
    [] : Context
    _,_ : (Γ : Context) → Type → Context

data _∋_ : (Γ : Context) → Type → Set where
  Z : ∀ {A} {Γ : Context}
    →  (Γ , A) ∋ A

  S : ∀ {A} {B} {Γ : Context}
    -- Ensure there is a lookup judgement in submodule
    → Γ ∋ A
    →  (Γ , B) ∋ A

data Type where
    -- Types
    Nat : Type
    List : Type → Type
    _⟶_ : Type → Type → Type
    
data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ_ : Term → Term
    _·_ : Term → Term → Term

    -- data cons
    ---- Nats
    z : Term
    s : Term → Term 
    -- list 
    nill : Term 
    _∷l_ : Term → Term → Term 
    
    ---- elims 
    -- Nat
    elimnat_zb∶_sb∶_ : Term → Term → Term → Term
    -- List
    eliml_nb∶_cb∶_ : (list : Term) → (nilB : Term) → (∷B : Term) → Term