module ListCalc.QTT.Syntax where

open import Data.Nat using (ℕ)
-- open import Data.Product using (_×_; _,_)

data PreContext : Set
data Context : PreContext → Set
data Term : Set 

data Quantity : Set where 
    𝟘 : Quantity
    ω : Quantity

private variable
    Γ Δ Θ : PreContext
    cΓ cΓ' cΓ'' : Context Γ
    cΔ cΔ' cΔ'' : Context Δ
    cΘ : Context Θ
    A B C D P : Term
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term

data Annotation : Term → Quantity → Set where
    _𝕢_ : (A : Term) → (σ : Quantity) → Annotation A σ

-- might need well formed relation on this shit
data PreContext where
    [] : PreContext
    _,_ : (Γ : PreContext) → Term → PreContext

data Context where
    [] : Context []
    _,_ : Context Γ → Annotation A σ → Context (Γ , A)


infix 10 _,_
infix 12 _𝕢_
infix 8 _∋_

data _∋_ : Context Γ → Annotation A σ → Set where
  Z : ∀ {cΓ : Context Γ}
    →  (cΓ , (A 𝕢 σ)) ∋ (A 𝕢 σ)

  S : ∀ {A} {B} {cΓ : Context Γ}
    -- Ensure there is a lookup judgement in submodule
    → cΓ ∋ A 𝕢 σ
    →  (cΓ , B 𝕢 π) ∋ (A 𝕢 σ)

data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ∶_♭_ : Annotation A σ → Term → Term
    _·_ : Term → Term → Term

    -- data constructors
    ---- Nats
    z : Term
    s : Term → Term 
    -- list 
    nill : Term 
    _∷l_ : Term → Term → Term 
    -- vec
    nilv : Term 
    _∷v_𝕟_ : Term → Term → Term → Term 

    ---- elims 
    -- Nat
    elimnat_P∶_zb∶_sb∶_ : Term → Term → Term → Term → Term
    -- List
    -- For now annotate parametrized type
    eliml_P∶_nb∶_cb∶_ : (list : Term) → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    -- vec
    -- For now annotate length
    elimv_P∶_nb∶_cb∶_ : (vec : Term) → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    
    -- Types
    Nat : Term
    List : Term → Term
    Vec : Annotation A σ → Term → Term
    ∶_⟶_ : Annotation A σ → Term → Term -- Pi type
    Sett : ℕ → Term -- Universe 
