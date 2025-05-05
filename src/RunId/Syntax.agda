module RunId.Syntax where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)


data PreContext : Set
data Context : PreContext → Set
data Term : Set 

data Quantity : Set where 
    𝟘 : Quantity
    ω : Quantity

-- Add an alias for types for clarity
Type = Term

private variable
    Γ Δ Θ : PreContext
    cΓ cΓ' cΓ'' : Context Γ
    cΔ cΔ' cΔ'' : Context Δ
    cΘ : Context Θ
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Type
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term



data Annotation : Type → Quantity → Set where
    _𝕢_ : (A : Type) → (σ : Quantity) → Annotation A σ

data PreContext where
    [] : PreContext
    _,_ : (Γ : PreContext) → Type → PreContext

data Context where
    [] : Context []
    _,_ : Context Γ → Annotation A σ → Context (Γ , A)

infixl 10 _,_
infix 12 _𝕢_
infix 8 _∋_

data _∋_ : Context Γ → Annotation A σ → Set where
  Z : ∀ {cΓ : Context Γ}
    →  (cΓ , (A 𝕢 σ)) ∋ (A 𝕢 σ)

  S : ∀ {A} {B} {cΓ : Context Γ}
    -- Ensure there is a lookup judgement in submodule
    → cΓ ∋ A 𝕢 σ
    →  (cΓ , B 𝕢 π) ∋ A 𝕢 σ

data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ∶_♭_ : Annotation A σ → Term → Term
    -- Better to take an extra arg to determine its a runtime ID (annot)
    -- RuntimeId, any erased args? Forced annotations?
    ƛr∶_♭_ : Type → Term → Term
    _·_𝕢_ : Term → Term → Quantity → Term
    _·ᵣ_ : Term → Term → Term

    ---- data cons
    -- Sigma 
    ⟨_,_⟩ : Annotation A σ → Annotation B π → Type
    -- Sum 
    inl<_,_> : 
        Quantity → Quantity → 
        Term → 
        Term
    inr<_,_> : 
        Quantity → Quantity → 
        Term → 
        Term
    -- Nats
    z : Term
    s : Term → Term 
    -- list 
    nill : Term 
    _∷l_ : Term → Term → Term 
    -- vec
    nilv𝕢_ : Quantity → Term 
    _∷v_𝕟_𝕢_ : Term → Term → Term → Quantity → Term 

    ---- elims 
    -- Sigma
    el×<_,_>[_,_] : 
        Quantity → Quantity → 
        Type → Type → 
        Term → 
        Term → 
        Term → 
        Term
    el×ᵣ<_,_>[_,_] : 
        Quantity → Quantity → 
        Type → Type → 
        Term → 
        Term → 
        Term → 
        Term
    -- Sum 
    el＋<_,_>[_,_] : 
        Quantity → Quantity →
        Type → Type → 
        -- a
        Term →  
        -- P
        Term →  
        -- b
        Term →
        -- c 
        Term →  
        Term   
    el＋ᵣ<_,_>[_,_] : 
        Quantity → Quantity →
        Type → Type → 
        -- a
        Term →  
        -- P
        Term →  
        -- b
        Term →
        -- c 
        Term →  
        Term   
    -- Nat
    elNat : Term → Term → Term → Term → Term
    elNatᵣ : Term → Term → Term → Term → Term
    -- List
    elList[_] : (innerty : Type) → (list : Term) → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    elListᵣ[_] : (innerty : Type) → (list : Term) → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    -- vec
    -- Annotation is for if vec has erased index or not
    elVec[_]<_> : (innerty : Type) → Quantity → Term → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    elVecᵣ[_]<_> : (innerty : Type) → Quantity → Term → (P : Term) → (nilB : Term) → (∷B : Term) → Term
    
    -- Types
    Nat : Type
    List : Type → Type
    Vec : Type → Annotation n σ → Type
    ∶_⟶_ : Annotation A σ → Type → Type -- Pi type
    r∶_⟶_ : Type → Type → Type -- Runtime Pi type
    ∶_×∶_ : Annotation A σ → Annotation B π → Type 
    _＋_ : Annotation A σ → Annotation B π → Type
    Sett : ℕ → Type -- Universe 

infixr 9 ∶_⟶_

pattern ƛ𝟘∶_♭_ A b = ƛ∶_♭_ (A 𝕢 𝟘) b
pattern ƛω∶_♭_ A b = ƛ∶_♭_ (A 𝕢 ω) b
pattern _·𝟘_ f a = _·_𝕢_ f a 𝟘
pattern _·ω_ f a = _·_𝕢_ f a ω

infixl 9 _·ω_
infixl 9 _·𝟘_

pattern Vec𝟘 A n = Vec A (n 𝕢 𝟘)
pattern Vecω A n = Vec A (n 𝕢 ω)
pattern nilv𝟘 = nilv𝕢_ 𝟘
pattern nilvω = nilv𝕢_ ω
pattern _∷v_𝕟𝟘_ a as n = _∷v_𝕟_𝕢_ a as n 𝟘
pattern _∷v_𝕟ω_ a as n = _∷v_𝕟_𝕢_ a as n ω
 