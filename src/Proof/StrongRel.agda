module Proof.StrongRel where

open import Data.Nat
open import RunId

private variable
    A B C D P : Type
    a a' b c d : Term
    as bs cs nb cb : Term
    zb sb : Term
    n m : Term

    σ π ρ δ : Quantity

    i j k : ℕ

data _~ₛ_ : Term → Term → Set where
    ------ Equiv rules
    ~ₛrefl :
        A ~ₛ A
    ~ₛsym :
        B ~ₛ A →
        A ~ₛ B
    ~ₛtrans :
        A ~ₛ B →
        B ~ₛ C →
        A ~ₛ C
 
    ------ Types
    ---- Functions
    ~ₛpiω : 
        A ~ₛ C  →
        B ~ₛ D →
        (A 𝕢 ω ⟶ B) ~ₛ (C 𝕢 ω ⟶ D) 
    ~ₛpi𝟘 : 
        B ~ₛ( D ↑ 1 ≥ 0) →
        (A 𝕢 𝟘 ⟶ B) ~ₛ D 
    ~ₛpir :  
        A ~ₛ B →
        (A ⟶r B) ~ₛ (A ⟶r A) 
    ---- Sigma 
    ~ₛ×𝟘₁ :
        B ~ₛ (C ↑ 1 ≥ 0) → 
        ((A 𝕢 𝟘) × (B 𝕢 ω)) ~ₛ C
    ~ₛ×𝟘₂ :
        A ~ₛ C → 
        ((A 𝕢 ω) × (B 𝕢 𝟘)) ~ₛ C
    ---- Sum 
    ~ₛ＋𝟘₁ : 
        A ~ₛ C →
        ((A 𝕢 𝟘) ＋ (B 𝕢 ω)) ~ₛ C
    ~ₛ＋𝟘₂ : 
        B ~ₛ C →
        ((A 𝕢 ω) ＋ (B 𝕢 𝟘)) ~ₛ C
    ---- Vec
    ~ₛvecω : 
        n ~ₛ m →
        A ~ₛ B →
        Vec A (n 𝕢 ω) ~ₛ Vec B (m 𝕢 ω)
    ~ₛvec𝟘 :
        A ~ₛ B →
        Vec A (n 𝕢 𝟘) ~ₛ List B
    
    ------ Terms
    
    ---- Constructors 
    -- Functions
    ~ₛlamω :
        b ~ₛ c →
        (ƛ∶ A 𝕢 ω ♭ b)  ~ₛ (ƛ∶ A 𝕢 ω ♭ c)
    ~ₛlam𝟘 :
        b ~ₛ (c ↑ 1 ≥ 0) →
        (ƛ∶ A 𝕢 𝟘 ♭ b)  ~ₛ c
    ~ₛlamr : 
        b ~ₛ var 0 → 
        (ƛr∶ A ♭ b) ~ₛ (ƛr∶ A ♭ var 0)
    -- Sigma 
    ~ₛ⟨,𝟘⟩ : 
        a ~ₛ c → 
        ⟨ a 𝕢 ω , b 𝕢 𝟘 ⟩ ~ₛ c 
    ~ₛ⟨𝟘,⟩ : 
        b ~ₛ (c ↑ 1 ≥ 0) → 
        ⟨ a 𝕢 𝟘 , b 𝕢 ω ⟩ ~ₛ c 
    -- Sum 
    ~ₛinl<,𝟘> :
        a ~ₛ c →
        (inl< ω , 𝟘 > a) ~ₛ c
    ~ₛinr<𝟘,> :
        b ~ₛ c →
        (inr< 𝟘 , ω > b) ~ₛ c 
    -- Nat
    ~ₛs : 
        n ~ₛ m →
        s n ~ₛ s m
    -- List
    ~ₛlist : 
        A ~ₛ B →
        List A ~ₛ List B
    ~ₛ∷l :
        a ~ₛ c →
        as ~ₛ cs →
        (a ∷l as) ~ₛ (c ∷l cs)    
    -- Vec 
    ~ₛnilvω :
        nilvω ~ₛ nilvω
    ~ₛnilv𝟘 :
        nilv𝟘 ~ₛ nill 
    ~ₛ∷vω : 
        a ~ₛ c →
        as ~ₛ cs →
        n ~ₛ m →
        (a ∷v as 𝕟ω n) ~ₛ (c ∷v cs 𝕟ω m)
    ~ₛ∷v𝟘 : 
        a ~ₛ c →
        as ~ₛ cs →
        (a ∷v as 𝕟𝟘 n) ~ₛ (c ∷l cs)

    ---- Eliminators
    -- Functions
    ~ₛappω : 
        b ~ₛ d →
        a ~ₛ c →
        (b ·ω a) ~ₛ (d ·ω c)
    ~ₛapp𝟘 : 
        b ~ₛ d →
        (b ·𝟘 a) ~ₛ d
    ~ₛappr : 
        -- Need A here annotated in app
        b ~ₛ (ƛω∶ A ♭ var 0) → 
        a ~ₛ c → 
        (b ·ᵣ a) ~ₛ c
    -- Sigmas 
    ~ₛel<𝟘,> :
        -- weaken with erased _ : B 
        b ~ₛ (c ↑ 1 ≥ 0) → 
        (el×< 𝟘 , ω >[ A , B ] a P b) ~ₛ ((ƛω∶ A ♭ c) ·ω a)
    ~ₛel<,𝟘> :
        -- weaken with erased _ : A 
        b ~ₛ (c ↑ 1 ≥ 1) → 
        -- Need to change B because of strengthening..?
        (el×< 𝟘 , ω >[ A , B ] a P b) ~ₛ ((ƛω∶ B ♭ c) ·ω a)
    -- Should this rule only exist for variables?
    ~ₛelᵣ<,> : 
        -- Shift by two? 
        (d [ 2 + i / ⟨ (var 1 𝕢 π) , (var 0 𝕢 ρ) ⟩ ]) ~ᵣ ⟨ (var 1 𝕢 π) , (var 0 𝕢 ρ) ⟩ →
        elᵣ×< σ , π >[ A , B ] (var i) P b ~ₛ var i
    -- Sum 
    ~ₛel＋<𝟘,> : 
        a ~ₛ a' →
        c ~ₛ d → 
        (el＋< 𝟘 , ω >[ A , B ] a P b c) ~ₛ ((ƛω∶ B ♭ d) ·ω a')
    ~ₛel＋<,𝟘> : 
        a ~ₛ a' →
        b ~ₛ d → 
        (el＋< ω , 𝟘 >[ A , B ] a P b c) ~ₛ ((ƛω∶ A ♭ d) ·ω a')
    ~ₛelᵣ＋ : 
        (b [ suc i / inl< π , ρ > (var 0) ]) ~ᵣ inl< π , ρ > (var 0) → 
        (c [ suc i / inr< π , ρ > (var 0) ]) ~ᵣ inr< π , ρ > (var 0) → 
        (elᵣ＋< ω , 𝟘 >[ A , B ] (var i) P b c) ~ₛ var i
    -- Nat 
    ~ₛelᵣℕ : 
        (zb [ i / z ]) ~ᵣ z →
        (sb [ 1 / var 0 ] [ 2 + i / s  (var 0) ]) ~ᵣ (s (var 0)) →
        (elᵣNat (var i) P b c) ~ₛ var i 
    -- List 
    -- Should this rule only exist for variables?
    ~ₛelᵣList : 
        (nb [ i / nill ]) ~ᵣ nill →
        (cb [ 1 / var 0 ] [ 3 + i / var 2 ∷l var 0 ]) ~ᵣ (var 2 ∷l var 0) →
        (elᵣList[ A ] (var i) P nb cb) ~ₛ var i 
    -- Vec 
    ~ₛelᵣVec : 
        (nb [ i / nilv𝕢 δ ]) ~ᵣ (nilv𝕢 δ) → 
        (cb [ 1 / var 0 ] [ 4 + i / var 2 ∷v var 0 𝕟 var 3 𝕢 δ ]) ~ᵣ (var 2 ∷v var 0 𝕟 var 3 𝕢 δ) → 
        (elᵣVec[ A ]< δ > (var i) P nb cb) ~ₛ var i