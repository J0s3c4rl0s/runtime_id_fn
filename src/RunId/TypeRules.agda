module RunId.TypeRules where

open import RunId.Syntax
open import RunId.Utils

-- open import Data.Product using (_×_) renaming (_,_ to _,'_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
    Γ : Context
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Type
    a a' b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term
    
    i j 𝓁 𝓁₁ 𝓁₂ : ℕ


data _＝_ : Term → Term → Set
data _⊢_∶_ : Context → Annotation a σ → Type → Set
data _~ᵣ_ : Term → Term → Set

-- For now it can be an annotation bc quants are only 0 or 1
data _⊢_∶_ where
    ⊢var :
        (i : Γ ∋ (A 𝕢 ρ)) →
        σ ≤q ρ →
        -- Avoiding green slime in the easiest way possible
        {num : ℕ} →
        (eq : (∋→ℕ i) ≡ num) →
        Γ ⊢ var num 𝕢 σ ∶ (A ↑ (suc (∋→ℕ i)) ≥ 0)
    
    -- functions
    ⊢pi :
        -- Not sure if this should be 0 usage for : Sett ? 
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- same universe level?
        Γ ⊢ (A 𝕢 π ⟶ B ) 𝕢 𝟘 ∶ Sett 𝓁 
    -- Add special rules!!
    ⊢rpi : 
        -- (A ↑ 1 ≥ 0) ~ᵣ B →
        -- Not sure if this should be 0 usage for : Sett ? 
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- needs to be nonzero arg
        -- same universe level?
        Γ ⊢ A ⟶r B 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢lam : ∀ {Γ : Context} →
        -- Are the annotations in Γ arbitrary? 
        (Γ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        Γ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (A 𝕢 π ⟶ B)
    ⊢rlam : ∀ {Γ : Context} →
        b ~ᵣ var 0 →
        -- Are the annotations in Γ arbitrary? 
        (Γ , A 𝕢 (ω *q σ)) ⊢ b 𝕢 σ ∶ B →
        -- Is this rule redundant since there is a formation rule
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        Γ ⊢ (ƛr∶ A ♭ b) 𝕢 σ ∶ (A ⟶r B)
    ⊢app : 
        Γ ⊢ a 𝕢 σ ∶ (A 𝕢 π ⟶ B) →
        Γ ⊢ b 𝕢 π *q σ ∶ A →
        Γ ⊢ (a · b 𝕢 π) 𝕢 σ ∶  (B [ 0 / b ])
    ⊢appᵣ : 
        Γ ⊢ a 𝕢 σ ∶ (A ⟶r B) →
        Γ ⊢ b 𝕢 ω *q σ ∶ A →
        Γ ⊢ (a ·ᵣ b) 𝕢 σ ∶  (B [ 0 /  b ])

    -- Products
    -- Fix universe levels 
    -- Exclude having both sides erased?
    ⊢× : 
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁 →
        (Γ , A 𝕢 π) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁 →
        Γ ⊢ (A 𝕢 π) × (B 𝕢 ρ) 𝕢 𝟘 ∶ Sett 𝓁
    ⊢⟨,⟩ : 
        Γ ⊢ a 𝕢 σ *q π ∶ A → 
        (Γ , A 𝕢 π) ⊢ b 𝕢 σ *q ρ ∶ B → 
        Γ ⊢ ⟨(a 𝕢 π) , (b 𝕢 ρ)⟩ 𝕢 σ ∶ ((A 𝕢 π) × (B 𝕢 ρ))
    -- finish this 
    ⊢el× :  
        Γ ⊢ c 𝕢 σ ∶ ((A 𝕢 π) × (B 𝕢 ρ)) → 
        Γ ⊢ P 𝕢 𝟘 ∶ ((A 𝕢 π) × (B 𝕢 ρ) 𝕢 σ ⟶ Sett 𝓁) → 
        (Γ , A 𝕢 π , B 𝕢 ρ) ⊢ d 𝕢 σ ∶ (P · ⟨ (A 𝕢 π) , (B 𝕢 ρ) ⟩ 𝕢 σ) →
        Γ ⊢ el×< π , ρ >[ A , B ] c P d 𝕢 σ ∶ (P · c 𝕢 σ)
    ⊢elᵣ× : 
        Γ ⊢ var i 𝕢 σ ∶ ((A 𝕢 π) × (B 𝕢 ρ)) → 
        Γ ⊢ P 𝕢 𝟘 ∶ ((A 𝕢 π) × (B 𝕢 ρ) 𝕢 σ ⟶ Sett 𝓁) → 
        (Γ , A 𝕢 π , B 𝕢 ρ) ⊢ d 𝕢 σ ∶ (P · ⟨ (A 𝕢 π) , (B 𝕢 ρ) ⟩ 𝕢 σ) →
        (d [ i / ⟨ (var 1 𝕢 π) , (var 0 𝕢 ρ) ⟩ ]) ~ᵣ ⟨ (var 1 𝕢 π) , (var 0 𝕢 ρ) ⟩ → 
        Γ ⊢ elᵣ×< π , ρ >[ A , B ] (var i) P d 𝕢 σ ∶ (P · ⟨ (A 𝕢 π) , (B 𝕢 ρ) ⟩ 𝕢 σ)

    -- Sums
    -- Exclude having both sides erased?
    ⊢＋ : 
        -- Fix universe levels, should differ and join
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁 → 
        Γ ⊢ B 𝕢 𝟘 ∶ Sett 𝓁 → 
        Γ ⊢ (A 𝕢 π) ＋ (B 𝕢 ρ) 𝕢 𝟘 ∶ Sett 𝓁
    ⊢inl : 
        Γ ⊢ a 𝕢 σ *q π ∶ A → 
        Γ ⊢ (inl< π , ρ > a) 𝕢 σ ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ))
    ⊢inr : 
        Γ ⊢ a 𝕢 σ *q ρ ∶ B → 
        Γ ⊢ (inr< π , ρ > a) 𝕢 σ ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ))
    ⊢el＋ : ∀ {bₗ bᵣ} →
        Γ ⊢ c 𝕢 σ ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ)) → 
        Γ ⊢ P 𝕢 𝟘 ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ) 𝕢 σ ⟶ Sett 𝓁) → 
        (Γ , A 𝕢 π) ⊢ bₗ 𝕢 σ *q π ∶ (P · inl< π , ρ > (var 0) 𝕢 σ) → 
        (Γ , B 𝕢 ρ) ⊢ bᵣ 𝕢 σ *q ρ ∶ (P · inr< π , ρ > (var 0) 𝕢 σ) →
        Γ ⊢ el＋< π , ρ >[ A , B ] c P bₗ bᵣ 𝕢 σ ∶ (P · c 𝕢 σ) 
    ⊢elᵣ＋ : ∀ {bₗ bᵣ} →
        Γ ⊢ var i 𝕢 σ ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ)) → 
        Γ ⊢ P 𝕢 𝟘 ∶ ((A 𝕢 π) ＋ (B 𝕢 ρ) 𝕢 σ ⟶ Sett 𝓁) → 
        (Γ , A 𝕢 π) ⊢ bₗ 𝕢 σ *q π ∶ (P · inl< π , ρ > (var 0) 𝕢 σ) → 
        (Γ , B 𝕢 ρ) ⊢ bᵣ 𝕢 σ *q ρ ∶ (P · inr< π , ρ > (var 0) 𝕢 σ) →
        (bₗ [ i / inl< π , ρ > (var 0) ]) ~ᵣ inl< π , ρ > (var 0) → 
        (bᵣ [ i / inr< π , ρ > (var 0) ]) ~ᵣ inr< π , ρ > (var 0) → 
        Γ ⊢ elᵣ＋< π , ρ >[ A , B ] (var i) P bₗ bᵣ 𝕢 σ ∶ (P · var i 𝕢 σ)  



    -- Nats
    ⊢Nat : 
        Γ ⊢ Nat 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢z : 
        Γ ⊢ z 𝕢 σ ∶ Nat
    ⊢s : 
        Γ ⊢ a 𝕢 σ ∶ Nat →
        Γ ⊢ s a 𝕢 σ ∶ Nat
    -- either nothing is erased or everything is (?)
    ⊢natel : ∀ {zb sb} →
        Γ ⊢ n 𝕢 σ ∶ Nat →
        -- Maybe P and n should match usage (check?) or comes naturally from rule
        -- Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett 𝓁 ) →
        -- enforces that argument to forming this type are erased
        (Γ , Nat 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        Γ ⊢ zb 𝕢 σ ∶ (P [ 0 / z ]) →
        (Γ , Nat 𝕢 ρ , P [ 0 / var 0 ] 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P [ 0 / s (var 1) ]) →
        Γ ⊢ elNat n P 
                zb 
                sb 
            𝕢 σ ∶ (P [ 0 / n ])
    ⊢natelᵣ : ∀ {zb sb} →
        Γ ⊢ var i 𝕢 σ ∶ Nat →
        (Γ , Nat 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        -- check type? Depends on n?
        Nat ~ᵣ P →
        Γ ⊢ zb 𝕢 σ ∶ (P [ 0 / z ]) →
        (zb [ i / z ]) ~ᵣ z →
        (Γ , Nat 𝕢 ρ , P [ 0 / var 0 ] 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P [ 0 / s (var 1) ]) →
        -- Cons branch is runid, sub tail to acc
        (sb [ 1 / var 0 ] [ i / s (var 0) ]) ~ᵣ (s (var 0)) →
        Γ ⊢ elᵣNat (var i) P 
                zb 
                sb 
            𝕢 σ ∶ (P [ 0 / n ])
    
    -- Lists
    ⊢List : 
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        Γ ⊢ List A 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nill :
        Γ ⊢ nill 𝕢 σ ∶ List A -- may need to add annotations later
    ⊢∷l :
        Γ ⊢ a 𝕢 σ ∶ A →
        Γ ⊢ b 𝕢 σ ∶ List A →
        Γ ⊢ a ∷l b 𝕢 σ ∶ List A
    ⊢listel : 
        Γ ⊢ l 𝕢 σ ∶ List A →
        (Γ , List A 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 → 
        Γ ⊢ nb 𝕢 σ ∶ (P [ 0 / nill ]) → 
        -- I presume list elements must have same erasure as List
        (Γ , 
            A 𝕢 σ , 
            List A 𝕢 σ , 
            P [ 0 / var 0 ] 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P [ 0 / (var 2 ∷l var 1) ]) → 
        Γ ⊢ elList[ A ] l P 
                nb 
                cb 
            𝕢 σ ∶ (P [ 0 / l ])
    ⊢listelᵣ : 
        (Γ Γ Γ : Context) →
        Γ ⊢ var i 𝕢 σ ∶ List A →
        -- changing it back bc I dont need compiler anymore (maybe)
        Γ ⊢ P 𝕢 𝟘 ∶ (List A 𝕢 𝟘 ⟶ Sett 𝓁) → 
        -- shifts?
        List A ~ᵣ (P ·𝟘 var 0) →
        Γ ⊢ nb 𝕢 σ ∶ (P ·𝟘 nill ) → 
        (nb [ i / nill ]) ~ᵣ nill →
        (Γ , 
            A 𝕢 σ , 
            List A 𝕢 σ , 
            (P ·𝟘 var 0) 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P ·𝟘  (var 2 ∷l var 1)) →
        (cb [ 1 / var 0 ] [ 3 + i / var 2 ∷l var 0 ]) ~ᵣ (var 2 ∷l var 0) →
        Γ ⊢ elᵣList[ A ] (var i) P 
                nb 
                cb 
            𝕢 σ ∶ (P ·𝟘 var i)
    
    -- Vecs
    ⊢Vec : {Γ : Context} →
        Γ ⊢ n 𝕢 σ ∶ Nat  →
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        Γ ⊢ Vec A (n 𝕢 σ) 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nilv :  
        Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        Γ ⊢ nilv𝕢 π 𝕢 σ ∶ Vec A (z 𝕢 π)
    ⊢∷v :
        Γ ⊢ a 𝕢 σ ∶ A →
        Γ ⊢ n 𝕢 π ∶ Nat →
        Γ ⊢ b 𝕢 σ ∶ Vec A (n 𝕢 π) →
        Γ ⊢ (a ∷v b 𝕟 n 𝕢 π) 𝕢 σ ∶ Vec A (s n 𝕢 π)
    ⊢vecel :  
        Γ ⊢ b 𝕢 σ ∶ Vec A (n 𝕢 δ) →
        -- I enforce that P is only compile time? should I?
        (Γ , Nat 𝕢 𝟘 , Vec A (var 0 𝕢 δ) 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        Γ ⊢ nb 𝕢 σ ∶ (P [ 0 / z ] [ 1 / nilv𝕢 δ ]) → 
        (Γ , 
            Nat 𝕢 π , 
            A 𝕢 σ , 
            Vec A (var 1 𝕢 δ) 𝕢  σ , 
            P [ 0 / var 0 ] [ 1 / var 2 ] 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P [ 0 / var 3 ] [ 1 / var 2 ∷v var 1 𝕟 var 3 𝕢 δ ]) →
        Γ ⊢ elVec[ A ]< δ > b P 
                nb 
                cb 
            𝕢 σ ∶ (P [ 0 / n ] [ 1 / b ])
    ⊢vecelᵣ :  
        Γ ⊢ var i 𝕢 σ ∶ Vec A (n 𝕢 δ) →
        -- I enforce that P is only compile time? should I?
        (Γ , Nat 𝕢 𝟘 , Vec A (var 0 𝕢 δ) 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        -- how to connect index in P and index in type?
        -- cant substitute for 1 in here
        (Vec (A ↑ 2 ≥ 0) (n ↑ 2 ≥ 0 𝕢 δ)) ~ᵣ (P [ 0 / n ↑ 2 ≥ 0 ]) → 
        Γ ⊢ nb 𝕢 σ ∶ (P [ 0 / z ] [ 1 / nilv𝕢 δ ]) → 
        (nb [ i / nilv𝕢 σ ]) ~ᵣ (nilv𝕢 σ) → 
        (Γ , 
            Nat 𝕢 π , 
            A 𝕢 σ , 
            Vec A (var 1 𝕢 δ) 𝕢  σ , 
            P [ 0 / var 0 ] [ 1 / var 2 ] 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P [ 0 / var 3 ] [ 1 / var 2 ∷v var 1 𝕟 var 3 𝕢 δ ]) →
        -- IH through choice, left acc right tail
        (cb [ 4 + i / var 2 ∷v var 0 𝕟 var 3 𝕢 σ ]) ~ᵣ (var 2 ∷v var 0 𝕟 var 3 𝕢 σ) ⊎ 
            (cb [ 4 + i / var 2 ∷v var 1 𝕟 var 3 𝕢 σ ]) ~ᵣ (var 2 ∷v var 1 𝕟 var 3 𝕢 σ) → 
        Γ ⊢ elᵣVec[ A ]< δ > (var i) P 
                nb 
                cb 
            𝕢 σ ∶ (P [ 0 / n ] [ 1 / b ])
    
    -- Prop equal
    ⊢≃ : 
        Γ ⊢ a 𝕢 𝟘 ∶ A →
        Γ ⊢ b 𝕢 𝟘 ∶ A → 
        Γ ⊢ (a ≃ b) 𝕢 𝟘 ∶ Sett 𝓁
    ⊢rfl : 
        Γ ⊢ rfl 𝕢 σ ∶ (a ≃ a)
    ⊢subst : 
        -- Need to know the type of equality?
        Γ ⊢ a 𝕢 σ ∶ (A [ i / c ] [ j / rfl ]) →
        -- where I get A from?
        -- This seems absurd.... I cant use the given equality without the eliminator...
        Γ ⊢ P 𝕢 𝟘 ∶ ((A 𝕢 σ) ⟶ ((c ≃ d) 𝕢 π) ⟶ Sett 𝓁) → 
        Γ ⊢ b 𝕢 π ∶ (c ≃ d) → 
        -- Should I check that i and j are in scope? 
        -- Is there a different way to define this?
        Γ ⊢ (subst< π > a P b) 𝕢 σ ∶ ((P · a 𝕢 σ) · b 𝕢 π) 

    ⊢Sett : 
        Γ ⊢ Sett 𝓁 𝕢 𝟘 ∶ Sett (suc 𝓁) 
    ⊢conv : {Γ : Context} → 
        Γ ⊢ a 𝕢 σ ∶ A →
        A ＝ B → 
        Γ ⊢ a 𝕢 σ ∶ B

    ---- QTT rules 
    ⊢TM-𝟘 : {Γ : Context} →
        Γ ⊢ a 𝕢 σ ∶ A →
        Γ ⊢ a 𝕢 𝟘 ∶ A


infix 30 _＝_
-- rewrite this so its consistent in order (e.g. introducion-formation-congruence-reduction)
-- Do I need to make all judgements be in 𝟘
data _＝_ where
    {-   
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ a ↑_≥_  (suc (∋→ℕ i)) 0
    -}
    ＝pi : 
        A ＝ C → 
        B ＝ D →
        (A 𝕢 σ ⟶ B) ＝ (C 𝕢 σ ⟶ D)

    ＝piᵣ : 
        A ＝ C → 
        B ＝ D →
        (A ⟶r B) ＝ (C ⟶r D)
    ＝lam :
        b ＝ c →
        (ƛ∶ A 𝕢 σ ♭ b)  ＝ (ƛ∶ A 𝕢 σ ♭ c)
    ＝lamᵣ :
        A ＝ B →
        b ＝ c →
        (ƛr∶ A ♭ b)  ＝ (ƛr∶ B ♭ c)
    ＝app : 
        b ＝ d →
        a ＝ c →
        (b · a 𝕢 σ) ＝ (d · c 𝕢 σ)
    ＝appᵣ : 
        b ＝ d →
        a ＝ c →
        (b ·ᵣ a) ＝ (d ·ᵣ c)
    -- Look into substitution rules 
    ＝beta : ((ƛ∶ A 𝕢 σ ♭ b) · a 𝕢 σ) ＝ (b [ 0 / a ])
    ＝betaᵣ : ((ƛ∶ A 𝕢 ω ♭ b) ·ᵣ a) ＝ (b [ 0 / a ])
    {-
    ＝lift : 
        (Γ , A 𝕢  σ) ⊢ b 𝕢 π ∶ B →
        a ＝ c →
        b [ a / 0 ] ＝ ( b [ c / 0 ]) 
    -}
    -- equiv properties
    ＝refl : A ＝ A
    ＝sym : 
        A ＝ B →
        B ＝ A 
    ＝trans : 
        A ＝ B →
        B ＝ C →
        A ＝ C
    
    ---- eliminators 
    -- nats
    ＝natelz :
        m ＝ z →
        (elNat m P 
            zb 
            sb) 
            ＝ 
            zb
    ＝natels :
        n ＝ s n →
        (elNat n P 
                zb 
                sb) 
            ＝ 
            a →
        (elNat m P 
                zb 
                sb) 
            ＝ 
            ((sb [ 1 / n ]) [ 0 / a ])
    -- list
    ＝listeln :
        cs ＝ nill →
        (elList[ A ] cs P 
                nb 
                cb) 
            ＝ 
            nb
    ＝listelc :     
        cs ＝ (a ∷l as) →
        (elList[ A ] as P 
                nb 
                cb) 
            ＝ 
            b →
        (elList[ A ] cs P 
                nb 
                cb) 
            ＝ 
            (((cb [ 2 / a ]) [ 1 / as ]) [ 0 / b ])
            
    -- vec
    ＝veceln :
        cs ＝ (nilv𝕢 σ) →
        (elVec[ A ]< σ > cs P 
                nb 
                cb) 
            ＝  
            nb
    ＝vecelc :
        cs ＝ (a ∷v as 𝕟 n 𝕢 σ) → 
        (elVec[ A ]< σ > (nilv𝕢 σ) P
                nb 
                cb) 
            ＝ 
            b →
        (elVec[ A ]< σ > cs P
                nb 
                cb) 
            ＝ 
            -- Might be worthwhile to change n to fit the structure of ∷v
            ((((cb [ 3 / n ]) [ 2 / a ]) [ 1 / as ]) [ 0 / b ])
    
    ---- Cong rules for datatypes 
    -- Nat
    ＝s : 
        n ＝ m →
        s n ＝ s m
    -- List
    ＝list : 
        A ＝ B →
        List A ＝ List B
    ＝∷l :
        a ＝ c →
        as ＝ cs →
        (a ∷l as) ＝ (c ∷l cs)
    -- Vec
    ＝vec : 
        n ＝ m →
        A ＝ B →
        Vec A (n  𝕢 σ) ＝ Vec B (m 𝕢 σ)
    ＝∷v :
        a ＝ c →
        as ＝ cs →
        n ＝ m →
        (a ∷v as 𝕟 n 𝕢 σ) ＝ (c ∷v cs 𝕟 m 𝕢 σ)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    ⊢TM＝𝟘 : {Γ : Context} →
        a ＝ b →
        a ＝ b

infix 30 _~ᵣ_ 

-- Rearrenge this with boring and interesting rules
-- Should I only define this 
-- Could add types 
data _~ᵣ_ where
    ------ Equiv rules
    ~ᵣrefl :
        A ~ᵣ A
    ~ᵣsym :
        B ~ᵣ A →
        A ~ᵣ B
    ~ᵣtrans :
        A ~ᵣ B →
        B ~ᵣ C →
        A ~ᵣ C

    ------ Types
    ---- Functions
    ~ᵣpiω : 
        A ~ᵣ C  →
        B ~ᵣ D →
        (A 𝕢 ω ⟶ B) ~ᵣ (C 𝕢 ω ⟶ D) 
    ~ᵣpi𝟘 : 
        B ~ᵣ( D ↑ 1 ≥ 0) →
        (A 𝕢 𝟘 ⟶ B) ~ᵣ D 
    ~ᵣpir : 
        A ~ᵣ B →
        (A ⟶r B) ~ᵣ (A ⟶r A) 
    ---- Sigma 
    ~ᵣ×𝟘₁ :
        B ~ᵣ (C ↑ 1 ≥ 0) → 
        ((A 𝕢 𝟘) × (B 𝕢 ω)) ~ᵣ C
    ~ᵣ×𝟘₂ :
        A ~ᵣ C → 
        ((A 𝕢 ω) × (B 𝕢 𝟘)) ~ᵣ C
    ---- Sum 
    ~ᵣ＋𝟘₁ : 
        A ~ᵣ C →
        ((A 𝕢 𝟘) ＋ (B 𝕢 ω)) ~ᵣ C
    ~ᵣ＋𝟘₂ : 
        B ~ᵣ C →
        ((A 𝕢 ω) ＋ (B 𝕢 𝟘)) ~ᵣ C
    ---- Vec
    ~ᵣvecω : 
        n ~ᵣ m →
        A ~ᵣ B →
        Vec A (n 𝕢 ω) ~ᵣ Vec B (m 𝕢 ω)
    ~ᵣvec𝟘 :
        A ~ᵣ B →
        Vec A (n 𝕢 𝟘) ~ᵣ List B
    
    ------ Terms
    
    ---- Constructors 
    -- Functions
    ~ᵣlamω :
        b ~ᵣ c →
        (ƛ∶ A 𝕢 ω ♭ b)  ~ᵣ (ƛ∶ A 𝕢 ω ♭ c)
    ~ᵣlam𝟘 :
        b ~ᵣ (c ↑ 1 ≥ 0) →
        (ƛ∶ A 𝕢 𝟘 ♭ b)  ~ᵣ c
    ~ᵣlamr : 
        (ƛr∶ A ♭ b) ~ᵣ (ƛr∶ A ♭ var 0)
    -- Sigma 
    ~ᵣ⟨,𝟘⟩ : 
        a ~ᵣ c → 
        ⟨ a 𝕢 ω , b 𝕢 𝟘 ⟩ ~ᵣ c 
    ~ᵣ⟨𝟘,⟩ : 
        b ~ᵣ (c ↑ 1 ≥ 0) → 
        ⟨ a 𝕢 𝟘 , b 𝕢 ω ⟩ ~ᵣ c 
    -- Sum 
    ~ᵣinl<,𝟘> :
        a ~ᵣ c →
        (inl< ω , 𝟘 > a) ~ᵣ c
    ~ᵣinr<𝟘,> :
        b ~ᵣ c →
        (inr< 𝟘 , ω > b) ~ᵣ c 
    -- Nat
    ~ᵣs : 
        n ~ᵣ m →
        s n ~ᵣ s m
    -- List
    ~ᵣlist : 
        A ~ᵣ B →
        List A ~ᵣ List B
    ~ᵣ∷l :
        a ~ᵣ c →
        as ~ᵣ cs →
        (a ∷l as) ~ᵣ (c ∷l cs)    
    -- Vec 
    ~ᵣnilvω :
        nilvω ~ᵣ nilvω
    ~ᵣnilv𝟘 :
        nilv𝟘 ~ᵣ nill 
    ~ᵣ∷vω : 
        a ~ᵣ c →
        as ~ᵣ cs →
        n ~ᵣ m →
        (a ∷v as 𝕟ω n) ~ᵣ (c ∷v cs 𝕟ω m)
    ~ᵣ∷v𝟘 : 
        a ~ᵣ c →
        as ~ᵣ cs →
        (a ∷v as 𝕟𝟘 n) ~ᵣ (c ∷l cs)

    ---- Eliminators
    -- Functions
    ~ᵣappω : 
        b ~ᵣ d →
        a ~ᵣ c →
        (b ·ω a) ~ᵣ (d ·ω c)
    ~ᵣapp𝟘 : 
        b ~ᵣ d →
        (b ·𝟘 a) ~ᵣ d
    ~ᵣappr : 
        a ~ᵣ c →
        (b ·ᵣ a) ~ᵣ c
    -- Sigmas 
    ~ᵣel<𝟘,> :
        -- weaken with erased _ : B 
        b ~ᵣ (c ↑ 1 ≥ 0) → 
        (el×< 𝟘 , ω >[ A , B ] a P b) ~ᵣ ((ƛω∶ A ♭ c) ·ω a)
    ~ᵣel<,𝟘> :
        -- weaken with erased _ : A 
        b ~ᵣ (c ↑ 1 ≥ 1) → 
        -- Need to change B because of strengthening..?
        (el×< 𝟘 , ω >[ A , B ] a P b) ~ᵣ ((ƛω∶ B ♭ c) ·ω a)
    -- Should this rule only exist for variables?
    ~ᵣel<,>ᵣ : 
        elᵣ×< σ , π >[ A , B ] (var i) P b ~ᵣ var i
    -- Sum 
    ~ᵣel＋<𝟘,> : 
        a ~ᵣ a' →
        c ~ᵣ d → 
        (el＋< 𝟘 , ω >[ A , B ] a P b c) ~ᵣ ((ƛω∶ B ♭ d) ·ω a')
    ~ᵣel＋<,𝟘> : 
        a ~ᵣ a' →
        b ~ᵣ d → 
        (el＋< ω , 𝟘 >[ A , B ] a P b c) ~ᵣ ((ƛω∶ A ♭ d) ·ω a')
    ~ᵣelᵣ＋ : 
        (el＋< ω , 𝟘 >[ A , B ] (var i) P b c) ~ᵣ var i
    -- Nat 
    ~ᵣelℕᵣ :
        (elᵣNat (var i) P b c) ~ᵣ var i 
    -- List 
    -- Should this rule only exist for variables?
    ~ᵣelᵣList : 
        (elᵣList[ A ] (var i) P nb cb) ~ᵣ var i 
        