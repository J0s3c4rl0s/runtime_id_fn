module ListCalc.QTT.TypeRules where

open import ListCalc.QTT.Syntax
open import ListCalc.QTT.Utils

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)


private variable
    Γ : PreContext
    cΓ cΓ' : Context Γ
    A B C D P : Term
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term
    𝓁 𝓁₁ 𝓁₂ : ℕ
    
data _⊢_＝_ : Context Γ → Term → Term → Set

-- For now it can be an annotation bc quants are only 0 or 1
data _⊢_∶_ : Context Γ → Annotation A σ → Term → Set where
    ⊢var :
        (i : cΓ ∋ (A 𝕢 σ)) →
        -- weird hack to do selected zeroing, may be nicer to have pre PreContext
        cΓ ⊢ var (∋→ℕ i) 𝕢 σ ∶ shiftindices A (suc (∋→ℕ i)) 0
    -- functions
    ⊢pi :
        -- Not sure if this should be 0 usage for : Sett ? 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- same universe level?
        zeroC Γ ⊢ ∶ A 𝕢 π ⟶ B 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢lam : ∀ {cΓ : Context Γ} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B)
    ⊢app : 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ π σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- addition in bottom sounds potentially annoying
        ( cΓ +c (π *c cΓ') ) ⊢ a · b 𝕢 σ ∶  (B [ b / 0 ])
    -- Nats
    ⊢Nat : 
        zeroC Γ ⊢ Nat 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢z : 
        zeroC Γ ⊢ z 𝕢 σ ∶ Nat
    ⊢s : 
        cΓ ⊢ a 𝕢 σ ∶ Nat →
        cΓ ⊢ s a 𝕢 σ ∶ Nat
    -- either nothing is erased or everything is (?)
    ⊢natel : ∀ {zb sb} →
        cΓ ⊢ n 𝕢 σ ∶ Nat →
        -- Maybe P and n should match usage (check?) or comes naturally from rule
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett 𝓁 ) →
        cΓ' ⊢ zb 𝕢 σ ∶ (P · z) →
        ((cΓ' , Nat 𝕢 ρ) , (P · var 0) 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P · s (var 1)) →
        (cΓ +c cΓ') ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            𝕢 σ ∶ (P · n)
    -- Lists
    ⊢List : 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ List A 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nill :
        zeroC Γ ⊢ nill 𝕢 σ ∶ List A -- may need to add annotations later
    ⊢∷l :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ b 𝕢 σ ∶ List A →
        cΓ ⊢ a ∷l b 𝕢 σ ∶ List A
    ⊢listel : {cΓ cΓ' : Context Γ} →
        cΓ ⊢ l 𝕢 σ ∶ List A →
        -- is it really 0 usage mode?
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ List A 𝕢 ρ ⟶ Sett 𝓁 ) → 
        cΓ' ⊢ nb 𝕢 σ ∶ (P · nill) → 
        -- I presume list elements must have same erasure as List
        (((cΓ' , A 𝕢 σ) , List A 𝕢 σ) , P · var 0 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P · (var 2 ∷l var 1)) → 
        (cΓ +c cΓ') ⊢ eliml l P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · l)
    -- Vecs
    ⊢Vec : {cΓ : Context Γ} →
        cΓ ⊢ n 𝕢 σ ∶ Nat  →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ Vec (n 𝕢 σ) A 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nilv :  
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ nilv 𝕢 σ ∶ Vec (z 𝕢 π) A
    ⊢∷v :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ n 𝕢 π ∶ Nat →
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 π) A →
        cΓ ⊢ a ∷v b 𝕟 n 𝕢 σ ∶ Vec (s n 𝕢 π) A
    ⊢vecel : {cΓ cΓ' : Context Γ} → 
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        -- should pi = delta?
        -- is it really 0 usage mode?
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ (∶ Vec (var 0 𝕢 δ) A 𝕢 ρ ⟶ Sett 𝓁 )) →
        cΓ' ⊢ nb 𝕢 σ ∶ ((P · z) · nilv) →
        -- assuming that the constructors are not heterogenous, I think they might need to be rho
        ((((cΓ' , Nat 𝕢 π) , A 𝕢 σ) , Vec (var 1 𝕢 δ) A 𝕢  σ) , P · var 0  𝕢 σ) ⊢ cb 𝕢 σ ∶ ((((((P · var 3) · (var 2 ∷v var 1 𝕟 var 3)))))) →
        (cΓ +c cΓ') ⊢ elimv b P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ ((P · n) · b)
    
    ⊢Sett : 
        zeroC Γ ⊢ Sett 𝓁 𝕢 𝟘 ∶ Sett (suc 𝓁) 
    {-
    ---- Prop equility
    -- bit superfluous/code duplication could make a = a and rely directly on ⊢conv
    ⊢≡ :
        zeroC Γ ⊢ a 𝕢 𝟘 ∶ A →
        zeroC Γ ⊢ b 𝕢 𝟘 ∶ A →
        zeroC Γ ⊢ (a ≡ b) 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢refl : {cΓ : Context Γ} →
        zeroC Γ ⊢ a ＝ b →
        zeroC Γ ⊢ (a ≡ b) 𝕢 𝟘 ∶ Sett 𝓁 →
        cΓ ⊢ refl 𝕢 σ ∶ (a ≡ b)
    ⊢contra :
        {!   !} →
        {!   !} →
        {!   !} ⊢ {!   !} ∶ {!   !} 
    -}
    
    ⊢conv : {cΓ : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ A ＝ B →
        cΓ ⊢ a 𝕢 σ ∶ B

    ---- QTT rules 
    ⊢TM-𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ a 𝕢 𝟘 ∶ A
    -- Maybe add TM-EQ-Zero?

-- Do I need to make all judgements be in 𝟘
data _⊢_＝_ where

    ＝pi : 
        cΓ ⊢ A ＝ C → 
        (cΓ , A 𝕢 σ) ⊢ B ＝ D →
        cΓ ⊢ ∶ A 𝕢 σ ⟶ B ＝ (∶ C 𝕢 σ ⟶ D)
    ＝lam :
        (cΓ , A 𝕢 σ) ⊢ b ＝ c →
        cΓ ⊢ ƛ∶ A 𝕢 σ ♭ b  ＝ (ƛ∶ A 𝕢 σ ♭ c)
    ＝app : 
        cΓ ⊢ b ＝ d →
        cΓ ⊢ a ＝ c →
        cΓ ⊢ b · a ＝ (d · c)

    -- Look into substitution rules 
    ＝beta : cΓ ⊢ (ƛ∶ A 𝕢 σ ♭ b) · a ＝ (b [ a / 0 ])

    ＝lift : 
        (cΓ , A 𝕢  σ) ⊢ b 𝕢 π ∶ B →
        cΓ ⊢ a ＝ c →
        cΓ ⊢ b [ a / 0 ] ＝ ( b [ c / 0 ]) 
    
    -- equiv properties
    ＝refl : cΓ ⊢ A ＝ A
    ＝sym : 
        cΓ ⊢ A ＝ B →
        cΓ ⊢ B ＝ A 
    ＝trans : 
        cΓ ⊢ A ＝ B →
        cΓ ⊢ B ＝ C →
        cΓ ⊢ A ＝ C
    
    ---- eliminators 
    -- nats
    ＝natelz :
        cΓ ⊢ m ＝ z →
        cΓ ⊢ elimnat m P∶ P 
            zb∶ zb 
            sb∶ sb 
            ＝ 
            zb
    ＝natels :
        cΓ ⊢ n ＝ s n →
        cΓ ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            a →
        cΓ ⊢ elimnat m P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            ((sb [ n / 1 ]) [ a / 0 ])
            -- ((sb · n) · a)
    -- list
    ＝listeln :
        cΓ ⊢ cs ＝ nill →
        cΓ ⊢ eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝listelc :     
        cΓ ⊢ cs ＝ (a ∷l as) →
        cΓ ⊢ eliml as P∶ P 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        cΓ ⊢ eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            (((cb [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- (((cb · a) · as) ·  b)
    -- vec
    ＝veceln :
        cΓ ⊢ cs ＝ nilv →
        cΓ ⊢ elimv cs P∶ P 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝vecelc :
        cΓ ⊢ cs ＝ (a ∷v as 𝕟 n) → 
        cΓ ⊢ elimv nilv P∶ P
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        cΓ ⊢ elimv cs P∶ P
                nb∶ nb 
                cb∶ cb 
            ＝ 
            -- Might be worthwhile to change n to fit the structure of ∷v
            ((((cb [ n / 3 ]) [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- ((((cb · n) · a) · as) · b)
    
    ---- Cong rules for datatypes 
    -- Nat
    ＝s : 
        cΓ ⊢ n ＝ m →
        cΓ ⊢ s n ＝ s m
    -- List
    ＝list : 
        cΓ ⊢ A ＝ B →
        cΓ ⊢ List A ＝ List B
    ＝∷l :
        cΓ ⊢ a ＝ c →
        cΓ ⊢ as ＝ cs →
        cΓ ⊢ a ∷l as ＝ (c ∷l cs)
    -- Vec
    ＝vec : 
        cΓ ⊢ n ＝ m →
        cΓ ⊢ A ＝ B →
        cΓ ⊢ Vec (n 𝕢 σ) A ＝ Vec (m 𝕢 σ) B
    ＝∷v :
        cΓ ⊢ a ＝ c →
        cΓ ⊢ as ＝ cs →
        cΓ ⊢ n ＝ m →
        cΓ ⊢ a ∷v as 𝕟 n ＝ (c ∷v cs 𝕟 m)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    -- Might need to make this prop eq
    ⊢TM＝𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a ＝ b →
        zeroC Γ ⊢ a ＝ b
 