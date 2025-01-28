module ListCalc.RunId.TypeRules where

open import ListCalc.RunId.Syntax
open import ListCalc.RunId.Utils
import ListCalc.STLC.TypeRules as T
open T using () 
    renaming (
        _⟶_ to _T⟶_;
        _·_ to _T·_;
        _∷l_ to _T∷l_;
        _∷v_𝕟_ to _T∷v_T𝕟_;
        _,_ to _T,_;
        _⊢_∶_ to _T⊢_T∶_
    )

open import Data.Product using (_×_) renaming (_,_ to _,'_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
    Γ Δ Θ : PreContext
    cΓ cΓ' cΓ'' : Context Γ
    cΔ cΔ' cΔ'' : Context Δ
    cΘ : Context Θ
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Term
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term
    𝓁 𝓁₁ 𝓁₂ : ℕ
    
    Γᵣ : T.Context
    Aᵣ Bᵣ Cᵣ : T.Type
    aᵣ bᵣ cᵣ : T.Term

data _⊢_＝_ : Context Γ → Term → Term → Set
data _⊢_∶_ : Context Γ → Annotation A σ → Term → Set

-- For now it can be an annotation bc quants are only 0 or 1
data _⊢_∶_ where
    ⊢var :
        (i : cΓ ∋ (A 𝕢 σ)) →
        -- Avoiding green slime in the easiest way possible
        {num : ℕ} →
        {eq : (∋→ℕ i) ≡ num} →
        cΓ ⊢ var num 𝕢 σ ∶ shiftindices A (suc (∋→ℕ i)) 0
    -- functions
    ⊢pi :
        -- Not sure if this should be 0 usage for : Sett ? 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- same universe level?
        zeroC Γ ⊢ ∶ A 𝕢 π ⟶ B 𝕢 𝟘 ∶ Sett 𝓁 
    -- Add special rules!!
    ⊢rpi : 
        -- A =>r Ar
        -- B => Br
        -- Γr Ar C.= Br 
        {!   !} ≡ {!   !} →
        {!   !} ≡ {!   !} →
        -- Not sure if this should be 0 usage for : Sett ? 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- needs to be nonzero arg
        -- same universe level?
        zeroC Γ ⊢ r∶ A 𝕢 ω ⟶ B 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢lam : ∀ {cΓ : Context Γ} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B)
    ⊢rlam : ∀ {cΓ : Context Γ} →
        {!   !} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛr∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (r∶ A 𝕢 π ⟶ B)
    ⊢app : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ π σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- avoid green slime with eq
        {eq : cΓ'' ≡ (cΓ +c (π *c cΓ'))} →
        cΓ'' ⊢ a · b 𝕢 σ ∶  (B [ b / 0 ])
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
    ⊢conv : {cΓ : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ A ＝ B →
        cΓ ⊢ a 𝕢 σ ∶ B

    ---- QTT rules 
    ⊢TM-𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ a 𝕢 𝟘 ∶ A
    

-- Do I need to make all judgements be in 𝟘
data _⊢_＝_ where
    {-   
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ shiftindices a (suc (∋→ℕ i)) 0
    -}

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
    {-
    ＝lift : 
        (cΓ , A 𝕢  σ) ⊢ b 𝕢 π ∶ B →
        cΓ ⊢ a ＝ c →
        cΓ ⊢ b [ a / 0 ] ＝ ( b [ c / 0 ]) 
    -}
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
        cΓ ⊢ Vec (n  𝕢 σ) A ＝ Vec (m 𝕢 σ) B
    ＝∷v :
        cΓ ⊢ a ＝ c →
        cΓ ⊢ as ＝ cs →
        cΓ ⊢ n ＝ m →
        cΓ ⊢ a ∷v as 𝕟 n ＝ (c ∷v cs 𝕟 m)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    ⊢TM＝𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a ＝ b →
        zeroC Γ ⊢ a ＝ b

compileTy : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁 → Maybe T.Type
compileTy {A = Nat} d = just T.Nat
compileTy {A = List A} (⊢List dA) = do 
    Aᵣ ← compileTy dA
    just (T.List Aᵣ)
compileTy {A = Vec (_ 𝕢 𝟘) A} (⊢Vec _ dA) = do 
    Aᵣ ← compileTy dA
    just (T.List Aᵣ) 
compileTy {A = Vec (_ 𝕢 ω) A} (⊢Vec dn dA) = do 
    Aᵣ ← compileTy dA
    just (T.Vec Aᵣ)
-- I sense issues here with a lack of conversion
compileTy {A = ∶ A 𝕢 𝟘 ⟶ B} (⊢pi dA dB) = do 
    Bᵣ ← compileTy dB
    just (Bᵣ)
compileTy {A = ∶ A 𝕢 ω ⟶ B} (⊢pi dA dB) = do 
    Aᵣ ← compileTy dA
    Bᵣ ← compileTy dB
    just (Aᵣ T⟶ Bᵣ)
-- Run id compiled into Id fun? Or just into function?
compileTy {A = r∶ A 𝕢 ω ⟶ B} d = {!   !}
compileTy {A = Sett x} d = nothing
-- Avoid all conversion/normalization needed for now
compileTy d = nothing
{-
-- Can I avoid dealing with vars?
compileTy {Γ} {A = var x} d = {!   !}
compileTy {A = ƛ∶ A ♭ b} (⊢conv d x) = {! x  !}
compileTy {A = ƛ∶ A ♭ b} (⊢TM-𝟘 d) = {!   !}
compileTy {A = ƛr∶ x ♭ A} d = {!   !}
compileTy {A = A · A₁} d = {! d  !}
compileTy {A = z} d = {!   !}
compileTy {A = s A} d = {!   !}
compileTy {A = nill} d = {!   !}
compileTy {A = A ∷l A₁} d = {!   !}
compileTy {A = nilv} d = {!   !}
compileTy {A = A ∷v A₁ 𝕟 A₂} d = {!   !}
compileTy {A = elimnat A P∶ A₁ zb∶ A₂ sb∶ A₃} d = {!   !}
compileTy {A = eliml A P∶ A₁ nb∶ A₂ cb∶ A₃} d = {!   !}
compileTy {A = elimv A P∶ A₁ nb∶ A₂ cb∶ A₃} d = {!   !}
compileTy {A = List A} (⊢conv d x) = {!   !}
compileTy {A = List A} (⊢TM-𝟘 d) = {!   !}
compileTy {A = Vec (_ 𝕢 𝟘) A} (⊢conv d x) = {!   !}
compileTy {A = Vec (_ 𝕢 𝟘) A} (⊢TM-𝟘 d) = {!   !}
compileTy {A = Vec (_ 𝕢 ω) A} (⊢conv d x) = {!   !}
compileTy {A = Vec (_ 𝕢 ω) A} (⊢TM-𝟘 d) = {!   !}
compileTy {A = ∶ A 𝕢 ω ⟶ B} (⊢conv d x) = {!   !}
compileTy {A = ∶ A 𝕢 ω ⟶ B} (⊢TM-𝟘 d) = {!   !}
compileTy {A = r∶ A 𝕢 ω ⟶ B} (⊢conv d x) = {!   !}
compileTy {A = r∶ A 𝕢 ω ⟶ B} (⊢TM-𝟘 d) = {!   !}
compileTy {A = r∶ A 𝕢 𝟘 ⟶ B} (⊢conv d x) = {!   !}
compileTy {A = r∶ A 𝕢 𝟘 ⟶ B} (⊢TM-𝟘 d) = {!   !}
compileTy {A = ∶ A 𝕢 𝟘 ⟶ B} (⊢conv d x) = {!   !}
compileTy {A = ∶ A 𝕢 𝟘 ⟶ B} (⊢TM-𝟘 d) = {!   !}
-}

compileTys : Term → Maybe T.Type

-- Kind of annoying because I need to exclude invalid contexts
compileTes : Context Γ → Term → Maybe T.Term

compileTys Nat = just T.Nat
compileTys (List A) = do 
    Aᵣ ← compileTys A
    just (T.List Aᵣ) 
compileTys (Vec (n 𝕢 𝟘) A) = do 
    Aᵣ ← compileTys A
    just (T.List Aᵣ)
-- Should I only compile if valid n?
compileTys (Vec (n 𝕢 ω) A) = do 
    Aᵣ ← compileTys A
    just (T.Vec Aᵣ)
compileTys (∶ A 𝕢 𝟘 ⟶ B) = do 
    Bᵣ ← compileTys B
    just Bᵣ
compileTys (∶ A 𝕢 ω ⟶ B) = do 
    Aᵣ ← compileTys A
    Bᵣ ← compileTys B
    just (Aᵣ T⟶ Bᵣ)
-- Can a RunId function be 0 use? I think not right?
compileTys (r∶ A 𝕢 𝟘 ⟶ B) = nothing
-- Same compilation as for regular functions or not?
compileTys (r∶ A 𝕢 ω ⟶ B) = do 
    Aᵣ ← compileTys A
    Bᵣ ← compileTys B
    just (Aᵣ T⟶ Bᵣ)
-- Exclude sett?
compileTys (Sett x) = nothing
-- Dont normalize yet
compileTys A = nothing


-- Annoying to compile this without the typing derivation, maybe a data type of mapping old indices to new?
compileTes cΓ (var x) = {!   !}
compileTes cΓ (ƛ∶ x ♭ b) = {!   !}
compileTes cΓ (ƛr∶ x ♭ b) = {!   !}
compileTes cΓ (f · a) = do
    -- Which context... same one? depends if f is 0 or not right?
    fᵣ ← compileTes {!   !} f
    aᵣ ← compileTes {!   !} a
    just (fᵣ T· aᵣ)
compileTes cΓ z = just T.z
compileTes cΓ (s a) = do 
    aᵣ ← compileTes cΓ a 
    just aᵣ
compileTes cΓ nill = {!   !}
compileTes cΓ (a ∷l a₁) = {!   !}
compileTes cΓ nilv = {!   !}
compileTes cΓ (a ∷v a₁ 𝕟 a₂) = {!   !}
compileTes cΓ (elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃) = {!   !}
compileTes cΓ (eliml a P∶ a₁ nb∶ a₂ cb∶ a₃) = {!   !}
compileTes cΓ (elimv a P∶ a₁ nb∶ a₂ cb∶ a₃) = {!   !}
-- No types in Term position
compileTes cΓ Ty = nothing

-- Can make contexts correct by construction....
-- Then I can make use of the derivation here as well and know that terms are well typed...
-- Honestly will be faster to not deal with that though 
compileContextS : Context Γ → Maybe T.Context
compileContextS [] = just T.[]
compileContextS (cΓ , A 𝕢 𝟘) = compileContextS cΓ
compileContextS (cΓ , A 𝕢 ω) = do 
    Γᵣ ← compileContextS cΓ
    -- Might want to pass Γᵣ in future when smarter
    Aᵣ ← compileTys A
    just (Γᵣ T, Aᵣ)

-- What if one function with Maybe (Context x (Either Term or Type))
-- Either context x term, or a relation that says term is well scoped?
compileTerm : cΓ ⊢ a 𝕢 ω ∶ A → Maybe (T.Context × T.Term)
compileTerm {a = var x} (⊢var i) = just ({!   !} ,' {!   !}) 
-- can I be certain this is correct Γᵣ? Should get it from d
compileTerm {a = ƛ∶ A 𝕢 𝟘 ♭ b} (⊢lam db dA) = do 
    -- uncertain about this destructing
    (Γᵣ T, Aᵣ) ,' bᵣ ← compileTerm db 
    just (Γᵣ ,' bᵣ)
-- how do I get context here vs with 0 case?
compileTerm {a = ƛ∶ A 𝕢 ω ♭ b} (⊢lam db dA) = do 
    Aᵣ ← compileTy dA
    -- Not sure if this enforces what Aᵣ is supposed to be
    (Γᵣ T, Aᵣ) ,' bᵣ ← compileTerm db
    just (Γᵣ ,' T.ƛ bᵣ)
compileTerm {a = ƛr∶ x ♭ a} d = {!   !}
compileTerm {a = f · a} (⊢app {π = 𝟘} df da {eq = refl}) = {!   !}
compileTerm {a = f · a} (⊢app {π = ω} df da {eq = refl}) = do 
    Γᵣf ,' fᵣ ← compileTerm df
    Γᵣa ,' aᵣ ← compileTerm da
    -- Context should not matter, they have same PreContext, should I check?
    just (Γᵣf ,' (fᵣ T· aᵣ))  
-- Will context be emptied here?
compileTerm {a = z} (⊢z {Γ = Γ}) = just ({!   !} ,' T.z)
compileTerm {a = s a} (⊢s da) = do 
    (Γᵣ ,' aᵣ) ← compileTerm da
    just (Γᵣ ,' aᵣ)
compileTerm {a = nill} (⊢nill {Γ = Γ}) = just ({!   !} ,' T.nill)
compileTerm {a = a ∷l as} (⊢∷l da das) = do
    (Γᵣ ,' aᵣ) ← compileTerm da
    -- Again should be same, should I check?
    (Γᵣ ,' asᵣ) ← compileTerm das
    just (Γᵣ ,' (aᵣ T∷l asᵣ))
compileTerm {a = nilv} (⊢nilv {Γ = Γ} d) = just ({!   !} ,' T.nilv)
compileTerm {a = a ∷v as 𝕟 n} (⊢∷v {π = 𝟘} da dn das) = do 
    (Γᵣ ,' aᵣ) ← compileTerm da 
    -- Check Γᵣ?
    (Γᵣ ,' asᵣ) ← compileTerm das
    -- check n?
    just (Γᵣ ,' (aᵣ T∷l asᵣ))
compileTerm {a = a ∷v as 𝕟 n} (⊢∷v {π = ω} da das dn) = {!   !}
compileTerm {a = elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃} d = {!   !}
compileTerm {a = eliml a P∶ a₁ nb∶ a₂ cb∶ a₃} d = {!   !}
compileTerm {a = elimv a P∶ a₁ nb∶ a₂ cb∶ a₃} d = {!   !}
-- No conversion for terms
compileTerm {a = var x} (⊢conv d x₁) = {!   !}
compileTerm {a = ƛ∶ A 𝕢 ω ♭ b} (⊢conv d x) = {!   !}
compileTerm {a = ƛ∶ A 𝕢 𝟘 ♭ b} (⊢conv d x) = {!   !}
compileTerm {a = f · a} (⊢conv d x) = {!   !} 
compileTerm {a = z} (⊢conv d x) = {!   !}
compileTerm {a = s a} (⊢conv d x) = {!   !}
compileTerm {a = nill} (⊢conv d x) = {!   !}
compileTerm {a = a ∷l as} (⊢conv d x) = {!   !}
compileTerm {a = nilv} (⊢conv d x) = {!   !}
compileTerm {a = a ∷v a₁ 𝕟 a₂} (⊢conv d x) = {!   !}
-- No types in terms
compileTerm {a = Nat} d = {!   !}
compileTerm {a = List a} d = {!   !}
compileTerm {a = Vec x a} d = {!   !}
compileTerm {a = ∶ x ⟶ a} d = {!   !}
compileTerm {a = r∶ x ⟶ a} d = {!   !}
compileTerm {a = Sett x} d = {!   !}


compileProgram : {cΓ : Context Γ} → 
    zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁 → 
    cΓ ⊢ a 𝕢 ω ∶ A → 
    Maybe ({!   !} T⊢ {!   !} T∶ {!   !}) 
compileProgram dTy dTerm = {!   !}

-- Should be in compile time mode right?
data _⇒c_ : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁 → T.Type → Set where
    -- Do I need a var option here?

    ⇒cNat :
        {d : zeroC Γ ⊢ Nat 𝕢 𝟘 ∶ Sett 𝓁} →
        d ⇒c T.Nat
     
    ⇒cPiω :
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} 
        {dB : (zeroC Γ , A 𝕢 𝟘) ⊢  B  𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        dB ⇒c Bᵣ →
        ⊢pi {π = ω} dA dB ⇒c (Aᵣ T⟶ Bᵣ)
     
    ⇒cPi𝟘 :
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} 
        {dB : (zeroC Γ , A 𝕢 𝟘) ⊢  B  𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        dB ⇒c Bᵣ →
        ⊢pi {π = 𝟘} dA dB ⇒c (Aᵣ T⟶ Bᵣ)

    ⇒cList :
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        ⊢List dA ⇒c T.List Aᵣ 

    ⇒cVec𝟘 : {cΓ : Context Γ} →
        {dn : cΓ ⊢ n 𝕢 𝟘 ∶ Nat}
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        ⊢Vec dn dA ⇒c T.List Aᵣ
    ⇒cVecω : {cΓ : Context Γ} →
        {dn : cΓ ⊢ n 𝕢 ω ∶ Nat}
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        ⊢Vec dn dA ⇒c T.Vec Aᵣ 

    ---- Maybe I dont need this and im enforcing some "high level" quality/entry point

    -- Does this have to be 0? Can I "normalize" non-erased portions?
    ⇒cConv : {cΓ : Context Γ}
        {da : cΓ ⊢ b 𝕢 {!   !} ∶ a}
        {dA : zeroC Γ ⊢ a 𝕢 𝟘 ∶ A} 
        {＝Sett : zeroC Γ ⊢ A ＝ Sett 𝓁}  →
        {!  da  !} ⇒c {!   !} →
        ⊢conv dA ＝Sett ⇒c {!   !}
    
    -- Feel like I may need conv here or vice versa
    ⇒cTM : {cΓ : Context Γ}
        {da : cΓ ⊢ a 𝕢 σ ∶ A} →
        {! da  !} ⇒c {!   !} →
        ⊢TM-𝟘 {!   !} ⇒c {!   !} 
    

-- Does this have to be nonzero?
data _⇒_ : cΓ ⊢ a 𝕢 ω ∶ A → Γᵣ T⊢ aᵣ T∶ Aᵣ → Set where
    ⇒var : ∀ {j} →  
        (v :  cΓ ⊢ var j  𝕢 ω ∶ A) →
        {!   !} →         
        {!   !} ⇒ {!   !}   
    
    ⇒lam : {cΓ : Context Γ} 
        {dA : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} →
        dA ⇒c Aᵣ →
        {dB : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁} → 
        {db : (cΓ , A  𝕢 {!   !} ) ⊢ b 𝕢 ω ∶ B} →
        dB ⇒c Bᵣ →
        {dbᵣ : {!   !} T⊢ bᵣ T∶ {!   !}} →
        db ⇒ dbᵣ →                
        ⊢lam db dA ⇒ T.⊢lam dbᵣ   