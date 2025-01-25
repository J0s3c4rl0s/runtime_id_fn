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
        _⊢_∶_ to _T⊢_T∶_
    )

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Maybe

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
        -- weird hack to do selected zeroing, may be nicer to have pre PreContext
        cΓ ⊢ var (∋→ℕ i) 𝕢 σ ∶ shiftindices A (suc (∋→ℕ i)) 0
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
        {!   !} →
        -- Not sure if this should be 0 usage for : Sett ? 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett 𝓁  →
        -- needs to be nonzero arg
        -- same universe level?
        zeroC Γ ⊢ r∶ A 𝕢 π ⟶ B 𝕢 𝟘 ∶ Sett 𝓁 
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
compileTy {Γ} {A = var x} d = {! d !}
compileTy {A = ƛ∶ A ♭ b} (⊢conv d x) = {! x  !}
compileTy {A = ƛ∶ A ♭ b} (⊢TM-𝟘 d) = {!   !}
compileTy {A = ƛr∶ x ♭ A} d = {!   !}
-- this guy has to eval lambda to create type right?
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
compileTy {A = Nat} d = just T.Nat
compileTy {A = List A} (⊢List dA) = do 
    Aᵣ ← compileTy dA
    just (T.List Aᵣ)
compileTy {A = List A} (⊢conv d x) = {!   !}
compileTy {A = List A} (⊢TM-𝟘 d) = {!   !}
compileTy {A = Vec x A} d = {!   !}
compileTy {A = ∶ x ⟶ A} d = {!   !}
compileTy {A = r∶ x ⟶ A} d = {!   !}
compileTy {A = Sett x} d = {!   !}

compileTerm : Term → Maybe T.Term
-- Need context for this no? 
compileTerm (var x) = {!   !}
-- Do I even need to check A?
compileTerm (ƛ∶ A 𝕢 𝟘 ♭ b) = {!   !}
compileTerm (ƛ∶ A 𝕢 ω ♭ b) = do 
    Aᵣ ← {!   !}
    bᵣ ← compileTerm b
    just (T.ƛ bᵣ)
compileTerm (ƛr∶ x ♭ a) = {!   !}
compileTerm (f · a) = do 
    fᵣ ← compileTerm f 
    aᵣ ← compileTerm a
    just (fᵣ T· aᵣ)
compileTerm z = just T.z
compileTerm (s a) = do 
    aᵣ ← compileTerm a
    just (T.s aᵣ)
compileTerm nill = just T.nill
compileTerm (a ∷l as) = do 
    aᵣ ← compileTerm a
    asᵣ ← compileTerm as
    just (aᵣ T∷l asᵣ)
compileTerm nilv = just T.nilv
compileTerm (a ∷v as 𝕟 n) = do 
    aᵣ ← compileTerm a
    asᵣ ← compileTerm as
    nᵣ ← compileTerm n
    just (aᵣ T∷v asᵣ T𝕟 nᵣ)
compileTerm (elimnat n P∶ a₁ zb∶ zb sb∶ sb) = {!    !}
compileTerm (eliml a P∶ a₁ nb∶ a₂ cb∶ a₃) = {!   !}
compileTerm (elimv a P∶ a₁ nb∶ a₂ cb∶ a₃) = {!   !}
compileTerm Nat = nothing
compileTerm (List a) = nothing
compileTerm (Vec x a) = nothing
compileTerm (∶ x ⟶ a) = nothing
compileTerm (r∶ x ⟶ a) = nothing
compileTerm (Sett x) = nothing  


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