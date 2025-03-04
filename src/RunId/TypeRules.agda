module RunId.TypeRules where

open import RunId.Syntax
open import RunId.Utils
import STLC.TypeRules as T
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
    A B C D P : Type
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term
    
    i j 𝓁 𝓁₁ 𝓁₂ : ℕ
    
    Γᵣ : T.Context
    Aᵣ Bᵣ Cᵣ : T.Type
    aᵣ bᵣ cᵣ : T.Term


data _＝_ : Term → Term → Set
data _⊢_∶_ : Context Γ → Annotation A σ → Type → Set
data _~ᵣ_ : Term → Term → Set

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
        A ~ᵣ B →
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
        -- This may cause problems with patter matched expressions
        b ~ᵣ var 0 →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (ω *q σ)) ⊢ b 𝕢 σ ∶ B →
        -- Is this rule redundant since there is a formation rule
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛr∶ A 𝕢 ω ♭ b) 𝕢 σ ∶ (r∶ A 𝕢 ω ⟶ B)
    ⊢app : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ π σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- avoid green slime with eq
        {eq : cΓ'' ≡ (cΓ +c (π *c cΓ'))} →
        cΓ'' ⊢ (a · b 𝕢 π) 𝕢 σ ∶  (B [ b / 0 ])
    ⊢appᵣ : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 ω ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ ω σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- avoid green slime with eq
        {eq : cΓ'' ≡ (cΓ +c (ω *c cΓ'))} →
        cΓ'' ⊢ (a ·ᵣ b) 𝕢 σ ∶  (B [ b / 0 ])

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
        cΓ' ⊢ zb 𝕢 σ ∶ (P · z 𝕢 π) →
        ((cΓ' , Nat 𝕢 ρ) , (P · var 0 𝕢 π) 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P · s (var 1) 𝕢 π) →
        (cΓ +c cΓ') ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            𝕢 σ ∶ (P · n 𝕢 π)
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
        cΓ' ⊢ nb 𝕢 σ ∶ (P · (nill) 𝕢 ρ) → 
        -- I presume list elements must have same erasure as List
        (((cΓ' , A 𝕢 σ) , List A 𝕢 σ) , (P · (var 0) 𝕢 ρ) 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P · (var 2 ∷l var 1) 𝕢 ρ) → 
        (cΓ +c cΓ') ⊢ eliml l P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · l 𝕢 ρ)
    -- Vecs
    ⊢Vec : {cΓ : Context Γ} →
        cΓ ⊢ n 𝕢 σ ∶ Nat  →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ Vec (n 𝕢 σ) A 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nilv :  
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ nilv𝕢 π 𝕢 σ ∶ Vec (z 𝕢 π) A
    ⊢∷v :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ n 𝕢 π ∶ Nat →


        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 π) A →
        cΓ ⊢ (a ∷v b 𝕟 n 𝕢 π) 𝕢 σ ∶ Vec (s n 𝕢 π) A
    ⊢vecel : {cΓ cΓ' : Context Γ} → 
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        -- should pi = delta?
        -- is it really 0 usage mode?
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ (∶ Vec (var 0 𝕢 δ) A 𝕢 ρ ⟶ Sett 𝓁 )) →
        cΓ' ⊢ nb 𝕢 σ ∶ ((P · z 𝕢 π) · (nilv𝕢 δ) 𝕢 ρ) →
        -- assuming that the constructors are not heterogenous, I think they might need to be rho
        ((((cΓ' , Nat 𝕢 π) , A 𝕢 σ) , Vec (var 1 𝕢 δ) A 𝕢  σ) , (P · var 0 𝕢 π)  𝕢 σ) ⊢ cb 𝕢 σ ∶ ((((((P · var 3 𝕢 π) · (var 2 ∷v var 1 𝕟 var 3 𝕢 δ) 𝕢 ρ))))) →
        (cΓ +c cΓ') ⊢ elimv b P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ ((P · n 𝕢 π) · b 𝕢 ρ)
    
    ⊢Sett : 
        zeroC Γ ⊢ Sett 𝓁 𝕢 𝟘 ∶ Sett (suc 𝓁) 
    ⊢conv : {cΓ : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ A →
        A ＝ B →
        cΓ ⊢ a 𝕢 σ ∶ B

    ---- QTT rules 
    ⊢TM-𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ a 𝕢 𝟘 ∶ A
    
infix 30 _＝_
-- rewrite this so its consistent in order (e.g. introducion-formation-congruence-reduction)
-- Do I need to make all judgements be in 𝟘
data _＝_ where
    {-   
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ shiftindices a (suc (∋→ℕ i)) 0
    -}

    ＝pi : 
        A ＝ C → 
        B ＝ D →
        (∶ A 𝕢 σ ⟶ B) ＝ (∶ C 𝕢 σ ⟶ D)

    ＝piᵣ : 
        A ＝ C → 
        B ＝ D →
        (r∶ A 𝕢 σ ⟶ B) ＝ (r∶ C 𝕢 σ ⟶ D)
    ＝lam :
        b ＝ c →
        (ƛ∶ A 𝕢 σ ♭ b)  ＝ (ƛ∶ A 𝕢 σ ♭ c)
    ＝lamᵣ :
        b ＝ c →
        (ƛr∶ A 𝕢 σ ♭ b)  ＝ (ƛr∶ A 𝕢 σ ♭ c)
    ＝app : 
        b ＝ d →
        a ＝ c →
        (b · a 𝕢 σ) ＝ (d · c 𝕢 σ)
    ＝appᵣ : 
        b ＝ d →
        a ＝ c →
        (b ·ᵣ a) ＝ (d ·ᵣ c)
    -- Look into substitution rules 
    ＝beta : ((ƛ∶ A 𝕢 σ ♭ b) · a 𝕢 σ) ＝ (b [ a / 0 ])
    ＝betaᵣ : ((ƛ∶ A 𝕢 ω ♭ b) ·ᵣ a) ＝ (b [ a / 0 ])
    {-
    ＝lift : 
        (cΓ , A 𝕢  σ) ⊢ b 𝕢 π ∶ B →
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
        (elimnat m P∶ P 
            zb∶ zb 
            sb∶ sb) 
            ＝ 
            zb
    ＝natels :
        n ＝ s n →
        (elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb) 
            ＝ 
            a →
        (elimnat m P∶ P 
                zb∶ zb 
                sb∶ sb) 
            ＝ 
            ((sb [ n / 1 ]) [ a / 0 ])
    -- list
    ＝listeln :
        cs ＝ nill →
        (eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            nb
    ＝listelc :     
        cs ＝ (a ∷l as) →
        (eliml as P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            b →
        (eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            (((cb [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- (((cb · a) · as) ·  b)
    -- vec
    ＝veceln :
        cs ＝ (nilv𝕢 σ) →
        (elimv cs P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            nb
    ＝vecelc :
        cs ＝ (a ∷v as 𝕟 n 𝕢 σ) → 
        (elimv (nilv𝕢 σ) P∶ P
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            b →
        (elimv cs P∶ P
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            -- Might be worthwhile to change n to fit the structure of ∷v
            ((((cb [ n / 3 ]) [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- ((((cb · n) · a) · as) · b)
    
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
        Vec (n  𝕢 σ) A ＝ Vec (m 𝕢 σ) B
    ＝∷v :
        a ＝ c →
        as ＝ cs →
        n ＝ m →
        (a ∷v as 𝕟 n 𝕢 σ) ＝ (c ∷v cs 𝕟 m 𝕢 σ)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    ⊢TM＝𝟘 : {cΓ : Context Γ} →
        a ＝ b →
        a ＝ b

infix 30 _~ᵣ_ 

-- Rearrenge this with boring and interesting rules
-- Should I only define this 
-- Could add types 
data _~ᵣ_ where
    ~ᵣrefl :
        A ~ᵣ A
    ~ᵣsym :
        B ~ᵣ A →
        A ~ᵣ B
    ~ᵣtrans :
        A ~ᵣ B →
        B ~ᵣ C →
        A ~ᵣ C
    
    ---- eliminators 
    -- nats
    ~ᵣnatelz :
        m ~ᵣ z →
        (elimnat m P∶ P 
            zb∶ zb 
            sb∶ sb) 
            ~ᵣ 
            zb
    ~ᵣnatels :
        n ~ᵣ s n →
        (elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb) 
            ~ᵣ 
            a →
        (elimnat m P∶ P 
                zb∶ zb 
                sb∶ sb) 
            ~ᵣ 
            ((sb [ n / 1 ]) [ a / 0 ])
    -- list
    ~ᵣlisteln :
        cs ~ᵣ nill →
        (eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            nb
    ~ᵣlistelc :     
        cs ~ᵣ (a ∷l as) →
        (eliml as P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            b →
        (eliml cs P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            (((cb [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- (((cb · a) · as) ·  b)
    -- vec
    ~ᵣveceln :
        -- generic computation rules
        cs ~ᵣ (nilv𝕢 σ) →
        (elimv cs P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            nb
    ~ᵣvecelc :
        cs ~ᵣ (a ∷v as 𝕟 n 𝕢 σ) → 
        (elimv (nilv𝕢 σ) P∶ P
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            b →
        (elimv cs P∶ P
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            -- Might be worthwhile to change n to fit the structure of ∷v
            ((((cb [ n / 3 ]) [ a / 2 ]) [ as / 1 ]) [ b / 0 ])
            -- ((((cb · n) · a) · as) · b)
    
    ---- Cong rules for datatypes 
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

    ------ interesting rules-- Do I need two rules depending on usage and then like ignore argument 
    -- or just pass it along?
    ~ᵣpiω : 
        A ~ᵣ C  →
        -- Which of the two should I extend it with? Does it matter? 
        -- Must I "pass along" proof of equiv or maybe substitution? 
        -- Does subst even work?
        -- Must I shift the indiceses here?
        B ~ᵣ D →
        (∶ A 𝕢 ω ⟶ B) ~ᵣ (∶ C 𝕢 ω ⟶ D) 
    -- does this make sense  
    ~ᵣpi𝟘 : 
        -- shift em, wait maybe shift B??
        B ~ᵣ shiftindices D 1 0 →
        (∶ A 𝕢 𝟘 ⟶ B) ~ᵣ D 
    -- must I add some for the A being different or nah?
    -- distinguish between usages?
    ~ᵣlamω :
        -- I guess this implicitly checks that the targ et types match
        b ~ᵣ c →
        (ƛ∶ A 𝕢 ω ♭ b)  ~ᵣ (ƛ∶ A 𝕢 ω ♭ c)
    ~ᵣlam𝟘 :
        -- I guess this implicitly checks that the target types match
        b ~ᵣ shiftindices c 1 0 →
        -- This feels like it wont play well with prev rule
        (ƛ∶ A 𝕢 𝟘 ♭ b)  ~ᵣ c
    -- I need distinguish between applications of erased or unerased functions? 
    -- maybe distinguish erased and unerased application in syntax (or parametrize)
    ~ᵣappω : 
        b ~ᵣ d →
        a ~ᵣ c →
        (b ·ω a) ~ᵣ (d ·ω c)
    ~ᵣapp𝟘 : 
        b ~ᵣ d →
        (b ·𝟘 a) ~ᵣ d
    -- Any case where id accept ·𝟘?
    ~ᵣbetaω : ((ƛ∶ A 𝕢 ω ♭ b) ·ω a) ~ᵣ (b [ a / 0 ])
    -- isnt this covered by app0?
    {-
    -- ???? This feels very wrong, maybe it is even unnecessary
    ~ᵣbeta𝟘 : (ƛ∶ A 𝕢 𝟘 ♭ b) · a ~ᵣ b
    -}
    -- Vec
    ~ᵣvecω : 
        n ~ᵣ m →
        A ~ᵣ B →
        Vec (n 𝕢 ω) A ~ᵣ Vec (m 𝕢 ω) B
    ~ᵣvec𝟘 :
        A ~ᵣ B →
        Vec (n 𝕢 𝟘) A ~ᵣ List B
    
    -- redundant with refl
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
    
    -- eta rules
    ~ᵣηlist :
        nb ~ᵣ (a [ nill / i ]) →
        -- substitute into branch replacing tail with acc
        (cb [ var 1 / 0 ]) ~ᵣ (a [ var 2 ∷l var 1 / i ]) →
        (eliml var i P∶ P 
            nb∶ nb 
            cb∶ cb) 
            ~ᵣ 
        a
    ~ᵣηvec :
        -- do I gotta shift any indices?
        nb ~ᵣ (a [ nilv𝕢 σ / i ]) →
        -- Make use of context rather than forall
        -- Also not well typed because ill be mixing potentially different constructors
        cb ~ᵣ (a [ var 2 ∷v var 1 𝕟 var 3 𝕢 σ / i ]) →
        (elimv var i P∶ P
            nb∶ nb 
            cb∶ cb) 
            ~ᵣ 
        a
    

    -- add rules for runid funs (maybe)

    {-
    -- Do I even need these still after copying them? 
    -- Should I remove the repeats? Or just remove this rule?
    ~ᵣconv :
        A ＝ C  →
        A ~ᵣ C 
    -}
