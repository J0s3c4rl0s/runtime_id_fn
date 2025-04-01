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
open import Data.Sum
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
data _⊢_∶_ : Context Γ → Annotation a σ → Type → Set
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
        zeroC Γ ⊢ r∶ A ⟶ B 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢lam : ∀ {cΓ : Context Γ} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B)
    ⊢rlam : ∀ {cΓ : Context Γ} →
        b ~ᵣ var 0 →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (ω *q σ)) ⊢ b 𝕢 σ ∶ B →
        -- Is this rule redundant since there is a formation rule
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        cΓ ⊢ (ƛr∶ A ♭ b) 𝕢 σ ∶ (r∶ A ⟶ B)
    ⊢app : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ π σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- avoid green slime with eq
        {eq : cΓ'' ≡ (cΓ +c (π *c cΓ'))} →
        cΓ'' ⊢ (a · b 𝕢 π) 𝕢 σ ∶  (B [ 0 / b ])
    ⊢appᵣ : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 ω ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ ω σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- avoid green slime with eq
        {eq : cΓ'' ≡ (cΓ +c (ω *c cΓ'))} →
        cΓ'' ⊢ (a ·ᵣ b) 𝕢 σ ∶  (B [ 0 /  b ])

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
        -- zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett 𝓁 ) →
        -- enforces that argument to forming this type are erased
        zeroC (Γ , Nat) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        cΓ' ⊢ zb 𝕢 σ ∶ (P [ 0 / z ]) →
        ((cΓ' , Nat 𝕢 ρ) , (P [ 0 / var 0 ]) 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P [ 0 / s (var 1) ]) →
        {eq : cΓ'' ≡ (cΓ +c cΓ')} →
        cΓ'' ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            𝕢 σ ∶ (P [ 0 / n ])
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
    ⊢listel : {cΓ cΓ' cΓ'' : Context Γ} →
        cΓ ⊢ l 𝕢 σ ∶ List A →
        zeroC (Γ , List A) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 → 
        cΓ' ⊢ nb 𝕢 σ ∶ (P [ 0 / nill ]) → 
        {eq : cΓ'' ≡ (cΓ +c cΓ')} →
        -- I presume list elements must have same erasure as List
        (((cΓ' , 
            A 𝕢 σ) , 
            List A 𝕢 σ) , 
            (P [ 0 / var 0 ]) 𝕢 σ) ⊢ cb 𝕢 σ ∶ (P [ 0 / (var 2 ∷l var 1) ]) → 
        cΓ'' ⊢ eliml l ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P [ 0 / l ])
    -- Vecs
    ⊢Vec : {cΓ : Context Γ} →
        cΓ ⊢ n 𝕢 σ ∶ Nat  →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ Vec A (n 𝕢 σ) 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢nilv :  
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett 𝓁  →
        zeroC Γ ⊢ nilv𝕢 π 𝕢 σ ∶ Vec A (z 𝕢 π)
    ⊢∷v :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ n 𝕢 π ∶ Nat →
        cΓ ⊢ b 𝕢 σ ∶ Vec A (n 𝕢 π) →
        cΓ ⊢ (a ∷v b 𝕟 n 𝕢 π) 𝕢 σ ∶ Vec A (s n 𝕢 π)
    ⊢vecel : {cΓ cΓ' cΓ'' : Context Γ} → 
        cΓ ⊢ b 𝕢 σ ∶ Vec A (n 𝕢 δ) →
        -- I enforce that P is only compile time? should I?
        zeroC ((Γ , Nat) , Vec A (var 0 𝕢 δ)) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
        cΓ' ⊢ nb 𝕢 σ ∶ (P [ 0 / z ] [ 1 / (nilv𝕢 δ) ]) → 
        {eq : cΓ'' ≡ (cΓ +c cΓ')} →
        -- assuming that the constructors are not heterogenous, I think they might need to be rho
        ((((cΓ' , 
            Nat 𝕢 π) , 
            A 𝕢 σ) , 
            Vec A (var 1 𝕢 δ) 𝕢  σ) , 
            (P [ 0 / var 0 ] [ 1 / var 2 ]) 𝕢 σ) ⊢ cb 𝕢 σ ∶ ((((((P [ 0 / var 3 ]) [ 1 / (var 2 ∷v var 1 𝕟 var 3 𝕢 δ) ]))))) →
        cΓ'' ⊢ elimv (b 𝕢 δ) ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ ((P [ 0 / n ]) [ 1 / b ])
    
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
        (r∶ A ⟶ B) ＝ (r∶ C ⟶ D)
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
            ((sb [ 1 / n ]) [ 0 / a ])
    -- list
    ＝listeln :
        cs ＝ nill →
        (eliml cs ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            nb
    ＝listelc :     
        cs ＝ (a ∷l as) →
        (eliml as ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            b →
        (eliml cs ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            (((cb [ 2 / a ]) [ 1 / as ]) [ 0 / b ])
            
    -- vec
    ＝veceln :
        cs ＝ (nilv𝕢 σ) →
        (elimv (cs 𝕢 σ) ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            nb
    ＝vecelc :
        cs ＝ (a ∷v as 𝕟 n 𝕢 σ) → 
        (elimv ((nilv𝕢 σ) 𝕢 σ) ty∶ A P∶ P
                nb∶ nb 
                cb∶ cb) 
            ＝ 
            b →
        (elimv (cs 𝕢 σ) ty∶ A P∶ P
                nb∶ nb 
                cb∶ cb) 
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
    {-
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
            ((sb [ 1 / n ]) [ 0 / a ])
    -}
    -- list
    {-
    ~ᵣlisteln :
        cs ~ᵣ nill →
        (eliml cs ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            nb
    ~ᵣlistelc :     
        cs ~ᵣ (a ∷l as) →
        (eliml as ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            b →
        (eliml cs ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            (((cb [ 2 / a ]) [ 1 / as ]) [ 0 / b ])
            -- (((cb · a) · as) ·  b)
    -}
    -- vec
    {-
    ~ᵣveceln :
        -- generic computation rules
        cs ~ᵣ (nilv𝕢 σ) →
        (elimv (cs 𝕢 σ) ty∶ A P∶ P 
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            nb
    ~ᵣvecelc :
        cs ~ᵣ (a ∷v as 𝕟 n 𝕢 σ) → 
        (elimv ((nilv𝕢 σ) 𝕢 σ) ty∶ A P∶ P
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            b →
        (elimv (cs 𝕢 σ) ty∶ A P∶ P
                nb∶ nb 
                cb∶ cb )
            ~ᵣ 
            -- Might be worthwhile to change n to fit the structure of ∷v
            ((((cb [ 3 / n ]) [ 2 / a ]) [ 1 / as ]) [ 0 / b ])
            -- ((((cb · n) · a) · as) · b)
    -}
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
    -- should it be runid equiv to a fun?
    ~ᵣpir : 
        A ~ᵣ B →
        (r∶ A ⟶ B) ~ᵣ (r∶ A ⟶ A) 
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
    ~ᵣlamr : 
        (ƛr∶ A ♭ b) ~ᵣ (ƛr∶ A ♭ var 0)
    -- I need distinguish between applications of erased or unerased functions? 
    -- maybe distinguish erased and unerased application in syntax (or parametrize)
    ~ᵣappω : 
        b ~ᵣ d →
        a ~ᵣ c →
        (b ·ω a) ~ᵣ (d ·ω c)
    ~ᵣapp𝟘 : 
        b ~ᵣ d →
        (b ·𝟘 a) ~ᵣ d
    ~ᵣappr : 
        (b ·ᵣ a) ~ᵣ a
    -- Any case where id accept ·𝟘?
    ~ᵣbetaω : ((ƛ∶ A 𝕢 ω ♭ b) ·ω a) ~ᵣ (b [ 0 / a ])
    -- Done by appr?
    -- ~ᵣbetar : ((ƛr∶ A ♭ b) ·ᵣ a) ~ᵣ a
    -- isnt this covered by app0?
    {-
    -- ???? This feels very wrong, maybe it is even unnecessary
    ~ᵣbeta𝟘 : (ƛ∶ A 𝕢 𝟘 ♭ b) · a ~ᵣ b
    -}

    -- Vec
    ~ᵣvecω : 
        n ~ᵣ m →
        A ~ᵣ B →
        Vec A (n 𝕢 ω) ~ᵣ Vec B (m 𝕢 ω)
    ~ᵣvec𝟘 :
        A ~ᵣ B →
        Vec A (n 𝕢 𝟘) ~ᵣ List B
    
    -- redundant with refl
    -- ~ᵣnilvω :
    --     nilvω ~ᵣ nilvω
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
        (nb 
            -- Replace scrutinee with destructor
            [ i / nill ])
            ~ᵣ 
        (a 
            -- Replace scrutinee with destructor
            [ i / nill ]) →
        -- Context has been weakened so update RHS to new context through shifting
        (cb 
            -- Replace scrutinee with destructor
            [ (3 + i) / var 2 ∷l var 1 ]
            -- Replace tail with acc
            [ 0 / var 1 ]) 
            ~ᵣ 
        (shiftindices a 3 0 
            -- Replace scrutinee with destructor
            [ (3 + i) / var 2 ∷l var 1 ]) →
        -- May not be necessary, subst acc for tail should suffice
        -- Add two options, either acc or tail, prev solution works bad with proof
        -- cb ~ᵣ ((a [ i / var 2 ∷l var 0 ])) ⊎ cb ~ᵣ ((a [ i / var 2 ∷l var 1 ])) →
        (eliml var i ty∶ A P∶ P 
            nb∶ nb 
            cb∶ cb) 
            ~ᵣ 
        a
    ~ᵣηvec :
        (nb
            -- Replace scrutinee with destructor
            [ i / nilv𝕢 σ ]) 
            ~ᵣ 
        (a 
            -- Replace scrutinee with destructor
            [ i / nilv𝕢 σ ]) →
        (cb 
            -- Replace scrutinee with destructor
            [ (4 + i) / var 2 ∷v var 1 𝕟 var 3 𝕢 σ ]
            -- Replace acc with tail 
            [ 0 / var 1 ]) 
            ~ᵣ 
        (shiftindices a 4 0 
            -- Replace scrutinee with destructor
            [ (4 + i) / var 2 ∷v var 1 𝕟 var 3 𝕢 σ ]) →
        (elimv (var i 𝕢 σ) ty∶ A P∶ P
            nb∶ nb 
            cb∶ cb) 
            ~ᵣ 
        a
  