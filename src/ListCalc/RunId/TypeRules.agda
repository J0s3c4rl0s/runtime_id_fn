module ListCalc.RunId.TypeRules where

open import ListCalc.RunId.Syntax
open import ListCalc.RunId.Utils
import ListCalc.STLC.TypeRules as T
open T using () renaming (_⊢_∶_ to _T⊢_T∶_)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

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
        -- Not sure if this should be 0 usage for : Sett
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ ∶ A 𝕢 π ⟶ B 𝕢 𝟘 ∶ Sett
    -- Add special rules!!
    ⊢rpi : 
        -- A =>r Ar
        -- B => Br
        -- Γr Ar C.= Br 
        {!   !} →
        -- Not sure if this should be 0 usage for : Sett
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett →
        -- needs to be nonzero arg
        zeroC Γ ⊢ r∶ A 𝕢 ω ⟶ B 𝕢 𝟘 ∶ Sett
    ⊢lam : ∀ {cΓ : Context Γ} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        cΓ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B)
    ⊢rlam : ∀ {cΓ : Context Γ} →
        -- Are the annotations in cΓ arbitrary? 
        (cΓ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        {!   !} →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        -- needs to be nonzero arg
        cΓ ⊢ (ƛr∶ A 𝕢 ω ♭ b) 𝕢 σ ∶ (r∶ A 𝕢 ω ⟶ B)
    ⊢app : 
        cΓ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        cΓ' ⊢ b 𝕢 selectQ π σ ∶ A →
        -- Need something to limit substitution according to atkey 
        -- addition in bottom sounds potentially annoying
        ( cΓ +c (π *c cΓ') ) ⊢ a · b 𝕢 σ ∶  (B [ b / 0 ])
    -- Nats
    ⊢Nat : 
        zeroC Γ ⊢ Nat 𝕢 𝟘 ∶ Sett
    ⊢z : 
        zeroC Γ ⊢ z 𝕢 σ ∶ Nat
    ⊢s : 
        cΓ ⊢ a 𝕢 σ ∶ Nat →
        cΓ ⊢ s a 𝕢 σ ∶ Nat
    -- either nothing is erased or everything is (?)
    ⊢natel : ∀ {zb sb} →
        cΓ ⊢ n 𝕢 σ ∶ Nat →
        -- Maybe P and n should match usage (check?) or comes naturally from rule
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett) →
        cΓ' ⊢ zb 𝕢 σ ∶ (P · z) →
        cΓ' ⊢ sb 𝕢 σ ∶ (∶ Nat 𝕢 ρ ⟶ (∶ P · var 0 𝕢 ρ'  ⟶ (P · s (var 1)))) →
        (cΓ +c cΓ') ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            𝕢 σ ∶ (P · n)
    -- Lists
    ⊢List : 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ List A 𝕢 𝟘 ∶ Sett
    ⊢nill :
        zeroC Γ ⊢ nill 𝕢 σ ∶ List A -- may need to add annotations later
    ⊢∷l :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ b 𝕢 σ ∶ List A →
        cΓ ⊢ a ∷l b 𝕢 σ ∶ List A
    ⊢listel : {cΓ cΓ' : Context Γ} →
        cΓ ⊢ l 𝕢 σ ∶ List A →
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ List A 𝕢 π ⟶ Sett) → 
        cΓ' ⊢ nb 𝕢 σ ∶ (P · nill) → 
        -- Maybe I need to do selection for these branches?
        cΓ' ⊢ cb 𝕢 σ ∶ (∶ A 𝕢 ρ ⟶ (∶ List A 𝕢 ρ' ⟶ (∶ P · var 0 𝕢 ρ'' ⟶ (P · (var 2 ∷l var 1))))) → 
        (cΓ +c cΓ') ⊢ eliml l P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · l)

    -- Vecs
    ⊢Vec : 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ n 𝕢 𝟘 ∶ Nat →
        zeroC Γ ⊢ Vec (n 𝕢 δ) A 𝕢 𝟘 ∶ Sett
    ⊢nilv : 
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ nilv 𝕢 σ ∶ Vec (z 𝕢 δ) A
    ⊢∷v :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ n 𝕢 σ ∶ Nat → 
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        cΓ ⊢ a ∷v b 𝕟 n 𝕢 σ ∶ Vec (s n 𝕢 δ) A
    ⊢vecel : {cΓ cΓ' : Context Γ} → 
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        zeroC Γ ⊢ P 𝕢 σ ∶ (∶ Nat 𝕢 π ⟶ (∶ Vec (var 0 𝕢 δ) A  𝕢 π' ⟶ Sett)) →
        cΓ' ⊢ nb 𝕢 σ ∶ ((P · z) · nilv) →
        cΓ' ⊢ cb 𝕢 σ ∶ (∶ Nat 𝕢 ρ ⟶ (∶ A 𝕢 ρ' ⟶ (∶ Vec (var 1 𝕢 δ) A 𝕢  ρ'' ⟶ (∶ P · var 0  𝕢 ρ''' ⟶ (P · (var 2 ∷v var 1 𝕟 var 3)))))) → 
        (cΓ +c cΓ') ⊢ elimv b P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · b)
    
    -- Pretty sure this breaks soundness
    ⊢Sett : 
        zeroC Γ ⊢ Sett 𝕢 𝟘 ∶ Sett
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
            ((sb · n) · a)
    -- list
    ＝listeln :
        cΓ ⊢ cs ＝ nill →
        cΓ ⊢ eliml cs P∶ P ty∶ A  
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝listelc : 
        cΓ ⊢ cs ＝ (a ∷l as) →
        cΓ ⊢ eliml as P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        cΓ ⊢ eliml cs P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            (((cb · a) · as) ·  b)
    -- vec
    ＝veceln :
        cΓ ⊢ cs ＝ nilv →
        cΓ ⊢ elimv cs P∶ P l∶ z ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝vecelc :
        cΓ ⊢ cs ＝ (a ∷v as 𝕟 n) → 
        cΓ ⊢ elimv nilv P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        cΓ ⊢ elimv cs P∶ P l∶ s n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            ((((cb · n) · a) · as) · b)
    
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

cty : zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett → T.Type
cty = {!   !}

-- Does this have to be nonzero?
data _⇒_ : cΓ ⊢ a 𝕢 ω ∶ A → Γᵣ T⊢ aᵣ T∶ Aᵣ → Set where
    ⇒var : ∀ {j} →
        (v :  cΓ ⊢ var j  𝕢 ω ∶ A) →
        {!   !} →   
        {!   !} ⇒ {!   !}