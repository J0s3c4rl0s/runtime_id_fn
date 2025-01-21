module RunIdCalc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open import Calc using () renaming (Term to TTerm; Context to TContext;_⊢_∶_ to _T⊢_T∶_;_⊢_＝_ to _T⊢_T＝_)


data PreContext : Set
data Context : PreContext → Set
data Term : Set 

data Quantity : Set where 
    𝟘 : Quantity
    ω : Quantity

_+q_ : Quantity → Quantity → Quantity
𝟘 +q q2 = q2
ω +q q2 = ω

_*q_ : Quantity → Quantity → Quantity
𝟘 *q q2 = 𝟘
ω *q q2 = q2

-- In our case equivalent to multd
selectQ : Quantity → Quantity → Quantity
selectQ π σ = π *q σ

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

    Aᵣ Bᵣ : Term
    aᵣ bᵣ : Term



data Annotation : Term → Quantity → Set where
    _𝕢_ : (A : Term) → (σ : Quantity) → Annotation A σ

-- might need well formed relation on this shit
data PreContext where
    [] : PreContext
    _,_ : (Γ : PreContext) → Term → PreContext

data Context where
    [] : Context []
    _,_ : Context Γ → Annotation A σ → Context (Γ , A)


infix 10 _𝕢_
infix 8 _∋_

data _∋_ : Context Γ → Annotation A σ → Set where
  Z : ∀ {cΓ : Context Γ}
    →  (cΓ , (A 𝕢 σ)) ∋ (A 𝕢 σ)

  S : ∀ {A} {B} {cΓ : Context Γ}
    -- Ensure there is a lookup judgement in submodule
    → cΓ ∋ A 𝕢 σ
    →  (cΓ , B 𝕢 π) ∋ A 𝕢 σ

-- PreContext scaling
_*c_ : Quantity → Context Γ → Context Γ
_*c_ π [] = []
_*c_ π (Γ , x 𝕢 ρ) = _*c_ π Γ , x 𝕢 (π *q ρ)  

zeroC : (Γ : PreContext) → Context Γ
zeroC [] = []
zeroC (Γ , a) = zeroC Γ , a 𝕢 𝟘

-- PreContext addition
_+c_ : Context Γ → Context Γ → Context Γ 
([] +c []) = []
((cΓ , a 𝕢 π) +c (cΔ , a 𝕢 σ)) = (cΓ +c cΔ) , a 𝕢 (π +q σ)

data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ∶_♭_ : Annotation A σ → Term → Term
    -- RuntimeId, any erased args? Forced annotations?
    ƛr∶_♭_ : Annotation A σ → Term → Term
    _·_ : Term → Term → Term

    -- data cons
    ---- Nats
    z : Term
    s : Term → Term 
    -- list 
    nill : Term 
    _∷l_ : Term → Term → Term 
    -- vec
    nilv : Term 
    _∷v_ : Term → Term → Term 

    ---- elims 
    -- Nat
    elimnat_P∶_zb∶_sb∶_ : Term → Term → Term → Term → Term
    -- List
    -- For now annotate parametrized type
    eliml_P∶_ty∶_nb∶_cb∶_ : (list : Term) → Term → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    -- vec
    -- For now annotate length
    elimv_P∶_l∶_ty∶_nb∶_cb∶_ : (vec : Term) → Term → (length : Term) → (innerTy : Term) → (nilB : Term) → (∷B : Term) → Term
    
    -- Types
    Nat : Term
    List : Term → Term
    Vec : Annotation A σ → Term → Term
    ∶_⟶_ : Annotation A σ → Term → Term -- Pi type
    r∶_⟶_ : Annotation A σ → Term → Term -- Runtime Pi type
    Sett : Term -- Universe 


∋→ℕ : cΓ ∋ (A 𝕢 σ) → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ shiftindices t i l 𝕢 σ ♭ shiftindices t₁ i (suc l)
shiftindices (ƛr∶ t 𝕢 σ ♭ t₁) i l = (ƛr∶ shiftindices t i l 𝕢 σ ♭ shiftindices t₁ i (suc l))
shiftindices (t · t₁) i l = shiftindices t i l · shiftindices t₁ i l
shiftindices z i l = z
shiftindices (s t) i l = s (shiftindices t i l) 
shiftindices nill i l = nill
shiftindices (t ∷l t₁) i l = shiftindices t i l ∷l shiftindices t₁ i l
shiftindices nilv i l = nilv
shiftindices (t ∷v t₁) i l = shiftindices t i l ∷v shiftindices t₁ i l
shiftindices (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) i l = 
    elimnat_P∶_zb∶_sb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l)
shiftindices (eliml t P∶ t₁ ty∶ t₂ nb∶ t₃ cb∶ t₄) i l = 
    eliml_P∶_ty∶_nb∶_cb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l) (shiftindices t₄ i l)
shiftindices (elimv t P∶ t₁ l∶ t₂ ty∶ t₃ nb∶ t₄ cb∶ t₅) i l = 
    elimv_P∶_l∶_ty∶_nb∶_cb∶_ (shiftindices t i l) (shiftindices t₁ i l) (shiftindices t₂ i l) (shiftindices t₃ i l) (shiftindices t₄ i l) (shiftindices t₅ i l)
shiftindices Nat i l = Nat
shiftindices (List t) i l = List (shiftindices t i l)
shiftindices (Vec (A 𝕢 σ) t₁) i l = Vec (shiftindices A i l 𝕢 σ) (shiftindices t₁ i l)
shiftindices (∶ t 𝕢 σ ⟶ t₁) i l = ∶ shiftindices t i l 𝕢 σ ⟶ shiftindices t₁ i (suc l)
shiftindices (r∶ t 𝕢 σ ⟶ t₁) i l = r∶ shiftindices t i l 𝕢 σ ⟶ shiftindices t₁ i (suc l)
shiftindices Sett i l = Sett

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ∶ bₜ 𝕢 σ ♭ b) [ a / i ] = ƛ∶ bₜ [ a / i ]  𝕢 σ ♭ (b [ shiftindices a 1 0 / suc i ])
(ƛr∶ b 𝕢 x ♭ b₁) [ a / i ] = (ƛr∶ b [ a / i ] 𝕢 x ♭ (b₁ [ shiftindices a 1 0 / suc i ]))
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b 𝕢 σ ⟶ c) [ a / i ] = ∶ b [ a / i ] 𝕢 σ ⟶ (c [ shiftindices a 1 0 / suc i ]) 
(r∶ b 𝕢 σ ⟶ c) [ a / i ] = r∶ b [ a / i ] 𝕢 σ ⟶ (c [ shiftindices a 1 0 / suc i ]) 
Sett [ a / i ] = Sett
z [ a / i ] = z
s b [ a / i ] = s (b [ a / i ]) 
nill [ a / i ] = nill
(h ∷l t) [ a / i ] = (h [ a / i ]) ∷l (t [ a / i ])
nilv [ a / i ] = nilv
(h ∷v t) [ a / i ] = (h [ a / i ]) ∷v (t [ a / i ])
(elimnat b P∶ P zb∶ zb sb∶ sb) [ a / i ] = 
    elimnat b [ a / i ] P∶ P [ a / i ] 
        zb∶ zb [ a / i ] 
        sb∶ (sb [ a / suc i ])
(eliml b P∶ P ty∶ bty nb∶ nb cb∶ cb) [ a / i ] = 
    eliml b [ a / i ] P∶ P [ a / i ] ty∶ bty [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ a / i ])
(elimv b P∶ P l∶ n ty∶ ty nb∶ nb cb∶ cb) [ a / i ] = 
    elimv b [ a / i ] P∶ P [ a / i ] l∶ n [ a / i ] ty∶ ty [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ a / i ])
Nat [ a / i ] = Nat
List b [ a / i ] = List (b [ a / i ])
Vec (n 𝕢 σ) b [ a / i ] = Vec (((n [ a / i ])) 𝕢 σ) (b [ a / i ])

data _⊢_＝_ : Context Γ → Term → Term → Set
data _⊢_∶_ : Context Γ → Annotation A σ → Term → Set
-- Type erasure into Calc.agda (dependently typed but no erasure)
data _⊢_⇒ᵣ_ : Context Γ → Term → TTerm → Set

erase : cΓ ⊢ a 𝕢 σ ∶ A → Calc.Term

-- maybe this shit? Maybe already define what target is 
_⊢_＝₀_ :{Aᵣ Bᵣ : TTerm} → Context Γ → Term → Term → Set
_⊢_＝₀_ {Aᵣ = Aᵣ} {Bᵣ = Bᵣ} cΓ A B = 
    cΓ ⊢ A ⇒ᵣ Aᵣ → 
    cΓ ⊢ B ⇒ᵣ Bᵣ → 
    {!   !} T⊢ Aᵣ T＝ Bᵣ


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
    ⊢rpi : 
        -- A =>r Ar
        -- B => Br
        -- Γr Ar C.= Br 
        {! zero Γ ⊢ A ⇒ᵣ Aᵣ  !} →
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
        zeroC Γ ⊢ Vec (z 𝕢 δ) A 𝕢 𝟘 ∶ Sett
    ⊢nilv : 
        zeroC Γ ⊢ nilv 𝕢 σ ∶ Vec (s n 𝕢 δ) A
    ⊢∷v :
        cΓ ⊢ a 𝕢 σ ∶ A →
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        cΓ ⊢ a ∷v b 𝕢 σ ∶ Vec (s n 𝕢 δ) A
    ⊢vecel : {cΓ cΓ' : Context Γ} → 
        cΓ ⊢ b 𝕢 σ ∶ Vec (n 𝕢 δ) A →
        zeroC Γ ⊢ P 𝕢 σ ∶ (∶ Nat 𝕢 π ⟶ (∶ Vec (var 0 𝕢 δ) A  𝕢 π' ⟶ Sett)) →
        cΓ' ⊢ nb 𝕢 σ ∶ ((P · z) · nilv) →
        cΓ' ⊢ cb 𝕢 σ ∶ (∶ Nat 𝕢 ρ ⟶ (∶ A 𝕢 ρ' ⟶ (∶ Vec (var 1 𝕢 δ) A 𝕢  ρ'' ⟶ (∶ P · var 0  𝕢 ρ''' ⟶ (P · (var 2 ∷v var 1)))))) → 
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
    
erase {σ = σ} (⊢var i) = {!   !}
erase (⊢pi ⊢d ⊢d₁) = {!   !}
erase (⊢rpi x ⊢d ⊢d₁) = {!   !}
erase (⊢lam ⊢d ⊢d₁) = {!   !}
erase (⊢rlam ⊢d x ⊢d₁) = {!   !}
erase (⊢app ⊢d ⊢d₁) = {!   !}
erase ⊢Nat = {!   !}
erase ⊢z = {!   !}
erase (⊢s ⊢d) = {!   !}
erase (⊢natel ⊢d ⊢d₁ ⊢d₂ ⊢d₃) = {!   !}
erase ⊢List = {!   !}
erase ⊢nill = {!   !}
erase (⊢∷l ⊢d ⊢d₁) = {!   !}
erase (⊢listel ⊢d ⊢d₁ ⊢d₂ ⊢d₃) = {!   !}
erase ⊢Vec = {!   !}
erase ⊢nilv = {!   !}
erase (⊢∷v ⊢d ⊢d₁) = {!   !}
erase (⊢vecel ⊢d ⊢d₁ ⊢d₂ ⊢d₃) = {!   !}
erase ⊢Sett = {!   !}
erase (⊢conv ⊢d x) = {!   !}
erase (⊢TM-𝟘 ⊢d) = {!   !}

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
        cΓ ⊢ cs ＝ (a ∷v as) → 
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
        cΓ ⊢ a ∷v as ＝ (c ∷v cs)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    ⊢TM＝𝟘 : {cΓ : Context Γ} →
        cΓ ⊢ a ＝ b →
        zeroC Γ ⊢ a ＝ b
{-
data _⊢_＝₀_ where
    -- seems weird
    ＝₀var : 
        {!   !} →
        (i : cΓ ∋ (A 𝕢 σ))  →
        cΓ ⊢ var (∋→ℕ i) ＝₀ var (∋→ℕ i)
    ＝₀vectolist : 
        cΓ ⊢ A ＝₀ B →
        cΓ ⊢ Vec (n 𝕢 𝟘) A ＝₀ List B
    
    -- Not sure this is right
    ＝₀refl :
        cΓ ⊢ A ＝₀ A
-}