module QTTCalc where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (True; toWitness)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)


data Context : Set
data Term : Set 
-- data Type : Set



data Quantity : Set where 
    𝟘 : Quantity
    ω : Quantity

_+q_ : Quantity → Quantity → Quantity
𝟘 +q q2 = q2
ω +q q2 = ω

_*q_ : Quantity → Quantity → Quantity
𝟘 *q q2 = 𝟘
ω *q q2 = q2

-- In our case equivalent to mult
selectQ : Quantity → Quantity → Quantity
selectQ π σ = π *q σ

private variable
    Γ Δ Θ : Context
    A B C D P : Term
    σ σ' π π' ρ ρ' ρ'' ρ''' : Quantity
    a b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term

-- might need well formed relation on this shit
data Context where
    [] : Context
    _,_𝕢_ : (Γ : Context) → Term → Quantity → Context

{-
data _≡₀_ : Context → Context → Set where
    []≡ : [] ≡₀ []
    -- Might need conversion for a = b
    ∷≡ : Γ ≡₀ Δ → a ≡ b → (Γ , a 𝕢 π ) ≡₀ (Δ , b 𝕢 σ)
-}

data _∋_𝕢_ : (Γ : Context) → Term → Quantity → Set where
  Z : ∀ {A} {Γ : Context}
    →  (Γ , A 𝕢 σ) ∋ A 𝕢 σ

  S : ∀ {A} {B} {Γ : Context}
    -- Ensure there is a lookup judgement in submodule
    → Γ ∋ A 𝕢 π
    →  (Γ , B 𝕢 σ) ∋ A 𝕢 π

-- Context scaling
_*c_ : Quantity → Context → Context
_*c_ π [] = []
_*c_ π (Γ , x 𝕢 ρ) = _*c_ π Γ , x 𝕢 (π *q ρ)  

zeroC : Context → Context
zeroC Γ = 𝟘 *c Γ

_≡₀_ : Context → Context → Set
[] ≡₀ [] = ⊤
[] ≡₀ (Δ , x 𝕢 x₁) = ⊥
(Γ , x 𝕢 x₁) ≡₀ [] = ⊥
(Γ , a 𝕢 π) ≡₀ (Δ , b 𝕢 σ) = (Γ ≡₀ Δ) × a ≡ b 

zeroExcept : Γ ∋ A 𝕢 σ → Context
zeroExcept {Γ , x 𝕢 π} Z = (zeroC Γ) , x 𝕢 π
zeroExcept {Γ , x 𝕢 π} (S i) = zeroExcept i , x 𝕢 𝟘

zeroExceptt : Γ ∋ A 𝕢 σ → Set
zeroExceptt {Γ , a 𝕢 σ} Z = ⊤
zeroExceptt {Γ , a 𝕢 𝟘} (S i) = zeroExceptt i
zeroExceptt {Γ , a 𝕢 ω} (S i) = ⊥

-- Context addition
_+c_ : (Γ : Context) → (Δ : Context) → {Γ ≡₀ Δ} → Context 
([] +c []) {eq} = []
((Γ , a 𝕢 x₁) +c (Δ , a 𝕢 x₃)) {fst , refl} = _+c_ Γ Δ {fst} , a 𝕢 𝟘

≡₀trans : Γ ≡₀ Δ → Δ ≡₀ Θ → Γ ≡₀ Θ
≡₀trans {[]} {[]} {[]} p p' = p
≡₀trans {Γ , a 𝕢 σ} {Δ , b 𝕢 ρ} {Θ , c 𝕢 π} (fst , snd) (fst₁ , snd₁) = (≡₀trans fst fst₁) , trans snd snd₁

scale≡₀ : Δ ≡₀ (π *c Δ) 
scale≡₀ {[]} = tt
scale≡₀ {Δ , a 𝕢 ρ} = scale≡₀ , refl



data Term where
    var :  ℕ → Term 
    
    -- function stuff
    ƛ∶_𝕢_♭_ : Term → Quantity → Term → Term
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
    Vec : Term → Term → Term
    ∶_𝕢_⟶_ : Term → Quantity → Term → Term -- Pi type
    Sett : Term -- Universe 

∋→ℕ : Γ ∋ A 𝕢 σ → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ shiftindices t i l 𝕢 σ ♭ shiftindices t₁ i (suc l)
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
shiftindices (Vec t t₁) i l = Vec (shiftindices t i l) (shiftindices t₁ i l)
shiftindices (∶ t 𝕢 σ ⟶ t₁) i l = ∶ shiftindices t i l 𝕢 σ ⟶ shiftindices t₁ i (suc l)
shiftindices Sett i l = Sett

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ∶ bₜ 𝕢 σ ♭ b) [ a / i ] = ƛ∶ bₜ [ a / i ]  𝕢 σ ♭ (b [ shiftindices a 1 0 / suc i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b 𝕢 σ ⟶ c) [ a / i ] = ∶ b [ a / i ] 𝕢 σ ⟶ (c [ shiftindices a 1 0 / suc i ]) 
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
Vec n b [ a / i ] = Vec (n [ a / i ]) (b [ a / i ])


data _⊢_＝_ : Context → Term → Term → Set

data _⊢_𝕢_∶_ : Context → Term → Quantity → Term → Set where
    {-
    ⊢var : ∀ {Γ A} →
        (i : Γ ∋ A 𝕢 σ) →
        -- weird hack to do selected zeroing, may be nicer to have pre context
        (j : zeroExcept i ∋ A 𝕢 σ) → 
        zeroExcept i ⊢ var (∋→ℕ j) 𝕢 σ ∶ shiftindices A (suc (∋→ℕ j)) 0
    -}
    -- alt attempt
    ⊢var : ∀ {Γ A} →
        (i : Γ ∋ A 𝕢 σ) →
        (_ : zeroExceptt i) →
        -- weird hack to do selected zeroing, may be nicer to have pre context
        Γ ⊢ var (∋→ℕ i) 𝕢 σ ∶ shiftindices A (suc (∋→ℕ i)) 0
    
    -- functions
    ⊢pi :
        -- Not sure if this should be 0 usage for : Sett
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        (zeroC Γ , A 𝕢 𝟘) ⊢ B 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ ∶ A 𝕢 π ⟶ B 𝕢 𝟘 ∶ Sett
    ⊢lam : 
        (Γ , A 𝕢 (π *q σ)) ⊢ b 𝕢 σ ∶ B →
        zeroC Γ ⊢ A 𝕢 𝟘 ∶ Sett →
        zeroC Γ ⊢ (ƛ∶ A 𝕢 π ♭ b) 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B)
    ⊢app : 
        Γ ⊢ a 𝕢 σ ∶ (∶ A 𝕢 π ⟶ B) →
        Δ ⊢ b 𝕢 selectQ π σ ∶ A →
        (eq : Γ ≡₀ Δ) → 
        -- Need something to limit substitution according to atkey 
        -- addition in bottom sounds potentially annoying
        (_+c_ Γ (π *c Δ) {≡₀trans eq scale≡₀}) ⊢ a · b 𝕢 σ ∶  (B [ b / 0 ])
    -- Nats
    ⊢Nat : 
        zeroC Γ ⊢ Nat 𝕢 𝟘 ∶ Sett
    ⊢z : 
        zeroC Γ ⊢ z 𝕢 σ ∶ Nat
    ⊢s : 
        Γ ⊢ a 𝕢 σ ∶ Nat →
        Γ ⊢ s a 𝕢 σ ∶ Nat
    -- either nothing is erased or everything is (?)
    ⊢natel : ∀ {zb sb} →
        (eq : Γ ≡₀ Δ) → 
        Γ ⊢ n 𝕢 σ ∶ Nat →
        -- Maybe P and n should match usage (check?) or comes naturally from rule
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett) →
        Δ ⊢ zb 𝕢 σ ∶ (P · z) →
        Δ ⊢ sb 𝕢 σ ∶ (∶ Nat 𝕢 ρ ⟶ (∶ P · var 0 𝕢 ρ'  ⟶ (P · s (var 1)))) →
        (_+c_ Γ Δ {eq}) ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            𝕢 σ ∶ (P · n)

    -- Lists
    ⊢List : 
        zeroC Γ ⊢ List A 𝕢 𝟘 ∶ Sett
    ⊢nill :
        zeroC Γ ⊢ nill 𝕢 σ ∶ List A -- may need to add annotations later
    ⊢∷l :
        Γ ⊢ a 𝕢 σ ∶ A →
        Γ ⊢ b 𝕢 σ ∶ List A →
        Γ ⊢ a ∷l b 𝕢 σ ∶ List A
    ⊢listel : 
        (eq : Γ ≡₀ Δ) →
        Γ ⊢ l 𝕢 σ ∶ List A →
        zeroC Γ ⊢ P 𝕢 𝟘 ∶ (∶ List A 𝕢 π ⟶ Sett) → 
        Δ ⊢ nb 𝕢 σ ∶ (P · nill) → 
        -- Maybe I need to do selection for these branches?
        Δ ⊢ cb 𝕢 σ ∶ (∶ A 𝕢 ρ ⟶ (∶ List A 𝕢 ρ' ⟶ (∶ P · var 0 𝕢 ρ'' ⟶ (P · (var 2 ∷l var 1))))) → 
        _+c_ Γ Δ {eq} ⊢ eliml l P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · l)

    -- Vecs
    ⊢Vec : 
        zeroC Γ ⊢ Vec n A 𝕢 𝟘 ∶ Sett
    ⊢nilv : 
        zeroC Γ ⊢ nilv 𝕢 𝟘 ∶ Vec z A
    ⊢∷v :
        Γ ⊢ a 𝕢 σ ∶ A →
        Γ ⊢ b 𝕢 σ ∶ Vec c A →
        Γ ⊢ a ∷v b 𝕢 σ ∶ Vec (s c) A
    ⊢vecel : 
        (eq : Γ ≡₀ Δ) →
        Γ ⊢ b 𝕢 σ ∶ Vec n A →
        zeroC Γ ⊢ P 𝕢 σ ∶ (∶ Nat 𝕢 π ⟶ (∶ Vec (var 0) A  𝕢 π' ⟶ Sett)) →
        Δ ⊢ nb 𝕢 σ ∶ ((P · z) · nilv) →
        Δ ⊢ cb 𝕢 σ ∶ (∶ Nat 𝕢 ρ ⟶ (∶ A 𝕢 ρ' ⟶ (∶ Vec (var 1) A 𝕢  ρ'' ⟶ (∶ P · var 0  𝕢 ρ''' ⟶ (P · (var 2 ∷v var 1)))))) → 
        Γ ⊢ elimv b P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            𝕢 σ ∶ (P · b)

    -- Pretty sure this breaks soundness
    ⊢Sett : 
        zeroC Γ ⊢ Sett 𝕢 𝟘 ∶ Sett
    ⊢conv : 
        Γ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ A ＝ B →
        Γ ⊢ a 𝕢 σ ∶ B

    ---- QTT rules 
    ⊢TM-𝟘 :
        Γ ⊢ a 𝕢 σ ∶ A →
        zeroC Γ ⊢ a 𝕢 𝟘 ∶ A
    
{-
data _⊢ : Context → Set where
    ⊢nil : Γ ⊢
    ⊢cons : 
        Γ ⊢ A ∶ Sett →
        (Γ , A) ⊢
-}

-- Do I need to make all judgements be in 𝟘
data _⊢_＝_ where
    {-   
    ＝var :
        (i : Γ ∋ a)  →
        Γ ⊢ var (∋→ℕ i) ＝ shiftindices a (suc (∋→ℕ i)) 0
    -}

    ＝pi : 
        Γ ⊢ A ＝ C → 
        (Γ , A 𝕢 σ) ⊢ B ＝ D →
        Γ ⊢ ∶ A 𝕢 σ ⟶ B ＝ (∶ C 𝕢 σ ⟶ D)
    ＝lam :
        (Γ , A 𝕢 σ) ⊢ b ＝ c →
        Γ ⊢ ƛ∶ A 𝕢 σ ♭ b  ＝ (ƛ∶ A 𝕢 σ ♭ c)
    ＝app : 
        Γ ⊢ b ＝ d →
        Γ ⊢ a ＝ c →
        Γ ⊢ b · a ＝ (d · c)

    -- Look into substitution rules 
    ＝beta : Γ ⊢ (ƛ∶ A 𝕢 σ ♭ b) · a ＝ (b [ a / 0 ])

    ＝lift : 
        (Γ , A 𝕢  σ) ⊢ b 𝕢 π ∶ B →
        Γ ⊢ a ＝ c →
        Γ ⊢ b [ a / 0 ] ＝ ( b [ c / 0 ]) 
    
    -- equiv properties
    ＝refl : Γ ⊢ A ＝ A
    ＝sym : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ A 
    ＝trans : 
        Γ ⊢ A ＝ B →
        Γ ⊢ B ＝ C →
        Γ ⊢ A ＝ C
    
    ---- eliminators 
    -- nats
    ＝natelz :
        Γ ⊢ m ＝ z →
        Γ ⊢ elimnat m P∶ P 
            zb∶ zb 
            sb∶ sb 
            ＝ 
            zb
    ＝natels :
        Γ ⊢ n ＝ s n →
        Γ ⊢ elimnat n P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            a →
        Γ ⊢ elimnat m P∶ P 
                zb∶ zb 
                sb∶ sb 
            ＝ 
            ((sb · n) · a)
    -- list
    ＝listeln :
        Γ ⊢ cs ＝ nill →
        Γ ⊢ eliml cs P∶ P ty∶ A  
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝listelc : 
        Γ ⊢ cs ＝ (a ∷l as) →
        Γ ⊢ eliml as P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        Γ ⊢ eliml cs P∶ P ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            (((cb · a) · as) ·  b)
    -- vec
    ＝veceln :
        Γ ⊢ cs ＝ nilv →
        Γ ⊢ elimv cs P∶ P l∶ z ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            nb
    ＝vecelc :
        Γ ⊢ cs ＝ (a ∷v as) → 
        Γ ⊢ elimv nilv P∶ P l∶ n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            b →
        Γ ⊢ elimv cs P∶ P l∶ s n ty∶ A 
                nb∶ nb 
                cb∶ cb 
            ＝ 
            ((((cb · n) · a) · as) · b)
    
    ---- Cong rules for datatypes 
    -- Nat
    ＝s : 
        Γ ⊢ n ＝ m →
        Γ ⊢ s n ＝ s m
    -- List
    ＝list : 
        Γ ⊢ A ＝ B →
        Γ ⊢ List A ＝ List B
    ＝∷l :
        Γ ⊢ a ＝ c →
        Γ ⊢ as ＝ cs →
        Γ ⊢ a ∷l as ＝ (c ∷l cs)
    -- Vec
    ＝vec : 
        Γ ⊢ n ＝ m →
        Γ ⊢ A ＝ B →
        Γ ⊢ Vec n A ＝ Vec m B
    ＝∷v :
        Γ ⊢ a ＝ c →
        Γ ⊢ as ＝ cs →
        Γ ⊢ a ∷v as ＝ (c ∷v cs)

    ---- QTT stuff
    -- Unsure if I am interpreting this right
    ⊢TM＝𝟘 :
        Γ ⊢ a ＝ b →
        zeroC Γ ⊢ a ＝ b
         