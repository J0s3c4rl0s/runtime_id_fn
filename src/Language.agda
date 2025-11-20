module Language where 

open import Data.Nat

data Quantity : Set where 
    𝟘 : Quantity
    ω : Quantity

data Context : Set
data Term : Set 

Type = Term

private variable
    Γ : Context
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Type
    a a' b c d e f g h l m n  : Term
    as cs : Term
    nb cb zb sb : Term


data Annotation : Type → Quantity → Set where
    _𝕢_ : (A : Type) → (σ : Quantity) → Annotation A σ

data Context where
    [] : Context
    _,_ : Context → Annotation A σ → Context

infixl 10 _,_
infix 12 _𝕢_
infix 8 _∋_

data _∋_ : Context → Annotation A σ → Set where
  Z : ∀ {Γ : Context}
    →  (Γ , (A 𝕢 σ)) ∋ (A 𝕢 σ)

  S : ∀ {A} {B} {Γ : Context}
    -- Ensure there is a lookup judgement in submodule
    → Γ ∋ A 𝕢 σ
    →  (Γ , B 𝕢 π) ∋ A 𝕢 σ

data Term where
    var :  ℕ → Term 
    
    -- Functions
    _⟶_ : Annotation A σ → Type → Type -- Pi type
    _⟶r_ : Type → Type → Type -- Runtime Pi type
    ƛ∶_♭_ : Annotation A σ → Term → Term
    -- Better to take an extra arg to determine its a runtime ID (annot)
    -- RuntimeId, any erased args? Forced annotations?
    ƛr∶_♭_ : Type → Term → Term
    _·_𝕢_ : Term → Term → Quantity → Term
    _·ᵣ_ : Term → Term → Term
    
    -- Nats
    Nat : Type
    z : Term
    s : Term → Term 
    elNat : Term → Term → Term → Term
    elᵣNat : Term → Term → Term → Term
    Sett : ℕ → Type -- Universe 


infixr 9 _⟶_

pattern ƛ𝟘∶_♭_ A b = ƛ∶_♭_ (A 𝕢 𝟘) b
pattern ƛω∶_♭_ A b = ƛ∶_♭_ (A 𝕢 ω) b
pattern _·𝟘_ f a = _·_𝕢_ f a 𝟘
pattern _·ω_ f a = _·_𝕢_ f a ω

infixl 9 _·ω_
infixl 9 _·𝟘_

-- Utils 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Data.Bool using (Bool; true; false; if_then_else_)


data _≤q_ : Quantity → Quantity → Set where
   𝟘≤q : 𝟘 ≤q ρ 
   ω≤qω : ω ≤q ω

≤q-refl : σ ≤q σ 
≤q-refl {𝟘} = 𝟘≤q
≤q-refl {ω} = ω≤qω


_*q_ : Quantity → Quantity → Quantity
𝟘 *q q2 = 𝟘
ω *q q2 = q2

*q-right-idω : σ *q ω ≡ σ
*q-right-idω {𝟘} = refl
*q-right-idω {ω} = refl



∋→ℕ : Γ ∋ (A 𝕢 σ) → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
_↑_≥_ : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
_↑_≥_ (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
-- constructors
_↑_≥_ (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ _↑_≥_ t i l 𝕢 σ ♭ _↑_≥_ t₁ i (suc l)
_↑_≥_ (ƛr∶ t ♭ t₁) i l = (ƛr∶ _↑_≥_ t i l ♭ _↑_≥_ t₁ i (suc l))
_↑_≥_ z i l = z
_↑_≥_ (s t) i l = s (_↑_≥_ t i l) 
-- eliminators
_↑_≥_ (t · t₁ 𝕢 σ) i l = _↑_≥_ t i l · _↑_≥_ t₁ i l 𝕢 σ
_↑_≥_ (f ·ᵣ a) i l = _↑_≥_ f i l ·ᵣ _↑_≥_ a i l
_↑_≥_ (elNat t₁ zb sb) i l = 
    elNat (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ zb i l) 
            (_↑_≥_ sb i (2 + l))
_↑_≥_ (elᵣNat t₁ zb sb) i l = 
    elᵣNat (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ zb i l) 
            (_↑_≥_ sb i (2 + l))
-- Types
_↑_≥_ Nat i l = Nat
_↑_≥_ (t 𝕢 σ ⟶ t₁) i l = _↑_≥_ t i l 𝕢 σ ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (t ⟶r t₁) i l = _↑_≥_ t i l ⟶r _↑_≥_ t₁ i (suc l)
_↑_≥_ (Sett level) i l = Sett level


-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → ℕ → Term → Term
-- Shift down all free variables, ie all variables "above" the one being substituted for
var j [ i / a ] = if i ≡ᵇ j then a else var (if i ≤ᵇ j then j ∸ 1 else j) 
-- Constructors
(ƛ∶ bₜ 𝕢 σ ♭ b) [ i / a ] = ƛ∶ bₜ [ i / a ]  𝕢 σ ♭ (b [ suc i / _↑_≥_ a 1 0 ])
(ƛr∶ b ♭ b₁) [ i / a ] = (ƛr∶ (b [ i / a ]) ♭ (b₁ [ suc i / _↑_≥_ a 1 0 ]))
z [ i / a ] = z
s b [ i / a ] = s ((b [ i / a ])) 
-- Eliminators
(b ·𝟘 c) [ i / a ] = ((b [ i / a ])) ·𝟘 (c [ i / a ])
(b ·ω c) [ i / a ] = ((b [ i / a ])) ·ω (c [ i / a ])
(f ·ᵣ b) [ i / a ] = (f [ i / a ]) ·ᵣ ((b [ i / a ]))
(elNat P zb sb) [ i / a ] = 
    elNat ((P [ i / a ]) )
        (zb [ i / a ]) 
        (sb [ i + 2 / _↑_≥_ a 2 0 ])
(elᵣNat P zb sb) [ i / a ] = 
    elNat ((P [ i / a ])) 
        (zb [ i / a ]) 
        (sb [ i + 2 / _↑_≥_ a 2 0 ])
-- Types
(b 𝕢 σ ⟶ c) [ i / a ] = (b [ i / a ]) 𝕢 σ ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
(b ⟶r c) [ i / a ] = (b [ i / a ]) ⟶r (c [ suc i / _↑_≥_ a 1 0 ]) 
Nat [ i / a ] = Nat
Sett level [ i / a ] = Sett level    

-- Rules

private variable
    i j 𝓁 𝓁₁ 𝓁₂ : ℕ

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

    -- Nats
    ⊢Nat : 
        Γ ⊢ Nat 𝕢 𝟘 ∶ Sett 𝓁 
    ⊢z : 
        Γ ⊢ z 𝕢 σ ∶ Nat
    ⊢s : 
        Γ ⊢ a 𝕢 σ ∶ Nat →
        Γ ⊢ s a 𝕢 σ ∶ Nat
    -- either nothing is erased or everything is (?)
    -- ⊢natel : ∀ {zb sb} →
    --     Γ ⊢ n 𝕢 σ ∶ Nat →
    --     -- Maybe P and n should match usage (check?) or comes naturally from rule
    --     -- Γ ⊢ P 𝕢 𝟘 ∶ (∶ Nat 𝕢 π ⟶ Sett 𝓁 ) →
    --     -- enforces that argument to forming this type are erased
    --     (Γ , Nat 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
    --     Γ ⊢ zb 𝕢 σ ∶ (P [ 0 / z ]) →
    --     (Γ , Nat 𝕢 ρ , P [ 0 / var 0 ] 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P [ 0 / s (var 1) ]) →
    --     Γ ⊢ elNat n P 
    --             zb 
    --             sb 
    --         𝕢 σ ∶ (P [ 0 / n ])
    -- ⊢natelᵣ : ∀ {zb sb} →
    --     Γ ⊢ var i 𝕢 σ ∶ Nat →
    --     (Γ , Nat 𝕢 𝟘) ⊢ P 𝕢 𝟘 ∶ Sett 𝓁 →
    --     -- check type? Depends on n?
    --     Nat ~ᵣ P →
    --     Γ ⊢ zb 𝕢 σ ∶ (P [ 0 / z ]) →
    --     (zb [ i / z ]) ~ᵣ z →
    --     (Γ , Nat 𝕢 ρ , P [ 0 / var 0 ] 𝕢 ρ' ) ⊢ sb 𝕢 σ ∶ (P [ 0 / s (var 1) ]) →
    --     -- Cons branch is runid, sub tail to acc
    --     (sb [ 1 / var 0 ] [ 2 + i / s (var 0) ]) ~ᵣ (s (var 0)) →
    --     Γ ⊢ elᵣNat (var i) P 
    --             zb 
    --             sb 
    --         𝕢 σ ∶ (P [ 0 / n ])
    
    ⊢Sett : 
        Γ ⊢ Sett 𝓁 𝕢 𝟘 ∶ Sett (suc 𝓁) 


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
    -- Nat
    ~ᵣs : 
        n ~ᵣ m →
        s n ~ᵣ s m
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
    -- Nat 
    ~ᵣelℕᵣ :
        elᵣNat P b c ~ᵣ (ƛr∶ Nat ♭ var 0) 