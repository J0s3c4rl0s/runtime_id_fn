module RunId.Utils where
open import RunId.Syntax

open import Data.Nat -- using (ℕ; suc; _+_; _≡ᵇ_; _≟_; _≤ᵇ_; _≤_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Agda.Builtin.Equality.Rewrite

private variable
    Γ : Context
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Type
    a b c d e f g h l m n  : Term
    as : Term
    nb cb zb sb : Term

open import Data.Unit
open import Data.Empty

data _≤q_ : Quantity → Quantity → Set where
   𝟘≤q : 𝟘 ≤q ρ 
   ω≤qω : ω ≤q ω

≤q-refl : σ ≤q σ 
≤q-refl {𝟘} = 𝟘≤q
≤q-refl {ω} = ω≤qω

_+q_ : Quantity → Quantity → Quantity
𝟘 +q q2 = q2
ω +q q2 = ω


+q-right-idω : σ +q ω ≡ ω 
+q-right-idω {𝟘} = refl
+q-right-idω {ω} = refl

+q-right-id𝟘 : σ +q 𝟘 ≡ σ 
+q-right-id𝟘 {𝟘} = refl
+q-right-id𝟘 {ω} = refl

+q-idempotent : σ +q σ ≡ σ
+q-idempotent {𝟘} = refl
+q-idempotent {ω} = refl

{-# REWRITE +q-right-idω +q-right-id𝟘 +q-idempotent #-}

_*q_ : Quantity → Quantity → Quantity
𝟘 *q q2 = 𝟘
ω *q q2 = q2

*q-right-idω : σ *q ω ≡ σ
*q-right-idω {𝟘} = refl
*q-right-idω {ω} = refl

{-# REWRITE *q-right-idω #-}



-- *c-right-idω : ω *c Γ ≡ Γ 
-- *c-right-idω {Γ = []} = refl
-- *c-right-idω {Γ = Γ , A 𝕢 σ} = cong (λ x → x , A 𝕢 σ) *c-right-idω

-- {-# REWRITE *c-right-idω #-}




-- open import Data.Unit 
-- open import Data.Product renaming (_,_ to ⟨_,_⟩)

-- _+c_＝_ : Context → Context → Context → Set
-- [] +c [] ＝ [] = ⊤
-- (Γₗ , A 𝕢 σ) +c Γᵣ , .A 𝕢 σ₁ ＝ (Γ , .A 𝕢 σ₂) = (Γₗ +c Γᵣ ＝ Γ) × (σ +q σ₁) ≡ σ₂


-- data _+c_＝_ : Context → Context → Context → Set where
--     instance +c[] : [] +c [] ＝ []
--     +c, : 
--         {Γₗ Γᵣ Γ : Context} →
--         {Γₗ +c Γᵣ ＝ Γ} → 
--         {(σ +q π) ≡ ρ} →
--         (Γₗ , A 𝕢 σ) +c Γᵣ , A 𝕢 π ＝ (Γ , A 𝕢 ρ) 

∋→ℕ : Γ ∋ (A 𝕢 σ) → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
_↑_≥_ : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
_↑_≥_ (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
-- constructors
_↑_≥_ (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ _↑_≥_ t i l 𝕢 σ ♭ _↑_≥_ t₁ i (suc l)
_↑_≥_ (ƛr∶ t ♭ t₁) i l = (ƛr∶ _↑_≥_ t i l ♭ _↑_≥_ t₁ i (suc l))
⟨ a 𝕢 σ , b 𝕢 π ⟩ ↑ i ≥ l = ⟨ ((a ↑ i ≥ l) 𝕢 σ) , (b ↑ i ≥ (suc l) 𝕢 π) ⟩
inl< σ , π > a ↑ i ≥ l = 
    inl< σ , π > (a ↑ i ≥ l)
inr< σ , π > a ↑ i ≥ l = 
    inr< σ , π > (a ↑ i ≥ l)
_↑_≥_ z i l = z
_↑_≥_ (s t) i l = s (_↑_≥_ t i l) 
_↑_≥_ nill i l = nill
_↑_≥_ (t ∷l t₁) i l = _↑_≥_ t i l ∷l _↑_≥_ t₁ i l
_↑_≥_ (nilv𝕢 σ) i l = nilv𝕢 σ
_↑_≥_ (t ∷v t₁ 𝕟 n 𝕢 σ) i l = _↑_≥_ t i l ∷v _↑_≥_ t₁ i l 𝕟 _↑_≥_ n i l 𝕢 σ
rfl ↑ i ≥ l = rfl
-- eliminators
_↑_≥_ (t · t₁ 𝕢 σ) i l = _↑_≥_ t i l · _↑_≥_ t₁ i l 𝕢 σ
_↑_≥_ (f ·ᵣ a) i l = _↑_≥_ f i l ·ᵣ _↑_≥_ a i l
el×< σ , π >[ A , B ] a P b ↑ i ≥ l = 
    -- Motive isnt correct
    el×< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ (suc l) ] (a ↑ i ≥ l) (P ↑ i ≥ l) 
        (b ↑ i ≥ l)
elᵣ×< σ , π >[ A , B ] a P b ↑ i ≥ l =  
    -- Motive isnt correct
    el×< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ (suc l) ] (a ↑ i ≥ l) (P ↑ i ≥ l) 
        (b ↑ i ≥ (2 + l))
el＋< σ , π >[ A , B ] a P b c ↑ i ≥ l = 
    el＋< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ l ] (a ↑ i ≥ l) (P ↑ i ≥ (suc l)) 
        (b ↑ i ≥ (suc l))
        (c ↑ i ≥ (suc l))
elᵣ＋< σ , π >[ A , B ] a P b c ↑ i ≥ l = 
    elᵣ＋< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ l ] (a ↑ i ≥ l) (P ↑ i ≥ (suc l)) 
        (b ↑ i ≥ (suc l))
        (c ↑ i ≥ (suc l))
_↑_≥_ (elNat t t₁ zb sb) i l = 
    elNat (_↑_≥_ t i l) (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ zb i l) 
            (_↑_≥_ sb i (2 + l))
_↑_≥_ (elᵣNat t t₁ zb sb) i l = 
    elᵣNat (_↑_≥_ t i l) (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ zb i l) 
            (_↑_≥_ sb i (2 + l))
_↑_≥_ (elList[ A ] t t₁ t₃ t₄) i l = 
    elList[  (_↑_≥_ A i l) ] (_↑_≥_ t i l) (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ t₃ i l) 
            (_↑_≥_ t₄ i (3 + l))
_↑_≥_ (elᵣList[ A ]  t t₁ t₃  t₄) i l = 
    elᵣList[  (_↑_≥_ A i l) ] (_↑_≥_ t i l) (_↑_≥_ t₁ i (suc l)) 
            (_↑_≥_ t₃ i l) 
             (_↑_≥_ t₄ i (3 + l))
_↑_≥_ (elVec[ A ]< σ >  t t₁ t₄ t₅) i l = 
    elVec[ (_↑_≥_ A i l) ]< σ > (_↑_≥_ t i l) (_↑_≥_ t₁ i (2+ l)) 
            (_↑_≥_ t₄ i l) 
             (_↑_≥_ t₅ i (4 + l))
_↑_≥_ (elᵣVec[ A ]< σ >  t t₁ t₄  t₅) i l = 
    elᵣVec[ (_↑_≥_ A i l) ]< σ > (_↑_≥_ t i l) (_↑_≥_ t₁ i (2+ l)) 
            (_↑_≥_ t₄ i l) 
             (_↑_≥_ t₅ i (4 + l))
(subst a by (b 𝕢 σ)) ↑ i ≥ l = 
    subst a ↑ i ≥ l by ((b ↑ i ≥ l) 𝕢 σ)
-- Types
_↑_≥_ Nat i l = Nat
_↑_≥_ (List t) i l = List (_↑_≥_ t i l)
_↑_≥_ (Vec t₁ (A 𝕢 σ)) i l = Vec (_↑_≥_ t₁ i l) ((_↑_≥_ A i l) 𝕢 σ)
((A 𝕢 σ) × (B 𝕢 π)) ↑ i ≥ l =  ((A ↑ i ≥ l) 𝕢 σ) × ((B ↑ i ≥ (suc l)) 𝕢 π)
_↑_≥_ (t 𝕢 σ ⟶ t₁) i l = _↑_≥_ t i l 𝕢 σ ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (t ⟶r t₁) i l = _↑_≥_ t i l ⟶r _↑_≥_ t₁ i (suc l)
_↑_≥_ (Sett level) i l = Sett level
((A 𝕢 σ) ＋ (B 𝕢 π)) ↑ i ≥ l = ((A ↑ i ≥ l) 𝕢 σ) ＋ ((B ↑ i ≥ l) 𝕢 π)
(a ≃ b) ↑ i ≥ l = (a ↑ i ≥ l) ≃ (b ↑ i ≥ l)

-- conLen : PreContext → ℕ
-- conLen [] = 0
-- conLen (Γ , x) = suc (conLen Γ) 

-- insertTypePre : (Γ : PreContext) → (i : ℕ) → (p : i ≤ conLen Γ) → Type → PreContext 
-- insertTypePre Γ 0 p A = Γ , A
-- insertTypePre (Γ , B) (suc i) (s≤s p) A = insertTypePre Γ i p A , _↑_≥_ B 1 i

-- -- use Annotation instead?
-- insertType : Context → (i : ℕ) → (p : i ≤ conLen Γ)  → (A : Type) → Quantity → Context (insertTypePre Γ i p A)
-- insertType Γ 0 z≤n A σ = Γ , A 𝕢 σ
-- insertType (Γ , B 𝕢 ρ) (suc i) (s≤s p) A σ = insertType Γ i p A σ , _↑_≥_ B 1 i 𝕢 ρ 

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → ℕ → Term → Term
var j [  i / a ] = if i ≡ᵇ j then a else var j 
-- Constructors
(ƛ∶ bₜ 𝕢 σ ♭ b) [ i / a ] = ƛ∶ bₜ [ i / a ]  𝕢 σ ♭ (b [ suc i / _↑_≥_ a 1 0 ])
(ƛr∶ b ♭ b₁) [ i / a ] = (ƛr∶ (b [ i / a ]) ♭ (b₁ [ suc i / _↑_≥_ a 1 0 ]))
⟨ c 𝕢 σ , b 𝕢 π ⟩ [ i / a ] = ⟨ ((c [ i / a ]) 𝕢 σ) , ((b [ (suc i) / (a ↑ 1 ≥ 0) ]) 𝕢 π) ⟩
inl< σ , π > b [ i / a ] = inl< σ , π > ((b [ i / a ]))
inr< σ , π > b [ i / a ] = inr< σ , π > ((b [ i / a ]))
z [ i / a ] = z
s b [ i / a ] = s ((b [ i / a ])) 
nill [ i / a ] = nill
(h ∷l t) [ i / a ] = (h [ i / a ]) ∷l (t [ i / a ])
nilv𝟘 [ i / a ] = nilv𝟘
nilvω [ i / a ] = nilvω
(h ∷v t 𝕟 n 𝕢 σ) [ i / a ] = (h [ i / a ]) ∷v (t [ i / a ]) 𝕟 (n [ i / a ]) 𝕢 σ
rfl [ i / a ] = rfl
-- Eliminators
(b ·𝟘 c) [ i / a ] = ((b [ i / a ])) ·𝟘 (c [ i / a ])
(b ·ω c) [ i / a ] = ((b [ i / a ])) ·ω (c [ i / a ])
(f ·ᵣ b) [ i / a ] = (f [ i / a ]) ·ᵣ ((b [ i / a ]))
el×< σ , π >[ A , B ] c P b [ i / a ] = 
    el×< σ , π >[ (A [ i / a ]) , B [ suc i / a ↑ 1 ≥ 0 ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ 2 + i / a ↑ 2 ≥ 0 ])
elᵣ×< σ , π >[ A , B ] c P b [ i / a ] = 
    elᵣ×< σ , π >[ (A [ i / a ]) , B [ suc i / a ↑ 1 ≥ 0 ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ 2 + i / a ↑ 2 ≥ 0 ])
el＋< σ , π >[ A , B ] c P b d [ i / a ] = 
    -- motive is wrong?
    el＋< σ , π >[ (A [ i / a ]) , B [ i / a ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ suc i / a ↑ 1 ≥ 0 ]) 
        (d [ suc i / a ↑ 1 ≥ 0 ])
elᵣ＋< σ , π >[ A , B ] c P b d [ i / a ] =  
    -- motive is wrong?
    elᵣ＋< σ , π >[ (A [ i / a ]) , B [ i / a ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ suc i / a ↑ 1 ≥ 0 ]) 
        (d [ suc i / a ↑ 1 ≥ 0 ])
(elNat b P zb sb) [ i / a ] = 
    elNat ((b [ i / a ])) ((P [ i / a ]) )
        (zb [ i / a ]) 
        (sb [ i + 2 / _↑_≥_ a 2 0 ])
(elᵣNat b P zb sb) [ i / a ] = 
    elNat ((b [ i / a ])) ((P [ i / a ])) 
        (zb [ i / a ]) 
        (sb [ i + 2 / _↑_≥_ a 2 0 ])
(elList[ A ] b P nb  cb) [ i / a ] = 
    elList[ (A [ i / a ]) ] (b [ i / a ]) (P [ i / a ]) 
        ((nb [ i / a ])) 
        (cb [ i + 3 / _↑_≥_ a 3 0 ])
(elᵣList[ A ]  b P nb  cb) [ i / a ] = 
    elᵣList[ (A [ i / a ]) ] (b [ i / a ]) (P [ i / a ]) 
        (nb [ i / a ]) 
        (cb [ i + 3 / _↑_≥_ a 3 0 ])
(elVec[ A ]< σ >  b P nb  cb) [ i / a ] = 
    elVec[ (A [ i / a ]) ]< σ > (b [ i / a ]) (P [ i / a ]) 
        (nb [ i / a ]) 
         (cb [ i + 4 / _↑_≥_ a 4 0 ])
(elᵣVec[ A ]< σ >  b P nb  cb) [ i / a ] = 
    elᵣVec[ (A [ i / a ]) ]< σ > (b [ i / a ]) (P [ i / a ]) 
        (nb [ i / a ]) 
         (cb [ i + 4 / _↑_≥_ a 4 0 ])
(subst b by (eq 𝕢 σ)) [ i / a ] = subst (b [ i / a ]) by ((eq [ i / a ]) 𝕢 σ)
-- Types
(b 𝕢 σ ⟶ c) [ i / a ] = (b [ i / a ]) 𝕢 σ ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
(b ⟶r c) [ i / a ] = (b [ i / a ]) ⟶r (c [ suc i / _↑_≥_ a 1 0 ]) 
((A 𝕢 σ) × (B 𝕢 π)) [ i / a ] = ((A [ i / a ]) 𝕢 σ) × ((B [ i + 1 / (B ↑ 1 ≥ 0) ]) 𝕢 π)
((A 𝕢 σ) ＋ (B 𝕢 π)) [ i / a ] = (((A [ i / a ])) 𝕢 σ) ＋ ((B [ i / a ]) 𝕢 π)
Nat [ i / a ] = Nat
List b [ i / a ] = List ((b [ i / a ]))
Vec b (n 𝕢 σ) [ i / a ] = Vec ((b [ i / a ])) (((n [ i / a ])) 𝕢 σ)
(l ≃ r) [ i / a ] = (l [ i / a ]) ≃ (r [ i / a ])
Sett level [ i / a ] = Sett level    
