module RunId.Utils where
open import RunId.Syntax

open import Data.Nat -- using (ℕ; suc; _+_; _≡ᵇ_; _≟_; _≤ᵇ_; _≤_; s≤s; z≤n)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Agda.Builtin.Equality.Rewrite

private variable
    Γ Δ Θ : PreContext
    cΓ cΓ' cΓ'' : Context Γ
    cΔ cΔ' cΔ'' : Context Δ
    cΘ : Context Θ
    σ σ' π π' ρ ρ' ρ'' ρ''' δ : Quantity
    A B C D P : Type
    a b c d e f g h l m n  : Term
    as : Term
    nb cb zb sb : Term

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

-- In our case equivalent to multd
selectQ : Quantity → Quantity → Quantity
selectQ π σ = π *q σ

zeroC : (Γ : PreContext) → Context Γ
zeroC [] = []
zeroC (Γ , a) = zeroC Γ , a 𝕢 𝟘

-- PreContext scaling
_*c_ : Quantity → Context Γ → Context Γ
-- 0 reduces everything
_*c_ {Γ} 𝟘 cΓ = zeroC Γ
-- ω is identity
ω *c cΓ = cΓ


-- *c-right-idω : ω *c cΓ ≡ cΓ 
-- *c-right-idω {cΓ = []} = refl
-- *c-right-idω {cΓ = cΓ , A 𝕢 σ} = cong (λ x → x , A 𝕢 σ) *c-right-idω

-- {-# REWRITE *c-right-idω #-}

-- PreContext addition
_+c_ : Context Γ → Context Γ → Context Γ 
([] +c []) = []
((cΓ , a 𝕢 π) +c (cΔ , a 𝕢 σ)) = (cΓ +c cΔ) , a 𝕢 (π +q σ)

+c-leftid0 : ∀ {Γ : PreContext} {cΓ : Context Γ} → 
    (zeroC Γ +c cΓ) ≡ cΓ
+c-leftid0 {[]} {[]} = refl
+c-leftid0 {Γ , x} {cΓ , .x 𝕢 σ} = cong (λ x₁ → x₁ , (x 𝕢 σ)) +c-leftid0

+c-rightid0 : ∀ {Γ : PreContext} {cΓ : Context Γ} → 
    (cΓ +c zeroC Γ) ≡ cΓ
+c-rightid0 {[]} {[]} = refl
+c-rightid0 {Γ , x} {cΓ , .x 𝕢 σ} = cong (λ cΓ' → cΓ' , x 𝕢 σ) +c-rightid0

+c-idempotent : cΓ +c cΓ ≡ cΓ
+c-idempotent {cΓ = []} = refl
+c-idempotent {cΓ = cΓ , A 𝕢 σ} = cong (λ x → x , (A 𝕢 σ)) +c-idempotent



-- open import Data.Unit 
-- open import Data.Product renaming (_,_ to ⟨_,_⟩)

-- _+c_＝_ : Context Γ → Context Γ → Context Γ → Set
-- [] +c [] ＝ [] = ⊤
-- (cΓₗ , A 𝕢 σ) +c cΓᵣ , .A 𝕢 σ₁ ＝ (cΓ , .A 𝕢 σ₂) = (cΓₗ +c cΓᵣ ＝ cΓ) × (σ +q σ₁) ≡ σ₂


-- data _+c_＝_ : Context Γ → Context Γ → Context Γ → Set where
--     instance +c[] : [] +c [] ＝ []
--     +c, : 
--         {cΓₗ cΓᵣ cΓ : Context Γ} →
--         {cΓₗ +c cΓᵣ ＝ cΓ} → 
--         {(σ +q π) ≡ ρ} →
--         (cΓₗ , A 𝕢 σ) +c cΓᵣ , A 𝕢 π ＝ (cΓ , A 𝕢 ρ) 

∋→ℕ : cΓ ∋ (A 𝕢 σ) → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
_↑_≥_ : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
_↑_≥_ (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
_↑_≥_ (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ _↑_≥_ t i l 𝕢 σ ♭ _↑_≥_ t₁ i (suc l)
_↑_≥_ (ƛr∶ t ♭ t₁) i l = (ƛr∶ _↑_≥_ t i l ♭ _↑_≥_ t₁ i (suc l))
⟨ a 𝕢 σ , b 𝕢 π ⟩ ↑ i ≥ l = ⟨ ((a ↑ i ≥ l) 𝕢 σ) , (b ↑ i ≥ (suc l) 𝕢 π) ⟩
_↑_≥_ (t · t₁ 𝕢 σ) i l = _↑_≥_ t i l · _↑_≥_ t₁ i l 𝕢 σ
_↑_≥_ (f ·ᵣ a) i l = _↑_≥_ f i l ·ᵣ _↑_≥_ a i l
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
el×< σ , π >[ A , B ] a P b ↑ i ≥ l = 
    -- Motive isnt correct
    el×< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ (suc l) ] (a ↑ i ≥ l) (P ↑ i ≥ l) 
        (b ↑ i ≥ l)
el×ᵣ< σ , π >[ A , B ] a P b ↑ i ≥ l =  
    -- Motive isnt correct
    el×< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ (suc l) ] (a ↑ i ≥ l) (P ↑ i ≥ l) 
        (b ↑ i ≥ (2 + l))
el＋< σ , π >[ A , B ] a P b c ↑ i ≥ l = 
    el＋< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ l ] (a ↑ i ≥ l) (P ↑ i ≥ (suc l)) 
        (b ↑ i ≥ (suc l))
        (c ↑ i ≥ (suc l))
el＋ᵣ< σ , π >[ A , B ] a P b c ↑ i ≥ l = 
    el＋ᵣ< σ , π >[ A ↑ i ≥ l , B ↑ i ≥ l ] (a ↑ i ≥ l) (P ↑ i ≥ (suc l)) 
        (b ↑ i ≥ (suc l))
        (c ↑ i ≥ (suc l))
_↑_≥_ (elimnat t P∶ t₁ zb∶ zb sb∶ sb) i l = 
    elimnat (_↑_≥_ t i l) P∶ (_↑_≥_ t₁ i (suc l)) 
            zb∶ (_↑_≥_ zb i l) 
            sb∶ (_↑_≥_ sb i (2 + l))
_↑_≥_ (elimnatᵣ t P∶ t₁ zb∶ zb sb∶ sb) i l = 
    elimnatᵣ (_↑_≥_ t i l) P∶ (_↑_≥_ t₁ i (suc l)) 
            zb∶ (_↑_≥_ zb i l) 
            sb∶ (_↑_≥_ sb i (2 + l))
_↑_≥_ (eliml t ty∶ A P∶ t₁ nb∶ t₃ cb∶ t₄) i l = 
    eliml (_↑_≥_ t i l) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (suc l)) 
            nb∶ (_↑_≥_ t₃ i l) 
            cb∶ (_↑_≥_ t₄ i (3 + l))
_↑_≥_ (elimlᵣ t ty∶ A P∶ t₁ nb∶ t₃ cb∶ t₄) i l = 
    elimlᵣ (_↑_≥_ t i l) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (suc l)) 
            nb∶ (_↑_≥_ t₃ i l) 
            cb∶ (_↑_≥_ t₄ i (3 + l))
_↑_≥_ (elimv (t 𝕢 σ) ty∶ A P∶ t₁ nb∶ t₄ cb∶ t₅) i l = 
    elimv ((_↑_≥_ t i l) 𝕢 σ) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (2+ l)) 
            nb∶ (_↑_≥_ t₄ i l) 
            cb∶ (_↑_≥_ t₅ i (4 + l))
_↑_≥_ (elimvᵣ (t 𝕢 σ) ty∶ A P∶ t₁ nb∶ t₄ cb∶ t₅) i l = 
    elimv ((_↑_≥_ t i l) 𝕢 σ) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (2+ l)) 
            nb∶ (_↑_≥_ t₄ i l) 
            cb∶ (_↑_≥_ t₅ i (4 + l))
_↑_≥_ Nat i l = Nat
_↑_≥_ (List t) i l = List (_↑_≥_ t i l)
_↑_≥_ (Vec t₁ (A 𝕢 σ)) i l = Vec (_↑_≥_ t₁ i l) (_↑_≥_ A i l 𝕢 σ)
(∶ A 𝕢 σ ×∶ (B 𝕢 π)) ↑ i ≥ l = ∶ ((A ↑ i ≥ l) 𝕢 σ) ×∶ ((B ↑ i ≥ (suc l)) 𝕢 π)
_↑_≥_ (∶ t 𝕢 σ ⟶ t₁) i l = ∶ _↑_≥_ t i l 𝕢 σ ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (r∶ t ⟶ t₁) i l = r∶ _↑_≥_ t i l ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (Sett level) i l = Sett level
((A 𝕢 σ) ＋ (B 𝕢 π)) ↑ i ≥ l = ((A ↑ i ≥ l) 𝕢 σ) ＋ ((B ↑ i ≥ l) 𝕢 π)


conLen : PreContext → ℕ
conLen [] = 0
conLen (Γ , x) = suc (conLen Γ) 

insertTypePre : (Γ : PreContext) → (i : ℕ) → (p : i ≤ conLen Γ) → Type → PreContext 
insertTypePre Γ 0 p A = Γ , A
insertTypePre (Γ , B) (suc i) (s≤s p) A = insertTypePre Γ i p A , _↑_≥_ B 1 i

-- use Annotation instead?
insertType : Context Γ → (i : ℕ) → (p : i ≤ conLen Γ)  → (A : Type) → Quantity → Context (insertTypePre Γ i p A)
insertType cΓ 0 z≤n A σ = cΓ , A 𝕢 σ
insertType (cΓ , B 𝕢 ρ) (suc i) (s≤s p) A σ = insertType cΓ i p A σ , _↑_≥_ B 1 i 𝕢 ρ 

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → ℕ → Term → Term
var j [  i / a ] = if i ≡ᵇ j then a else var j 
(ƛ∶ bₜ 𝕢 σ ♭ b) [ i / a ] = ƛ∶ bₜ [ i / a ]  𝕢 σ ♭ (b [ suc i / _↑_≥_ a 1 0 ])
(ƛr∶ b ♭ b₁) [ i / a ] = (ƛr∶ b [ i / a ] ♭ (b₁ [ suc i / _↑_≥_ a 1 0 ]))
⟨ c 𝕢 σ , b 𝕢 π ⟩ [ i / a ] = ⟨ ((c [ i / a ]) 𝕢 σ) , ((b [ (suc i) / (a ↑ 1 ≥ 0) ]) 𝕢 π) ⟩
inl< σ , π > b [ i / a ] = inl< σ , π > (b [ i / a ])
inr< σ , π > b [ i / a ] = inr< σ , π > (b [ i / a ])
z [ i / a ] = z
s b [ i / a ] = s (b [ i / a ]) 
nill [ i / a ] = nill
(h ∷l t) [ i / a ] = (h [ i / a ]) ∷l (t [ i / a ])
nilv𝟘 [ i / a ] = nilv𝟘
nilvω [ i / a ] = nilvω
(h ∷v t 𝕟 n 𝕢 σ) [ i / a ] = (h [ i / a ]) ∷v (t [ i / a ]) 𝕟 (n [ i / a ]) 𝕢 σ
(b ·𝟘 c) [ i / a ] = (b [ i / a ]) ·𝟘 (c [ i / a ])
(b ·ω c) [ i / a ] = (b [ i / a ]) ·ω (c [ i / a ])
(f ·ᵣ b) [ i / a ] = (f [ i / a ]) ·ᵣ (b [ i / a ])
el×< σ , π >[ A , B ] c P b [ i / a ] = 
    el×< σ , π >[ A [ i / a ] , B [ suc i / a ↑ 1 ≥ 0 ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ 2 + i / a ↑ 2 ≥ 0 ])
el×ᵣ< σ , π >[ A , B ] c P b [ i / a ] = 
    el×ᵣ< σ , π >[ A [ i / a ] , B [ suc i / a ↑ 1 ≥ 0 ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ 2 + i / a ↑ 2 ≥ 0 ])
el＋< σ , π >[ A , B ] c P b d [ i / a ] = 
    -- motive is wrong?
    el＋< σ , π >[ A [ i / a ] , B [ i / a ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ suc i / a ↑ 1 ≥ 0 ]) 
        (d [ suc i / a ↑ 1 ≥ 0 ])
el＋ᵣ< σ , π >[ A , B ] c P b d [ i / a ] =  
    -- motive is wrong?
    el＋ᵣ< σ , π >[ A [ i / a ] , B [ i / a ] ] (c [ i / a ]) (P [ suc i / a ↑ 1 ≥ 0 ]) 
        (b [ suc i / a ↑ 1 ≥ 0 ]) 
        (d [ suc i / a ↑ 1 ≥ 0 ])
(elimnat b P∶ P zb∶ zb sb∶ sb) [ i / a ] = 
    elimnat b [ i / a ] P∶ P [ i / a ] 
        zb∶ zb [ i / a ] 
        sb∶ (sb [ i + 2 / _↑_≥_ a 2 0 ])
(elimnatᵣ b P∶ P zb∶ zb sb∶ sb) [ i / a ] = 
    elimnat b [ i / a ] P∶ P [ i / a ] 
        zb∶ zb [ i / a ] 
        sb∶ (sb [ i + 2 / _↑_≥_ a 2 0 ])
(eliml b ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    eliml b [ i / a ] ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 3 / _↑_≥_ a 3 0 ])
(elimlᵣ b ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    elimlᵣ b [ i / a ] ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 3 / _↑_≥_ a 3 0 ])
(elimv (b 𝕢 σ) ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    elimv (b [ i / a ] 𝕢 σ) ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 4 / _↑_≥_ a 4 0 ])
(elimvᵣ (b 𝕢 σ) ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    elimvᵣ (b [ i / a ] 𝕢 σ) ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 4 / _↑_≥_ a 4 0 ])
(∶ b 𝕢 σ ⟶ c) [ i / a ] = ∶ b [ i / a ] 𝕢 σ ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
(r∶ b ⟶ c) [ i / a ] = r∶ b [ i / a ] ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
(∶ A 𝕢 σ ×∶ (B 𝕢 π)) [ i / a ] = ∶ (A [ i / a ]) 𝕢 σ ×∶ ((B [ i + 1 / (B ↑ 1 ≥ 0) ]) 𝕢 π)
((A 𝕢 σ) ＋ (B 𝕢 π)) [ i / a ] = ((A [ i / a ]) 𝕢 σ) ＋ ((B [ i / a ]) 𝕢 π)
Nat [ i / a ] = Nat
List b [ i / a ] = List (b [ i / a ])
Vec b (n 𝕢 σ) [ i / a ] = Vec (b [ i / a ]) (((n [ i / a ])) 𝕢 σ)
Sett level [ i / a ] = Sett level  