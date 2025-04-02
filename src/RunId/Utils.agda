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

{-# REWRITE +q-right-idω +q-right-id𝟘 #-}

_*q_ : Quantity → Quantity → Quantity
𝟘 *q q2 = 𝟘
ω *q q2 = q2

-- In our case equivalent to multd
selectQ : Quantity → Quantity → Quantity
selectQ π σ = π *q σ


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


∋→ℕ : cΓ ∋ (A 𝕢 σ) → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)

-- Dont think this should change Quantity
_↑_≥_ : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
_↑_≥_ (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
_↑_≥_ (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ _↑_≥_ t i l 𝕢 σ ♭ _↑_≥_ t₁ i (suc l)
_↑_≥_ (ƛr∶ t ♭ t₁) i l = (ƛr∶ _↑_≥_ t i l ♭ _↑_≥_ t₁ i (suc l))
_↑_≥_ (t · t₁ 𝕢 σ) i l = _↑_≥_ t i l · _↑_≥_ t₁ i l 𝕢 σ
_↑_≥_ (f ·ᵣ a) i l = _↑_≥_ f i l ·ᵣ _↑_≥_ a i l
_↑_≥_ z i l = z
_↑_≥_ (s t) i l = s (_↑_≥_ t i l) 
_↑_≥_ nill i l = nill
_↑_≥_ (t ∷l t₁) i l = _↑_≥_ t i l ∷l _↑_≥_ t₁ i l
_↑_≥_ (nilv𝕢 σ) i l = nilv𝕢 σ
_↑_≥_ (t ∷v t₁ 𝕟 n 𝕢 σ) i l = _↑_≥_ t i l ∷v _↑_≥_ t₁ i l 𝕟 _↑_≥_ n i l 𝕢 σ
_↑_≥_ (elimnat t P∶ t₁ zb∶ zb sb∶ sb) i l = 
    elimnat (_↑_≥_ t i l) P∶ (_↑_≥_ t₁ i (suc l)) 
            zb∶ (_↑_≥_ zb i l) 
            sb∶ (_↑_≥_ sb i (2 + l))
_↑_≥_ (eliml t ty∶ A P∶ t₁ nb∶ t₃ cb∶ t₄) i l = 
    eliml (_↑_≥_ t i l) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (suc l)) 
            nb∶ (_↑_≥_ t₃ i l) 
            cb∶ (_↑_≥_ t₄ i (3 + l))
_↑_≥_ (elimv (t 𝕢 σ) ty∶ A P∶ t₁ nb∶ t₄ cb∶ t₅) i l = 
    elimv ((_↑_≥_ t i l) 𝕢 σ) ty∶ _↑_≥_ A i l P∶ (_↑_≥_ t₁ i (2+ l)) 
            nb∶ (_↑_≥_ t₄ i l) 
            cb∶ (_↑_≥_ t₅ i (4 + l))
_↑_≥_ Nat i l = Nat
_↑_≥_ (List t) i l = List (_↑_≥_ t i l)
_↑_≥_ (Vec t₁ (A 𝕢 σ)) i l = Vec (_↑_≥_ t₁ i l) (_↑_≥_ A i l 𝕢 σ)
_↑_≥_ (∶ t 𝕢 σ ⟶ t₁) i l = ∶ _↑_≥_ t i l 𝕢 σ ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (r∶ t ⟶ t₁) i l = r∶ _↑_≥_ t i l ⟶ _↑_≥_ t₁ i (suc l)
_↑_≥_ (Sett level) i l = Sett level


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
(b ·𝟘 c) [ i / a ] = (b [ i / a ]) ·𝟘 (c [ i / a ])
(b ·ω c) [ i / a ] = (b [ i / a ]) ·ω (c [ i / a ])
(f ·ᵣ b) [ i / a ] = (f [ i / a ]) ·ᵣ (b [ i / a ])
(∶ b 𝕢 σ ⟶ c) [ i / a ] = ∶ b [ i / a ] 𝕢 σ ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
(r∶ b ⟶ c) [ i / a ] = r∶ b [ i / a ] ⟶ (c [ suc i / _↑_≥_ a 1 0 ]) 
z [ i / a ] = z
s b [ i / a ] = s (b [ i / a ]) 
nill [ i / a ] = nill
(h ∷l t) [ i / a ] = (h [ i / a ]) ∷l (t [ i / a ])
nilv𝟘 [ i / a ] = nilv𝟘
nilvω [ i / a ] = nilvω
(h ∷v t 𝕟𝟘 n) [ i / a ] = (h [ i / a ]) ∷v (t [ i / a ]) 𝕟𝟘 (n [ i / a ])
(h ∷v t 𝕟ω n) [ i / a ] = (h [ i / a ]) ∷v (t [ i / a ]) 𝕟ω (n [ i / a ])
(elimnat b P∶ P zb∶ zb sb∶ sb) [ i / a ] = 
    elimnat b [ i / a ] P∶ P [ i / a ] 
        zb∶ zb [ i / a ] 
        sb∶ (sb [ i + 2 / _↑_≥_ a 2 0 ])
(eliml b ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    eliml b [ i / a ] ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 3 / _↑_≥_ a 3 0 ])
(elimv (b 𝕢 σ) ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    elimv (b [ i / a ] 𝕢 σ) ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 4 / _↑_≥_ a 4 0 ])
Nat [ i / a ] = Nat
List b [ i / a ] = List (b [ i / a ])
Vec b (n 𝕢 σ) [ i / a ] = Vec (b [ i / a ]) (((n [ i / a ])) 𝕢 σ)
Sett level [ i / a ] = Sett level 