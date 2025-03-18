module RunId.Utils where

open import RunId.Syntax

open import Data.Nat using (ℕ; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

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
shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ∶ t 𝕢 σ ♭ t₁) i l = ƛ∶ shiftindices t i l 𝕢 σ ♭ shiftindices t₁ i (suc l)
shiftindices (ƛr∶ t ♭ t₁) i l = (ƛr∶ shiftindices t i l ♭ shiftindices t₁ i (suc l))
shiftindices (t · t₁ 𝕢 σ) i l = shiftindices t i l · shiftindices t₁ i l 𝕢 σ
shiftindices (f ·ᵣ a) i l = shiftindices f i l ·ᵣ shiftindices a i l
shiftindices z i l = z
shiftindices (s t) i l = s (shiftindices t i l) 
shiftindices nill i l = nill
shiftindices (t ∷l t₁) i l = shiftindices t i l ∷l shiftindices t₁ i l
shiftindices (nilv𝕢 σ) i l = nilv𝕢 σ
shiftindices (t ∷v t₁ 𝕟 n 𝕢 σ) i l = shiftindices t i l ∷v shiftindices t₁ i l 𝕟 shiftindices n i l 𝕢 σ
shiftindices (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) i l = 
    elimnat (shiftindices t i l) P∶ (shiftindices t₁ i (suc l)) 
            zb∶ (shiftindices t₂ i l) 
            sb∶ (shiftindices t₃ i (2 + l))
shiftindices (eliml t ty∶ A P∶ t₁ nb∶ t₃ cb∶ t₄) i l = 
    eliml (shiftindices t i l) ty∶ shiftindices A i l P∶ (shiftindices t₁ i (suc l)) 
            nb∶ (shiftindices t₃ i l) 
            cb∶ (shiftindices t₄ i (3 + l))
shiftindices (elimv (t 𝕢 σ) ty∶ A P∶ t₁ nb∶ t₄ cb∶ t₅) i l = 
    elimv ((shiftindices t i l) 𝕢 σ) ty∶ shiftindices A i l P∶ (shiftindices t₁ i (suc l)) 
            nb∶ (shiftindices t₄ i l) 
            cb∶ (shiftindices t₅ i (4 + l))
shiftindices Nat i l = Nat
shiftindices (List t) i l = List (shiftindices t i l)
shiftindices (Vec t₁ (A 𝕢 σ)) i l = Vec (shiftindices t₁ i l) (shiftindices A i l 𝕢 σ)
shiftindices (∶ t 𝕢 σ ⟶ t₁) i l = ∶ shiftindices t i l 𝕢 σ ⟶ shiftindices t₁ i (suc l)
shiftindices (r∶ t ⟶ t₁) i l = r∶ shiftindices t i l ⟶ shiftindices t₁ i (suc l)
shiftindices (Sett level) i l = Sett level

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → ℕ → Term → Term
var 0 [  0 / a ] = a
var b [ i / a  ] = var b 
(ƛ∶ bₜ 𝕢 σ ♭ b) [ i / a ] = ƛ∶ bₜ [ i / a ]  𝕢 σ ♭ (b [ suc i / shiftindices a 1 0 ])
(ƛr∶ b ♭ b₁) [ i / a ] = (ƛr∶ b [ i / a ] ♭ (b₁ [ suc i / shiftindices a 1 0 ]))
(b ·𝟘 c) [ i / a ] = (b [ i / a ]) ·𝟘 (c [ i / a ])
(b ·ω c) [ i / a ] = (b [ i / a ]) ·ω (c [ i / a ])
(f ·ᵣ b) [ i / a ] = (f [ i / a ]) ·ᵣ (b [ i / a ])
(∶ b 𝕢 σ ⟶ c) [ i / a ] = ∶ b [ i / a ] 𝕢 σ ⟶ (c [ suc i / shiftindices a 1 0 ]) 
(r∶ b ⟶ c) [ i / a ] = r∶ b [ i / a ] ⟶ (c [ suc i / shiftindices a 1 0 ]) 
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
        sb∶ (sb [ i + 2 / shiftindices a 2 0 ])
(eliml b ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    eliml b [ i / a ] ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 3 / shiftindices a 3 0 ])
(elimv (b 𝕢 σ) ty∶ A P∶ P nb∶ nb cb∶ cb) [ i / a ] = 
    elimv (b [ i / a ] 𝕢 σ) ty∶ A [ i / a ] P∶ P [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 4 / shiftindices a 4 0 ])
Nat [ i / a ] = Nat
List b [ i / a ] = List (b [ i / a ])
Vec b (n 𝕢 σ) [ i / a ] = Vec (b [ i / a ]) (((n [ i / a ])) 𝕢 σ)
Sett level [ i / a ] = Sett level 