module ListCalc.QTT.Utils where

open import ListCalc.QTT.Syntax

open import Data.Nat using (ℕ; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

private variable   
    Γ : PreContext

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

∋→ℕ : ∀ {Γ A σ} {cΓ : Context Γ} → cΓ ∋ (A 𝕢 σ) → ℕ 
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
shiftindices (t ∷v t₁ 𝕟 n) i l = (shiftindices t i l) ∷v (shiftindices t₁ i l) 𝕟 shiftindices n i l
-- shiftindices refl i l = refl
shiftindices (elimnat t P∶ t₁ zb∶ t₂ sb∶ t₃) i l = 
    elimnat (shiftindices t i l) P∶ (shiftindices t₁ i l) 
            zb∶ (shiftindices t₂ i l) 
            sb∶ (shiftindices t₃ i (l + 2))
shiftindices (eliml t P∶ t₁ nb∶ t₃ cb∶ t₄) i l = 
    eliml (shiftindices t i l) P∶ (shiftindices t₁ i l) 
            nb∶ (shiftindices t₃ i l) 
            cb∶ (shiftindices t₄ i (l + 3))
shiftindices (elimv t P∶ t₁ nb∶ t₄ cb∶ t₅) i l = 
    elimv_P∶_nb∶_cb∶_ 
        (shiftindices t i l) (shiftindices t₁ i l) 
            (shiftindices t₄ i l) 
            (shiftindices t₅ i (l + 4))
-- shiftindices (subst a usingg eq) i l = subst {!   !} usingg {!   !}
shiftindices Nat i l = Nat
shiftindices (List t) i l = List (shiftindices t i l)
shiftindices (Vec (n 𝕢 σ) t₁) i l = Vec (shiftindices n i l 𝕢 σ) (shiftindices t₁ i l)
shiftindices (∶ t 𝕢 σ ⟶ t₁) i l = ∶ shiftindices t i l 𝕢 σ ⟶ shiftindices t₁ i (suc l)
-- shiftindices (a ≡ b) i l = shiftindices a i l ≡ shiftindices b i l
shiftindices (Sett level) i l = Sett level

-- There are some hijinks around when substitution is admissible, dont think quants change
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ∶ bₜ 𝕢 σ ♭ b) [ a / i ] = ƛ∶ bₜ [ a / i ]  𝕢 σ ♭ (b [ shiftindices a 1 0 / suc i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b 𝕢 σ ⟶ c) [ a / i ] = ∶ b [ a / i ] 𝕢 σ ⟶ (c [ shiftindices a 1 0 / suc i ]) 
z [ a / i ] = z
s b [ a / i ] = s (b [ a / i ]) 
nill [ a / i ] = nill
(h ∷l t) [ a / i ] = (h [ a / i ]) ∷l (t [ a / i ])
nilv [ a / i ] = nilv
(h ∷v t 𝕟 n) [ a / i ] = (h [ a / i ]) ∷v (t [ a / i ]) 𝕟 (n [ a / i ])
-- refl [ a / i ] = refl
(elimnat b P∶ P zb∶ zb sb∶ sb) [ a / i ] = 
    elimnat b [ a / i ] P∶ P [ a / i ] 
        zb∶ zb [ a / i ] 
        sb∶ (sb [ shiftindices a 2 0 / i + 2 ])
(eliml b P∶ P nb∶ nb cb∶ cb) [ a / i ] = 
    eliml b [ a / i ] P∶ P [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ shiftindices a 3 0 / i + 3 ])
(elimv b P∶ P nb∶ nb cb∶ cb) [ a / i ] = 
    elimv b [ a / i ] P∶ P [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ shiftindices a 4 0 / i + 4 ])
Nat [ a / i ] = Nat
List b [ a / i ] = List (b [ a / i ])
Vec (n 𝕢 σ) b [ a / i ] = Vec ((n [ a / i ]) 𝕢 σ) (b [ a / i ])
-- (b ≡ c) [ a / i ] = (b [ a / i ]) ≡ (c [ a / i ]) 
Sett level [ a / i ] = Sett level