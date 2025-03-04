module STLC.Utils where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ t₁) i l = ƛ (shiftindices t₁ i (suc l))
shiftindices (t · t₁) i l = shiftindices t i l · shiftindices t₁ i l
shiftindices z i l = z
shiftindices (s t) i l = s (shiftindices t i l) 
shiftindices nill i l = nill
shiftindices (t ∷l t₁) i l = shiftindices t i l ∷l shiftindices t₁ i l
shiftindices nilv i l = nilv
shiftindices (t ∷v t₁ 𝕟 n) i l = shiftindices t i l ∷v shiftindices t₁ i l 𝕟 shiftindices n i l
shiftindices (elimnat t zb∶ t₂ sb∶ t₃) i l = 
    elimnat_zb∶_sb∶_ (shiftindices t i l) 
        (shiftindices t₂ i l) 
        (shiftindices t₃ i (l + 1))
shiftindices (eliml t nb∶ t₃ cb∶ t₄) i l = 
    eliml_nb∶_cb∶_ (shiftindices t i l) 
        (shiftindices t₃ i l) 
        (shiftindices t₄ i (l + 2))
shiftindices (elimv x nb∶ nb cb∶ cb) i l = 
    elimv shiftindices x i l 
        nb∶ shiftindices nb i l
        cb∶ shiftindices cb i (l + 3)

-- Consider parallel subtitutions to deal with free variable capture

-- Could reflection make this more efficient?
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ b) [ a / i ] = ƛ (b [ shiftindices a 1 0 / suc i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
z [ a / i ] = z
s b [ a / i ] = s (b [ a / i ]) 
nill [ a / i ] = nill
(h ∷l t) [ a / i ] = (h [ a / i ]) ∷l (t [ a / i ])
nilv [ a / i ] = nilv
(h ∷v t 𝕟 n) [ a / i ] = (h [ a / i ]) ∷v (t [ a / i ]) 𝕟 (n [ a / i ])
(elimnat b zb∶ zb sb∶ sb) [ a / i ] = 
    elimnat b [ a / i ] 
        zb∶ zb [ a / i ] 
        sb∶ (sb [ shiftindices a 1 0 / suc i ])
(eliml b nb∶ nb cb∶ cb) [ a / i ] = 
    eliml b [ a / i ] 
        nb∶ nb [ a / i ] 
        cb∶ (cb [ shiftindices a 2 0 / i + 2 ])
(elimv b nb∶ nb cb∶ cb) [ a / i ] = 
    elimv b [ a / i ]
        nb∶ nb [ a / i ]
        cb∶ (cb [ shiftindices a 3 0 / i + 3 ])

∋→ℕ : ∀ {Γ A} → Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)