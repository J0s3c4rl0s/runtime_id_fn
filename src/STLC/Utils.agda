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
_[_/_]  : Term → ℕ → Term → Term
var 0 [ 0 / a ] = a
var b [ i / a ] = var b 
(ƛ b) [ i / a ] = ƛ (b [ suc i / shiftindices a 1 0 ])
(b · c) [ i / a ] = (b [ i / a ]) · (c [ i / a ])
z [ i / a ] = z
s b [ i / a ] = s (b [ i / a ]) 
nill [ i / a ] = nill
(h ∷l t) [ i / a ] = (h [ i / a ]) ∷l (t [ i / a ])
nilv [ i / a ] = nilv
(h ∷v t 𝕟 n) [ i / a ] = (h [ i / a ]) ∷v (t [ i / a ]) 𝕟 (n [ i / a ])
(elimnat b zb∶ zb sb∶ sb) [ i / a ] = 
    elimnat b [ i / a ] 
        zb∶ zb [ i / a ] 
        sb∶ (sb [ suc i / shiftindices a 1 0 ])
(eliml b nb∶ nb cb∶ cb) [ i / a ] = 
    eliml b [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 2 / shiftindices a 2 0 ])
(elimv b nb∶ nb cb∶ cb) [ i / a ] = 
    elimv b [ i / a ]
        nb∶ nb [ i / a ]
        cb∶ (cb [ i + 3 / shiftindices a 3 0 ])

∋→ℕ : ∀ {Γ A} → Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)