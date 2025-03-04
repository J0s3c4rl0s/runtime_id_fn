module ListCalc.Calc.Utils where

open import ListCalc.Calc.Syntax

open import Data.Nat using (ℕ; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

shiftindices : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
shiftindices (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
shiftindices (ƛ∶ t ♭ t₁) i l = ƛ∶ shiftindices t i l ♭ shiftindices t₁ i (suc l)
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
shiftindices (∶ t ⟶ t₁) i l = ∶ shiftindices t i l ⟶ shiftindices t₁ i (suc l)
shiftindices Sett i l = Sett -- Consider parallel subtitutions to deal with free variable capture


-- Could reflection make this more efficient?
_[_/_]  : Term → Term → ℕ → Term
var 0 [ a / 0 ] = a
var b [ a / i ] = var b 
(ƛ∶ bₜ ♭ b) [ a / i ] = ƛ∶ bₜ [ a / i ] ♭ (b [ shiftindices a 1 0 / suc i ])
(b · c) [ a / i ] = (b [ a / i ]) · (c [ a / i ])
(∶ b ⟶ c) [ a / i ] = ∶ bs ⟶ (c [ shiftindices a 1 0 / suc i ]) 
    where 
        bs = b [ a / i ]
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

∋→ℕ : ∀ {Γ A} → Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)