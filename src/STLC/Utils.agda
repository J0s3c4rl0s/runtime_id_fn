module STLC.Utils where

open import STLC.Syntax

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (if_then_else_)

_↑_≥_ : Term → ℕ → ℕ → Term -- Only do this for free variables, lower and upper bound
_↑_≥_ (var x) i l = if l ≤ᵇ x then var (x + i) else var x 
_↑_≥_ (ƛ t₁) i l = ƛ (_↑_≥_ t₁ i (suc l))
_↑_≥_ (t · t₁) i l = _↑_≥_ t i l · _↑_≥_ t₁ i l
_↑_≥_ z i l = z
_↑_≥_ (s t) i l = s (_↑_≥_ t i l) 
_↑_≥_ nill i l = nill
_↑_≥_ (t ∷l t₁) i l = _↑_≥_ t i l ∷l _↑_≥_ t₁ i l
_↑_≥_ nilv i l = nilv
_↑_≥_ (t ∷v t₁ 𝕟 n) i l = _↑_≥_ t i l ∷v _↑_≥_ t₁ i l 𝕟 _↑_≥_ n i l
_↑_≥_ (elimnat t zb∶ t₂ sb∶ t₃) i l = 
    elimnat_zb∶_sb∶_ (_↑_≥_ t i l) 
        (_↑_≥_ t₂ i l) 
        (_↑_≥_ t₃ i (l + 1))
_↑_≥_ (eliml t nb∶ t₃ cb∶ t₄) i l = 
    eliml_nb∶_cb∶_ (_↑_≥_ t i l) 
        (_↑_≥_ t₃ i l) 
        (_↑_≥_ t₄ i (l + 2))
_↑_≥_ (elimv x nb∶ nb cb∶ cb) i l = 
    elimv _↑_≥_ x i l 
        nb∶ _↑_≥_ nb i l
        cb∶ _↑_≥_ cb i (l + 3)

-- Consider parallel subtitutions to deal with free variable capture

-- Could reflection make this more efficient?
_[_/_]  : Term → ℕ → Term → Term
var 0 [ 0 / a ] = a
var b [ i / a ] = var b 
(ƛ b) [ i / a ] = ƛ (b [ suc i / _↑_≥_ a 1 0 ])
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
        sb∶ (sb [ suc i / _↑_≥_ a 1 0 ])
(eliml b nb∶ nb cb∶ cb) [ i / a ] = 
    eliml b [ i / a ] 
        nb∶ nb [ i / a ] 
        cb∶ (cb [ i + 2 / _↑_≥_ a 2 0 ])
(elimv b nb∶ nb cb∶ cb) [ i / a ] = 
    elimv b [ i / a ]
        nb∶ nb [ i / a ]
        cb∶ (cb [ i + 3 / _↑_≥_ a 3 0 ])

∋→ℕ : ∀ {Γ A} → Γ ∋ A → ℕ 
∋→ℕ Z = 0
∋→ℕ (S i) = suc (∋→ℕ i)