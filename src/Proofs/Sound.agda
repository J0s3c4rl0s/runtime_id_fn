module Proofs.Sound where

open import RunId  
-- open import RunIdComp
-- open import Proofs.Relations

private variable
    A B C D : Type 
    a b c d : Term 
    Γ : PreContext 
    cΓ : Context Γ

open import Relation.Nullary

nontriv : 
    s z ~ᵣ a →
    ¬ (z ~ᵣ a)  
nontriv {a} (~ᵣsym sz~) z~ = {!   !}
nontriv {a} (~ᵣtrans sz~ sz~₁) z~ = nontriv sz~ (~ᵣtrans z~ (~ᵣsym sz~₁))
nontriv {s a} ~ᵣrefl z~ = {!   !}
nontriv {s z} (~ᵣs ~ᵣrefl) (~ᵣsym z~) = {!   !}
nontriv {s z} (~ᵣs ~ᵣrefl) (~ᵣtrans z~ z~₁) = nontriv (~ᵣsym z~₁) z~
nontriv {s a} (~ᵣs (~ᵣsym sz~)) (~ᵣsym z~) = {!   !}
nontriv {s a} (~ᵣs (~ᵣsym sz~)) (~ᵣtrans z~ z~₁) = {!   !}
nontriv {s a} (~ᵣs (~ᵣtrans sz~ sz~₁)) z~ = {!   !}  


module Denot where
    ⟦_⟧ : Term → Set
    -- what do with var?
    ⟦ var x ⟧ = {!   !}
    ⟦ ƛ∶ A 𝕢 σ ♭ a ⟧ = {!   !}
    ⟦ ƛr∶ x ♭ a ⟧ = {!   !}
    ⟦ a · a₁ 𝕢 x ⟧ = {!   !}
    ⟦ a ·ᵣ a₁ ⟧ = {!   !}
    ⟦ z ⟧ = {!   !}
    ⟦ s a ⟧ = {!   !}
    ⟦ nill ⟧ = {!   !}
    ⟦ a ∷l a₁ ⟧ = {!   !}
    ⟦ nilv𝕢 x ⟧ = {!   !}
    ⟦ a ∷v a₁ 𝕟 a₂ 𝕢 x ⟧ = {!   !}
    ⟦ elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃ ⟧ = {!   !}
    ⟦ eliml a ty∶ innerty P∶ a₁ nb∶ a₂ cb∶ a₃ ⟧ = {!   !}
    ⟦ elimv x ty∶ innerty P∶ a nb∶ a₁ cb∶ a₂ ⟧ = {!   !}
    ⟦ Nat ⟧ = {!   !}
    ⟦ List x ⟧ = {!   !}
    ⟦ Vec x x₁ ⟧ = {!   !}
    ⟦ ∶ x ⟶ x₁ ⟧ = {!   !}
    ⟦ r∶ x ⟶ x₁ ⟧ = {!   !}
    ⟦ Sett x ⟧ = {!   !}

module CtxEquiv where

    -- Maybe will just produce Nat terms 
    --  indexed by Typing context and type of hole
    -- Maybe keep track of target type
    TermCtx : Context Γ → Type → Set

    -- Maybe context can take two types A ~r B 
    -- But ~r would be baked into it...
    -- Would perhaps use ~r to select which eliminator to use....
    TermCtx2 : Context Γ → Type → Set


    -- Plugs hole with a term, check type?
    _[_] : 
        TermCtx cΓ A →
        -- index on well typed terms?
        Term → 
        Term

    _⊢_＝ctx_∶_,_ : Context Γ → Term → Term → Type → Type → Set
    cΓ ⊢ a ＝ctx b ∶ A , B = 
        (CtxA : TermCtx cΓ A) →
        (CtxB : TermCtx cΓ B) →
        {!   !} →
        {!   !}

    sound : 
        cΓ ⊢ a 𝕢 ω ∶ A →
        cΓ ⊢ b 𝕢 ω ∶ B →
        A ~ᵣ B →
        a ~ᵣ b → 
        {!   !}

module Erasure where 
    -- Erase terms? 
    -- Isnt this just... compiler?
    -- Wont this just... sanctify the previous relation?
    -- Could be a relation to sanctify erasing terms, could take well typed terms only
    ⟦_⟧ : Term → Term
    ⟦ nilv𝟘 ⟧ = nill
    ⟦ a ∷v as 𝕟𝟘 n ⟧ = a ∷l as
    ⟦ var x ⟧ = {!   !}
    ⟦ ƛ∶ A 𝕢 σ ♭ a ⟧ = {!   !}
    ⟦ ƛr∶ x ♭ a ⟧ = {!   !}
    ⟦ a · a₁ 𝕢 x ⟧ = {!   !}
    ⟦ a ·ᵣ a₁ ⟧ = {!   !}
    ⟦ z ⟧ = {!   !}
    ⟦ s a ⟧ = {!   !}
    ⟦ nill ⟧ = {!   !}
    ⟦ a ∷l a₁ ⟧ = {!   !}
    ⟦ nilv𝕢 x ⟧ = {!   !}
    ⟦ a ∷v a₁ 𝕟 a₂ 𝕢 x ⟧ = {!   !}
    ⟦ elimnat a P∶ a₁ zb∶ a₂ sb∶ a₃ ⟧ = {!   !}
    ⟦ eliml a ty∶ innerty P∶ a₁ nb∶ a₂ cb∶ a₃ ⟧ = {!   !}
    ⟦ elimv x ty∶ innerty P∶ a nb∶ a₁ cb∶ a₂ ⟧ = {!   !}
    ⟦ Nat ⟧ = {!   !}
    ⟦ List x ⟧ = {!   !}
    ⟦ Vec x x₁ ⟧ = {!   !}
    ⟦ ∶ x ⟶ x₁ ⟧ = {!   !}
    ⟦ r∶ x ⟶ x₁ ⟧ = {!   !}
    ⟦ Sett x ⟧ = {!   !}  

