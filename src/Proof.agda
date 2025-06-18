module Proof where


open import RunId
-- open import Proof.Semantics

private variable
    Γ : Context
    a b c d A B C D : Term

-- Programm g context, indexed by types when plugged produces term thats only typed as a Nat
LangCon : Type → Set
LangCon A = (a : Term) → Term

data _⊢_~_∶_~_ : Context → Term → Term → Type → Type → Set where

data ContextRemap : Context  → Set where
    []ᵣ : ContextRemap []
    _,ᵣ_skip : ContextRemap Γ → (A : Type) → ContextRemap (Γ , A 𝕢 𝟘)  
    _,ᵣ_↦_ : ContextRemap Γ → (A : Type) → (B : Type) → ContextRemap (Γ , A 𝕢 ω)

⟦_⟧t : Term → ContextRemap Γ → Term
⟦_⟧C : ContextRemap Γ → Context
toRemap : (Γ : Context) → ContextRemap Γ


-- Gives an exhaustive set of substitutions for a context
FullSubst : Context → Set 
FullSubst Γ = (a : Term) → Term

-- Reduction relation
_⇓_ : Term → Term → Set

open import Relation.Binary.PropositionalEquality

proof : ∀ {vₐ vb} →
    Γ ⊢ a ~ b ∶ A ~ B →
    let 
        rΓ = toRemap Γ 
        in
    ∀ {C : LangCon (⟦ A ⟧t rΓ)} {δ : FullSubst Γ} → 
    -- Their erasure + optimization
    C (δ (⟦ a ⟧t rΓ)) ⇓ vₐ → 
    C (δ (⟦ b ⟧t rΓ)) ⇓ vb → 
    -- Reduce to the same term.
    vₐ ≡ vb 