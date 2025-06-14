module RunId where

-- Re-export syntax and typing rules
open import RunId.Syntax public
open import RunId.TypeRules public
open import RunId.Utils public

open import Relation.Binary.PropositionalEquality

private variable 
    Γ : Context
    a : Term 
    A : Type
    
data ContextRemap : Context  → Set where
    []ᵣ : ContextRemap []
    _,ᵣ_skip : ContextRemap Γ → (A : Type) → ContextRemap (Γ , A 𝕢 𝟘)  
    _,ᵣ_↦_ : ContextRemap Γ → (A : Type) → (B : Type) → ContextRemap (Γ , A 𝕢 ω)

-- Programming context, indexed by types when plugged produces term thats only typed as a Nat
LangCon : Type → Set
LangCon A = (a : Term) → Term

-- Performs erasure on source terms
⟦_⟧ₑ : Type → Type
⟦_⟧ₑ = {!   !}

-- Does runid optimization on source terms
⟦_⟧ₒ : Type → Type
⟦_⟧ₒ = {!   !}

-- Gives an exhaustive set of substitutions for a context
FullSubst : Context → Set 
FullSubst Γ = (a : Term) → Term

-- Reduction relation
_⇓_ : Term → Term → Set

lemma : ∀ {a b A vₐ vb} →
    a ~ᵣ b →
    let 
        aₒ = ⟦ a ⟧ₒ  
        bₒ = ⟦ b ⟧ₒ  
        in
    ∀ {C : LangCon ⟦ A ⟧ₑ} {δ : FullSubst Γ} → 
    -- Their erasure + optimization
    C (δ aₒ) ⇓ vₐ → 
    C (δ bₒ) ⇓ vb → 
    -- Reduce to the same term.
    vₐ ≡ vb

proof : ∀ {vₑ vₒ} →
    -- If a term is well typed
    Γ ⊢ a 𝕢 ω ∶ A → 
    let 
        aₑ = ⟦ a ⟧ₑ 
        aₒ = ⟦ aₑ ⟧ₒ 
        in
    -- Then for any valid program context and substitution of terms
    ∀ {C : LangCon ⟦ a ⟧ₑ} {δ : FullSubst Γ} → 
    -- Its erased optimization
    C (δ aₑ) ⇓ vₑ → 
    -- And its erased + runid optimization
    C (δ aₒ) ⇓ vₒ → 
    -- Reduce to the same term.
    vₒ ≡ vₑ
-- proof (⊢var i x eq) ↓e ↓o = {!   !}
-- proof (⊢lam ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof (⊢rlam x ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof (⊢app ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof (⊢appᵣ ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof ⊢z ↓e ↓o = {!   !}
-- proof (⊢s ⊢a) ↓e ↓o = {!   !}
-- proof (⊢natel ⊢a ⊢a₁ ⊢a₂ ⊢a₃) ↓e ↓o = {!   !}
-- proof (⊢natelᵣ ⊢a ⊢a₁ x ⊢a₂ x₁ ⊢a₃ x₂) ↓e ↓o = {!   !}
-- proof ⊢nill ↓e ↓o = {!   !}
-- proof (⊢∷l ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof (⊢listel ⊢a ⊢a₁ ⊢a₂ ⊢a₃) ↓e ↓o = {!   !}
-- proof (⊢listelᵣ Γ Γ₁ Γ₂ ⊢a ⊢a₁ x ⊢a₂ x₁ ⊢a₃ x₂) ↓e ↓o = {!   !}
-- proof (⊢nilv ⊢a) ↓e ↓o = {!   !}
-- proof (⊢∷v ⊢a ⊢a₁ ⊢a₂) ↓e ↓o = {!   !}
-- proof (⊢vecel ⊢a ⊢a₁ ⊢a₂ ⊢a₃) ↓e ↓o = {!   !}
-- proof (⊢vecelᵣ ⊢a ⊢a₁ x ⊢a₂ x₁ ⊢a₃ x₂) ↓e ↓o = {!   !}
-- proof ⊢rfl ↓e ↓o = {!   !}
-- proof (⊢subst ⊢a ⊢a₁) ↓e ↓o = {!   !}
-- proof (⊢conv ⊢a x) ↓e ↓o = {!   !}
-- eraseTerm : ContextRemap Γ → Term → Term 
-- eraseTerm rΓ (var x) = {!   !}
-- eraseTerm rΓ (ƛ𝟘∶ A ♭ a) = eraseTerm (rΓ ,ᵣ A skip) a
-- eraseTerm rΓ (ƛω∶ A ♭ a) = ƛω∶ (eraseTerm rΓ A) ♭ eraseTerm (rΓ ,ᵣ A ↦ (eraseTerm rΓ A)) a
-- -- simplify a to var 0 or keep erasing into body?
-- eraseTerm rΓ (ƛr∶ A ♭ a) = ƛr∶ eraseTerm rΓ A ♭ {!   !}
-- eraseTerm rΓ (f ·𝟘 a) = eraseTerm rΓ f
-- eraseTerm rΓ (f ·ω a) = (eraseTerm rΓ f) ·ω (eraseTerm rΓ a)
-- eraseTerm rΓ (f ·ᵣ a) = eraseTerm rΓ a
-- -- bogus term?
-- eraseTerm rΓ ⟨ a 𝕢 𝟘 , b 𝕢 𝟘 ⟩ = {!   !}
-- eraseTerm rΓ ⟨ a 𝕢 𝟘 , b 𝕢 ω ⟩ = eraseTerm rΓ b
-- eraseTerm rΓ ⟨ a 𝕢 ω , b 𝕢 𝟘 ⟩ = eraseTerm rΓ a
-- eraseTerm rΓ ⟨ a 𝕢 ω , b 𝕢 ω ⟩ = ⟨ ((eraseTerm rΓ a) 𝕢 ω) , ((eraseTerm rΓ b) 𝕢 ω) ⟩
-- eraseTerm rΓ (inl< 𝟘 , x₁ > a) = {!   !}
-- eraseTerm rΓ (inl< ω , 𝟘 > a) = eraseTerm rΓ a
-- eraseTerm rΓ (inl< ω , ω > a) = inl< ω , ω > (eraseTerm rΓ a)
-- eraseTerm rΓ (inr< _ , 𝟘 > b) = {!   !}
-- eraseTerm rΓ (inr< 𝟘 , ω > b) = eraseTerm rΓ b
-- eraseTerm rΓ (inr< ω , ω > b) = inr< ω , ω > (eraseTerm rΓ b)
-- eraseTerm rΓ z = z
-- eraseTerm rΓ (s a) = s (eraseTerm rΓ a)
-- eraseTerm rΓ nill = nill
-- eraseTerm rΓ (h ∷l t) = (eraseTerm rΓ h) ∷l (eraseTerm rΓ t)
-- eraseTerm rΓ nilv𝟘 = nill
-- eraseTerm rΓ nilvω = nilvω
-- eraseTerm rΓ (h ∷v t 𝕟𝟘 _) = (eraseTerm rΓ h) ∷l (eraseTerm rΓ t)
-- eraseTerm rΓ (h ∷v t 𝕟ω n) = (eraseTerm rΓ h) ∷v (eraseTerm rΓ t) 𝕟ω (eraseTerm rΓ n)
-- eraseTerm rΓ rfl = rfl
-- eraseTerm rΓ (el×< x , x₁ >[ x₂ , x₃ ] a a₁ a₂) = {!   !}
-- eraseTerm rΓ (el×ᵣ< x , x₁ >[ x₂ , x₃ ] a a₁ a₂) = eraseTerm rΓ a
-- eraseTerm rΓ (el＋< x , x₁ >[ x₂ , x₃ ] a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (el＋ᵣ< x , x₁ >[ x₂ , x₃ ] a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (elNat a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (elNatᵣ a P bz bs) = eraseTerm rΓ a
-- eraseTerm rΓ (elList[ innerty ] a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (elListᵣ[ innerty ] a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (elVec[ innerty ]< x > a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (elVecᵣ[ innerty ]< x > a a₁ a₂ a₃) = {!   !}
-- eraseTerm rΓ (subst a by x) = {!   !}
-- eraseTerm rΓ Nat = {!   !}
-- eraseTerm rΓ (List x) = {!   !}
-- eraseTerm rΓ (Vec x x₁) = {!   !}
-- eraseTerm rΓ (∶ x ⟶ x₁) = {!   !}
-- eraseTerm rΓ (r∶ x ⟶ x₁) = {!   !}
-- eraseTerm rΓ (∶ x ×∶ x₁) = {!   !}
-- eraseTerm rΓ (x ＋ x₁) = {!   !}
-- eraseTerm rΓ (a ≃ a₁) = {!   !}
-- eraseTerm rΓ (Sett x) = {!   !}


-- proof : ∀ {a b A rΓ} → 
--     a ~ᵣ b → 
--     Σ[ C ∈ LangCon A ] C (eraseTerm rΓ a) ≡ C (eraseTerm rΓ b)
