module Proof.Semantics where

open import RunId 
open import Proof.StrongRel

private variable
    Γ : Context 
    a b A B : Term

erasedVal : Term 
erasedVal = {!   !}

data ContextRemap : Context  → Set where
    []ᵣ : ContextRemap []
    _,ᵣ_skip : ContextRemap Γ → (A : Type) → ContextRemap (Γ , A 𝕢 𝟘)  
    _,ᵣ_↦_ : ContextRemap Γ → (A : Type) → (B : Type) → ContextRemap (Γ , A 𝕢 ω)

data ContextMarkings : Set where 
    []ᵣ : ContextMarkings 
    _,ᵣ𝟘 : ContextMarkings → ContextMarkings  
    _,ᵣω : ContextMarkings → ContextMarkings

⟦_⟧t : Term → ContextMarkings → Term 
⟦ var x ⟧t rΓ = {!   !}
⟦ ƛ𝟘∶ A ♭ a ⟧t rΓ = ⟦ a ⟧t {!   !} 
⟦ ƛω∶ A ♭ a ⟧t rΓ = ƛω∶ ⟦ A ⟧t {!   !} ♭ ⟦ a ⟧t {!   !}
⟦ ƛr∶ A ♭ a ⟧t rΓ = ƛω∶ ⟦ A ⟧t {!   !} ♭ ⟦ a ⟧t {!   !}
⟦ f ·𝟘 a ⟧t rΓ = ⟦ f ⟧t {!   !}
⟦ f ·ω a ⟧t rΓ = ⟦ f ⟧t {!   !} ·ω ⟦ a ⟧t {!   !}
⟦ f ·ᵣ a ⟧t rΓ = ⟦ f ⟧t {!   !} ·ω ⟦ a ⟧t {!   !}
⟦ ⟨ a 𝕢 𝟘 , b 𝕢 𝟘 ⟩ ⟧t rΓ = erasedVal
⟦ ⟨ a 𝕢 𝟘 , b 𝕢 ω ⟩ ⟧t rΓ = ⟦ b ⟧t (rΓ ,ᵣ𝟘)
⟦ ⟨ a 𝕢 ω , b 𝕢 𝟘 ⟩ ⟧t rΓ = ⟦ a ⟧t rΓ
⟦ ⟨ a 𝕢 ω , b 𝕢 ω ⟩ ⟧t rΓ = ⟨ (⟦ a ⟧t rΓ 𝕢 ω) , (⟦ b ⟧t (rΓ ,ᵣω) 𝕢 ω) ⟩
⟦ inl< 𝟘 , _ > a ⟧t rΓ = erasedVal
⟦ inl< ω , 𝟘 > a ⟧t rΓ = ⟦ a ⟧t rΓ
⟦ inl< ω , ω > a ⟧t rΓ = inl< ω , ω > (⟦ a ⟧t rΓ)
⟦ inr< 𝟘 , _ > a ⟧t rΓ = erasedVal
⟦ inr< ω , 𝟘 > a ⟧t rΓ = ⟦ a ⟧t rΓ
⟦ inr< ω , ω > a ⟧t rΓ = inr< ω , ω > (⟦ a ⟧t rΓ)
⟦ z ⟧t rΓ = z
⟦ s a ⟧t rΓ = s (⟦ a ⟧t rΓ)
⟦ nill ⟧t rΓ = nill
⟦ a ∷l as ⟧t rΓ = ⟦ a ⟧t rΓ ∷l ⟦ as ⟧t rΓ
⟦ nilv𝟘 ⟧t rΓ = nill
⟦ nilvω ⟧t rΓ = nilvω
⟦ a ∷v as 𝕟𝟘 n ⟧t rΓ = ⟦ a ⟧t rΓ ∷l ⟦ as ⟧t rΓ
⟦ a ∷v as 𝕟ω n ⟧t rΓ = ⟦ a ⟧t rΓ ∷v ⟦ as ⟧t rΓ 𝕟ω ⟦ n ⟧t rΓ
⟦ rfl ⟧t rΓ = rfl
⟦ el×< 𝟘 , 𝟘 >[ A , B ] a P b ⟧t rΓ = erasedVal
⟦ el×< 𝟘 , ω >[ A , B ] a P b ⟧t rΓ = (ƛω∶ ⟦ B ⟧t (rΓ ,ᵣ𝟘) ♭ {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ el×< ω , 𝟘 >[ A , B ] a P b ⟧t rΓ = (ƛω∶ ⟦ A ⟧t rΓ ♭ {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ el×< ω , ω >[ A , B ] a P b ⟧t rΓ = el×< ω , ω >[ ⟦ A ⟧t {!   !} , ⟦ B ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !})
⟦ elᵣ×< 𝟘 , 𝟘 >[ A , B ] a P b ⟧t rΓ = erasedVal
⟦ elᵣ×< 𝟘 , ω >[ A , B ] a P b ⟧t rΓ = (ƛω∶ ⟦ B ⟧t (rΓ ,ᵣ𝟘) ♭ {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ elᵣ×< ω , 𝟘 >[ A , B ] a P b ⟧t rΓ = (ƛω∶ ⟦ A ⟧t rΓ ♭ {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ elᵣ×< ω , ω >[ A , B ] a P b ⟧t rΓ = el×< ω , ω >[ ⟦ A ⟧t {!   !} , ⟦ B ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !})
⟦ el＋< 𝟘 , 𝟘 >[ A , B ] a P b c ⟧t rΓ = erasedVal
⟦ el＋< 𝟘 , ω >[ A , B ] a P b c ⟧t rΓ = (ƛω∶ ⟦ B ⟧t {!   !} ♭ ⟦ c ⟧t {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ el＋< ω , 𝟘 >[ A , B ] a P b c ⟧t rΓ = (ƛω∶ ⟦ A ⟧t {!   !} ♭ ⟦ b ⟧t {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ el＋< ω , ω >[ A , B ] a P b c ⟧t rΓ = el＋< ω , ω >[ ⟦ A ⟧t {!   !} , ⟦ B ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elᵣ＋< 𝟘 , 𝟘 >[ A , B ] a P b c ⟧t rΓ = erasedVal
⟦ elᵣ＋< 𝟘 , ω >[ A , B ] a P b c ⟧t rΓ = (ƛω∶ ⟦ B ⟧t {!   !} ♭ ⟦ c ⟧t {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ elᵣ＋< ω , 𝟘 >[ A , B ] a P b c ⟧t rΓ = (ƛω∶ ⟦ A ⟧t {!   !} ♭ ⟦ b ⟧t {!   !}) ·ω ⟦ a ⟧t {!   !}
⟦ elᵣ＋< ω , ω >[ A , B ] a P b c ⟧t rΓ = el＋< ω , ω >[ ⟦ A ⟧t {!   !} , ⟦ B ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elNat a P b c ⟧t rΓ = elNat (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elᵣNat a P b c ⟧t rΓ = elNat (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elList[ A ] a P b c ⟧t rΓ = elList[ ⟦ A ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elᵣList[ A ] a P b c ⟧t rΓ = elList[ ⟦ A ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elVec[ A ]< 𝟘 > a P b c ⟧t rΓ = elList[ ⟦ A ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !} [ 3 / erasedVal ])
⟦ elVec[ A ]< ω > a P b c ⟧t rΓ = elVec[ ⟦ A ⟧t {!   !} ]< ω > (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ elᵣVec[ A ]< 𝟘 > a P b c ⟧t rΓ = elList[ ⟦ A ⟧t {!   !} ] (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !} [ 3 / erasedVal ])
⟦ elᵣVec[ A ]< ω > a P b c ⟧t rΓ = elVec[ ⟦ A ⟧t {!   !} ]< ω > (⟦ a ⟧t {!   !}) (⟦ P ⟧t {!   !}) (⟦ b ⟧t {!   !}) (⟦ c ⟧t {!   !})
⟦ subst< x > a P b ⟧t rΓ = {!   !}
⟦ Nat ⟧t rΓ = Nat
⟦ List A ⟧t rΓ = List (⟦ A ⟧t {!   !})
⟦ Vec𝟘 A n ⟧t rΓ = List (⟦ A ⟧t {!   !})
⟦ Vecω A n ⟧t rΓ = Vecω (⟦ A ⟧t {!   !}) (⟦ n ⟧t {!   !})
⟦ A 𝕢 𝟘 ⟶ B ⟧t rΓ = ⟦ B ⟧t {!   !} [ 0 / erasedVal ]
⟦ A 𝕢 ω ⟶ B ⟧t rΓ = (⟦ A ⟧t {!   !} 𝕢 ω) ⟶ ⟦ B ⟧t {!   !}
⟦ A ⟶r B ⟧t rΓ = (⟦ A ⟧t {!   !} 𝕢 ω) ⟶ ⟦ B ⟧t {!   !}
⟦ (A 𝕢 𝟘) × (B 𝕢 𝟘) ⟧t rΓ = erasedVal
⟦ (A 𝕢 𝟘) × (B 𝕢 ω) ⟧t rΓ = ⟦ B ⟧t {!   !} [ 0 / erasedVal ]
⟦ (A 𝕢 ω) × (B 𝕢 𝟘) ⟧t rΓ = ⟦ A ⟧t {!   !}
⟦ (A 𝕢 ω) × (B 𝕢 ω) ⟧t rΓ = (⟦ A ⟧t {!   !} 𝕢 ω) × (⟦ B ⟧t {!   !} 𝕢 ω)
⟦ (A 𝕢 𝟘) ＋ (B 𝕢 𝟘) ⟧t rΓ = erasedVal
⟦ (A 𝕢 𝟘) ＋ (B 𝕢 ω) ⟧t rΓ = ⟦ B ⟧t {!   !}
⟦ (A 𝕢 ω) ＋ (B 𝕢 𝟘) ⟧t rΓ = ⟦ A ⟧t {!   !}
⟦ (A 𝕢 ω) ＋ (B 𝕢 ω) ⟧t rΓ = (⟦ A ⟧t {!   !} 𝕢 ω) ＋ (⟦ B ⟧t {!   !} 𝕢 ω)
⟦ a ≃ b ⟧t rΓ = ⟦ a ⟧t {!   !} ≃ ⟦ b ⟧t {!   !}
⟦ Sett x ⟧t rΓ = Sett x

⟦_⟧C : Context → Context
⟦ [] ⟧C = []
⟦ Γ , A 𝕢 𝟘 ⟧C = ⟦ Γ ⟧C
⟦ Γ , A 𝕢 ω ⟧C = ⟦ Γ ⟧C , ⟦ A ⟧t {!   !} 𝕢 ω

_⊨_∶_ : Context → Term → Type → Set
Γ ⊨ a ∶ A = ⟦ Γ ⟧C ⊢ ⟦ a ⟧t {!   !} 𝕢 ω ∶ ⟦ A ⟧t {!   !}

LangCon : Type → Set
LangCon A = (a : Term) → Term

-- Gives an exhaustive set of substitutions for a context
FullSubst : Context → Set 
FullSubst Γ = (a : Term) → Term

-- Reduction relation
_⇓_ : Term → Term → Set

