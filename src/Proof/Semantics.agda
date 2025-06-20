module Proof.Semantics where

open import Data.Nat

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

updateIndex : ℕ → ContextMarkings → ℕ
-- default value for false entries?
updateIndex i []ᵣ = {!   !}
-- erased var
updateIndex zero (rΓ ,ᵣ𝟘) = {!   !}
updateIndex (suc i) (rΓ ,ᵣ𝟘) = updateIndex i rΓ
updateIndex zero (rΓ ,ᵣω) = zero
updateIndex (suc i) (rΓ ,ᵣω) = suc (updateIndex i rΓ)

⟦_⟧t : Term → ContextMarkings → Term 
⟦ var x ⟧t rΓ = var (updateIndex x rΓ)
⟦ ƛ𝟘∶ A ♭ a ⟧t rΓ = ⟦ a ⟧t (rΓ ,ᵣ𝟘) 
⟦ ƛω∶ A ♭ a ⟧t rΓ = ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ a ⟧t (rΓ ,ᵣω)
⟦ ƛr∶ A ♭ a ⟧t rΓ = ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ a ⟧t (rΓ ,ᵣω)
⟦ f ·𝟘 a ⟧t rΓ = ⟦ f ⟧t rΓ
⟦ f ·ω a ⟧t rΓ = ⟦ f ⟧t rΓ ·ω ⟦ a ⟧t rΓ
⟦ f ·ᵣ a ⟧t rΓ = ⟦ f ⟧t rΓ ·ω ⟦ a ⟧t rΓ
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
---- Elims
-- Product 
⟦ el×< 𝟘 , 𝟘 >[ A , B ] a P b ⟧t rΓ = erasedVal
⟦ el×< 𝟘 , ω >[ A , B ] a P b ⟧t rΓ = 
    (ƛω∶ ⟦ B ⟧t (rΓ ,ᵣ𝟘) ♭ ⟦ b ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) ·ω ⟦ a ⟧t rΓ
⟦ el×< ω , 𝟘 >[ A , B ] a P b ⟧t rΓ = 
    (ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ b ⟧t (rΓ ,ᵣω ,ᵣ𝟘)) ·ω ⟦ a ⟧t rΓ
⟦ el×< ω , ω >[ A , B ] a P b ⟧t rΓ = 
    el×< ω , ω >[ ⟦ A ⟧t rΓ , ⟦ B ⟧t (rΓ ,ᵣω) ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t (rΓ ,ᵣω ,ᵣω))
⟦ elᵣ×< 𝟘 , 𝟘 >[ A , B ] a P b ⟧t rΓ = erasedVal
⟦ elᵣ×< 𝟘 , ω >[ A , B ] a P b ⟧t rΓ = 
    (ƛω∶ ⟦ B ⟧t (rΓ ,ᵣ𝟘) ♭ ⟦ b ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) ·ω ⟦ a ⟧t rΓ
⟦ elᵣ×< ω , 𝟘 >[ A , B ] a P b ⟧t rΓ = 
    (ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ b ⟧t (rΓ ,ᵣω ,ᵣ𝟘)) ·ω ⟦ a ⟧t rΓ
⟦ elᵣ×< ω , ω >[ A , B ] a P b ⟧t rΓ = 
    el×< ω , ω >[ ⟦ A ⟧t rΓ , ⟦ B ⟧t (rΓ ,ᵣω) ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t (rΓ ,ᵣω ,ᵣω))
-- Sums
⟦ el＋< 𝟘 , 𝟘 >[ A , B ] a P b c ⟧t rΓ = 
    erasedVal
⟦ el＋< 𝟘 , ω >[ A , B ] a P b c ⟧t rΓ = 
    (ƛω∶ ⟦ B ⟧t rΓ ♭ ⟦ c ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) ·ω ⟦ a ⟧t rΓ
⟦ el＋< ω , 𝟘 >[ A , B ] a P b c ⟧t rΓ = 
    (ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ b ⟧t (rΓ ,ᵣω ,ᵣ𝟘)) ·ω ⟦ a ⟧t rΓ
⟦ el＋< ω , ω >[ A , B ] a P b c ⟧t rΓ = 
    el＋< ω , ω >[ ⟦ A ⟧t rΓ , ⟦ B ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω ,ᵣω)) (⟦ b ⟧t (rΓ ,ᵣω)) (⟦ c ⟧t (rΓ ,ᵣω))
⟦ elᵣ＋< 𝟘 , 𝟘 >[ A , B ] a P b c ⟧t rΓ =  
    erasedVal
⟦ elᵣ＋< 𝟘 , ω >[ A , B ] a P b c ⟧t rΓ = 
    (ƛω∶ ⟦ B ⟧t rΓ ♭ ⟦ c ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) ·ω ⟦ a ⟧t rΓ
⟦ elᵣ＋< ω , 𝟘 >[ A , B ] a P b c ⟧t rΓ = 
    (ƛω∶ ⟦ A ⟧t rΓ ♭ ⟦ b ⟧t (rΓ ,ᵣω ,ᵣ𝟘)) ·ω ⟦ a ⟧t rΓ
⟦ elᵣ＋< ω , ω >[ A , B ] a P b c ⟧t rΓ = 
    el＋< ω , ω >[ ⟦ A ⟧t rΓ , ⟦ B ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω ,ᵣω)) (⟦ b ⟧t (rΓ ,ᵣω)) (⟦ c ⟧t (rΓ ,ᵣω))
-- Nat
⟦ elNat a P b c ⟧t rΓ = 
    elNat (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω))
⟦ elᵣNat a P b c ⟧t rΓ = 
    elNat (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω))
-- List
⟦ elList[ A ] a P b c ⟧t rΓ = 
    elList[ ⟦ A ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω ,ᵣω))
⟦ elᵣList[ A ] a P b c ⟧t rΓ = 
    elList[ ⟦ A ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω ,ᵣω))
-- Vec
⟦ elVec[ A ]< 𝟘 > a P b c ⟧t rΓ = 
    elList[ ⟦ A ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣ𝟘 ,ᵣω ,ᵣω ,ᵣω))
⟦ elVec[ A ]< ω > a P b c ⟧t rΓ = 
    elVec[ ⟦ A ⟧t rΓ ]< ω > (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω ,ᵣω ,ᵣω))
⟦ elᵣVec[ A ]< 𝟘 > a P b c ⟧t rΓ = 
    elList[ ⟦ A ⟧t rΓ ] (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣ𝟘 ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣ𝟘 ,ᵣω ,ᵣω ,ᵣω))
⟦ elᵣVec[ A ]< ω > a P b c ⟧t rΓ = 
    elVec[ ⟦ A ⟧t rΓ ]< ω > (⟦ a ⟧t rΓ) (⟦ P ⟧t (rΓ ,ᵣω ,ᵣω)) (⟦ b ⟧t rΓ) (⟦ c ⟧t (rΓ ,ᵣω ,ᵣω ,ᵣω ,ᵣω))
-- propeq
⟦ subst< x > a P b ⟧t rΓ = {!   !}
⟦ Nat ⟧t rΓ = Nat
⟦ List A ⟧t rΓ = List (⟦ A ⟧t rΓ)
⟦ Vec𝟘 A n ⟧t rΓ = List (⟦ A ⟧t rΓ)
⟦ Vecω A n ⟧t rΓ = Vecω (⟦ A ⟧t rΓ) (⟦ n ⟧t rΓ)
⟦ A 𝕢 𝟘 ⟶ B ⟧t rΓ = ⟦ B ⟧t (rΓ ,ᵣ𝟘) 
⟦ A 𝕢 ω ⟶ B ⟧t rΓ = (⟦ A ⟧t rΓ 𝕢 ω) ⟶ ⟦ B ⟧t (rΓ ,ᵣω)
⟦ A ⟶r B ⟧t rΓ = (⟦ A ⟧t rΓ 𝕢 ω) ⟶ ⟦ B ⟧t (rΓ ,ᵣω)
⟦ (A 𝕢 𝟘) × (B 𝕢 𝟘) ⟧t rΓ = erasedVal
⟦ (A 𝕢 𝟘) × (B 𝕢 ω) ⟧t rΓ = ⟦ B ⟧t (rΓ ,ᵣ𝟘) 
⟦ (A 𝕢 ω) × (B 𝕢 𝟘) ⟧t rΓ = ⟦ A ⟧t rΓ
⟦ (A 𝕢 ω) × (B 𝕢 ω) ⟧t rΓ = (⟦ A ⟧t rΓ 𝕢 ω) × (⟦ B ⟧t (rΓ ,ᵣω) 𝕢 ω)
⟦ (A 𝕢 𝟘) ＋ (B 𝕢 𝟘) ⟧t rΓ = erasedVal
⟦ (A 𝕢 𝟘) ＋ (B 𝕢 ω) ⟧t rΓ = ⟦ B ⟧t rΓ
⟦ (A 𝕢 ω) ＋ (B 𝕢 𝟘) ⟧t rΓ = ⟦ A ⟧t rΓ
⟦ (A 𝕢 ω) ＋ (B 𝕢 ω) ⟧t rΓ = (⟦ A ⟧t rΓ 𝕢 ω) ＋ (⟦ B ⟧t rΓ 𝕢 ω)
⟦ a ≃ b ⟧t rΓ = ⟦ a ⟧t rΓ ≃ ⟦ b ⟧t rΓ
⟦ Sett x ⟧t rΓ = Sett x

toMarkings : Context → ContextMarkings 
toMarkings [] = []ᵣ
toMarkings (Γ , A 𝕢 𝟘) = toMarkings Γ ,ᵣ𝟘
toMarkings (Γ , A 𝕢 ω) = toMarkings Γ ,ᵣω

⟦_⟧C : Context → Context
⟦ [] ⟧C = []
⟦ Γ , A 𝕢 𝟘 ⟧C = ⟦ Γ ⟧C
⟦ Γ , A 𝕢 ω ⟧C = ⟦ Γ ⟧C , ⟦ A ⟧t (toMarkings Γ) 𝕢 ω

CanType : Set
_↓ : Term → CanType

LangCon : CanType → Set
LangCon A = (a : Term) → Term

-- Gives an exhaustive set of substitutions for a context
FullSubst : Context → Set 
FullSubst Γ = (a : Term) → Term

-- Reduction relation
_⇓_ : Term → Term → Set

