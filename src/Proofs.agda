module Proofs where

import RunId as S
import STLC as T
open import RunIdComp

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

open import Data.Nat
open import Data.List
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)
open import Data.Bool using (if_then_else_; Bool)
open import Data.Unit
open import Data.Empty


private variable
    sΓ sΔ : S.PreContext
    scΓ : S.Context sΓ
    scΔ : S.Context sΔ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    i l k : ℕ

    rΓ : ContextRemap scΓ

    tA tB : T.Type
    ta tb : T.Term

lemmaIgnorePaths : ∀ {res} →
    (cond : Bool) → 
    (thenB : _ ) →
    (elseB : _)
    {teq : compileType thenB ≡ res} → 
    {eeq : compileType elseB ≡ res} →  
    compileType (if cond then thenB else elseB) ≡ res
lemmaIgnorePaths Bool.false thenB elseB {eeq = eeq} = eeq
lemmaIgnorePaths Bool.true thenB elseB {teq} = teq

{-
conver∋→Pre : {scΓ : S.Context sΓ} → scΓ S.∋ sA 𝕢 σ → sΓ S.∋Pre sA
conver∋→Pre S.Z = S.Z
conver∋→Pre (S.S p) = S.S (conver∋→Pre p)

dropTypePre : (sΓ : S.PreContext) → sΓ S.∋Pre sA → S.PreContext
dropTypePre (sΓ S., sA) S.Z = sΓ
dropTypePre (sΓ S., sA) (S.S p) = dropTypePre sΓ p S., {!   !}

dropType : (scΓ : S.Context sΓ) → (p : scΓ S.∋ sA 𝕢 σ) → S.Context (dropTypePre sΓ (conver∋→Pre p))
dropType (scΓ S., _) S.Z = scΓ
dropType (scΓ S., sA 𝕢 σ) (S.S p) = dropType scΓ p S., {!   !} 𝕢 σ

-- do I need arbitrary drops and not just skips?
dropSkip :  ContextRemap scΓ → (p : scΓ S.∋ sA 𝕢 𝟘) → ContextRemap (dropType scΓ p)
dropSkip (rΓ ,ᵣ sA skip) S.Z = rΓ
dropSkip (rΓ ,ᵣ sA skip) (S.S p) = {!   !} ,ᵣ {!  S.shiftindices ? ? ?  !} skip
dropSkip (rΓ ,ᵣ sA ↦ tA) (S.S p) = {!   !}
-}

conLen : S.PreContext → ℕ
conLen S.[] = 0
conLen (sΓ S., x) = suc (conLen sΓ) 

insertTypePre : (sΓ : S.PreContext) → (i : ℕ) → (p : i ≤ conLen sΓ) → S.Type → S.PreContext 
insertTypePre sΓ zero p sA = sΓ S., sA
insertTypePre (sΓ S., sB) (suc i) (s≤s p) sA = insertTypePre sΓ i p sA S., S.shiftindices sB 1 i

-- use Annotation instead?
insertType : S.Context sΓ → (i : ℕ) → (p : i ≤ conLen sΓ)  → (sA : S.Type) → S.Quantity → S.Context (insertTypePre sΓ i p sA)
insertType scΓ zero z≤n sA σ = scΓ S., sA 𝕢 σ
insertType (scΓ S., sB 𝕢 ρ) (suc i) (s≤s p) sA σ = insertType scΓ i p sA σ S., S.shiftindices sB 1 i 𝕢 ρ

insertSkip : {scΓ : S.Context sΓ} → ContextRemap scΓ → (i : ℕ) → (p : i ≤ conLen sΓ)  → (sA : S.Type) → ContextRemap (insertType scΓ i p sA 𝟘)
insertSkip rΓ zero z≤n sA = rΓ ,ᵣ sA skip
insertSkip (rΓ ,ᵣ sB skip) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i skip
insertSkip (rΓ ,ᵣ sB ↦ tB) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i ↦ tB

compTyIgnShift : ∀ {i l} → (sA : _) → compileType sA ≡ compileType (S.shiftindices sA i l)

lemmaRemap : {p : _} {rΓ : ContextRemap scΓ} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (insertType scΓ i p sA 𝟘) ≡ just (insertSkip rΓ i p sA) 
lemmaRemap {scΓ = scΓ} {i = zero} {p = z≤n} eqrΓ rewrite eqrΓ = refl
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ} eqrΓ = {!   !}

tmp : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) →
    (i≤k : Dec (i ≤ k)) →
    compileTerm (insertType scΓ i p sB 𝟘)
      (if ⌊ i≤k ⌋  then S.var (k + 1) else S.var k)
      ≡
      (compileTerm scΓ (S.var k) ) 
tmp scΓ i p (Bool.false because proof₁) = {!   !}
tmp scΓ i p (Bool.true because proof₁) = {!   !}

compTeIgnSh :  
    (sa : S.Term) → 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) → 
    compileTerm (insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) ≡ compileTerm scΓ sa
compTeIgnSh (S.var x) scΓ i p = {!   !}
compTeIgnSh (S.ƛ∶ A 𝕢 𝟘 ♭ sa) scΓ i p = compTeIgnSh sa (scΓ S., A 𝕢 𝟘) (suc i) (s≤s p)
compTeIgnSh {sB = sB} (S.ƛ∶ A 𝕢 ω ♭ sa) scΓ i p rewrite compTeIgnSh {sB = sB} sa (scΓ S., A 𝕢 ω) (suc i) (s≤s p) = refl
compTeIgnSh (S.ƛr∶ x ♭ sa) scΓ i p = refl
compTeIgnSh (sa S.· sa₁ 𝕢 𝟘) scΓ i p = compTeIgnSh sa scΓ i p
compTeIgnSh (sa S.· sa₁ 𝕢 ω) scΓ i p = {!   !}
compTeIgnSh (sa S.·ᵣ sa₁) scΓ i p = compTeIgnSh sa₁ scΓ i p
compTeIgnSh S.z scΓ i p = refl
compTeIgnSh {sB = sB} (S.s sa) scΓ i p rewrite compTeIgnSh {sB = sB} sa scΓ i p = refl
compTeIgnSh S.nill scΓ i p = refl
compTeIgnSh (sa S.∷l sas) scΓ i p = {!   !}
compTeIgnSh (S.nilv𝕢 x) scΓ i p = {!   !}
compTeIgnSh (sa S.∷v sas 𝕟 sa₂ 𝕢 x) scΓ i p = {!   !}
compTeIgnSh (S.elimnat sa P∶ sa₁ zb∶ sa₂ sb∶ sa₃) scΓ i p = {!   !}
compTeIgnSh (S.eliml sa ty∶ innerty P∶ sa₁ nb∶ sa₂ cb∶ sa₃) scΓ i p = {!   !}
compTeIgnSh (S.elimv x ty∶ innerty P∶ sa nb∶ sa₁ cb∶ sa₂) scΓ i p = {!   !}
compTeIgnSh S.Nat scΓ i p = refl
compTeIgnSh (S.List x) scΓ i p = refl
compTeIgnSh (S.Vec sa (A 𝕢 σ)) scΓ i p = refl
compTeIgnSh (S.∶ A 𝕢 σ ⟶ x₁) scΓ i p = refl
compTeIgnSh (S.r∶ x ⟶ x₁) scΓ i p = refl
compTeIgnSh (S.Sett x) scΓ i p = refl

~ᵣtermproof :
    (scΓ : S.Context sΓ) →
    sa ~ᵣ sc → 
    compileTerm scΓ sa ≡ compileTerm scΓ sc
~ᵣtermproof scΓ S.~ᵣrefl = {!   !}
~ᵣtermproof scΓ (S.~ᵣsym ~) = {!   !}
~ᵣtermproof scΓ (S.~ᵣtrans ~ ~₁) = {!   !}
~ᵣtermproof scΓ (S.~ᵣs ~) = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷l ~ ~₁) = {!   !}
~ᵣtermproof scΓ (S.~ᵣlamω ~) = {!   !}
~ᵣtermproof {sc = sc} scΓ (S.~ᵣlam𝟘 {A = sA} ~) rewrite ~ᵣtermproof (scΓ S., sA 𝕢 𝟘) ~  = compTeIgnSh sc scΓ 0 z≤n
~ᵣtermproof scΓ S.~ᵣlamr = refl 
~ᵣtermproof scΓ (S.~ᵣappω ~ ~₁) = {!   !}
~ᵣtermproof scΓ (S.~ᵣapp𝟘 ~) = {!   !}
~ᵣtermproof scΓ S.~ᵣappr = {!   !}
~ᵣtermproof scΓ S.~ᵣbetaω = {!   !}
~ᵣtermproof scΓ S.~ᵣnilvω = {!   !}
~ᵣtermproof scΓ S.~ᵣnilv𝟘 = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷vω ~ ~₁ ~₂) = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷v𝟘 ~ ~₁) = {!   !}
~ᵣtermproof scΓ (S.~ᵣηlist ~ (inj₁ x)) = {!   !}
~ᵣtermproof scΓ (S.~ᵣηlist ~ (inj₂ y)) = {!   !}
~ᵣtermproof scΓ (S.~ᵣηvec ~ ~₁) = {!   !}
---- Types
~ᵣtermproof scΓ (S.~ᵣlist ~) = refl 
~ᵣtermproof scΓ (S.~ᵣvecω ~ ~₁) = refl 
~ᵣtermproof scΓ (S.~ᵣvec𝟘 ~) = refl 
~ᵣtermproof scΓ (S.~ᵣpiω ~ ~₁) = refl
-- Cant state anything about B or sc from this info 
~ᵣtermproof scΓ (S.~ᵣpi𝟘 {A = sA} ~) = {!   !}
~ᵣtermproof scΓ (S.~ᵣpir ~) = refl

compTyIgnShift {i} {l} (S.var x) = sym (lemmaIgnorePaths (l ≤ᵇ x) (S.var (x + i)) (S.var x) {refl} {refl}) 
compTyIgnShift S.Nat = refl
compTyIgnShift (S.List x) rewrite compTyIgnShift x = refl
compTyIgnShift {i} {l} (S.Vec sA (n 𝕢 𝟘)) rewrite compTyIgnShift sA = refl
compTyIgnShift {i} {l} (S.Vec sA (n 𝕢 ω)) rewrite compTyIgnShift {i = i} {l = l} sA = refl
compTyIgnShift {i} {l} (S.∶ A 𝕢 𝟘 ⟶ B) = compTyIgnShift B
compTyIgnShift {i} {l} (S.∶ A 𝕢 ω ⟶ B) 
    rewrite compTyIgnShift A | compTyIgnShift B = refl
compTyIgnShift (S.r∶ A ⟶ B) 
    rewrite compTyIgnShift A | compTyIgnShift B = refl
compTyIgnShift (S.Sett x) = refl
---- Terms
compTyIgnShift (S.ƛ∶ A 𝕢 σ ♭ sA) = refl
compTyIgnShift (S.ƛr∶ x ♭ sA) = refl
compTyIgnShift (sA S.· sA₁ 𝕢 x) = refl
compTyIgnShift (sA S.·ᵣ sA₁) = refl 
compTyIgnShift S.z = refl
compTyIgnShift (S.s sA) = refl
compTyIgnShift S.nill = refl
compTyIgnShift (sA S.∷l sA₁) = refl
compTyIgnShift (S.nilv𝕢 x) = refl
compTyIgnShift (sA S.∷v sA₁ 𝕟 sA₂ 𝕢 x) = refl
compTyIgnShift (S.elimnat sA P∶ sA₁ zb∶ sA₂ sb∶ sA₃) = refl 
compTyIgnShift (S.eliml sA ty∶ innerty P∶ sA₁ nb∶ sA₂ cb∶ sA₃) = refl
compTyIgnShift (S.elimv A 𝕢 σ ty∶ innerty P∶ sA nb∶ sA₁ cb∶ sA₂) = refl

~ᵣtypeproof :
    sA ~ᵣ sB → 
    compileType sA ≡ compileType sB
~ᵣtypeproof S.~ᵣrefl = refl
~ᵣtypeproof (S.~ᵣsym A~B) rewrite ~ᵣtypeproof A~B = refl
~ᵣtypeproof (S.~ᵣtrans A~B B~C) rewrite ~ᵣtypeproof A~B | ~ᵣtypeproof B~C = refl
~ᵣtypeproof (S.~ᵣlist A~B) rewrite ~ᵣtypeproof A~B = refl
~ᵣtypeproof (S.~ᵣpiω A~C B~D) rewrite ~ᵣtypeproof A~C | ~ᵣtypeproof B~D = refl
~ᵣtypeproof {sB = sB} (S.~ᵣpi𝟘 B~sB) rewrite ~ᵣtypeproof B~sB | compTyIgnShift sB = refl
~ᵣtypeproof (S.~ᵣpir A~B) rewrite ~ᵣtypeproof A~B = refl
~ᵣtypeproof (S.~ᵣvecω n~m A~B) rewrite ~ᵣtypeproof A~B = refl
~ᵣtypeproof (S.~ᵣvec𝟘 A~B) rewrite ~ᵣtypeproof A~B = refl
---- Terms 
~ᵣtypeproof (S.~ᵣs A~B) = refl
~ᵣtypeproof (S.~ᵣ∷l A~B A~B₁) = refl
~ᵣtypeproof (S.~ᵣlamω A~B) = refl
~ᵣtypeproof (S.~ᵣlam𝟘 B~sB) = {!   !}
~ᵣtypeproof S.~ᵣlamr = refl
~ᵣtypeproof (S.~ᵣappω A~B A~B₁) = refl
~ᵣtypeproof (S.~ᵣapp𝟘 B~sB) = {!   !}
~ᵣtypeproof S.~ᵣappr = {!   !}
~ᵣtypeproof S.~ᵣbetaω = {!   !}
~ᵣtypeproof S.~ᵣnilvω = refl 
~ᵣtypeproof S.~ᵣnilv𝟘 = refl 
~ᵣtypeproof (S.~ᵣ∷vω A~B A~B₁ A~B₂) = refl 
~ᵣtypeproof (S.~ᵣ∷v𝟘 A~B A~B₁) = refl 
~ᵣtypeproof (S.~ᵣηlist A~B A~B₁) = {!   !}
~ᵣtypeproof (S.~ᵣηvec A~B A~B₁) = {!   !}  
                                               
-- Add proof for type preservation             