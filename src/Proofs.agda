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

    i l : ℕ

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



compTyIgnShift : ∀ {i l} → (sA : _) → compileType sA ≡ compileType (S.shiftindices sA i l)

compTeIgnSh : {scΓ : S.Context sΓ} → 
    (sa : S.Term) → 
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) → 
    compileTerm (insertType scΓ i p sA {!   !}) (S.shiftindices sa 1 i) ≡ compileTerm {!   !} sa

~ᵣtermproof :
    sa ~ᵣ sc → 
    compileTerm scΓ sa ≡ compileTerm scΓ sc
~ᵣtermproof sa = {!   !}
{-
~ᵣtermproof :
    (rΓ : ContextRemap scΓ) →
    sa ~ᵣ sc → 
    compileTerm rΓ sa ≡ compileTerm rΓ sc
~ᵣtermproof rΓ S.~ᵣrefl = refl
~ᵣtermproof rΓ (S.~ᵣsym a~c) = sym (~ᵣtermproof rΓ a~c)
~ᵣtermproof rΓ (S.~ᵣtrans a~c a~c₁) = trans (~ᵣtermproof rΓ a~c) (~ᵣtermproof rΓ a~c₁)
~ᵣtermproof rΓ (S.~ᵣs a~c) rewrite ~ᵣtermproof rΓ a~c = refl
~ᵣtermproof rΓ (S.~ᵣ∷l a~c as~cs)
    rewrite ~ᵣtermproof rΓ a~c | ~ᵣtermproof rΓ as~cs = refl
-- Cant give sA and dont have tA either...
-- bc bound locally?
-- need lemmabind?
~ᵣtermproof rΓ (S.~ᵣlamω {A = sA} b~c) rewrite ~ᵣtermproof (rΓ ,ᵣ sA ↦ {!   !}) b~c = {!   !}
~ᵣtermproof rΓ (S.~ᵣlam𝟘 {A = A} b~c) rewrite ~ᵣtermproof (rΓ ,ᵣ A skip)  b~c = {!   !}
~ᵣtermproof rΓ S.~ᵣlamr = {!   !}
~ᵣtermproof rΓ (S.~ᵣappω a~c a~c₁) = {!   !}
~ᵣtermproof rΓ (S.~ᵣapp𝟘 a~c) = {!   !}
~ᵣtermproof rΓ S.~ᵣappr = {!   !}
~ᵣtermproof rΓ S.~ᵣbetaω = {!   !}
~ᵣtermproof rΓ S.~ᵣnilvω = {!   !}
~ᵣtermproof rΓ S.~ᵣnilv𝟘 = {!   !}
~ᵣtermproof rΓ (S.~ᵣ∷vω a~c a~c₁ a~c₂) = {!   !}
~ᵣtermproof rΓ (S.~ᵣ∷v𝟘 a~c a~c₁) = {!   !}
~ᵣtermproof rΓ (S.~ᵣηlist a~c x) = {!   !}
~ᵣtermproof rΓ (S.~ᵣηvec a~c a~c₁) = {!   !}
-- types 
~ᵣtermproof rΓ (S.~ᵣlist a~c) = refl
~ᵣtermproof rΓ (S.~ᵣpiω a~c a~c₁) = refl 
~ᵣtermproof rΓ (S.~ᵣvecω a~c a~c₁) = refl 
~ᵣtermproof rΓ (S.~ᵣvec𝟘 a~c) = refl 
-- may need weakening lemma, but generally dont know that subterms are types 
~ᵣtermproof rΓ (S.~ᵣpi𝟘 a~c) = {!   !}
~ᵣtermproof rΓ (S.~ᵣpir a~c) = refl 
-}
{-
~ᵣtermproof {scΓ = scΓ} S.~ᵣrefl = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣsym a~b) rewrite ~ᵣtermproof {scΓ = scΓ} a~b = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣtrans a~B B~b) = trans (~ᵣtermproof a~B) (~ᵣtermproof B~b)
-- These rules engage in some reduction, either 
---- 1. Optimize in the compiler 
---- 2. Remove reduction rules 
---- 3. Instead create observational equivalence between terms
-- Tried moving m ~ z style inversions into rule and also add a cong rule
~ᵣtermproof {scΓ = scΓ} (S.~ᵣs n~m) rewrite ~ᵣtermproof {scΓ = scΓ} n~m  = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷l a~c as~cs) 
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlamω {A = A} b~c) 
    rewrite ~ᵣtermproof {scΓ = scΓ S., A S.𝕢 S.ω} b~c = refl
~ᵣtermproof {sc = sc} {scΓ = scΓ} (S.~ᵣlam𝟘 {A = A} b~sc) rewrite ~ᵣtermproof {scΓ = (scΓ S., A 𝕢 𝟘)} b~sc = sym ({!   !}) 
~ᵣtermproof {scΓ = scΓ} S.~ᵣlamr = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣappω b~d a~c)
    rewrite ~ᵣtermproof {scΓ = scΓ} b~d | ~ᵣtermproof {scΓ = scΓ} a~c = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣapp𝟘 b~sb) rewrite ~ᵣtermproof {scΓ = scΓ} b~sb = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣappr = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣbetaω = {!   !}
~ᵣtermproof {scΓ = scΓ} S.~ᵣnilvω = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣnilv𝟘 = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷vω a~c as~cs n~m) 
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs | ~ᵣtermproof {scΓ = scΓ} n~m = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷v𝟘 a~c as~cs)
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs = refl
-- probably need lemma here, not sure if rewrite does any work
-- I think the eta rules are unprovable because theyre still "extensional"
~ᵣtermproof {scΓ = scΓ} (S.~ᵣηlist {A = A} {P} nb~ (inj₁ cb~acc))
    rewrite ~ᵣtermproof {scΓ = scΓ} nb~ | ~ᵣtermproof {scΓ = ((scΓ S., A 𝕢 ω) S., S.List A 𝕢 ω) S., (P S.· S.var 0 𝕢 𝟘) 𝕢 ω} cb~acc = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣηlist nb~ (inj₂ cb~tail)) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣηvec nb~ cb~)
    rewrite ~ᵣtermproof {scΓ = scΓ} nb~ = {!   !}
---- Types
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpiω a~b a~b₁) = refl
-- stuck why? Cant tell B is a type...
-- LHS and RHS contets do not necessarily align here
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpi𝟘 {B} a~b) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpir _) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlist _) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣvecω _ _) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣvec𝟘 _) = refl
-}

-- nothing ≡ compileType (if l ≤ᵇ x then S.var (x + i) else S.var x)
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