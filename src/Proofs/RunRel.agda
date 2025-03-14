module Proofs.RunRel where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Nullary.Decidable
open import Data.Bool using (if_then_else_; Bool)


private variable
    A : Set

    sΓ sΔ : S.PreContext
    scΓ : S.Context sΓ
    scΔ : S.Context sΔ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    i l k : ℕ

    rΓ : ContextRemap scΓ

    tA tB tC : T.Type
    ta tb tc : T.Term

{-
lemmaIgnorePaths : ∀ {res} →
    (cond : Bool) → 
    (thenB : _ ) →
    (elseB : _)
    {teq : compileType thenB ↔ty res} → 
    {eeq : compileType elseB ↔ty res} →  
    compileType (if cond then thenB else elseB) ↔ty res
lemmaIgnorePaths Bool.false thenB elseB {eeq = eeq} = eeq
lemmaIgnorePaths Bool.true thenB elseB {teq} = teq
-}

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

-- Uncertain how to reframe this now
{-
lemmaRemap : {p : _} {rΓ : ContextRemap scΓ} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (insertType scΓ i p sA 𝟘) ≡ just (insertSkip rΓ i p sA) 
lemmaRemap {scΓ = scΓ} {i = zero} {p = z≤n} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ} eqrΓ = {!   !}
-}

-- Maybe order preserving embeddings
-- try simple case just inserting at end/beginning
tmp : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) →
    (i≤k : Dec (i ≤ k)) →
    {!   !}
    {-
    compileTerm (insertType scΓ i p sB 𝟘)
      (if ⌊ i≤k ⌋  then S.var (k + 1) else S.var k)
      ↔te
      (compileTerm scΓ (S.var k) ) 
      -}
tmp scΓ i p (Bool.false because proof₁) = {!   !}
tmp scΓ i p (Bool.true because proof₁) = {!   !}

compTeIgnSh :  
    (sa : S.Term) → 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) → 
    {!   !}
    -- compileTerm (insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) ↔te compileTerm scΓ sa
compTeIgnSh = {!   !}

private variable  
    ma mb mc : Maybe A


~ᵣtermproof :
    (scΓ : S.Context sΓ) →
    sa ~ᵣ sc → 
    (compileTerm scΓ sa) compilesTo ta →
    (compileTerm scΓ sc) compilesTo tc → 
    ta ↔te tc
~ᵣtermproof {sa = sa} {ta = ta} {tc} scΓ S.~ᵣrefl aComps cComps 
    rewrite compIsDeterministic aComps cComps = Te.lemmaRefl
~ᵣtermproof scΓ (S.~ᵣsym ~) aComps cComps = Te.lemmaSym (~ᵣtermproof scΓ ~ cComps aComps)
-- Kind of a workaround no? Need general lemma to introduce new intermediate terms to compile (or not)? 
-- Except if B fails to compile it dont really matter here :/
~ᵣtermproof scΓ (S.~ᵣtrans {B = B} ~ ~₁) aComps cComps = {!   !}
{- 
    Te.lemmaTrans 
        -- missing proof of compilation for B (intermediate term)
        -- funext? for all B this holds
        (~ᵣtermproof scΓ ~ aComps {!   !}) 
        (~ᵣtermproof scΓ ~₁ {!   !} cComps)
-}
~ᵣtermproof {ta = ta} scΓ (S.~ᵣs {n} {m} ~) aComps cComps = 
    Te.lemmaBindL aComps cComps λ nComps mComps → ~ᵣtermproof scΓ ~ nComps mComps
~ᵣtermproof scΓ (S.~ᵣ∷l ~h ~t) aComps cComps = 
    Te.lemmaBind aComps cComps 
        (λ hlComps hrComps → ~ᵣtermproof scΓ ~h hlComps hrComps) 
        λ hComps tlCompsB trCompsB → 
            Te.lemmaBindL tlCompsB trCompsB (λ tlComps trComps → ~ᵣtermproof scΓ ~t tlComps trComps) 
~ᵣtermproof scΓ (S.~ᵣlamω {A = A} ~) aComps cComps = 
    Te.lemmaBindL aComps cComps 
        λ bodyCompL bodyCompR → ~ᵣtermproof (scΓ S., A 𝕢 ω) ~ bodyCompL bodyCompR 
~ᵣtermproof scΓ (S.~ᵣlam𝟘 ~) aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣlamr aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣappω ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣapp𝟘 ~) aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣappr aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣbetaω aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣnilvω aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣnilv𝟘 aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷vω ~ ~₁ ~₂) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷v𝟘 ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣηlist ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣηvec ~ ~₁) aComps cComps = {!   !}
---- Types
~ᵣtermproof scΓ (S.~ᵣlist ~) aComps cComps = compAbsurd aComps
~ᵣtermproof scΓ (S.~ᵣpiω ~ ~₁) aComps cComps = compAbsurd aComps
~ᵣtermproof scΓ (S.~ᵣpi𝟘 ~) aComps cComps = compAbsurd  aComps
~ᵣtermproof scΓ (S.~ᵣpir ~) aComps cComps = compAbsurd  aComps
~ᵣtermproof scΓ (S.~ᵣvecω ~ ~₁) aComps cComps = compAbsurd  aComps
~ᵣtermproof scΓ (S.~ᵣvec𝟘 ~) aComps cComps = compAbsurd  aComps

compTyIgnShift : ∀ {i l tA↑} → (sA : _) → 
    compileType sA compilesTo tA →
    compileType (S.shiftindices sA i l) compilesTo tA↑ →
    tA ↔ty tA↑
compTyIgnShift = {!   !}

~ᵣtypeproof :
    sA ~ᵣ sB → 
    (compileType sA) compilesTo tA →
    (compileType sB) compilesTo tB →
    tA ↔ty tB
~ᵣtypeproof S.~ᵣrefl = {!   !}
~ᵣtypeproof (S.~ᵣsym A~B) = {!   !}
~ᵣtypeproof (S.~ᵣtrans A~B B~C) = {!   !}
~ᵣtypeproof (S.~ᵣlist A~B) = {!   !}
~ᵣtypeproof (S.~ᵣpiω A~C B~D) = {!   !}
~ᵣtypeproof {sB = sB} (S.~ᵣpi𝟘 B~sB) = {!   !}
~ᵣtypeproof (S.~ᵣpir A~B) = {!   !}
~ᵣtypeproof (S.~ᵣvecω n~m A~B) = {!   !}
~ᵣtypeproof (S.~ᵣvec𝟘 A~B) = {!   !}
---- Terms 
~ᵣtypeproof (S.~ᵣs A~B) = {!   !}
~ᵣtypeproof (S.~ᵣ∷l A~B A~B₁) = {!   !}
~ᵣtypeproof (S.~ᵣlamω A~B) = {!   !}
~ᵣtypeproof (S.~ᵣlam𝟘 B~sB) = {!   !}
~ᵣtypeproof S.~ᵣlamr = {!   !}
~ᵣtypeproof (S.~ᵣappω A~B A~B₁) = {!   !}
~ᵣtypeproof (S.~ᵣapp𝟘 B~sB) = {!   !}
~ᵣtypeproof S.~ᵣappr = {!   !}
~ᵣtypeproof S.~ᵣbetaω = {!   !}
~ᵣtypeproof S.~ᵣnilvω = {!   !} 
~ᵣtypeproof S.~ᵣnilv𝟘 = {!   !} 
~ᵣtypeproof (S.~ᵣ∷vω A~B A~B₁ A~B₂) = {!   !} 
~ᵣtypeproof (S.~ᵣ∷v𝟘 A~B A~B₁) = {!   !} 
~ᵣtypeproof (S.~ᵣηlist A~B A~B₁) = {!   !}
~ᵣtypeproof (S.~ᵣηvec A~B A~B₁) = {!   !}  
                                               
-- Add proof for type preservation             