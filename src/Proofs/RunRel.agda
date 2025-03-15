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


lemmaWeaken : 
    (sa : S.Term) → 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) →
    compileTerm scΓ sa compilesTermTo ta →
    compileTerm (insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) compilesTermTo ta
lemmaWeaken (S.var x) scΓ i p saComps = {!   !}
lemmaWeaken (S.ƛ∶ sA 𝕢 𝟘 ♭ sa) scΓ i p saComps = 
    lemmaWeaken sa (scΓ S., sA 𝕢 𝟘) (suc i) (s≤s p) saComps
lemmaWeaken {sB = sB} (S.ƛ∶ sA 𝕢 ω ♭ sa) scΓ i p saBComps = 
    Te.lemmaBindSubst
        (compileTerm (scΓ S., sA 𝕢 ω) sa) (compileTerm (insertType (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB 𝟘) (S.shiftindices sa 1 (suc i)))
        (λ tbody → just (T.ƛ tbody)) 
        saBComps 
        λ saComps → lemmaWeaken sa (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) saComps 
lemmaWeaken (S.ƛr∶ x ♭ sa) scΓ i p saComps = saComps
lemmaWeaken (sa S.· sa₁ 𝕢 x) scΓ i p saComps = {!   !}
lemmaWeaken (sa S.·ᵣ sa₁) scΓ i p saComps = lemmaWeaken sa₁ scΓ i p saComps
lemmaWeaken S.z scΓ i p saComps = saComps
lemmaWeaken (S.s sa) scΓ i p saComps = {!   !}
lemmaWeaken S.nill scΓ i p saComps = saComps
lemmaWeaken (sa S.∷l sa₁) scΓ i p saComps = {!   !}
lemmaWeaken (S.nilv𝕢 𝟘) scΓ i p saComps = saComps
lemmaWeaken (S.nilv𝕢 ω) scΓ i p saComps = saComps
lemmaWeaken (sa S.∷v sa₁ 𝕟 sa₂ 𝕢 𝟘) scΓ i p saComps = {!   !}
lemmaWeaken (sa S.∷v sa₁ 𝕟 sa₂ 𝕢 ω) scΓ i p saComps = {!   !}
lemmaWeaken (S.elimnat sa P∶ sa₁ zb∶ sa₂ sb∶ sa₃) scΓ i p saComps = {!   !}
lemmaWeaken (S.eliml sa ty∶ innerty P∶ sa₁ nb∶ sa₂ cb∶ sa₃) scΓ i p saComps = {!   !}
lemmaWeaken (S.elimv x ty∶ innerty P∶ sa nb∶ sa₁ cb∶ sa₂) scΓ i p saComps = {!   !}
-- Types
lemmaWeaken S.Nat scΓ i p saComps = saComps 
lemmaWeaken (S.List x) scΓ i p saComps = saComps 
lemmaWeaken (S.Vec sa (A 𝕢 σ)) scΓ i p saComps = saComps 
lemmaWeaken (S.∶ A 𝕢 σ ⟶ x₁) scΓ i p saComps = saComps
lemmaWeaken (S.r∶ x ⟶ x₁) scΓ i p saComps = saComps 
lemmaWeaken (S.Sett x) scΓ i p saComps = saComps 

~ᵣtermproof :
    (scΓ : S.Context sΓ) →
    sa ~ᵣ sc → 
    (compileTerm scΓ sa) compilesTermTo ta →
    (compileTerm scΓ sc) compilesTermTo tc → 
    ta ↔te tc
~ᵣtermproof {sa = sa} {ta = ta} {tc} scΓ S.~ᵣrefl aComps cComps = 
    Te.compIsDeterministic 
        (compileTerm scΓ sa) 
        aComps cComps
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
    Te.lemmaBindL (compileTerm scΓ n) (compileTerm scΓ m) (λ ta₁ → just (T.s ta₁)) aComps cComps 
        λ nComps mComps → ~ᵣtermproof scΓ ~ nComps mComps
~ᵣtermproof scΓ (S.~ᵣ∷l {a} {c} {as} {cs} ~h ~t) aComps cComps = 
    Te.lemmaBind 
        -- ma mb
        (compileTerm scΓ a) (compileTerm scΓ c) 
        -- bodies
        (λ ta₁ → compileTerm scΓ as >>= (λ tas → just (ta₁ T.∷l tas))) (λ ta₁ → compileTerm scΓ cs >>= (λ tas → just (ta₁ T.∷l tas))) 
        -- bindComps
        aComps cComps 
        (λ hlComps hrComps → ~ᵣtermproof scΓ ~h hlComps hrComps) 
        λ res tlCompsB trCompsB → 
            Te.lemmaBindL 
                (compileTerm scΓ as) (compileTerm scΓ cs) 
                (λ tas → just (res T.∷l tas)) 
                tlCompsB trCompsB 
                (λ tlComps trComps → ~ᵣtermproof scΓ ~t tlComps trComps) 
~ᵣtermproof scΓ (S.~ᵣlamω {b} {c} {A = A} ~) aComps cComps =   
    Te.lemmaBindL 
        (compileTerm (scΓ S., A 𝕢 ω) b) (compileTerm (scΓ S., A 𝕢 ω) c) 
        (λ tbody → just (T.ƛ tbody)) 
        aComps cComps 
        λ bodyCompL bodyCompR → ~ᵣtermproof (scΓ S., A 𝕢 ω) ~ bodyCompL bodyCompR 
-- Either convert compilesTo or make lemma that takes it into account
-- some rewrite lemma based on target?
~ᵣtermproof {sc = sc} scΓ (S.~ᵣlam𝟘 {A = A} ~) bComps cComps = 
    ~ᵣtermproof (scΓ S., A 𝕢 𝟘) ~ bComps (lemmaWeaken sc scΓ zero z≤n cComps) 
~ᵣtermproof scΓ S.~ᵣlamr aComps cComp = 
    Te.compIsDeterministic 
        (just (T.ƛ (T.var 0))) 
        aComps cComp
~ᵣtermproof scΓ (S.~ᵣappω {b} {d} {a} {c} ~ ~₁) bBindComps dBindComps = 
    Te.lemmaBind 
        (compileTerm scΓ b) (compileTerm scΓ d)
        (λ tf → compileTerm scΓ a >>= (λ ta₁ → just (tf T.· ta₁))) (λ tf → compileTerm scΓ c >>= (λ ta₁ → just (tf T.· ta₁))) 
        bBindComps dBindComps 
        (λ bComps dComps → ~ᵣtermproof scΓ ~ bComps dComps)
        λ res aBindComps cBindComps → 
            Te.lemmaBindL 
                (compileTerm scΓ a) (compileTerm scΓ c)
                (λ ta₁ → just (res T.· ta₁)) 
                aBindComps cBindComps 
                λ {c = c₁} {d = d₁} → ~ᵣtermproof scΓ ~₁
~ᵣtermproof scΓ (S.~ᵣapp𝟘 ~) aComps cComps = ~ᵣtermproof scΓ ~ aComps cComps 
~ᵣtermproof {sc = sc} scΓ S.~ᵣappr aComps cComps = 
    Te.compIsDeterministic 
        (compileTerm scΓ sc)
        aComps cComps  
~ᵣtermproof scΓ S.~ᵣbetaω aComps cComps = {!   !}
~ᵣtermproof scΓ S.~ᵣnilvω aComps cComps = 
    Te.compIsDeterministic 
        (just T.nilv) 
        aComps cComps  
~ᵣtermproof scΓ S.~ᵣnilv𝟘 aComps cComps = 
    Te.compIsDeterministic 
        (just T.nill)         
        aComps cComps
~ᵣtermproof scΓ (S.~ᵣ∷vω {a} {c} {as} {cs} {n} {m} ~a ~as ~n) aBindComps cBindComps = 
    Te.lemmaBind 
        (compileTerm scΓ a) (compileTerm scΓ c) 
        body-a body-c  
        aBindComps cBindComps 
        (λ aComps cComps → ~ᵣtermproof scΓ ~a aComps cComps)  
        (λ resH asBindComps csBindComps → 
            Te.lemmaBind 
                (compileTerm scΓ as) (compileTerm scΓ cs) 
                (body-as resH) (body-cs resH)
                asBindComps csBindComps 
                (λ asComps csComps → ~ᵣtermproof scΓ ~as asComps csComps)  
                λ resT nBindComps mBindComps → 
                    Te.lemmaBindL 
                        (compileTerm scΓ n) (compileTerm scΓ m) 
                        (body-base resH resT) 
                        nBindComps mBindComps 
                        λ nComps mComps → ~ᵣtermproof scΓ ~n nComps mComps)          
        where 
            body-base = λ ta tas tn → just (ta T.∷v tas 𝕟 tn)
            body-as = λ ta → (λ tas → compileTerm scΓ n >>= body-base ta tas)
            body-cs = λ ta → (λ tas → compileTerm scΓ m >>= body-base ta tas)
            body-a = (λ ta → compileTerm scΓ as >>= body-as ta)
            body-c = (λ ta → compileTerm scΓ cs >>= body-cs ta)
~ᵣtermproof scΓ (S.~ᵣ∷v𝟘 ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣηlist ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣηvec ~ ~₁) aComps cComps = {!   !}
---- Types
~ᵣtermproof {ta = ta} scΓ (S.~ᵣlist ~) aComps cComps = Te.compAbsurd {a = ta} aComps 
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpiω ~ ~₁) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpi𝟘 ~) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpir ~) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣvecω ~ ~₁) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣvec𝟘 ~) aComps cComps = Te.compAbsurd {a = ta} aComps

compTyIgnShift : ∀ {i l tA↑} → (sA : _) → 
    compileType sA compilesTypeTo tA →
    compileType (S.shiftindices sA i l) compilesTypeTo tA↑ →
    tA ↔ty tA↑
compTyIgnShift = {!   !}

~ᵣtypeproof :
    sA ~ᵣ sB → 
    (compileType sA) compilesTypeTo tA →
    (compileType sB) compilesTypeTo tB →
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