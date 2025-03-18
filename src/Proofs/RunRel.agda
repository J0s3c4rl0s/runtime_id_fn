{-# OPTIONS --rewriting #-}
module Proofs.RunRel where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations
open import Proofs.Utils

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

open import Data.Nat
open import Data.List
open import Data.Bool using (if_then_else_; Bool)
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Nullary.Decidable
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

private variable
    A : Set

    sΓ sΔ : S.PreContext
    scΓ : S.Context sΓ
    scΔ : S.Context sΔ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    i l k x : ℕ

    rΓ rΓ' : ContextRemap scΓ

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

-- Uncertain how to reframe this now
{-
insertSkip : {scΓ : S.Context sΓ} → ContextRemap scΓ → (i : ℕ) → (p : i ≤ conLen sΓ)  → (sA : S.Type) → ContextRemap (insertType scΓ i p sA 𝟘)
insertSkip rΓ zero z≤n sA = rΓ ,ᵣ sA skip
insertSkip (rΓ ,ᵣ sB skip) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i skip
insertSkip (rΓ ,ᵣ sB ↦ tB) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i ↦ tB

lemmaRemap : {p : _} {rΓ : ContextRemap scΓ} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (insertType scΓ i p sA 𝟘) ≡ just (insertSkip rΓ i p sA) 
lemmaRemap {scΓ = scΓ} {i = zero} {p = z≤n} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ} eqrΓ = {!   !}
-}




        
{-
lemmaRemapInversionSkip : 
    (compileRemap scΓ >>= (λ rΓ₁ → just (rΓ₁ ,ᵣ sA skip))) ≡ just (rΓ ,ᵣ sA skip) →
    compileRemap scΓ ≡ just rΓ

lemmaRemapInversionAss :     
    (compileRemap scΓ >>= (λ rΓ₁ → compileType sA >>= (λ tA → just (rΓ₁ ,ᵣ sA ↦ tA)))) ≡ just (rΓ ,ᵣ sA ↦ tA) →
    compileRemap scΓ ≡ just rΓ

-- Need to find abstract version, maybe
lemmaRemap : ∀ {p} {rΓ : ContextRemap scΓ} {rΓ↑ : ContextRemap (insertType scΓ i p sB 𝟘)} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (insertType scΓ i p sB 𝟘) ≡ just rΓ↑ →
    remapIndex x rΓ ≡ remapIndex (if i ≤ᵇ x then (x + 1) else x) rΓ↑
lemmaRemap {scΓ = scΓ} {zero} {x = x} {p = z≤n} {rΓ = rΓ} {rΓ↑ = rΓ↑ ,ᵣ sA skip} scΓComps scΓ↑Comps
    rewrite scΓComps | tmpJustSkip scΓ↑Comps | +-comm x 1 = refl
lemmaRemap {scΓ = scΓ S., sA 𝕢 𝟘} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .sA skip} {rΓ↑ ,ᵣ .(S.shiftindices sA 1 i) skip} scΓComps scΓ↑Comps = refl
lemmaRemap {scΓ = scΓ S., sA 𝕢 𝟘} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .sA skip} {rΓ↑ ,ᵣ .(S.shiftindices sA 1 i) skip} scΓComps scΓ↑Comps
    rewrite lemmaRemap {x = x} (lemmaRemapInversionSkip scΓComps) (lemmaRemapInversionSkip scΓ↑Comps) with (i ≤ᵇ suc x) 
... | Bool.false = {!   !}
... | Bool.true = {!   !}
lemmaRemap {scΓ = scΓ S., sA 𝕢 ω} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .sA ↦ tA} {rΓ↑ ,ᵣ .(S.shiftindices sA 1 i) ↦ tA₁} scΓComps scΓ↑Comps = refl
lemmaRemap {scΓ = scΓ S., sA 𝕢 ω} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .sA ↦ tA} {rΓ↑ ,ᵣ .(S.shiftindices sA 1 i) ↦ tA₁} scΓComps scΓ↑Comps 
    rewrite lemmaRemap {x = x} (lemmaRemapInversionAss scΓComps) (lemmaRemapInversionAss scΓ↑Comps) = {!  !}
-}

lemmaPushIf : {cond : Bool} →
    compileTerm scΓ (if cond then S.var (x + 1) else S.var x) 
    ≡ 
    (compileRemap scΓ >>=
    (λ remap → remapIndex (if cond then (x + 1) else x) remap >>= (λ n → just (T.var n))))
lemmaPushIf {cond = Bool.false} = refl
lemmaPushIf {cond = Bool.true} = refl

tmpJustSkip : ∀ {scΓ : S.Context sΓ} {rΓ rΓ↑ : ContextRemap scΓ} →
    just (rΓ ,ᵣ sA skip) ≡ just (rΓ↑ ,ᵣ sA skip) →
    rΓ ≡ rΓ↑
tmpJustSkip refl = refl

---- Either: 
-- Equivalence of remaps (i.e. compile to same target)
lemmaWeakenVar : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) →
    compileTerm scΓ (S.var x) compilesTermTo ta →
    compileTerm (insertType scΓ i p sB 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo ta
lemmaWeakenVar {x = x} {sB = sB} scΓ i p varComps 
    with (i ≤ᵇ x) | compileRemap (insertType scΓ i p sB 𝟘)
... | cond | rΓ↑ = {!   !}   

-- make scΓ↑ and sa↑ actual args? Need to turn them into relations
lemmaWeaken : 
    (sa : S.Term) → 
    -- maybe make it a record type? cont, i, p, sB
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ conLen sΓ) →
    (sB : S.Type) →
    compileTerm scΓ sa compilesTermTo ta →
    compileTerm (insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) compilesTermTo ta
lemmaWeaken (S.var x) scΓ i p sB saComps = {!   !}
lemmaWeaken (S.ƛ∶ sA 𝕢 𝟘 ♭ sa) scΓ i p sB saComps = 
    lemmaWeaken sa (scΓ S., sA 𝕢 𝟘) (suc i) (s≤s p) sB saComps
lemmaWeaken (S.ƛ∶ sA 𝕢 ω ♭ sa) scΓ i p sB saBComps = 
    Te.lemmaBindSubstBase
        (compileTerm (scΓ S., sA 𝕢 ω) sa) (compileTerm (insertType (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB 𝟘) (S.shiftindices sa 1 (suc i)))
        (λ tbody → just (T.ƛ tbody)) 
        saBComps 
        λ saComps → lemmaWeaken sa (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB saComps 
lemmaWeaken (S.ƛr∶ x ♭ sa) scΓ i p sB saComps = saComps
lemmaWeaken (sa S.· sa₁ 𝕢 𝟘) scΓ i p sB saComps = lemmaWeaken sa scΓ i p sB saComps
lemmaWeaken (sf S.· sarg 𝕢 ω) scΓ i p sB bindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sf) (compileTerm scΓ↑ sf↑) 
        body-arg body-arg↑ 
        bindComps 
        (λ sfComps → lemmaWeaken sf scΓ i p sB sfComps) 
        λ res sargBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sarg) (compileTerm scΓ↑ sarg↑) 
                (body-base res) 
                sargBindComps 
                λ sargComps → lemmaWeaken sarg scΓ i p sB sargComps
        where
            scΓ↑ = insertType scΓ i p sB 𝟘
            sf↑ = S.shiftindices sf 1 i 
            sarg↑ = S.shiftindices sarg 1 i
            body-base = λ tf ta → just (tf T.· ta)
            body-arg = λ tf → compileTerm scΓ sarg >>= body-base tf
            body-arg↑ = λ tf → compileTerm scΓ↑ sarg↑ >>= body-base tf
lemmaWeaken (sa S.·ᵣ sa₁) scΓ i p sB saComps = lemmaWeaken sa₁ scΓ i p sB saComps
lemmaWeaken S.z scΓ i p sB saComps = saComps
lemmaWeaken (S.s sa) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstBase 
        (compileTerm scΓ sa) (compileTerm (insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i)) 
        (λ ta → just (T.s ta)) 
        saBindComps 
        λ saComps → lemmaWeaken sa scΓ i p sB saComps
lemmaWeaken S.nill scΓ i p sB saComps = saComps
lemmaWeaken (sa S.∷l sas) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeaken sa scΓ i p sB saComps) 
        λ res sasBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-base res) 
                sasBindComps 
                λ sasComps → lemmaWeaken sas scΓ i p sB sasComps
        where
            scΓ↑ = insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            body-base = (λ ta  tas → just (ta T.∷l tas))
            body-as = (λ ta → compileTerm scΓ sas >>= body-base ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-base ta)
lemmaWeaken (S.nilv𝕢 𝟘) scΓ i p sB saComps = saComps
lemmaWeaken (S.nilv𝕢 ω) scΓ i p sB saComps = saComps
lemmaWeaken (sa S.∷v sas 𝕟 sn 𝕢 𝟘) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeaken sa scΓ i p sB saComps) 
        λ res sasBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-base res) 
                sasBindComps 
                λ sasComps → lemmaWeaken sas scΓ i p sB sasComps
        where
            scΓ↑ = insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            body-base = (λ ta  tas → just (ta T.∷l tas))
            body-as = (λ ta → compileTerm scΓ sas >>= body-base ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-base ta)
lemmaWeaken (sa S.∷v sas 𝕟 sn 𝕢 ω) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeaken sa scΓ i p sB saComps)  
        λ res-a sasBindComps → 
            Te.lemmaBindSubstInd 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-n res-a) (body-n↑ res-a) 
                sasBindComps 
                (λ sasComps → lemmaWeaken sas scΓ i p sB sasComps) 
                λ res-as nBindComps → 
                    Te.lemmaBindSubstBase 
                        (compileTerm scΓ sn) (compileTerm scΓ↑ sn↑) 
                        (body-base res-a res-as) 
                        nBindComps 
                        λ snComps → lemmaWeaken sn scΓ i p sB snComps
        where
            scΓ↑ = insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            sn↑ = S.shiftindices sn 1 i
            body-base = (λ ta tas tn → just (ta T.∷v tas 𝕟 tn))
            body-n = λ ta tas → compileTerm scΓ sn >>= body-base ta tas
            body-n↑ = λ ta tas → compileTerm scΓ↑ sn↑ >>= body-base ta tas
            body-as = (λ ta → compileTerm scΓ sas >>= body-n ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-n↑ ta)
lemmaWeaken (S.elimnat sn P∶ sP zb∶ sz sb∶ ss) scΓ i p sB snBindComps = 
    {! insertType ((scΓ S., S.Nat 𝕢 ω) S., sP 𝕢 ω) (2+ i) (s≤s (s≤s p)) sB 𝟘   !}
    -- Te.lemmaBindSubstInd 
    --     (compileTerm scΓ sn) (compileTerm scΓ↑ sn↑) 
    --     body-sz body-sz↑ 
    --     snBindComps 
    --     (λ snComps → lemmaWeaken sn scΓ i p sB snComps) 
    --     λ res-n szBindComps → 
    --         Te.lemmaBindSubstInd 
    --             (compileTerm scΓ sz) (compileTerm scΓ↑ sz↑) 
    --             (body-ss res-n) (body-ss↑ res-n) 
    --             szBindComps 
    --             (λ szComps → lemmaWeaken sz scΓ i p sB szComps) 
    --             λ res-sz ssBindComps → 
    --                 Te.lemmaBindSubstBase 
    --                     (compileTerm scΓs ss) (compileTerm ? ss↑) 
    --                     (body-base res-n res-sz) 
    --                     ssBindComps 
    --                     λ ssComps → lemmaWeaken {! ss  !} scΓs (2+ i) (s≤s (s≤s p)) sB ssComps
        -- Annoying wrt scΓs and insertTypes cant resolve it
        where
            scΓ↑ = insertType scΓ i p sB 𝟘
            scΓs = ((scΓ S., S.Nat 𝕢 ω) S., (sP S.[ 0 / S.var 0 ]) 𝕢 ω)
            scΓs↑ = (scΓ↑ S., S.Nat 𝕢 ω) S., (S.shiftindices sP 1 (suc i) S.[ 0 / S.var 0 ]) 𝕢 ω
            sn↑ = S.shiftindices sn 1 i
            sz↑ = S.shiftindices sz 1 i
            ss↑ = S.shiftindices ss 1 (i + 2)
            body-base = λ tn tz ts → just (T.elimnat tn zb∶ tz sb∶ ts)
            body-ss↑ = λ ta tz → compileTerm scΓs↑ ss↑ >>= body-base ta tz
            body-ss = λ ta tz → compileTerm scΓs ss >>= body-base ta tz
            body-sz↑ = λ ta → compileTerm scΓ↑ sz↑ >>= body-ss↑ ta 
            body-sz = λ ta → compileTerm scΓ sz >>= body-ss ta 
lemmaWeaken (S.eliml sl ty∶ innerty P∶ sa₁ nb∶ sa₂ cb∶ sa₃) scΓ i p sB saComps = {!   !}
lemmaWeaken (S.elimv sv 𝕢 σ ty∶ innerty P∶ sa nb∶ sa₁ cb∶ sa₂) scΓ i p sB saComps = {!   !}
-- Types
lemmaWeaken S.Nat scΓ i p sB saComps = saComps 
lemmaWeaken (S.List x) scΓ i p sB saComps = saComps 
lemmaWeaken (S.Vec sa (A 𝕢 σ)) scΓ i p sB saComps = saComps 
lemmaWeaken (S.∶ A 𝕢 σ ⟶ x₁) scΓ i p sB saComps = saComps
lemmaWeaken (S.r∶ x ⟶ x₁) scΓ i p sB saComps = saComps 
lemmaWeaken (S.Sett x) scΓ i p sB saComps = saComps 


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
    Te.lemmaBindBase (compileTerm scΓ n) (compileTerm scΓ m) (λ ta₁ → just (T.s ta₁)) aComps cComps 
        λ nComps mComps → ~ᵣtermproof scΓ ~ nComps mComps
~ᵣtermproof scΓ (S.~ᵣ∷l {a} {c} {as} {cs} ~h ~t) aComps cComps = 
    Te.lemmaBindInd 
        -- ma mb
        (compileTerm scΓ a) (compileTerm scΓ c) 
        -- bodies
        (λ ta₁ → compileTerm scΓ as >>= (λ tas → just (ta₁ T.∷l tas))) (λ ta₁ → compileTerm scΓ cs >>= (λ tas → just (ta₁ T.∷l tas))) 
        -- bindComps
        aComps cComps 
        (λ hlComps hrComps → ~ᵣtermproof scΓ ~h hlComps hrComps) 
        λ res tlCompsB trCompsB → 
            Te.lemmaBindBase 
                (compileTerm scΓ as) (compileTerm scΓ cs) 
                (λ tas → just (res T.∷l tas)) 
                tlCompsB trCompsB 
                (λ tlComps trComps → ~ᵣtermproof scΓ ~t tlComps trComps) 
~ᵣtermproof scΓ (S.~ᵣlamω {b} {c} {A = A} ~) aComps cComps =   
    Te.lemmaBindBase 
        (compileTerm (scΓ S., A 𝕢 ω) b) (compileTerm (scΓ S., A 𝕢 ω) c) 
        (λ tbody → just (T.ƛ tbody)) 
        aComps cComps 
        λ bodyCompL bodyCompR → ~ᵣtermproof (scΓ S., A 𝕢 ω) ~ bodyCompL bodyCompR 
-- Either convert compilesTermTo or make lemma that takes it into account
-- some rewrite lemma based on target?
~ᵣtermproof {sc = sc} scΓ (S.~ᵣlam𝟘 {A = A} ~) bComps cComps = 
    ~ᵣtermproof (scΓ S., A 𝕢 𝟘) ~ bComps (lemmaWeaken sc scΓ zero z≤n A cComps) 
~ᵣtermproof scΓ S.~ᵣlamr aComps cComp = 
    Te.compIsDeterministic 
        (just (T.ƛ (T.var 0))) 
        aComps cComp
~ᵣtermproof scΓ (S.~ᵣappω {b} {d} {a} {c} ~ ~₁) bBindComps dBindComps = 
    Te.lemmaBindInd 
        (compileTerm scΓ b) (compileTerm scΓ d)
        (λ tf → compileTerm scΓ a >>= (λ ta₁ → just (tf T.· ta₁))) (λ tf → compileTerm scΓ c >>= (λ ta₁ → just (tf T.· ta₁))) 
        bBindComps dBindComps 
        (λ bComps dComps → ~ᵣtermproof scΓ ~ bComps dComps)
        λ res aBindComps cBindComps → 
            Te.lemmaBindBase 
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
    Te.lemmaBindInd 
        (compileTerm scΓ a) (compileTerm scΓ c) 
        body-a body-c  
        aBindComps cBindComps 
        (λ aComps cComps → ~ᵣtermproof scΓ ~a aComps cComps)  
        (λ resH asBindComps csBindComps → 
            Te.lemmaBindInd 
                (compileTerm scΓ as) (compileTerm scΓ cs) 
                (body-as resH) (body-cs resH)
                asBindComps csBindComps 
                (λ asComps csComps → ~ᵣtermproof scΓ ~as asComps csComps)  
                λ resT nBindComps mBindComps → 
                    Te.lemmaBindBase 
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
~ᵣtermproof scΓ (S.~ᵣ∷v𝟘 {a} {c} {as} {cs} ~a ~as) aBindComps cBindComps = 
    Te.lemmaBindInd 
        (compileTerm scΓ a) (compileTerm scΓ c)
        body-as body-cs 
        aBindComps cBindComps 
        (λ aComps cComps → ~ᵣtermproof scΓ ~a aComps cComps)
        λ res asBindComps csBindComps → 
            Te.lemmaBindBase 
                (compileTerm scΓ as) (compileTerm scΓ cs) 
                (body-base res) 
                asBindComps csBindComps 
                (λ asComps csComps → ~ᵣtermproof scΓ ~as asComps csComps)          
        where
            body-base =  λ ta tas → just (ta T.∷l tas)
            body-cs = λ ta → compileTerm scΓ cs >>= body-base ta  
            body-as = λ ta → compileTerm scΓ as >>= body-base ta
-- Need lemmaEta to consider different sc cases, here I need to be more observational stuff
~ᵣtermproof {sc = sc} scΓ (S.~ᵣηlist {nb} {cb = cb} ~ ~₁) bindComps cComps = 
    Te.lemmaBindInd 
        {!   !} {!   !} 
        {!   !} (λ z → nothing)
        bindComps cComps 
        {!   !} 
        {!   !} 
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

open import Data.Product

~proofidea : 
    sa ~ᵣ sb →
    sA ~ᵣ sB →
    compile sa sA ≡ just (ta , tA) →
    compile sb sB ≡ just (ta , tA)
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣrefl ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣsym ~te) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣtrans ~te ~te₁) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣs ~te) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {sB} {ta = ta} {tA} (S.~ᵣ∷l {c = c} {cs = cs} ~te ~te₁) ~ty aComps = {! compile (c S.∷l cs) sB  !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣlamω ~te) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣlam𝟘 ~te) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣlamr ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣappω ~te ~te₁) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣapp𝟘 ~te) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣappr ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣbetaω ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣnilvω ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} S.~ᵣnilv𝟘 ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣ∷vω ~te ~te₁ ~te₂) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣ∷v𝟘 ~te ~te₁) ~ty aComps = {!   !}
~proofidea {sa} {sA = sA} {ta = ta} {tA} (S.~ᵣηvec ~te ~te₁) ~ty aComps = {!   !}


-- Add proof for type preservation             