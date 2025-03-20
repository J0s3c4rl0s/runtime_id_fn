module Proofs.RunRelAlt where

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

open import Data.Nat.Properties

tmpJustSkip : ∀ {scΓ : S.Context sΓ} {rΓ rΓ↑ : ContextRemap scΓ} →
    just (rΓ ,ᵣ sA skip) ≡ just (rΓ↑ ,ᵣ sA skip) →
    rΓ ≡ rΓ↑
tmpJustSkip refl = refl
        
lemmaRemapInversionSkip : 
    (compileRemap scΓ >>= (λ rΓ₁ → just (rΓ₁ ,ᵣ sA skip))) ≡ just (rΓ ,ᵣ sA skip) →
    compileRemap scΓ ≡ just rΓ

lemmaRemapInversionAss :     
    (compileRemap scΓ >>= (λ rΓ₁ → compileType sA >>= (λ tA → just (rΓ₁ ,ᵣ sA ↦ tA)))) ≡ just (rΓ ,ᵣ sA ↦ tA) →
    compileRemap scΓ ≡ just rΓ

-- Need to find abstract version, maybe
lemmaRemap : ∀ {p} {rΓ : ContextRemap scΓ} {rΓ↑ : ContextRemap (S.insertType scΓ i p sB 𝟘)} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (S.insertType scΓ i p sB 𝟘) ≡ just rΓ↑ →
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

lemmaPushIf : {cond : Bool} →
    compileTerm scΓ (if cond then S.var (x + 1) else S.var x) 
    ≡ 
    (compileRemap scΓ >>=
    (λ remap → remapIndex (if cond then (x + 1) else x) remap >>= (λ n → just (T.var n))))
lemmaPushIf {cond = Bool.false} = refl
lemmaPushIf {cond = Bool.true} = refl

---- Either: 
-- Equivalence of remaps (i.e. compile to same target)
lemmaWeakenVar : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    compileTerm scΓ (S.var x) compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo ta
lemmaWeakenVar {x = x} {sB = sB} scΓ i p varComps 
    with (i ≤ᵇ x) | compileRemap (S.insertType scΓ i p sB 𝟘)
... | cond | rΓ↑ = {!   !}   

-- make scΓ↑ and sa↑ actual args? Need to turn them into relations
lemmaWeaken : 
    (sa : S.Term) → 
    -- maybe make it a record type? cont, i, p, sB
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    (sB : S.Type) →
    compileTerm scΓ sa compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) compilesTermTo ta
lemmaWeaken (S.var x) scΓ i p sB saComps = {!   !}
lemmaWeaken (S.ƛ∶ sA 𝕢 𝟘 ♭ sa) scΓ i p sB saComps = 
    lemmaWeaken sa (scΓ S., sA 𝕢 𝟘) (suc i) (s≤s p) sB saComps
lemmaWeaken (S.ƛ∶ sA 𝕢 ω ♭ sa) scΓ i p sB saBComps = 
    Te.lemmaBindSubstBase
        (compileTerm (scΓ S., sA 𝕢 ω) sa) (compileTerm (S.insertType (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB 𝟘) (S.shiftindices sa 1 (suc i)))
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
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            sf↑ = S.shiftindices sf 1 i 
            sarg↑ = S.shiftindices sarg 1 i
            body-base = λ tf ta → just (tf T.· ta)
            body-arg = λ tf → compileTerm scΓ sarg >>= body-base tf
            body-arg↑ = λ tf → compileTerm scΓ↑ sarg↑ >>= body-base tf
lemmaWeaken (sa S.·ᵣ sa₁) scΓ i p sB saComps = lemmaWeaken sa₁ scΓ i p sB saComps
lemmaWeaken S.z scΓ i p sB saComps = saComps
lemmaWeaken (S.s sa) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstBase 
        (compileTerm scΓ sa) (compileTerm (S.insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i)) 
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
            scΓ↑ = S.insertType scΓ i p sB 𝟘
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
            scΓ↑ = S.insertType scΓ i p sB 𝟘
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
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            sn↑ = S.shiftindices sn 1 i
            body-base = (λ ta tas tn → just (ta T.∷v tas 𝕟 tn))
            body-n = λ ta tas → compileTerm scΓ sn >>= body-base ta tas
            body-n↑ = λ ta tas → compileTerm scΓ↑ sn↑ >>= body-base ta tas
            body-as = (λ ta → compileTerm scΓ sas >>= body-n ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-n↑ ta)
lemmaWeaken (S.elimnat sn P∶ sP zb∶ sz sb∶ ss) scΓ i p sB snBindComps = -- {!   !}
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sn) (compileTerm scΓ↑ sn↑) 
        body-sz body-sz↑ 
        snBindComps 
        (λ snComps → lemmaWeaken sn scΓ i p sB snComps) 
        λ res-n szBindComps → 
            Te.lemmaBindSubstInd 
                (compileTerm scΓ sz) (compileTerm scΓ↑ sz↑) 
                (body-ss res-n) (body-ss↑ res-n) 
                szBindComps 
                (λ szComps → lemmaWeaken sz scΓ i p sB szComps) 
                λ res-sz ssBindComps → 
                    Te.lemmaBindSubstBase 
                        (compileTerm scΓs ss) (compileTerm scΓs↑ ss↑) 
                        (body-base res-n res-sz) 
                        ssBindComps 
                        λ ssComps → lemmaWeaken ss scΓs (2+ i) (s≤s (s≤s p)) sB ssComps
        -- Annoying wrt scΓs and S.insertTypes cant resolve it
        where
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            scΓs = (scΓ S., S.Nat 𝕢 ω) S., sP 𝕢 ω
            scΓs↑ = S.insertType scΓs (2+ i) (s≤s (s≤s p)) sB 𝟘
            sn↑ = S.shiftindices sn 1 i
            sz↑ = S.shiftindices sz 1 i
            ss↑ = S.shiftindices ss 1 (2+ i)
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


lemmaStrengthenTe : 
    (sa : S.Term) → 
    -- maybe make it a record type? cont, i, p, sB
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    (sB : S.Type) →
    compileTerm (S.insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) compilesTermTo ta →
    compileTerm scΓ sa compilesTermTo ta 

~ᵣtermproof :
    (sa : S.Term) →
    (scΓ : S.Context sΓ) →
    sa ~ᵣ sc → 
    (compileTerm scΓ sa) compilesTermTo ta →
    (compileTerm scΓ sc) compilesTermTo ta
~ᵣtermproof sa scΓ S.~ᵣrefl aComps = aComps
~ᵣtermproof sa scΓ (S.~ᵣsym ~) aComps = {!   !}
~ᵣtermproof sa scΓ (S.~ᵣtrans {B = B} ~ ~₁) aComps = ~ᵣtermproof B scΓ ~₁ (~ᵣtermproof sa scΓ ~ aComps) 
~ᵣtermproof (S.ƛ∶ A 𝕢 𝟘 ♭ sa) scΓ (S.~ᵣlam𝟘 ~) aComps = {!   !}
~ᵣtermproof (S.ƛ∶ A 𝕢 ω ♭ sa) scΓ (S.~ᵣlamω ~) aComps = {!   !}
~ᵣtermproof (S.ƛr∶ x ♭ sa) scΓ S.~ᵣlamr aComps = {!   !}
~ᵣtermproof (sa S.· sa₁ 𝕢 𝟘) scΓ (S.~ᵣapp𝟘 ~) aComps = {!   !}
~ᵣtermproof (sa S.· sa₁ 𝕢 ω) scΓ (S.~ᵣappω ~ ~₁) aComps = {!   !}
~ᵣtermproof (sa S.· sa₁ 𝕢 ω) scΓ S.~ᵣbetaω aComps = {!   !}
~ᵣtermproof (sa S.·ᵣ sa₁) scΓ S.~ᵣappr aComps = {!   !}
~ᵣtermproof (S.s sa) scΓ (S.~ᵣs {m = m} ~) aComps = 
    Te.lemmaBindSubstBase 
        (compileTerm scΓ sa) {!   !} 
        (λ ta₁ → just (T.s ta₁)) 
        aComps 
        {!   !} 
~ᵣtermproof (sa S.∷l sa₁) scΓ ~ aComps = 
    Te.lemmaBindSubstInd
        {!   !} {!   !}
        {!   !} {!   !}
        {!   !}
        {!   !}
        {!   !}
        where
            body-base = {!   !}
~ᵣtermproof (S.nilv𝕢 x) scΓ ~ aComps = {!   !}
~ᵣtermproof (sa S.∷v sa₁ 𝕟 sa₂ 𝕢 x) scΓ ~ aComps = {!   !}
-- missing (?) cong rules here so unreachable natel
~ᵣtermproof (S.elimnat sa P∶ sa₁ zb∶ sa₂ sb∶ sa₃) scΓ ~ aComps = {!   !}
~ᵣtermproof (S.eliml sa ty∶ innerty P∶ sa₁ nb∶ sa₂ cb∶ sa₃) scΓ ~ aComps = {!   !}
~ᵣtermproof (S.elimv x ty∶ innerty P∶ sa nb∶ sa₁ cb∶ sa₂) scΓ ~ aComps = {!   !}
-- ~ᵣtermproof sa scΓ S.~ᵣrefl aComps = aComps
-- ~ᵣtermproof {sc = sc} sa scΓ (S.~ᵣsym ~c) aComps = {!   !} -- Te.lemmaRewriteComp {!   !} aComps
-- ~ᵣtermproof sa scΓ (S.~ᵣtrans {B = B} ~a ~B) aComps = ~ᵣtermproof B scΓ ~B (~ᵣtermproof sa scΓ ~a aComps)
-- ~ᵣtermproof sa scΓ (S.~ᵣs ~n) aComps = {! sa  !}
-- ~ᵣtermproof sa scΓ (S.~ᵣ∷l ~a ~a₁) aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣlamω ~a) aComps = {!   !}
-- ~ᵣtermproof {sc = sc} sa scΓ (S.~ᵣlam𝟘 {b} {A = A} ~b) aComps = 
--     lemmaStrengthenTe 
--         sc scΓ 0 z≤n A 
--         (~ᵣtermproof b (scΓ S., A 𝕢 𝟘) ~b aComps) 
-- ~ᵣtermproof sa scΓ S.~ᵣlamr aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣappω ~a ~a₁) aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣapp𝟘 ~a) aComps = {!   !}
-- ~ᵣtermproof sa scΓ S.~ᵣappr aComps = {!   !}
-- ~ᵣtermproof sa scΓ S.~ᵣbetaω aComps = {!   !}
-- ~ᵣtermproof sa scΓ S.~ᵣnilvω aComps = {!   !}
-- ~ᵣtermproof sa scΓ S.~ᵣnilv𝟘 aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣ∷vω ~a ~a₁ ~a₂) aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣ∷v𝟘 ~a ~a₁) aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣηlist ~a ~a₁) aComps = {!   !}
-- ~ᵣtermproof sa scΓ (S.~ᵣηvec ~a ~a₁) aComps = {!   !}



lemmaStrengthen : ∀ {i l} → (sA : _) → 
    compileType (S.shiftindices sA i l) compilesTypeTo tA →
    compileType sA compilesTypeTo tA 
lemmaStrengthen {i = i} {l} (S.List sA) shiftComps = 
    Ty.lemmaBindSubstBase 
        (compileType (S.shiftindices sA i l)) (compileType sA)
        (λ tA → just (T.List tA))  
        shiftComps 
        λ shiftAComps → lemmaStrengthen sA shiftAComps  
lemmaStrengthen (S.Vec sA x) shiftComps = {!   !}
lemmaStrengthen (S.∶ A 𝕢 𝟘 ⟶ B) shiftComps = lemmaStrengthen B shiftComps 
lemmaStrengthen {i = i} {l} (S.∶ A 𝕢 ω ⟶ B) shiftComps = 
    Ty.lemmaBindSubstInd 
        (compileType (S.shiftindices A i l)) (compileType A) 
        {!   !} {!   !} 
        shiftComps
        {!   !} 
        {!   !} 
lemmaStrengthen (S.r∶ x ⟶ x₁) shiftComps = {!   !}
---- Terms 
lemmaStrengthen (S.var x) shiftComps = {! shiftComps  !}
lemmaStrengthen (S.ƛ∶ x ♭ sA) shiftComps = {!   !}
lemmaStrengthen (S.elimv x ty∶ innerty P∶ sA nb∶ sA₁ cb∶ sA₂) shiftComps = {!   !}
lemmaStrengthen S.Nat shiftComps = {!   !}


~ᵣtypeproof :
    sA ~ᵣ sB → 
    (compileType sA) compilesTypeTo tA →
    (compileType sB) compilesTypeTo tB →
    tA ↔ty tB
~ᵣtypeproof ~ AComps BComps = {!   !}

-- Try alternative 
~ᵣtypeproofAlt :
    sA ~ᵣ sB → 
    (compileType sA) compilesTypeTo tA →
    (compileType sB) compilesTypeTo tA
~ᵣtypeproofAlt S.~ᵣrefl sAComps = sAComps 
~ᵣtypeproofAlt (S.~ᵣsym ~) sAComps = {!   !} -- ~ᵣtypeproofAlt ~ sAComps 
~ᵣtypeproofAlt (S.~ᵣtrans ~ ~₁) sAComps = ~ᵣtypeproofAlt ~₁ (~ᵣtypeproofAlt ~ sAComps) 
~ᵣtypeproofAlt (S.~ᵣlist {A = A} {B = B} ~A) sABindComps = 
    Ty.lemmaBindSubstBase 
        (compileType A) (compileType B)
        (λ tA → just (T.List tA))
        sABindComps 
        λ AComps → ~ᵣtypeproofAlt ~A AComps 
~ᵣtypeproofAlt (S.~ᵣpiω ~A ~B) sAComps = {!   !}
~ᵣtypeproofAlt (S.~ᵣpi𝟘 ~B) sAComps = 
    {!   !} 
~ᵣtypeproofAlt (S.~ᵣpir ~) sAComps = {!   !}
~ᵣtypeproofAlt (S.~ᵣvecω ~n ~A) sAComps = {!   !}
~ᵣtypeproofAlt (S.~ᵣvec𝟘 ~A) sAComps = {!   !}  

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