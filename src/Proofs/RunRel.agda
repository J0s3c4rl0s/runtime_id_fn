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
open import Data.Bool using (if_then_else_; Bool)
open import Data.Sum
open import Data.Maybe -- using (Maybe; just; nothing; _>>=_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality.Rewrite

private variable
    A B : Set

    sΓ sΔ : S.PreContext
    scΓ : S.Context sΓ
    scΔ : S.Context sΔ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    i l j k x : ℕ

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

lemmaRemap : {p : _} {rΓ : ContextRemap scΓ} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (S.insertType scΓ i p sA 𝟘) ≡ just (insertSkip rΓ i p sA) 
lemmaRemap {scΓ = scΓ} {i = zero} {p = z≤n} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} eqrΓ = {!   !}
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ} eqrΓ = {!   !}
-}

insertSkip : {scΓ : S.Context sΓ} → ContextRemap scΓ → (i : ℕ) → (p : i ≤ S.conLen sΓ)  → (sA : S.Type) → ContextRemap (S.insertType scΓ i p sA 𝟘)
insertSkip rΓ zero z≤n sA = rΓ ,ᵣ sA skip
insertSkip (rΓ ,ᵣ sB skip) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i skip
insertSkip (rΓ ,ᵣ sB ↦ tB) (suc i) (s≤s p) sA = insertSkip rΓ i p sA ,ᵣ S.shiftindices sB 1 i ↦ tB

open import Data.Nat.Properties

,ᵣskip-injective₁ : ∀ {scΓ : S.Context sΓ} {rΓ rΓ↑ : ContextRemap scΓ} →
    just (rΓ ,ᵣ sA skip) ≡ just (rΓ↑ ,ᵣ sA skip) →
    rΓ ≡ rΓ↑
,ᵣskip-injective₁ refl = refl

,ᵣass-injective₁ : ∀ {scΓ : S.Context sΓ} {rΓ rΓ↑ : ContextRemap scΓ} →
    just (rΓ ,ᵣ sA ↦ tA) ≡ just (rΓ↑ ,ᵣ sA  ↦ tB) →
    rΓ ≡ rΓ↑
,ᵣass-injective₁ refl = refl

-- ,ᵣass-injective₂ : ∀ {scΓ : S.Context sΓ} {rΓ rΓ↑ : ContextRemap scΓ} →
--     just (rΓ ,ᵣ sA ↦ tA) ≡ just (rΓ↑ ,ᵣ sA  ↦ tB) →
--     tA ≡ tB

invertRemapSkip : 
    (compileRemap scΓ >>= (λ rΓ₁ → just (rΓ₁ ,ᵣ sA skip))) ≡ just (rΓ ,ᵣ sA skip) →
    compileRemap scΓ ≡ just rΓ
invertRemapSkip {scΓ = S.[]} refl = refl
invertRemapSkip {scΓ = scΓ S., A 𝕢 𝟘} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap scΓ
... | just rΓ' 
        rewrite ,ᵣskip-injective₁ bindComps = refl
invertRemapSkip {scΓ = scΓ S., A 𝕢 ω} {rΓ = rΓ ,ᵣ .A ↦ tA} bindComps with compileRemap scΓ | compileType A
... | just rΓ' | just tA'
        rewrite ,ᵣskip-injective₁ bindComps = refl

invertRemapAss₁ :     
    (compileRemap scΓ >>= (λ rΓ₁ → compileType sA >>= (λ tA → just (rΓ₁ ,ᵣ sA ↦ tA)))) ≡ just (rΓ ,ᵣ sA ↦ tA) →
    compileRemap scΓ ≡ just rΓ
invertRemapAss₁ {scΓ = S.[]} {rΓ = []ᵣ} bindComps = refl
invertRemapAss₁ {scΓ = scΓ S., A 𝕢 𝟘} {sA} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap scΓ | compileType sA
... | just rΓ' | just tA'
        rewrite ,ᵣass-injective₁ bindComps = refl
invertRemapAss₁ {scΓ = scΓ S., A 𝕢 ω} {sA} {rΓ = rΓ ,ᵣ .A ↦ tA} bindComps with compileRemap scΓ | compileType A | compileType sA
... | just rΓ' | just tA' | just _ 
        rewrite ,ᵣass-injective₁ bindComps = refl

invertCompTy : 
    (compileType sA >>= (λ tA → just (rΓ ,ᵣ sA ↦ tA))) ≡ just (rΓ ,ᵣ sA ↦ tA) →
    compileType sA ≡ just tA
invertCompTy {sA = sA} bindComps with compileType sA
invertCompTy {sA = sA} refl | just x = refl

-- invertRemapAss₂ : 
--     (compileRemap scΓ >>= (λ rΓ₁ → compileType sA >>= (λ tA → just (rΓ₁ ,ᵣ sA ↦ tA)))) ≡ just (rΓ ,ᵣ sA ↦ tA) →
--     compileType sA ≡ just tA
-- invertRemapAss₂ {scΓ = S.[]} {rΓ = []ᵣ} bindComps = invertCompTy bindComps
-- invertRemapAss₂ {scΓ = scΓ S., A 𝕢 𝟘} {rΓ = rΓ ,ᵣ .A skip} bindComps with invertRemapAss₁ bindComps
-- ... | eq rewrite eq = invertCompTy bindComps
-- invertRemapAss₂ {scΓ = scΓ S., A 𝕢 ω} {rΓ = rΓ ,ᵣ .A ↦ tA} bindComps with invertRemapAss₁ bindComps
-- ... | eq rewrite eq = invertCompTy bindComps

-- rewrite rule?
lemmaPushIf : ∀ {cond : Bool} {cons : A → B} {x₁ x₂ : A} →
    (if cond then cons x₁ else cons x₂) 
    ≡ 
    cons (if cond then x₁ else x₂)
lemmaPushIf {cond = Bool.false} = refl
lemmaPushIf {cond = Bool.true} = refl

≤b-injective : (suc i ≤ᵇ suc j) ≡ (i ≤ᵇ j)
≤b-injective {zero} {j} = refl
≤b-injective {suc i} {j} = refl

-- Need to find abstract version, maybe
lemmaRemap : ∀ {p} {rΓ : ContextRemap scΓ} {rΓ↑ : ContextRemap (S.insertType scΓ i p sB 𝟘)} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (S.insertType scΓ i p sB 𝟘) ≡ just rΓ↑ →
    remapIndex x rΓ ≡ remapIndex (if i ≤ᵇ x then (x + 1) else x) rΓ↑
lemmaRemap {scΓ = _} {zero} {x = x} {z≤n} {rΓ↑ = rΓ↑ ,ᵣ sA skip} scΓComps scΓ↑Comps
    rewrite scΓComps | ,ᵣskip-injective₁ scΓ↑Comps | +-comm x 1 = refl 
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip} scΓComps scΓ↑Comps = refl
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .A ↦ tA} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ tA₁} scΓComps scΓ↑Comps = refl
lemmaRemap {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip} scΓComps scΓ↑Comps 
    rewrite ≤b-injective {i = i} {j = x} | lemmaPushIf {cond = i ≤ᵇ x} {cons = suc} {x₁ = x + 1} {x₂ = x} = 
        lemmaRemap (invertRemapSkip scΓComps) (invertRemapSkip scΓ↑Comps)
lemmaRemap {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .A ↦ tA} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ tA₁} scΓComps scΓ↑Comps
    rewrite ≤b-injective {i = i} {j = x} | lemmaPushIf {cond = i ≤ᵇ x} {cons = suc} {x₁ = x + 1} {x₂ = x}
        rewrite lemmaRemap {x = x} (invertRemapAss₁ scΓComps) (invertRemapAss₁ scΓ↑Comps) = refl

-- change this to some module?
compTyShiftIgn : 
    compileType sA ≡ compileType (S.shiftindices sA i l)
compTyShiftIgn {S.List A} = {!   !}
compTyShiftIgn {S.Vec sA x} = {!   !}
compTyShiftIgn {S.∶ x ⟶ x₁} = {!   !}
compTyShiftIgn {S.r∶ x ⟶ x₁} = {!   !}
compTyShiftIgn {S.Sett x} = {!   !}
---- Terms 
compTyShiftIgn {S.var x} = {!   !}
compTyShiftIgn {S.ƛ∶ A 𝕢 σ ♭ sA} = refl
compTyShiftIgn {S.ƛr∶ x ♭ sA} = refl
compTyShiftIgn {sA S.· sA₁ 𝕢 x} = refl
compTyShiftIgn {sA S.·ᵣ sA₁} = refl
compTyShiftIgn {S.z} = refl
compTyShiftIgn {S.s sA} = refl
compTyShiftIgn {S.nill} = refl
compTyShiftIgn {sA S.∷l sA₁} = refl
compTyShiftIgn {S.nilv𝕢 x} = refl
compTyShiftIgn {sA S.∷v sA₁ 𝕟 sA₂ 𝕢 x} = refl
compTyShiftIgn {S.elimnat sA P∶ sA₁ zb∶ sA₂ sb∶ sA₃} = refl
compTyShiftIgn {S.eliml sA ty∶ innerty P∶ sA₁ nb∶ sA₂ cb∶ sA₃} = refl
compTyShiftIgn {S.elimv A 𝕢 σ ty∶ innerty P∶ sA nb∶ sA₁ cb∶ sA₂} = refl
compTyShiftIgn {S.Nat} = refl


rΓ⇒rΓ↑ : ∀ {p} {rΓ : ContextRemap scΓ} →
    compileRemap scΓ ≡ just rΓ →
    compileRemap (S.insertType scΓ i p sB 𝟘) ≡ just (insertSkip rΓ i p sB)
rΓ⇒rΓ↑ {i = zero} {p = z≤n} {rΓ} scΓComps rewrite scΓComps = refl
rΓ⇒rΓ↑ {scΓ = scΓ S., A 𝕢 𝟘} {i = suc i} {sB} {p = s≤s p} {rΓ ,ᵣ .A skip} scΓComps  
    rewrite rΓ⇒rΓ↑ {i = i} {sB = sB} {p = p} {rΓ = rΓ} (invertRemapSkip scΓComps) = refl
rΓ⇒rΓ↑ {scΓ = scΓ S., A 𝕢 ω} {i = suc i} {sB} {p = s≤s p} {rΓ ,ᵣ .A ↦ tA} bindComps 
    with invertRemapAss₁ bindComps | rΓ⇒rΓ↑ {i = i} {sB = sB} {p = p} {rΓ = rΓ} (invertRemapAss₁ bindComps)
... | eq | eqRec rewrite eq | eqRec | sym (compTyShiftIgn {sA = A} {i = 1} {l = i}) | invertCompTy {sA = A} bindComps = refl

    
remap↑Comps : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    compileTerm scΓ (S.var x) compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo ta
remap↑Comps {x = x} {sB = sB} scΓ i p varComps 
    rewrite lemmaPushIf {cond = i ≤ᵇ x} {cons = S.var} {x₁ = x + 1} {x₂ = x} with compileRemap scΓ in scΓComps 
... | just rΓ 
        rewrite lemmaRemap {sB = sB} {x = x} {p = p} {rΓ = rΓ} scΓComps (rΓ⇒rΓ↑ {i = i} {sB = sB} {p = p} scΓComps) | rΓ⇒rΓ↑ {i = i} {sB = sB} {p = p} scΓComps = varComps


---- Either: 
-- How to link this to previous results, mismatch between abstract and concrete, maybe need abstract interface for compiling remap too (or move lemma to abstract realm)
lemmaWeakenTermVar : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    compileTerm scΓ (S.var x) compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo tb →
    ta ↔te tb
lemmaWeakenTermVar {x = x} {sB = sB} scΓ i p varComps var↑Comps 
    rewrite lemmaPushIf {cond = i ≤ᵇ x} {cons = S.var} {x₁ = x + 1} {x₂ = x} 
        with compileRemap scΓ in scΓComps  | compileRemap (S.insertType scΓ i p sB 𝟘) in scΓ↑Comps
... | just rΓ | just rΓ↑ 
        rewrite sym (lemmaRemap {x = x} scΓComps scΓ↑Comps) = 
            Te.compIsDeterministic mrΓ varComps var↑Comps
            where 
                mrΓ = remapIndex x rΓ >>= (λ n → just (T.var n))

lemmaWeakenTermVar2 : 
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    compileTerm scΓ (S.var x) compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo ta
lemmaWeakenTermVar2 = {!   !}

-- make scΓ↑ and sa↑ actual args? Need to turn them into relations
lemmaWeakenTerm : 
    (sa : S.Term) → 
    -- maybe make it a record type? cont, i, p, sB
    (scΓ : S.Context sΓ) →
    (i : ℕ) → 
    (p : i ≤ S.conLen sΓ) →
    (sB : S.Type) →
    compileTerm scΓ sa compilesTermTo ta →
    compileTerm (S.insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i) compilesTermTo ta
-- this seems... roundabout
lemmaWeakenTerm (S.var x) scΓ i p sB saComps rewrite lemmaPushIf {cond = i ≤ᵇ x} {cons = S.var} {x₁ = (x + 1)} {x₂ = x} = 
    {!   !} -- Te.lemmaRewriteComp {ma = compileTerm scΓ {! S.var x  !}} (lemmaWeakenTermVar {sB = sB} scΓ i p saComps (remap↑Comps scΓ i p saComps)) saComps -- Te.lemmaRewriteComp {ma = compileTerm scΓ {! compileRemap scΓ  !}} (lemmaWeakenTermVar {sB = sB} scΓ i p saComps (remap↑Comps scΓ i p saComps)) saComps
lemmaWeakenTerm (S.ƛ∶ sA 𝕢 𝟘 ♭ sa) scΓ i p sB saComps = 
    lemmaWeakenTerm sa (scΓ S., sA 𝕢 𝟘) (suc i) (s≤s p) sB saComps
lemmaWeakenTerm (S.ƛ∶ sA 𝕢 ω ♭ sa) scΓ i p sB saBComps = 
    Te.lemmaBindSubstBase
        (compileTerm (scΓ S., sA 𝕢 ω) sa) (compileTerm (S.insertType (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB 𝟘) (S.shiftindices sa 1 (suc i)))
        (λ tbody → just (T.ƛ tbody)) 
        saBComps 
        λ saComps → lemmaWeakenTerm sa (scΓ S., sA 𝕢 ω) (suc i) (s≤s p) sB saComps 
lemmaWeakenTerm (S.ƛr∶ x ♭ sa) scΓ i p sB saComps = saComps
lemmaWeakenTerm (sa S.· sa₁ 𝕢 𝟘) scΓ i p sB saComps = lemmaWeakenTerm sa scΓ i p sB saComps
lemmaWeakenTerm (sf S.· sarg 𝕢 ω) scΓ i p sB bindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sf) (compileTerm scΓ↑ sf↑) 
        body-arg body-arg↑ 
        bindComps 
        (λ sfComps → lemmaWeakenTerm sf scΓ i p sB sfComps) 
        λ res sargBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sarg) (compileTerm scΓ↑ sarg↑) 
                (body-base res) 
                sargBindComps 
                λ sargComps → lemmaWeakenTerm sarg scΓ i p sB sargComps
        where
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            sf↑ = S.shiftindices sf 1 i 
            sarg↑ = S.shiftindices sarg 1 i
            body-base = λ tf ta → just (tf T.· ta)
            body-arg = λ tf → compileTerm scΓ sarg >>= body-base tf
            body-arg↑ = λ tf → compileTerm scΓ↑ sarg↑ >>= body-base tf
lemmaWeakenTerm (sa S.·ᵣ sa₁) scΓ i p sB saComps = lemmaWeakenTerm sa₁ scΓ i p sB saComps
lemmaWeakenTerm S.z scΓ i p sB saComps = saComps
lemmaWeakenTerm (S.s sa) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstBase 
        (compileTerm scΓ sa) (compileTerm (S.insertType scΓ i p sB 𝟘) (S.shiftindices sa 1 i)) 
        (λ ta → just (T.s ta)) 
        saBindComps 
        λ saComps → lemmaWeakenTerm sa scΓ i p sB saComps
lemmaWeakenTerm S.nill scΓ i p sB saComps = saComps
lemmaWeakenTerm (sa S.∷l sas) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeakenTerm sa scΓ i p sB saComps) 
        λ res sasBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-base res) 
                sasBindComps 
                λ sasComps → lemmaWeakenTerm sas scΓ i p sB sasComps
        where
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            body-base = (λ ta  tas → just (ta T.∷l tas))
            body-as = (λ ta → compileTerm scΓ sas >>= body-base ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-base ta)
lemmaWeakenTerm (S.nilv𝕢 𝟘) scΓ i p sB saComps = saComps
lemmaWeakenTerm (S.nilv𝕢 ω) scΓ i p sB saComps = saComps
lemmaWeakenTerm (sa S.∷v sas 𝕟 sn 𝕢 𝟘) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeakenTerm sa scΓ i p sB saComps) 
        λ res sasBindComps → 
            Te.lemmaBindSubstBase 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-base res) 
                sasBindComps 
                λ sasComps → lemmaWeakenTerm sas scΓ i p sB sasComps
        where
            scΓ↑ = S.insertType scΓ i p sB 𝟘
            sa↑ = S.shiftindices sa 1 i 
            sas↑ = S.shiftindices sas 1 i
            body-base = (λ ta  tas → just (ta T.∷l tas))
            body-as = (λ ta → compileTerm scΓ sas >>= body-base ta)
            body-as↑ = (λ ta → compileTerm scΓ↑ sas↑ >>= body-base ta)
lemmaWeakenTerm (sa S.∷v sas 𝕟 sn 𝕢 ω) scΓ i p sB saBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sa) (compileTerm scΓ↑ sa↑) 
        body-as body-as↑ 
        saBindComps 
        (λ saComps → lemmaWeakenTerm sa scΓ i p sB saComps)  
        λ res-a sasBindComps → 
            Te.lemmaBindSubstInd 
                (compileTerm scΓ sas) (compileTerm scΓ↑ sas↑) 
                (body-n res-a) (body-n↑ res-a) 
                sasBindComps 
                (λ sasComps → lemmaWeakenTerm sas scΓ i p sB sasComps) 
                λ res-as nBindComps → 
                    Te.lemmaBindSubstBase 
                        (compileTerm scΓ sn) (compileTerm scΓ↑ sn↑) 
                        (body-base res-a res-as) 
                        nBindComps 
                        λ snComps → lemmaWeakenTerm sn scΓ i p sB snComps
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
lemmaWeakenTerm (S.elimnat sn P∶ sP zb∶ sz sb∶ ss) scΓ i p sB snBindComps = 
    Te.lemmaBindSubstInd 
        (compileTerm scΓ sn) (compileTerm scΓ↑ sn↑) 
        body-sz body-sz↑ 
        snBindComps 
        (λ snComps → lemmaWeakenTerm sn scΓ i p sB snComps) 
        λ res-n szBindComps → 
            Te.lemmaBindSubstInd 
                (compileTerm scΓ sz) (compileTerm scΓ↑ sz↑) 
                (body-ss res-n) (body-ss↑ res-n) 
                szBindComps 
                (λ szComps → lemmaWeakenTerm sz scΓ i p sB szComps) 
                λ res-sz ssBindComps → 
                    Te.lemmaBindSubstBase 
                        (compileTerm scΓs ss) (compileTerm scΓs↑ ss↑) 
                        (body-base res-n res-sz) 
                        ssBindComps 
                        λ ssComps → lemmaWeakenTerm ss scΓs (2+ i) (s≤s (s≤s p)) sB ssComps
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
lemmaWeakenTerm (S.eliml sl ty∶ innerty P∶ sa₁ nb∶ sa₂ cb∶ sa₃) scΓ i p sB saComps = {!   !}
lemmaWeakenTerm (S.elimv sv 𝕢 σ ty∶ innerty P∶ sa nb∶ sa₁ cb∶ sa₂) scΓ i p sB saComps = {!   !}
-- Types
lemmaWeakenTerm S.Nat scΓ i p sB saComps = saComps 
lemmaWeakenTerm (S.List x) scΓ i p sB saComps = saComps 
lemmaWeakenTerm (S.Vec sa (A 𝕢 σ)) scΓ i p sB saComps = saComps 
lemmaWeakenTerm (S.∶ A 𝕢 σ ⟶ x₁) scΓ i p sB saComps = saComps
lemmaWeakenTerm (S.r∶ x ⟶ x₁) scΓ i p sB saComps = saComps 
lemmaWeakenTerm (S.Sett x) scΓ i p sB saComps = saComps 


private variable
    snb scb sP : S.Term


-- Is there a more general lemma here? i.e. general observational equivalence
-- Make this say that elim compiles to elim and then do extensionality on what var i is 
lemmaElimLExt : 
    compileTerm scΓ 
        (S.eliml S.var i ty∶ sA P∶ sP 
            nb∶ snb 
            cb∶ scb) 
        compilesTermTo ta →
    compileTerm scΓ sb compilesTermTo tb →
    -- if lookup var i = [] then sc = nb, or sc comps to same as nb 
    (∀ {tc td} →
        compileTerm scΓ snb compilesTermTo tc → 
        compileTerm scΓ (sb S.[ i / S.nill ]) compilesTermTo td → 
        tc ↔te td ) →
    -- if lookup var i = x :: xs then sc = cb, or sc comps to same as cb 
    (∀ {tc td} →
        -- should I subst into cb here? mirroring the current rule?
        compileTerm ((((scΓ S., sA 𝕢 ω) S., S.List sA 𝕢 ω) S., sP 𝕢 ω)) (scb S.[ 0 / S.var 1 ]) compilesTermTo tc → 
        compileTerm scΓ (sb S.[ i / S.var 2 S.∷l S.var 1 ]) compilesTermTo td → 
        tc ↔te td ) →
    -- Both held so elimL = sc
    ta ↔te tb
lemmaElimLExt elimComps sbComps ind[] ind:: = {!  ind[]  !}

invertElimListVar : 
    (compileTerm scΓ 
        (S.eliml S.var x ty∶ sA P∶ sP 
            nb∶ snb 
            cb∶ scb)) 
        compilesTermTo ta →
    (compileTerm scΓ (S.var x) compilesTermTo {! T.[]  !}) ⊎ (compileTerm scΓ (S.var x) compilesTermTo {!   !})

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
    ~ᵣtermproof (scΓ S., A 𝕢 𝟘) ~ bComps (lemmaWeakenTerm sc scΓ zero z≤n A cComps) 
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
-- Might be example why I need option, need cb doesnt align with cb [ 0 / S.var 1]
-- Need lemmaEta to consider different sc cases, here I need to be more observational stuff
-- funext on what var i is? or on result of substitution?
-- Maybe invert var i?
-- Invert to show ta = T.eliml then do funext on what var i (or lookup var i) can be
~ᵣtermproof {sc = sc} scΓ (S.~ᵣηlist {nb} {cb = cb} ~nb ~cb) bindComps cComps = 
    lemmaElimLExt 
        bindComps cComps 
        (λ nbComps scComps → ~ᵣtermproof scΓ ~nb nbComps scComps)
        -- scΓ isnt the same in both here tho...?
        λ cbComps scComps → ~ᵣtermproof scΓ ~cb cbComps scComps
~ᵣtermproof scΓ (S.~ᵣηvec ~ ~₁) aComps cComps = {!   !}
---- Types
~ᵣtermproof {ta = ta} scΓ (S.~ᵣlist ~) aComps cComps = Te.compAbsurd {a = ta} aComps 
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpiω ~ ~₁) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpi𝟘 ~) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣpir ~) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣvecω ~ ~₁) aComps cComps = Te.compAbsurd {a = ta} aComps
~ᵣtermproof {ta = ta} scΓ (S.~ᵣvec𝟘 ~) aComps cComps = Te.compAbsurd {a = ta} aComps


lemmaWeakenType : 
    (sA : S.Term) → 
    (i : ℕ) → 
    (l : ℕ) →
    compileType sA compilesTypeTo tA →
    compileType (S.shiftindices sA i l) compilesTypeTo tA
lemmaWeakenType S.Nat i l sAComps = sAComps
lemmaWeakenType (S.List A) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ tA₁ → just (T.List tA₁))
        bindComps
        λ {A = A₁} → lemmaWeakenType A i l
lemmaWeakenType (S.Vec A (n 𝕢 𝟘)) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ tA₁ → just (T.List tA₁))
        bindComps
        λ {A = A₁} → lemmaWeakenType A i l
lemmaWeakenType (S.Vec A (n 𝕢 ω)) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ tA₁ → just (T.Vec tA₁))
        bindComps
        λ {A = A₁} → lemmaWeakenType A i l
lemmaWeakenType (S.∶ A 𝕢 𝟘 ⟶ B) i l bindComps = lemmaWeakenType B i (suc l) bindComps
lemmaWeakenType (S.∶ A 𝕢 ω ⟶ B) i l bindComps = 
    Ty.lemmaBindSubstInd
        (compileType A) (compileType A↑)
        body-B body-B↑
        bindComps
        (λ AComps → lemmaWeakenType A i l AComps)
        λ res BBindComps → 
            Ty.lemmaBindSubstBase
                (compileType B) (compileType B↑)
                (body-base res)
                BBindComps
                λ BComps → lemmaWeakenType B i (suc l) BComps
        where
            A↑ = S.shiftindices A i l
            B↑ = S.shiftindices B i (suc l)
            body-base = λ tA tB → just (tA T.⟶ tB)
            body-B = λ tA → compileType B >>= body-base tA
            body-B↑ = λ tA → compileType B↑ >>= body-base tA
lemmaWeakenType (S.r∶ A ⟶ B) i l bindComps = 
    Ty.lemmaBindSubstInd
        (compileType A) (compileType A↑)
        body-B body-B↑
        bindComps
        (λ AComps → lemmaWeakenType A i l AComps)
        λ res BBindComps → 
            Ty.lemmaBindSubstBase
                (compileType B) (compileType B↑)
                (body-base res)
                BBindComps
                λ BComps → lemmaWeakenType B i (suc l) BComps
        where
            A↑ = S.shiftindices A i l
            B↑ = S.shiftindices B i (suc l)
            body-base = λ tA tB → just (tA T.⟶ tB)
            body-B = λ tA → compileType B >>= body-base tA
            body-B↑ = λ tA → compileType B↑ >>= body-base tA

~ᵣtypeproof :
    sA ~ᵣ sB → 
    (compileType sA) compilesTypeTo tA →
    (compileType sB) compilesTypeTo tB →
    tA ↔ty tB
~ᵣtypeproof {sA} S.~ᵣrefl AComps BComps = 
    Ty.compIsDeterministic (compileType sA) AComps BComps
~ᵣtypeproof {sA} (S.~ᵣsym ~) AComps BComps = Ty.lemmaSym (~ᵣtypeproof ~ BComps AComps)
~ᵣtypeproof {sA} (S.~ᵣtrans ~ ~₁) AComps BComps = Ty.lemmaTrans (~ᵣtypeproof ~ AComps {!   !}) {!   !}
~ᵣtypeproof {S.List .A} (S.~ᵣlist {A} {B} ~) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ tA₁ → just (T.List tA₁))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~ AComps BComps
~ᵣtypeproof {sA} (S.~ᵣpiω {A} {C} {B = B} {D} ~ ~₁) ABindComps CBindCompss = 
    Ty.lemmaBindInd
        (compileType A) (compileType C)
        body-B body-D
        ABindComps CBindCompss
        (λ AComps CComps → ~ᵣtypeproof ~ AComps CComps)
        λ res BBindComps DBindComps → 
            Ty.lemmaBindBase
                (compileType B) (compileType D)
                (body-base res)
                BBindComps DBindComps
                λ BComps DComps → ~ᵣtypeproof ~₁ BComps DComps
        where
            body-base = λ tA tB → just (tA T.⟶ tB)
            body-D = λ tA → compileType D >>= body-base tA
            body-B = λ tA → compileType B >>= body-base tA
~ᵣtypeproof {sA} {sB} (S.~ᵣpi𝟘 {A = A} ~) AComps BComps =  
    ~ᵣtypeproof ~ AComps (lemmaWeakenType sB 1 0 BComps)
~ᵣtypeproof {sA} (S.~ᵣpir {A} {B} ~) ABindCompsₗ ABindCompsᵣ = 
    Ty.lemmaBindInd
        (compileType A) (compileType A)
        body-B body-A
        ABindCompsₗ ABindCompsᵣ
        (λ ACompsₗ ACompsᵣ → Ty.compIsDeterministic (compileType A) ACompsₗ ACompsᵣ)
        λ res BBindComps ABindComps → 
            Ty.lemmaBindBase
                (compileType B) (compileType A)
                (body-base res)
                BBindComps ABindComps
                λ BComps AComps → Ty.lemmaSym (~ᵣtypeproof ~ AComps BComps)
        where
            body-base = λ tA tB → just (tA T.⟶ tB)
            body-B = λ tA → compileType B >>= body-base tA
            body-A = λ tA → compileType A >>= body-base tA  
~ᵣtypeproof {sA} (S.~ᵣvecω {A = A} {B} ~n ~A) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ tA → just (T.Vec tA))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~A AComps BComps
~ᵣtypeproof {sA} (S.~ᵣvec𝟘 {A} {B} ~) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ tA → just (T.List tA))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~ AComps BComps

