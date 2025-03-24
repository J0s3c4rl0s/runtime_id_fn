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
open import Data.Bool using (if_then_else_; Bool)
open import Data.Sum
open import Data.Maybe 
-- open import Relation.Nullary.Decidable
open import Agda.Builtin.Equality.Rewrite

private variable
    A B : Set

    Γₛ : S.PreContext
    cΓₛ : S.Context Γₛ
    Aₛ Bₛ : S.Type
    aₛ bₛ cₛ asₛ bsₛ fₛ : S.Term
    σ π ρ : S.Quantity

    i l j k x : ℕ

    rΓ rΓ' : ContextRemap cΓₛ

    Aₜ Bₜ Cₜ : T.Type
    aₜ bₜ cₜ : T.Term


module Weakening where
    open import Relation.Binary.PropositionalEquality
    open import Data.Nat.Properties using (+-comm)

    insertSkip : {cΓₛ : S.Context Γₛ} → ContextRemap cΓₛ → (i : ℕ) → (p : i ≤ S.conLen Γₛ)  → (Aₛ : S.Type) → ContextRemap (S.insertType cΓₛ i p Aₛ 𝟘)
    insertSkip rΓ zero z≤n Aₛ = rΓ ,ᵣ Aₛ skip
    insertSkip (rΓ ,ᵣ Bₛ skip) (suc i) (s≤s p) Aₛ = insertSkip rΓ i p Aₛ ,ᵣ S.shiftindices Bₛ 1 i skip
    insertSkip (rΓ ,ᵣ Bₛ ↦ Bₜ) (suc i) (s≤s p) Aₛ = insertSkip rΓ i p Aₛ ,ᵣ S.shiftindices Bₛ 1 i ↦ Bₜ


    ,ᵣskip-injective₁ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
        just (rΓ ,ᵣ Aₛ skip) ≡ just (rΓ↑ ,ᵣ Aₛ skip) →
        rΓ ≡ rΓ↑
    ,ᵣskip-injective₁ refl = refl

    ,ᵣass-injective₁ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
        just (rΓ ,ᵣ Aₛ ↦ Aₜ) ≡ just (rΓ↑ ,ᵣ Aₛ  ↦ Bₜ) →
        rΓ ≡ rΓ↑
    ,ᵣass-injective₁ refl = refl

    -- ,ᵣass-injective₂ : ∀ {cΓₛ : S.Context Γₛ} {rΓ rΓ↑ : ContextRemap cΓₛ} →
    --     just (rΓ ,ᵣ Aₛ ↦ Aₜ) ≡ just (rΓ↑ ,ᵣ Aₛ  ↦ Bₜ) →
    --     Aₜ ≡ Bₜ

    invertRemapSkip : 
        (compileRemap cΓₛ >>= (λ rΓ₁ → just (rΓ₁ ,ᵣ Aₛ skip))) ≡ just (rΓ ,ᵣ Aₛ skip) →
        compileRemap cΓₛ ≡ just rΓ
    invertRemapSkip {cΓₛ = S.[]} refl = refl
    invertRemapSkip {cΓₛ = cΓₛ S., A 𝕢 𝟘} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap cΓₛ
    ... | just rΓ' 
            rewrite ,ᵣskip-injective₁ bindComps = refl
    invertRemapSkip {cΓₛ = cΓₛ S., A 𝕢 ω} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with compileRemap cΓₛ | compileType A
    ... | just rΓ' | just Aₜ'
            rewrite ,ᵣskip-injective₁ bindComps = refl

    invertRemapAss₁ :     
        (compileRemap cΓₛ >>= (λ rΓ₁ → compileType Aₛ >>= (λ Aₜ → just (rΓ₁ ,ᵣ Aₛ ↦ Aₜ)))) ≡ just (rΓ ,ᵣ Aₛ ↦ Aₜ) →
        compileRemap cΓₛ ≡ just rΓ
    invertRemapAss₁ {cΓₛ = S.[]} {rΓ = []ᵣ} bindComps = refl
    invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 𝟘} {Aₛ} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap cΓₛ | compileType Aₛ
    ... | just rΓ' | just Aₜ'
            rewrite ,ᵣass-injective₁ bindComps = refl
    invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 ω} {Aₛ} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with compileRemap cΓₛ | compileType A | compileType Aₛ
    ... | just rΓ' | just Aₜ' | just _ 
            rewrite ,ᵣass-injective₁ bindComps = refl

    invertCompTy : 
        (compileType Aₛ >>= (λ Aₜ → just (rΓ ,ᵣ Aₛ ↦ Aₜ))) ≡ just (rΓ ,ᵣ Aₛ ↦ Aₜ) →
        compileType Aₛ ≡ just Aₜ
    invertCompTy {Aₛ = Aₛ} bindComps with compileType Aₛ
    invertCompTy {Aₛ = Aₛ} refl | just x = refl

    -- invertRemapAss₂ : 
    --     (compileRemap cΓₛ >>= (λ rΓ₁ → compileType Aₛ >>= (λ Aₜ → just (rΓ₁ ,ᵣ Aₛ ↦ Aₜ)))) ≡ just (rΓ ,ᵣ Aₛ ↦ Aₜ) →
    --     compileType Aₛ ≡ just Aₜ
    -- invertRemapAss₂ {cΓₛ = S.[]} {rΓ = []ᵣ} bindComps = invertCompTy bindComps
    -- invertRemapAss₂ {cΓₛ = cΓₛ S., A 𝕢 𝟘} {rΓ = rΓ ,ᵣ .A skip} bindComps with invertRemapAss₁ bindComps
    -- ... | eq rewrite eq = invertCompTy bindComps
    -- invertRemapAss₂ {cΓₛ = cΓₛ S., A 𝕢 ω} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with invertRemapAss₁ bindComps
    -- ... | eq rewrite eq = invertCompTy bindComps

    -- rewrite rule?
    if-injective : ∀ {cond : Bool} {cons : A → B} {x₁ x₂ : A} →
        (if cond then cons x₁ else cons x₂) 
        ≡ 
        cons (if cond then x₁ else x₂)
    if-injective {cond = Bool.false} = refl
    if-injective {cond = Bool.true} = refl

    ≤b-injective : (suc i ≤ᵇ suc j) ≡ (i ≤ᵇ j)
    ≤b-injective {zero} {j} = refl
    ≤b-injective {suc i} {j} = refl

    -- Need to find abstract version, maybe
    lemmaRemap : ∀ {p} {rΓ : ContextRemap cΓₛ} {rΓ↑ : ContextRemap (S.insertType cΓₛ i p Bₛ 𝟘)} →
        compileRemap cΓₛ ≡ just rΓ →
        compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ just rΓ↑ →
        remapIndex x rΓ ≡ remapIndex (if i ≤ᵇ x then (x + 1) else x) rΓ↑
    lemmaRemap {cΓₛ = _} {zero} {x = x} {z≤n} {rΓ↑ = rΓ↑ ,ᵣ Aₛ skip} cΓₛComps cΓₛ↑Comps
        rewrite cΓₛComps | ,ᵣskip-injective₁ cΓₛ↑Comps | +-comm x 1 = refl 
    lemmaRemap {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip} cΓₛComps cΓₛ↑Comps = refl
    lemmaRemap {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {x = zero} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ Aₜ₁} cΓₛComps cΓₛ↑Comps = refl
    lemmaRemap {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip} cΓₛComps cΓₛ↑Comps 
        rewrite ≤b-injective {i = i} {j = x} | if-injective {cond = i ≤ᵇ x} {cons = suc} {x₁ = x + 1} {x₂ = x} = 
            lemmaRemap (invertRemapSkip cΓₛComps) (invertRemapSkip cΓₛ↑Comps)
    lemmaRemap {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {x = suc x} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ Aₜ₁} cΓₛComps cΓₛ↑Comps
        rewrite ≤b-injective {i = i} {j = x} | if-injective {cond = i ≤ᵇ x} {cons = suc} {x₁ = x + 1} {x₂ = x}
            rewrite lemmaRemap {x = x} (invertRemapAss₁ cΓₛComps) (invertRemapAss₁ cΓₛ↑Comps) = refl

    -- change this to some module?
    compTyShiftIgn : 
        compileType Aₛ ≡ compileType (S.shiftindices Aₛ i l)
    -- compTyShiftIgn {S.List A} = {!   !}
    -- compTyShiftIgn {S.Vec Aₛ x} = {!   !}
    -- compTyShiftIgn {S.∶ x ⟶ x₁} = {!   !}
    -- compTyShiftIgn {S.r∶ x ⟶ x₁} = {!   !}
    -- compTyShiftIgn {S.Sett x} = {!   !}
    -- ---- Terms 
    -- compTyShiftIgn {S.var x} = {!   !}
    -- compTyShiftIgn {S.ƛ∶ A 𝕢 σ ♭ Aₛ} = refl
    -- compTyShiftIgn {S.ƛr∶ x ♭ Aₛ} = refl
    -- compTyShiftIgn {Aₛ S.· Aₛ₁ 𝕢 x} = refl
    -- compTyShiftIgn {Aₛ S.·ᵣ Aₛ₁} = refl
    -- compTyShiftIgn {S.z} = refl
    -- compTyShiftIgn {S.s Aₛ} = refl
    -- compTyShiftIgn {S.nill} = refl
    -- compTyShiftIgn {Aₛ S.∷l Aₛ₁} = refl
    -- compTyShiftIgn {S.nilv𝕢 x} = refl
    -- compTyShiftIgn {Aₛ S.∷v Aₛ₁ 𝕟 Aₛ₂ 𝕢 x} = refl
    -- compTyShiftIgn {S.elimnat Aₛ P∶ Aₛ₁ zb∶ Aₛ₂ sb∶ Aₛ₃} = refl
    -- compTyShiftIgn {S.eliml Aₛ ty∶ innerty P∶ Aₛ₁ nb∶ Aₛ₂ cb∶ Aₛ₃} = refl
    -- compTyShiftIgn {S.elimv A 𝕢 σ ty∶ innerty P∶ Aₛ nb∶ Aₛ₁ cb∶ Aₛ₂} = refl
    -- compTyShiftIgn {S.Nat} = refl


    rΓ⇒rΓ↑ : ∀ {p} {rΓ : ContextRemap cΓₛ} →
        compileRemap cΓₛ ≡ just rΓ →
        compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ just (insertSkip rΓ i p Bₛ)
    rΓ⇒rΓ↑ {i = zero} {p = z≤n} {rΓ} cΓₛComps rewrite cΓₛComps = refl
    rΓ⇒rΓ↑ {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {Bₛ} {p = s≤s p} {rΓ ,ᵣ .A skip} cΓₛComps  
        rewrite rΓ⇒rΓ↑ {i = i} {Bₛ = Bₛ} {p = p} {rΓ = rΓ} (invertRemapSkip cΓₛComps) = refl
    rΓ⇒rΓ↑ {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {Bₛ} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} bindComps 
        with invertRemapAss₁ bindComps | rΓ⇒rΓ↑ {i = i} {Bₛ = Bₛ} {p = p} {rΓ = rΓ} (invertRemapAss₁ bindComps)
    ... | eq | eqRec rewrite eq | eqRec | sym (compTyShiftIgn {Aₛ = A} {i = 1} {l = i}) | invertCompTy {Aₛ = A} bindComps = refl

        
    remap↑Comps : 
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        compileTerm cΓₛ (S.var x) compilesTermTo aₜ →
        compileTerm (S.insertType cΓₛ i p Bₛ 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo aₜ
    remap↑Comps {x = x} {Bₛ = Bₛ} cΓₛ i p varComps 
        rewrite if-injective {cond = i ≤ᵇ x} {cons = S.var} {x₁ = x + 1} {x₂ = x} with compileRemap cΓₛ in cΓₛComps 
    ... | just rΓ 
            rewrite lemmaRemap {Bₛ = Bₛ} {x = x} {p = p} {rΓ = rΓ} cΓₛComps (rΓ⇒rΓ↑ {i = i} {Bₛ = Bₛ} {p = p} cΓₛComps) | rΓ⇒rΓ↑ {i = i} {Bₛ = Bₛ} {p = p} cΓₛComps = varComps


    ---- Either: 
    -- How to link this to previous results, mismacₜh between abstract and concrete, maybe need abstract interface for compiling remap too (or move lemma to abstract realm)
    lemmaWeakenTermVar : 
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        compileTerm cΓₛ (S.var x) compilesTermTo aₜ →
        compileTerm (S.insertType cΓₛ i p Bₛ 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo bₜ →
        aₜ ↔te bₜ
    lemmaWeakenTermVar {x = x} {Bₛ = Bₛ} cΓₛ i p varComps var↑Comps 
        rewrite if-injective {cond = i ≤ᵇ x} {cons = S.var} {x₁ = x + 1} {x₂ = x} 
            with compileRemap cΓₛ in cΓₛComps  | compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in cΓₛ↑Comps
    ... | just rΓ | just rΓ↑ 
            rewrite sym (lemmaRemap {x = x} cΓₛComps cΓₛ↑Comps) = 
                Te.compIsDeterministic mrΓ varComps var↑Comps
                where 
                    mrΓ = remapIndex x rΓ >>= (λ n → just (T.var n))

    lemmaWeakenTermVar2 : 
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        compileTerm cΓₛ (S.var x) compilesTermTo aₜ →
        compileTerm (S.insertType cΓₛ i p Bₛ 𝟘) (if i ≤ᵇ x then S.var (x + 1) else S.var x) compilesTermTo aₜ
    lemmaWeakenTermVar2 = {!   !}

    lemmaWeakenTerm : 
        (aₛ : S.Term) → 
        -- maybe make it a record type? cont, i, p, Bₛ
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        (Bₛ : S.Type) →
        compileTerm cΓₛ aₛ compilesTermTo aₜ →
        compileTerm (S.insertType cΓₛ i p Bₛ 𝟘) (S.shiftindices aₛ 1 i) compilesTermTo aₜ
    -- this seems... roundabout
    lemmaWeakenTerm (S.var x) cΓₛ i p Bₛ aₛComps rewrite if-injective {cond = i ≤ᵇ x} {cons = S.var} {x₁ = (x + 1)} {x₂ = x} = 
        {!   !}
        -- Te.lemmaRewriteComp {ma = compileTerm cΓₛ {! compileRemap cΓₛ  !}} (lemmaWeakenTermVar {Bₛ = Bₛ} cΓₛ i p aₛComps (remap↑Comps cΓₛ i p aₛComps)) aₛComps
    lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ) cΓₛ i p Bₛ aₛComps = 
        lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 𝟘) (suc i) (s≤s p) Bₛ aₛComps
    lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ) cΓₛ i p Bₛ aₛBComps = 
        Te.lemmaBindSubstBase
            (compileTerm (cΓₛ S., Aₛ 𝕢 ω) aₛ) (compileTerm (S.insertType (cΓₛ S., Aₛ 𝕢 ω) (suc i) (s≤s p) Bₛ 𝟘) (S.shiftindices aₛ 1 (suc i)))
            (λ bₜody → just (T.ƛ bₜody)) 
            aₛBComps 
            λ aₛComps → lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 ω) (suc i) (s≤s p) Bₛ aₛComps 
    lemmaWeakenTerm (S.ƛr∶ x ♭ aₛ) cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (aₛ S.· aₛ₁ 𝕢 𝟘) cΓₛ i p Bₛ aₛComps = lemmaWeakenTerm aₛ cΓₛ i p Bₛ aₛComps
    lemmaWeakenTerm (fₛ S.· aₛrg 𝕢 ω) cΓₛ i p Bₛ bindComps = 
        Te.lemmaBindSubstInd 
            (compileTerm cΓₛ fₛ) (compileTerm cΓₛ↑ fₛ↑) 
            body-arg body-arg↑ 
            bindComps 
            (λ fₛComps → lemmaWeakenTerm fₛ cΓₛ i p Bₛ fₛComps) 
            λ res aₛrgBindComps → 
                Te.lemmaBindSubstBase 
                    (compileTerm cΓₛ aₛrg) (compileTerm cΓₛ↑ aₛrg↑) 
                    (body-base res) 
                    aₛrgBindComps 
                    λ aₛrgComps → lemmaWeakenTerm aₛrg cΓₛ i p Bₛ aₛrgComps
            where
                cΓₛ↑ = S.insertType cΓₛ i p Bₛ 𝟘
                fₛ↑ = S.shiftindices fₛ 1 i 
                aₛrg↑ = S.shiftindices aₛrg 1 i
                body-base = λ tf aₜ → just (tf T.· aₜ)
                body-arg = λ tf → compileTerm cΓₛ aₛrg >>= body-base tf
                body-arg↑ = λ tf → compileTerm cΓₛ↑ aₛrg↑ >>= body-base tf
    lemmaWeakenTerm (aₛ S.·ᵣ aₛ₁) cΓₛ i p Bₛ aₛComps = lemmaWeakenTerm aₛ₁ cΓₛ i p Bₛ aₛComps
    lemmaWeakenTerm S.z cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (S.s aₛ) cΓₛ i p Bₛ aₛBindComps = 
        Te.lemmaBindSubstBase 
            (compileTerm cΓₛ aₛ) (compileTerm (S.insertType cΓₛ i p Bₛ 𝟘) (S.shiftindices aₛ 1 i)) 
            (λ aₜ → just (T.s aₜ)) 
            aₛBindComps 
            λ aₛComps → lemmaWeakenTerm aₛ cΓₛ i p Bₛ aₛComps
    lemmaWeakenTerm S.nill cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (aₛ S.∷l asₛ) cΓₛ i p Bₛ aₛBindComps = 
        Te.lemmaBindSubstInd 
            (compileTerm cΓₛ aₛ) (compileTerm cΓₛ↑ aₛ↑) 
            body-as body-as↑ 
            aₛBindComps 
            (λ aₛComps → lemmaWeakenTerm aₛ cΓₛ i p Bₛ aₛComps) 
            λ res aₛBₛindComps → 
                Te.lemmaBindSubstBase 
                    (compileTerm cΓₛ asₛ) (compileTerm cΓₛ↑ asₛ↑) 
                    (body-base res) 
                    aₛBₛindComps 
                    λ asₛComps → lemmaWeakenTerm asₛ cΓₛ i p Bₛ asₛComps
            where
                cΓₛ↑ = S.insertType cΓₛ i p Bₛ 𝟘
                aₛ↑ = S.shiftindices aₛ 1 i 
                asₛ↑ = S.shiftindices asₛ 1 i
                body-base = (λ aₜ  aₜs → just (aₜ T.∷l aₜs))
                body-as = (λ aₜ → compileTerm cΓₛ asₛ >>= body-base aₜ)
                body-as↑ = (λ aₜ → compileTerm cΓₛ↑ asₛ↑ >>= body-base aₜ)
    lemmaWeakenTerm (S.nilv𝕢 𝟘) cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (S.nilv𝕢 ω) cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 sn 𝕢 𝟘) cΓₛ i p Bₛ aₛBindComps = 
        Te.lemmaBindSubstInd 
            (compileTerm cΓₛ aₛ) (compileTerm cΓₛ↑ aₛ↑) 
            body-as body-as↑ 
            aₛBindComps 
            (λ aₛComps → lemmaWeakenTerm aₛ cΓₛ i p Bₛ aₛComps) 
            λ res aₛBₛindComps → 
                Te.lemmaBindSubstBase 
                    (compileTerm cΓₛ asₛ) (compileTerm cΓₛ↑ asₛ↑) 
                    (body-base res) 
                    aₛBₛindComps 
                    λ asₛComps → lemmaWeakenTerm asₛ cΓₛ i p Bₛ asₛComps
            where
                cΓₛ↑ = S.insertType cΓₛ i p Bₛ 𝟘
                aₛ↑ = S.shiftindices aₛ 1 i 
                asₛ↑ = S.shiftindices asₛ 1 i
                body-base = (λ aₜ  aₜs → just (aₜ T.∷l aₜs))
                body-as = (λ aₜ → compileTerm cΓₛ asₛ >>= body-base aₜ)
                body-as↑ = (λ aₜ → compileTerm cΓₛ↑ asₛ↑ >>= body-base aₜ)
    lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 sn 𝕢 ω) cΓₛ i p Bₛ aₛBindComps = 
        Te.lemmaBindSubstInd 
            (compileTerm cΓₛ aₛ) (compileTerm cΓₛ↑ aₛ↑) 
            body-as body-as↑ 
            aₛBindComps 
            (λ aₛComps → lemmaWeakenTerm aₛ cΓₛ i p Bₛ aₛComps)  
            λ res-a aₛBₛindComps → 
                Te.lemmaBindSubstInd 
                    (compileTerm cΓₛ asₛ) (compileTerm cΓₛ↑ asₛ↑) 
                    (body-n res-a) (body-n↑ res-a) 
                    aₛBₛindComps 
                    (λ asₛComps → lemmaWeakenTerm asₛ cΓₛ i p Bₛ asₛComps) 
                    λ res-as nBindComps → 
                        Te.lemmaBindSubstBase 
                            (compileTerm cΓₛ sn) (compileTerm cΓₛ↑ sn↑) 
                            (body-base res-a res-as) 
                            nBindComps 
                            λ snComps → lemmaWeakenTerm sn cΓₛ i p Bₛ snComps
            where
                cΓₛ↑ = S.insertType cΓₛ i p Bₛ 𝟘
                aₛ↑ = S.shiftindices aₛ 1 i 
                asₛ↑ = S.shiftindices asₛ 1 i
                sn↑ = S.shiftindices sn 1 i
                body-base = (λ aₜ aₜs tn → just (aₜ T.∷v aₜs 𝕟 tn))
                body-n = λ aₜ aₜs → compileTerm cΓₛ sn >>= body-base aₜ aₜs
                body-n↑ = λ aₜ aₜs → compileTerm cΓₛ↑ sn↑ >>= body-base aₜ aₜs
                body-as = (λ aₜ → compileTerm cΓₛ asₛ >>= body-n aₜ)
                body-as↑ = (λ aₜ → compileTerm cΓₛ↑ asₛ↑ >>= body-n↑ aₜ)
    lemmaWeakenTerm (S.elimnat sn P∶ sP zb∶ sz sb∶ ss) cΓₛ i p Bₛ snBindComps = 
        Te.lemmaBindSubstInd 
            (compileTerm cΓₛ sn) (compileTerm cΓₛ↑ sn↑) 
            body-sz body-sz↑ 
            snBindComps 
            (λ snComps → lemmaWeakenTerm sn cΓₛ i p Bₛ snComps) 
            λ res-n szBindComps → 
                Te.lemmaBindSubstInd 
                    (compileTerm cΓₛ sz) (compileTerm cΓₛ↑ sz↑) 
                    (body-ss res-n) (body-ss↑ res-n) 
                    szBindComps 
                    (λ szComps → lemmaWeakenTerm sz cΓₛ i p Bₛ szComps) 
                    λ res-sz sBₛindComps → 
                        Te.lemmaBindSubstBase 
                            (compileTerm cΓₛs ss) (compileTerm cΓₛs↑ ss↑) 
                            (body-base res-n res-sz) 
                            sBₛindComps 
                            λ ssComps → lemmaWeakenTerm ss cΓₛs (2+ i) (s≤s (s≤s p)) Bₛ ssComps
            -- Annoying wrt cΓₛs and S.insertTypes cant resolve it
            where
                cΓₛ↑ = S.insertType cΓₛ i p Bₛ 𝟘
                cΓₛs = (cΓₛ S., S.Nat 𝕢 ω) S., sP 𝕢 ω
                cΓₛs↑ = S.insertType cΓₛs (2+ i) (s≤s (s≤s p)) Bₛ 𝟘
                sn↑ = S.shiftindices sn 1 i
                sz↑ = S.shiftindices sz 1 i
                ss↑ = S.shiftindices ss 1 (2+ i)
                body-base = λ tn tz ts → just (T.elimnat tn zb∶ tz sb∶ ts)
                body-ss↑ = λ aₜ tz → compileTerm cΓₛs↑ ss↑ >>= body-base aₜ tz
                body-ss = λ aₜ tz → compileTerm cΓₛs ss >>= body-base aₜ tz
                body-sz↑ = λ aₜ → compileTerm cΓₛ↑ sz↑ >>= body-ss↑ aₜ 
                body-sz = λ aₜ → compileTerm cΓₛ sz >>= body-ss aₜ 
    lemmaWeakenTerm (S.eliml sl ty∶ innerty P∶ aₛ₁ nb∶ aₛ₂ cb∶ aₛ₃) cΓₛ i p Bₛ aₛComps = {!   !}
    lemmaWeakenTerm (S.elimv sv 𝕢 σ ty∶ innerty P∶ aₛ nb∶ aₛ₁ cb∶ aₛ₂) cΓₛ i p Bₛ aₛComps = {!   !}
    -- Types
    lemmaWeakenTerm S.Nat cΓₛ i p Bₛ aₛComps = aₛComps 
    lemmaWeakenTerm (S.List x) cΓₛ i p Bₛ aₛComps = aₛComps 
    lemmaWeakenTerm (S.Vec aₛ (A 𝕢 σ)) cΓₛ i p Bₛ aₛComps = aₛComps 
    lemmaWeakenTerm (S.∶ A 𝕢 σ ⟶ x₁) cΓₛ i p Bₛ aₛComps = aₛComps
    lemmaWeakenTerm (S.r∶ x ⟶ x₁) cΓₛ i p Bₛ aₛComps = aₛComps 
    lemmaWeakenTerm (S.Sett x) cΓₛ i p Bₛ aₛComps = aₛComps 

open Weakening

module ElimExt where
    open import Data.Product
    private variable
        []bₛ ∷bₛ sP : S.Term


    subStillCompiles : 
        (aₛ : S.Term) →
        (i : ℕ) →
        (bₛ : S.Term) →
        compileTerm cΓₛ aₛ compilesTermTo aₜ →
        compileTerm cΓₛ bₛ compilesTermTo bₜ →
        -- does this always hold??
        Σ[ aₜₛ ∈ T.Term ] (compileTerm cΓₛ (aₛ S.[ i / bₛ ]) compilesTermTo aₜₛ)
        

    invertElimL[]b : 
        compileTerm cΓₛ 
            (S.eliml S.var i ty∶ Aₛ P∶ sP 
                nb∶ []bₛ 
                cb∶ ∷bₛ) 
            compilesTermTo aₜ →
        -- cant compute what aₜ is 
        -- compileTerm cΓₛ []bₛ compilesTermTo {!   !}
        Σ[ aₜ ∈ T.Term ] (compileTerm cΓₛ []bₛ compilesTermTo aₜ)
        
    -- lemma on how one compiles substitution?
    -- Is there a more general lemma here? i.e. general observational equivalence
    -- Make this aₛy that elim compiles to elim and then do extensionality on what var i is 
    lemmaElimLExt : 
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ ) →
        ([]bₛ : S.Term ) →
        (∷bₛ : S.Term ) →
        (bₛ : S.Term ) →
        compileTerm cΓₛ 
            (S.eliml S.var i ty∶ Aₛ P∶ sP 
                nb∶ []bₛ 
                cb∶ ∷bₛ) 
            compilesTermTo aₜ →
        compileTerm cΓₛ bₛ compilesTermTo bₜ →
        -- if lookup var i = [] then cₛ = []b, or cₛ comps to aₛme as []b 
        (∀ {cₜ td} →
            compileTerm cΓₛ []bₛ compilesTermTo cₜ → 
            compileTerm cΓₛ (bₛ S.[ i / S.nill ]) compilesTermTo td → 
            cₜ ↔te td ) →
        -- if lookup var i = x :: xs then cₛ = ∷b, or cₛ comps to aₛme as ∷b 
        (∀ {cₜ td} →
            -- should I subst into ∷b here? mirroring the current rule?
            compileTerm ((((cΓₛ S., Aₛ 𝕢 ω) S., S.List Aₛ 𝕢 ω) S., sP 𝕢 ω)) (∷bₛ S.[ 0 / S.var 1 ]) compilesTermTo cₜ → 
            compileTerm cΓₛ (bₛ S.[ i / S.var 2 S.∷l S.var 1 ]) compilesTermTo td → 
            cₜ ↔te td ) →
        -- Both held so elimL = cₛ
        aₜ ↔te bₜ
    lemmaElimLExt = {!   !}
        -- where
        --     cₛsub1 = subStillCompiles {bₜ = T.nill} bₛ i S.nill bₛComps Te.lemmaRefl
        --     aₜₛ = proj₁ cₛsub1
        --     cₛsub1Comps = proj₂ cₛsub1
        --     []bₛCompsP = invertElimL[]b {cΓₛ = cΓₛ}  {sP = sP} {[]bₛ = []bₛ} {∷bₛ = ∷bₛ} {aₜ = aₜ} elimComps
        --     []bₛComps = proj₂ []bₛCompsP

    lemmaFunExt : ∀ {f g} →  
        (∀ {aₜ} →
            (f T.· aₜ) ↔te (g T.· aₜ)) →
        f ↔te g

    -- Need lemma that will compile substitution in S to substitution in T with updated i

    lemmaElimComps :
        compileTerm cΓₛ aₛ compilesTermTo aₜ →
        compileTerm cΓₛ []bₛ compilesTermTo bₜ →
        compileTerm ((((cΓₛ S., Aₛ 𝕢 ω) S., S.List Aₛ 𝕢 ω) S., sP 𝕢 ω)) ∷bₛ compilesTermTo cₜ →
        compileTerm cΓₛ (S.eliml aₛ ty∶ Aₛ P∶ sP 
                nb∶ []bₛ 
                cb∶ ∷bₛ) 
            compilesTermTo 
        (T.eliml aₜ 
            nb∶ bₜ 
            cb∶ cₜ) 
    lemmaElimComps = {!   !}


    -- postulate??
    lemmaElimTarg : ∀ {tn bₜ} →
        tn ↔te (cₜ T.[ i / T.nill ]) →
        -- does the i have to be suc suc ?
        bₜ ↔te (cₜ T.[ i / T.var 2 T.∷l T.var 1 ]) →
        (T.eliml T.var i 
            nb∶ tn 
            cb∶ bₜ) 
        ↔te cₜ
    lemmaElimTarg nilExt consExt = {!   !}

    invertElimListVar : 
        (compileTerm cΓₛ 
            (S.eliml S.var x ty∶ Aₛ P∶ sP 
                nb∶ []bₛ 
                cb∶ ∷bₛ)) 
            compilesTermTo aₜ →
        (compileTerm cΓₛ (S.var x) compilesTermTo {! T.[]  !}) ⊎ (compileTerm cΓₛ (S.var x) compilesTermTo {!   !})
open ElimExt


~ᵣtermproof :
    (cΓₛ : S.Context Γₛ) →
    aₛ ~ᵣ cₛ → 
    (compileTerm cΓₛ aₛ) compilesTermTo aₜ →
    (compileTerm cΓₛ cₛ) compilesTermTo cₜ → 
    aₜ ↔te cₜ
~ᵣtermproof {aₛ = aₛ} {aₜ = aₜ} {cₜ} cΓₛ S.~ᵣrefl aComps cComps = 
    Te.compIsDeterministic 
        (compileTerm cΓₛ aₛ) 
        aComps cComps
~ᵣtermproof cΓₛ (S.~ᵣsym ~) aComps cComps = Te.lemmaSym (~ᵣtermproof cΓₛ ~ cComps aComps)
-- Kind of a workaround no? Need general lemma to introduce new intermediate terms to compile (or not)? 
-- Except if B fails to compile it dont really matter here :/
~ᵣtermproof cΓₛ (S.~ᵣtrans {B = B} ~ ~₁) aComps cComps = {!   !}
{- 
    Te.lemmaTrans 
        -- missing proof of compilation for B (intermediate term)
        -- funext? for all B this holds
        (~ᵣtermproof cΓₛ ~ aComps {!   !}) 
        (~ᵣtermproof cΓₛ ~₁ {!   !} cComps)
-}
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣs {n} {m} ~) aComps cComps = 
    Te.lemmaBindBase (compileTerm cΓₛ n) (compileTerm cΓₛ m) (λ aₜ₁ → just (T.s aₜ₁)) aComps cComps 
        λ nComps mComps → ~ᵣtermproof cΓₛ ~ nComps mComps
~ᵣtermproof cΓₛ (S.~ᵣ∷l {a} {c} {as} {cs} ~h ~t) aComps cComps = 
    Te.lemmaBindInd 
        -- ma mb
        (compileTerm cΓₛ a) (compileTerm cΓₛ c) 
        -- bodies
        (λ aₜ₁ → compileTerm cΓₛ as >>= (λ aₜs → just (aₜ₁ T.∷l aₜs))) (λ aₜ₁ → compileTerm cΓₛ cs >>= (λ aₜs → just (aₜ₁ T.∷l aₜs))) 
        -- bindComps
        aComps cComps 
        (λ hlComps hrComps → ~ᵣtermproof cΓₛ ~h hlComps hrComps) 
        λ res tlCompBₛ trCompBₛ → 
            Te.lemmaBindBase 
                (compileTerm cΓₛ as) (compileTerm cΓₛ cs) 
                (λ aₜs → just (res T.∷l aₜs)) 
                tlCompBₛ trCompBₛ 
                (λ tlComps trComps → ~ᵣtermproof cΓₛ ~t tlComps trComps) 
~ᵣtermproof cΓₛ (S.~ᵣlamω {b} {c} {A = A} ~) aComps cComps =   
    Te.lemmaBindBase 
        (compileTerm (cΓₛ S., A 𝕢 ω) b) (compileTerm (cΓₛ S., A 𝕢 ω) c) 
        (λ bₜody → just (T.ƛ bₜody)) 
        aComps cComps 
        λ bodyCompL bodyCompR → ~ᵣtermproof (cΓₛ S., A 𝕢 ω) ~ bodyCompL bodyCompR 
-- Either convert compilesTermTo or make lemma that aₜkes it into account
-- some rewrite lemma based on aₜrget?
~ᵣtermproof {cₛ = cₛ} cΓₛ (S.~ᵣlam𝟘 {A = A} ~) bComps cComps = 
    ~ᵣtermproof (cΓₛ S., A 𝕢 𝟘) ~ bComps (lemmaWeakenTerm cₛ cΓₛ zero z≤n A cComps) 
~ᵣtermproof cΓₛ S.~ᵣlamr aComps cComp = 
    Te.compIsDeterministic 
        (just (T.ƛ (T.var 0))) 
        aComps cComp
~ᵣtermproof cΓₛ (S.~ᵣappω {b} {d} {a} {c} ~ ~₁) bBindComps dBindComps = 
    Te.lemmaBindInd 
        (compileTerm cΓₛ b) (compileTerm cΓₛ d)
        (λ tf → compileTerm cΓₛ a >>= (λ aₜ₁ → just (tf T.· aₜ₁))) (λ tf → compileTerm cΓₛ c >>= (λ aₜ₁ → just (tf T.· aₜ₁))) 
        bBindComps dBindComps 
        (λ bComps dComps → ~ᵣtermproof cΓₛ ~ bComps dComps)
        λ res aBindComps cBindComps → 
            Te.lemmaBindBase 
                (compileTerm cΓₛ a) (compileTerm cΓₛ c)
                (λ aₜ₁ → just (res T.· aₜ₁)) 
                aBindComps cBindComps 
                λ {c = c₁} {d = d₁} → ~ᵣtermproof cΓₛ ~₁
~ᵣtermproof cΓₛ (S.~ᵣapp𝟘 ~) aComps cComps = ~ᵣtermproof cΓₛ ~ aComps cComps 
~ᵣtermproof {cₛ = cₛ} cΓₛ S.~ᵣappr aComps cComps = 
    Te.compIsDeterministic 
        (compileTerm cΓₛ cₛ)
        aComps cComps  
~ᵣtermproof cΓₛ S.~ᵣbetaω aComps cComps = {!   !}
~ᵣtermproof cΓₛ S.~ᵣnilvω aComps cComps = 
    Te.compIsDeterministic 
        (just T.nilv) 
        aComps cComps  
~ᵣtermproof cΓₛ S.~ᵣnilv𝟘 aComps cComps = 
    Te.compIsDeterministic 
        (just T.nill)         
        aComps cComps
~ᵣtermproof cΓₛ (S.~ᵣ∷vω {a} {c} {as} {cs} {n} {m} ~a ~as ~n) aBindComps cBindComps = 
    Te.lemmaBindInd 
        (compileTerm cΓₛ a) (compileTerm cΓₛ c) 
        body-a body-c  
        aBindComps cBindComps 
        (λ aComps cComps → ~ᵣtermproof cΓₛ ~a aComps cComps)  
        (λ resH aBₛindComps cBₛindComps → 
            Te.lemmaBindInd 
                (compileTerm cΓₛ as) (compileTerm cΓₛ cs) 
                (body-as resH) (body-cs resH)
                aBₛindComps cBₛindComps 
                (λ asComps csComps → ~ᵣtermproof cΓₛ ~as asComps csComps)  
                λ resT nBindComps mBindComps → 
                    Te.lemmaBindBase 
                        (compileTerm cΓₛ n) (compileTerm cΓₛ m) 
                        (body-base resH resT) 
                        nBindComps mBindComps 
                        λ nComps mComps → ~ᵣtermproof cΓₛ ~n nComps mComps)          
        where 
            body-base = λ aₜ aₜs tn → just (aₜ T.∷v aₜs 𝕟 tn)
            body-as = λ aₜ → (λ aₜs → compileTerm cΓₛ n >>= body-base aₜ aₜs)
            body-cs = λ aₜ → (λ aₜs → compileTerm cΓₛ m >>= body-base aₜ aₜs)
            body-a = (λ aₜ → compileTerm cΓₛ as >>= body-as aₜ)
            body-c = (λ aₜ → compileTerm cΓₛ cs >>= body-cs aₜ)
~ᵣtermproof cΓₛ (S.~ᵣ∷v𝟘 {a} {c} {as} {cs} ~a ~as) aBindComps cBindComps = 
    Te.lemmaBindInd 
        (compileTerm cΓₛ a) (compileTerm cΓₛ c)
        body-as body-cs 
        aBindComps cBindComps 
        (λ aComps cComps → ~ᵣtermproof cΓₛ ~a aComps cComps)
        λ res aBₛindComps cBₛindComps → 
            Te.lemmaBindBase 
                (compileTerm cΓₛ as) (compileTerm cΓₛ cs) 
                (body-base res) 
                aBₛindComps cBₛindComps 
                (λ asComps csComps → ~ᵣtermproof cΓₛ ~as asComps csComps)          
        where
            body-base =  λ aₜ aₜs → just (aₜ T.∷l aₜs)
            body-cs = λ aₜ → compileTerm cΓₛ cs >>= body-base aₜ  
            body-as = λ aₜ → compileTerm cΓₛ as >>= body-base aₜ
-- Might be example why I need option, need ∷b doesnt align with ∷b [ 0 / S.var 1]
-- Need lemmaEaₜ to consider different cₛ cases, here I need to be more observational stuff
-- funext on what var i is? or on result of substitution?
-- Maybe invert var i?
-- Invert to show aₜ = T.eliml then do funext on what var i (or lookup var i) can be
~ᵣtermproof {cₛ = cₛ} cΓₛ (S.~ᵣηlist {[]b} {i = i} {cb = ∷b} ~[]b ~∷b) bindComps cComps =
    lemmaElimLExt 
        cΓₛ 
        i 
        []b ∷b cₛ
        bindComps cComps 
        (λ []bComps c[]Comps → ~ᵣtermproof cΓₛ ~[]b []bComps c[]Comps) 
        λ ∷bComps c∷bComps → ~ᵣtermproof {!   !} ~∷b ∷bComps {!   !}
~ᵣtermproof cΓₛ (S.~ᵣηvec ~ ~₁) aComps cComps = {!   !}
---- Types
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣlist ~) aComps cComps = Te.compAbsurd {a = aₜ} aComps 
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣpiω ~ ~₁) aComps cComps = Te.compAbsurd {a = aₜ} aComps
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣpi𝟘 ~) aComps cComps = Te.compAbsurd {a = aₜ} aComps
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣpir ~) aComps cComps = Te.compAbsurd {a = aₜ} aComps
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣvecω ~ ~₁) aComps cComps = Te.compAbsurd {a = aₜ} aComps
~ᵣtermproof {aₜ = aₜ} cΓₛ (S.~ᵣvec𝟘 ~) aComps cComps = Te.compAbsurd {a = aₜ} aComps


lemmaWeakenType : 
    (Aₛ : S.Term) → 
    (i : ℕ) → 
    (l : ℕ) →
    compileType Aₛ compilesTypeTo Aₜ →
    compileType (S.shiftindices Aₛ i l) compilesTypeTo Aₜ
lemmaWeakenType S.Nat i l AₛComps = AₛComps
lemmaWeakenType (S.List A) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ Aₜ₁ → just (T.List Aₜ₁))
        bindComps
        λ {A = A₁} → lemmaWeakenType A i l
lemmaWeakenType (S.Vec A (n 𝕢 𝟘)) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ Aₜ₁ → just (T.List Aₜ₁))
        bindComps
        λ {A = A₁} → lemmaWeakenType A i l
lemmaWeakenType (S.Vec A (n 𝕢 ω)) i l bindComps = 
    Ty.lemmaBindSubstBase
        (compileType A) (compileType (S.shiftindices A i l))
        (λ Aₜ₁ → just (T.Vec Aₜ₁))
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
            body-base = λ Aₜ Bₜ → just (Aₜ T.⟶ Bₜ)
            body-B = λ Aₜ → compileType B >>= body-base Aₜ
            body-B↑ = λ Aₜ → compileType B↑ >>= body-base Aₜ
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
            body-base = λ Aₜ Bₜ → just (Aₜ T.⟶ Bₜ)
            body-B = λ Aₜ → compileType B >>= body-base Aₜ
            body-B↑ = λ Aₜ → compileType B↑ >>= body-base Aₜ

~ᵣtypeproof :
    Aₛ ~ᵣ Bₛ → 
    (compileType Aₛ) compilesTypeTo Aₜ →
    (compileType Bₛ) compilesTypeTo Bₜ →
    Aₜ ↔ty Bₜ
~ᵣtypeproof {Aₛ} S.~ᵣrefl AComps BComps = 
    Ty.compIsDeterministic (compileType Aₛ) AComps BComps
~ᵣtypeproof {Aₛ} (S.~ᵣsym ~) AComps BComps = Ty.lemmaSym (~ᵣtypeproof ~ BComps AComps)
~ᵣtypeproof {Aₛ} (S.~ᵣtrans ~ ~₁) AComps BComps = Ty.lemmaTrans (~ᵣtypeproof ~ AComps {!   !}) {!   !}
~ᵣtypeproof {S.List .A} (S.~ᵣlist {A} {B} ~) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ Aₜ₁ → just (T.List Aₜ₁))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~ AComps BComps
~ᵣtypeproof {Aₛ} (S.~ᵣpiω {A} {C} {B = B} {D} ~ ~₁) ABindComps CBindCompss = 
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
            body-base = λ Aₜ Bₜ → just (Aₜ T.⟶ Bₜ)
            body-D = λ Aₜ → compileType D >>= body-base Aₜ
            body-B = λ Aₜ → compileType B >>= body-base Aₜ
~ᵣtypeproof {Aₛ} {Bₛ} (S.~ᵣpi𝟘 {A = A} ~) AComps BComps =  
    ~ᵣtypeproof ~ AComps (lemmaWeakenType Bₛ 1 0 BComps)
~ᵣtypeproof {Aₛ} (S.~ᵣpir {A} {B} ~) ABindCompsₗ ABindCompsᵣ = 
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
            body-base = λ Aₜ Bₜ → just (Aₜ T.⟶ Bₜ)
            body-B = λ Aₜ → compileType B >>= body-base Aₜ
            body-A = λ Aₜ → compileType A >>= body-base Aₜ  
~ᵣtypeproof {Aₛ} (S.~ᵣvecω {A = A} {B} ~n ~A) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ Aₜ → just (T.Vec Aₜ))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~A AComps BComps
~ᵣtypeproof {Aₛ} (S.~ᵣvec𝟘 {A} {B} ~) ABindComps BBindComps = 
    Ty.lemmaBindBase
        (compileType A) (compileType B)
        (λ Aₜ → just (T.List Aₜ))
        ABindComps BBindComps
        λ AComps BComps → ~ᵣtypeproof ~ AComps BComps

    