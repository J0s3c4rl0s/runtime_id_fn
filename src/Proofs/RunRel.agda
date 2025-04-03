module Proofs.RunRel where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations
open import Proofs.RunRel.Weakening

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_;
    _↑_≥_)

open import Data.Nat
open import Data.Bool hiding (_≤_)
open import Data.Sum
open import Data.Maybe
open import Data.Maybe.Properties 
open import Data.Empty

open import Relation.Binary.PropositionalEquality 
open import Relation.Nullary

private variable
    A B : Set

    Γₛ : S.PreContext
    cΓₛ : S.Context Γₛ
    Aₛ Bₛ Cₛ : S.Type
    aₛ bₛ cₛ asₛ bsₛ fₛ : S.Term
    σ π ρ : S.Quantity

    i l j k x n m : ℕ

    rΓ rΓ' : ContextRemap cΓₛ

    Aₜ Bₜ Cₜ : T.Type
    aₜ bₜ cₜ : T.Term
    

module ElimExt where
    open import Data.Product
    private variable
        []bₛ ∷bₛ Pₛ : S.Term
        []bₜ ∷bₜ Pₜ : T.Term

    
    list[]Comp : 
        (cₛ : S.Term) →
        compileRemap cΓₛ ≡ just rΓ → 
        remapIndex i rΓ ≡ just l →
        cΓₛ ⊢ cₛ ⇒ cₜ →
        cΓₛ ⊢ cₛ S.[ i / S.nill ] ⇒ (cₜ T.[ l / T.nill ])
    list[]Comp cₛ cΓₛComps remapEq cₛComps = {!   !}

    -- 
    listConsComp : 
        (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ ∷bₛ ⇒ ∷bₜ →
        -- What should result be? Perhaps give substitution with updated index?
        (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ ∷bₛ S.[ 0 / S.var 1 ] ⇒ (∷bₜ T.[ 0 / (T.var 1) ])

    tmp : 
        (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ 
            (cₛ ↑ 3 ≥ 0) S.[ (3 + i) / S.var 2 S.∷l S.var 1 ] ⇒ ((cₜ T.↑ 3 ≥ 0) T.[ (3 + n) / T.var 2 T.∷l T.var 1 ])


open ElimExt
open import Data.Product

~ᵣtermproof :
    (cΓₛ : S.Context Γₛ) →
    aₛ ~ᵣ cₛ → 
    cΓₛ ⊢ aₛ ⇒ aₜ →
    cΓₛ ⊢ cₛ ⇒ cₜ → 
    aₜ ↔te cₜ
~ᵣtermproof cΓₛ S.~ᵣrefl aComps cComps 
    rewrite aComps | just-injective cComps = 
        Te.lemmaRefl
~ᵣtermproof cΓₛ (S.~ᵣsym ~) aComps cComps = 
    Te.lemmaSym (~ᵣtermproof cΓₛ ~ cComps aComps)
~ᵣtermproof cΓₛ (S.~ᵣtrans ~ ~₁) aComps cComps = 
    {!   !} 
~ᵣtermproof cΓₛ (S.~ᵣs {nₛ} {mₛ} ~) lComps rComps 
    with compileTerm cΓₛ nₛ in nComps |  compileTerm cΓₛ mₛ in mComps  
... | just nₜ | just mₜ
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Te.s-cong (~ᵣtermproof cΓₛ ~ nComps mComps)
~ᵣtermproof cΓₛ (S.~ᵣ∷l {aₛ} {cₛ} {asₛ} {csₛ} ~a ~as) lComps rComps 
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ cₛ in cComps
... | just aₜ | just cₜ  
        with compileTerm cΓₛ asₛ in asComps |  compileTerm cΓₛ csₛ in csComps  
...     | just asₜ | just csₜ  
            rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
                Te.∷l-cong 
                    (~ᵣtermproof cΓₛ ~a aComps cComps) 
                    (~ᵣtermproof cΓₛ ~as asComps csComps)
~ᵣtermproof {aₛ = S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ} {cₛ} {aₜ} cΓₛ (S.~ᵣlam𝟘 ~) lComps rComps 
    with compileTerm (cΓₛ S., Aₛ 𝕢 𝟘) aₛ in aComps
... | just aₜ 
        rewrite just-injective (sym lComps) = 
            ~ᵣtermproof (cΓₛ S., Aₛ 𝕢 𝟘) ~ aComps (lemmaWeakenTerm cₛ cΓₛ 0 z≤n Aₛ rComps)
~ᵣtermproof {aₛ = S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ} {S.ƛ∶ .Aₛ 𝕢 ω ♭ cₛ} cΓₛ (S.~ᵣlamω ~) lComps rComps 
    with compileTerm (cΓₛ S., Aₛ 𝕢 ω) aₛ in aComps | compileTerm (cΓₛ S., Aₛ 𝕢 ω) cₛ in cComps 
... | just aₜ | just cₜ 
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Te.ƛ-cong (~ᵣtermproof (cΓₛ S., Aₛ 𝕢 ω) ~ aComps cComps)
~ᵣtermproof {aₛ = S.ƛr∶ Aₛ ♭ aₛ} {S.ƛr∶ .Aₛ ♭ cₛ} cΓₛ S.~ᵣlamr refl refl = Te.lemmaRefl
~ᵣtermproof {aₛ = fₛ S.· aₛ 𝕢 𝟘} cΓₛ (S.~ᵣapp𝟘 ~) lComps rComps
    with compileTerm cΓₛ fₛ in fComps
... | just fₜ
        rewrite just-injective (sym lComps) =
             ~ᵣtermproof cΓₛ ~ fComps rComps
~ᵣtermproof {aₛ = fₛ S.· aₛ 𝕢 ω} cΓₛ (S.~ᵣappω {d = gₛ} {c = cₛ} ~f ~a) lComps rComps
-- Invert subresults of compilation 
    with compileTerm cΓₛ fₛ in fComps | compileTerm cΓₛ gₛ in gComps
... | just fₜ | just dₜ 
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ cₛ  in cComps
...     | just aₜ | just cₜ
-- Rewrite target to be composition of subresults
            rewrite sym (just-injective lComps) | sym (just-injective rComps) = 
                Te.·-cong 
                    (~ᵣtermproof cΓₛ ~f fComps gComps) 
                    (~ᵣtermproof cΓₛ ~a aComps cComps)
~ᵣtermproof {aₛ = fₛ S.· aₛ 𝕢 ω} cΓₛ S.~ᵣbetaω lComps rComps = {!   !}
~ᵣtermproof {aₛ = fₛ S.·ᵣ aₛ} cΓₛ S.~ᵣappr lComps rComps 
    with compileTerm cΓₛ aₛ in aComps
... | just fₜ
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Te.lemmaRefl
~ᵣtermproof {aₛ = S.nilv𝕢 𝟘} cΓₛ S.~ᵣnilv𝟘 refl refl = 
    Te.lemmaRefl
~ᵣtermproof {aₛ = aₛ S.∷v asₛ 𝕟 nₛ 𝕢 𝟘} cΓₛ (S.~ᵣ∷v𝟘 {c = cₛ} {cs = csₛ} ~a ~as) lComps rComps
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ cₛ in cComps
... | just aₜ | just cₜ  
        with compileTerm cΓₛ asₛ in asComps |  compileTerm cΓₛ csₛ in csComps  
...     | just asₜ | just csₜ  
            rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
                Te.∷l-cong 
                    (~ᵣtermproof cΓₛ ~a aComps cComps) 
                    (~ᵣtermproof cΓₛ ~as asComps csComps)
~ᵣtermproof {aₛ = aₛ S.∷v asₛ 𝕟 nₛ 𝕢 ω} cΓₛ (S.~ᵣ∷vω {c = cₛ} {cs = csₛ} {m = mₛ} ~a ~as ~n) lComps rComps
    with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ cₛ in cComps
... | just aₜ | just cₜ  
        with compileTerm cΓₛ asₛ in asComps |  compileTerm cΓₛ csₛ in csComps  
...     | just asₜ | just csₜ 
            with compileTerm cΓₛ nₛ in nComps |  compileTerm cΓₛ mₛ in mComps
...         | just nₜ | just mₜ 
                rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
                    Te.∷v-cong 
                        (~ᵣtermproof cΓₛ ~a aComps cComps) 
                        (~ᵣtermproof cΓₛ ~as asComps csComps) 
                        (~ᵣtermproof cΓₛ ~n nComps mComps)
~ᵣtermproof {aₛ = S.eliml .(S.var i) ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ} {cₛ} cΓₛ (S.~ᵣηlist {i = i} ~[] ~∷) lComps rComps -- = {!   !}
-- varComps needs to be done manually, get rΓ then get reindex 
    with compileRemap cΓₛ in cΓComps
... | just rΓ 
        with remapIndex i rΓ in remapEq
...     | just n
            with compileTerm cΓₛ []bₛ in []bComps
...         | just []bₜ 
                with compileTerm 
                    (cΓₛ S., 
                        Aₛ 𝕢 ω S., 
                        S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S.,
                        (Pₛ ↑ 1 ≥ 1) 𝕢 ω) 
                    ∷bₛ in ∷bComps
...             | just ∷bₜ  
                    rewrite sym (just-injective lComps) = 
                        Te.elimlη 
                            (~ᵣtermproof cΓₛ ~[] []bComps (list[]Comp cₛ cΓComps remapEq rComps)) 
                            tmp∷
                        where
                            tmp[] = ~ᵣtermproof cΓₛ ~[] []bComps (list[]Comp cₛ cΓComps remapEq rComps)
                            -- what is implied context on either side of this?
                            tmp∷ = 
                                ~ᵣtermproof 
                                    ((cΓₛ S., 
                                            Aₛ 𝕢 ω S., 
                                            S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S.,
                                            (Pₛ ↑ 1 ≥ 1) 𝕢 ω)) 
                                    ~∷ 
                                    (listConsComp ∷bComps) -- (consComp ∷bComps) 
                                    {!   !}
~ᵣtermproof {aₛ = S.elimv x ty∶ innerty P∶ aₛ nb∶ aₛ₁ cb∶ aₛ₂} cΓₛ (S.~ᵣηvec ~ ~₁) lComps rComps = {!   !}


~ᵣtypeproof :
    Aₛ ~ᵣ Cₛ → 
    Aₛ ⇒ Aₜ →
    Cₛ ⇒ Cₜ → 
    Aₜ ↔ty Cₜ
~ᵣtypeproof S.~ᵣrefl lComps rComps 
    rewrite lComps | just-injective rComps = Ty.lemmaRefl
~ᵣtypeproof (S.~ᵣsym ~) lComps rComps = 
    Ty.lemmaSym (~ᵣtypeproof ~ rComps lComps)
~ᵣtypeproof (S.~ᵣtrans ~ ~₁) lComps rComps = {!   !}
~ᵣtypeproof {S.List Aₛ} (S.~ᵣlist {B = Bₛ} ~) lComps rComps
    with compileType Aₛ in AComps | compileType Bₛ in BComps
... | just Aₜ | just Bₜ
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Ty.List-cong (~ᵣtypeproof ~ AComps BComps)
~ᵣtypeproof {S.Vec Aₛ (nₛ 𝕢 𝟘)} (S.~ᵣvec𝟘 {B = Bₛ} ~) lComps rComps
    with compileType Aₛ in AComps | compileType Bₛ in BComps
... | just Aₜ | just Bₜ
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Ty.List-cong (~ᵣtypeproof ~ AComps BComps)
~ᵣtypeproof {S.Vec Aₛ (nₛ 𝕢 ω)} (S.~ᵣvecω {m = mₛ} {B = Bₛ} ~n ~A) lComps rComps
    with compileType Aₛ in AComps | compileType Bₛ in BComps
... | just Aₜ | just Bₜ
        rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
            Ty.Vec-cong (~ᵣtypeproof ~A AComps BComps)
~ᵣtypeproof {S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ} {Cₛ} (S.~ᵣpi𝟘 ~) lComps rComps 
    with compileType Bₛ in BComps 
... | just Bₜ 
        rewrite just-injective (sym lComps) =    
            ~ᵣtypeproof ~ BComps (lemmaWeakenType Cₛ 1 0 rComps)
~ᵣtypeproof {S.∶ Aₛ 𝕢 ω ⟶ Bₛ} (S.~ᵣpiω {C = Cₛ} {D = Dₛ} ~A ~B) lComps rComps  
    with compileType Aₛ in AComps | compileType Cₛ in CComps 
... | just Aₜ | just Cₜ
        with compileType Bₛ in BComps | compileType Dₛ in DComps 
...     | just Bₜ | just Dₜ
            rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
                Ty.⟶-cong 
                    (~ᵣtypeproof ~A AComps CComps) 
                    (~ᵣtypeproof ~B BComps DComps)
~ᵣtypeproof {S.r∶ Aₛ ⟶ Bₛ} (S.~ᵣpir ~) lComps rComps  
    with compileType Aₛ in AComps 
... | just Aₜ 
        with compileType Bₛ in BComps 
...     | just Bₜ
            rewrite just-injective (sym lComps) | just-injective (sym rComps) = 
                Ty.⟶-cong 
                    Ty.lemmaRefl   
                    (Ty.lemmaSym (~ᵣtypeproof ~ AComps BComps))  