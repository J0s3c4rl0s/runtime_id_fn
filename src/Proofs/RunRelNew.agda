module Proofs.RunRelNew where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

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

    i l j k x : ℕ

    rΓ rΓ' : ContextRemap cΓₛ

    Aₜ Bₜ Cₜ : T.Type
    aₜ bₜ cₜ : T.Term


module Weakening where
    open import Data.Nat.Properties using (+-comm)
    
    if-injective :
        (cond : Bool) →
        (cons : A → B) →
        (x₁ x₂ : A) →
        (if cond then cons x₁ else cons x₂) 
            ≡ 
        cons (if cond then x₁ else x₂)
    if-injective  Bool.false _ _ _ = refl
    if-injective  Bool.true _ _ _ = refl
    
    ≤b-injective : (suc i ≤ᵇ suc j) ≡ (i ≤ᵇ j)
    ≤b-injective {zero} {j} = refl
    ≤b-injective {suc i} {j} = refl

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
        (compileRemap cΓₛ >>= (λ rΓ₁ → compileType Aₛ >>= (λ Aₜ → just (rΓ₁ ,ᵣ Aₛ ↦ Aₜ)))) 
            ≡ 
        just (rΓ ,ᵣ Aₛ ↦ Aₜ) →
        compileRemap cΓₛ ≡ just rΓ
    invertRemapAss₁ {cΓₛ = S.[]} {rΓ = []ᵣ} bindComps = refl
    invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 𝟘} {Aₛ} {rΓ = rΓ ,ᵣ .A skip} bindComps with compileRemap cΓₛ | compileType Aₛ
    ... | just rΓ' | just Aₜ'
            rewrite ,ᵣass-injective₁ bindComps = refl
    invertRemapAss₁ {cΓₛ = cΓₛ S., A 𝕢 ω} {Aₛ} {rΓ = rΓ ,ᵣ .A ↦ Aₜ} bindComps with compileRemap cΓₛ | compileType A | compileType Aₛ
    ... | just rΓ' | just Aₜ' | just _ 
            rewrite ,ᵣass-injective₁ bindComps = refl


    -- Could avoid inversion business if I just with abstract the recursive compilation?
    lemmaRemap : ∀ {p} {rΓ : ContextRemap cΓₛ} {rΓ↑ : ContextRemap (S.insertType cΓₛ i p Bₛ 𝟘)} →
        (x : ℕ) →
        compileRemap cΓₛ ≡ just rΓ →
        compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ just rΓ↑ →
        remapIndex x rΓ ≡ remapIndex (if i ≤ᵇ x then (x + 1) else x) rΓ↑
    lemmaRemap {cΓₛ = _} {i = zero} {p = z≤n} {rΓ↑ = rΓ↑ ,ᵣ Aₛ skip} x cΓₛComps cΓₛ↑Comps
        rewrite cΓₛComps | ,ᵣskip-injective₁ cΓₛ↑Comps | +-comm x 1 = refl 
    lemmaRemap 
        {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip} 
        zero cΓₛComps cΓₛ↑Comps = refl
    lemmaRemap 
        {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ Aₜ₁}
        zero cΓₛComps cΓₛ↑Comps = refl
    lemmaRemap
        {cΓₛ = cΓₛ S., A 𝕢 𝟘} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A skip} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) skip}
        (suc x) cΓₛComps cΓₛ↑Comps 
        rewrite ≤b-injective {i = i} {j = x} | if-injective (i ≤ᵇ x) suc (x + 1) x = 
            lemmaRemap x (invertRemapSkip cΓₛComps) (invertRemapSkip cΓₛ↑Comps)
    lemmaRemap 
        {cΓₛ = cΓₛ S., A 𝕢 ω} {i = suc i} {p = s≤s p} {rΓ ,ᵣ .A ↦ Aₜ} {rΓ↑ ,ᵣ .(S.shiftindices A 1 i) ↦ Aₜ₁}
        (suc x) cΓₛComps cΓₛ↑Comps
        rewrite ≤b-injective {i = i} {j = x} | if-injective (i ≤ᵇ x) suc (x + 1) x
            rewrite lemmaRemap x (invertRemapAss₁ cΓₛComps) (invertRemapAss₁ cΓₛ↑Comps) = refl
    
    A↑MustCompile : 
        (Aₛ : S.Term) →
        (i : ℕ) → 
        (l : ℕ) →
        -- change this to other formulation?
        compileType Aₛ ≡ just Aₜ →
        ¬ (compileType (S.shiftindices Aₛ i l) ≡ nothing)
    A↑MustCompile S.Nat i l AComps = λ ()
    A↑MustCompile (S.List Aₛ) i l ListComps _
        with compileType Aₛ in AComps | compileType (S.shiftindices Aₛ i l) in A↑Comps
    ... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
    A↑MustCompile (S.Vec Aₛ (nₛ 𝕢 𝟘)) i l VecComps _
        with compileType Aₛ in AComps | compileType (S.shiftindices Aₛ i l) in A↑Comps
    ... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps 
    A↑MustCompile (S.Vec Aₛ (nₛ 𝕢 ω)) i l VecComps _
        with compileType Aₛ in AComps | compileType (S.shiftindices Aₛ i l) in A↑Comps
    ... | just Aₜ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
    A↑MustCompile (S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ) i l AComps = 
        A↑MustCompile Bₛ i (suc l) AComps
    A↑MustCompile (S.∶ Aₛ 𝕢 ω ⟶ Bₛ) i l FunComps _
    -- Either A or B fails (which neither of them can)
        with compileType Aₛ in AComps | compileType (S.shiftindices Aₛ i l) in A↑Comps
    ... | just _ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
    ... | just _ | just _
            with compileType Bₛ in BComps | compileType (S.shiftindices Bₛ i (suc l)) in B↑Comps
    ...     | just _ | nothing  = A↑MustCompile Bₛ i (suc l) BComps B↑Comps
    A↑MustCompile (S.r∶ Aₛ ⟶ Bₛ) i l FunComps _
    -- Either A or B fails (which neither of them can)
        with compileType Aₛ in AComps | compileType (S.shiftindices Aₛ i l) in A↑Comps
    ... | just _ | nothing = A↑MustCompile Aₛ i l AComps A↑Comps
    ... | just _ | just _
            with compileType Bₛ in BComps | compileType (S.shiftindices Bₛ i (suc l)) in B↑Comps
    ...     | just _ | nothing  = A↑MustCompile Bₛ i (suc l) BComps B↑Comps

    rΓ↑MustCompile : ∀ {cΓₛ : S.Context Γₛ} {rΓ : ContextRemap cΓₛ} →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        (Bₛ : S.Type) →
        compileRemap cΓₛ ≡ just rΓ →
        ¬ (compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) ≡ nothing)
    rΓ↑MustCompile {cΓₛ = cΓₛ} zero z≤n Bₛ cΓComps cΓ↑DoesntComp 
        with compileRemap cΓₛ
    rΓ↑MustCompile {cΓₛ = cΓₛ} zero z≤n Bₛ cΓComps () | just rΓ
    rΓ↑MustCompile {cΓₛ = cΓₛ S., A 𝕢 𝟘} (suc i) (s≤s p) Bₛ cΓEComps cΓ↑DoesntComp 
        with compileRemap cΓₛ in cΓComps | compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in cΓ↑Comps
    ... | just _ | nothing = 
            rΓ↑MustCompile i p Bₛ cΓComps cΓ↑Comps
    rΓ↑MustCompile {cΓₛ = cΓₛ S., Aₛ 𝕢 ω} (suc i) (s≤s p) Bₛ cΓEComps cΓ↑DoesntComp
        with compileRemap cΓₛ in cΓComps | compileType Aₛ in AComps
    ... | just _ | just _  
            with compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in cΓ↑Comps | compileType (S.shiftindices Aₛ 1 i) in A↑Comps
    ...     | nothing | _ = rΓ↑MustCompile i p Bₛ cΓComps cΓ↑Comps
    ...     | just _ | nothing = A↑MustCompile Aₛ 1 i AComps A↑Comps

    lemmaWeakenTerm : 
        (aₛ : S.Term) → 
        (cΓₛ : S.Context Γₛ) →
        (i : ℕ) → 
        (p : i ≤ S.conLen Γₛ) →
        (Bₛ : S.Type) →
        cΓₛ ⊢ aₛ ⇒ aₜ →
        (S.insertType cΓₛ i p Bₛ 𝟘)  ⊢ (S.shiftindices aₛ 1 i) ⇒ aₜ
    ---- Var
    lemmaWeakenTerm (S.var x) cΓₛ i p Bₛ lComps 
        rewrite if-injective (i ≤ᵇ x) S.var (x + 1) x with compileRemap cΓₛ in rΓComps | compileRemap (S.insertType cΓₛ i p Bₛ 𝟘) in rΓ↑Comps
    ... | just rΓ | just rΓ↑
        rewrite lemmaRemap x rΓComps rΓ↑Comps = lComps
    -- prove absurd somehow
    ... | just rΓ | nothing = contradiction rΓ↑Comps (rΓ↑MustCompile i p Bₛ rΓComps)
    -- Inductive cases
    lemmaWeakenTerm {aₜ = aₜ} (S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 𝟘) aₛ in aComps
    lemmaWeakenTerm {aₜ = aₜ} (S.ƛ∶ Aₛ 𝕢 𝟘 ♭ aₛ) cΓₛ i p Bₛ refl | just .aₜ = 
        lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 𝟘) (suc i) (s≤s p) Bₛ aComps
    lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 ω) aₛ in aComps
    lemmaWeakenTerm (S.ƛ∶ Aₛ 𝕢 ω ♭ aₛ) cΓₛ i p Bₛ refl | just aₜ 
        rewrite lemmaWeakenTerm aₛ (cΓₛ S., Aₛ 𝕢 ω) (suc i) (s≤s p) Bₛ aComps = refl
    lemmaWeakenTerm (S.ƛr∶ Aₛ ♭ aₛ) cΓₛ i p Bₛ lComps with compileTerm (cΓₛ S., Aₛ 𝕢 𝟘) aₛ
    ... | _ = lComps
    lemmaWeakenTerm (fₛ S.· aₛ 𝕢 𝟘) cΓₛ i p Bₛ lComps = 
        lemmaWeakenTerm fₛ cΓₛ i p Bₛ lComps
    lemmaWeakenTerm (fₛ S.· aₛ 𝕢 ω) cΓₛ i p Bₛ lComps with compileTerm cΓₛ fₛ in fComps |  compileTerm cΓₛ aₛ in aComps 
    ... | just fₜ | just aₜ
        rewrite lemmaWeakenTerm fₛ cΓₛ i p Bₛ fComps 
            |  lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps = lComps 
    lemmaWeakenTerm (fₛ S.·ᵣ aₛ) cΓₛ i p Bₛ lComps = 
        lemmaWeakenTerm aₛ cΓₛ i p Bₛ lComps
    lemmaWeakenTerm (S.s aₛ) cΓₛ i p Bₛ lComps with compileTerm cΓₛ aₛ in aComps
    ... | just aₜ 
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps = 
                lComps
    lemmaWeakenTerm (aₛ S.∷l asₛ) cΓₛ i p Bₛ lComps 
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps
    ... | just aₜ | just asₜ
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps = 
                lComps
    lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 𝟘) cΓₛ i p Bₛ lComps 
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps
    ... | just aₜ | just asₜ
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps = 
                lComps
    lemmaWeakenTerm (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 ω) cΓₛ i p Bₛ lComps
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ asₛ in asComps | compileTerm cΓₛ nₛ in nComps
    ... | just aₜ | just asₜ | just nₜ 
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps 
                | lemmaWeakenTerm asₛ cΓₛ i p Bₛ asComps
                | lemmaWeakenTerm nₛ cΓₛ i p Bₛ nComps  = 
                    lComps
    lemmaWeakenTerm (S.elimnat aₛ P∶ Pₛ zb∶ zₛ sb∶ sₛ) cΓₛ i p Bₛ lComps
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ zₛ in zComps | compileTerm (((cΓₛ S., S.Nat S.𝕢 ω) S., Pₛ S.𝕢 ω)) sₛ in sComps
    ... | just aₜ | just zₜ | just sₜ 
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps 
                | lemmaWeakenTerm zₛ cΓₛ i p Bₛ zComps
                | lemmaWeakenTerm sₛ (((cΓₛ S., S.Nat S.𝕢 ω) S., Pₛ S.𝕢 ω)) (2+ i) (s≤s (s≤s p)) Bₛ sComps = 
                   lComps
    lemmaWeakenTerm (S.eliml aₛ ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ []bₛ in []bComps | compileTerm (((cΓₛ S., Aₛ S.𝕢 ω) S., S.List Aₛ S.𝕢 ω) S., Pₛ S.𝕢 ω) ∷bₛ in ∷bComps
    ... | just aₜ | just []bₜ | just ∷bₜ
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
                | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps
                -- Shifts dont align in the context, bug somewhere in shiftindices or 
                | lemmaWeakenTerm ∷bₛ (((cΓₛ S., Aₛ S.𝕢 ω) S., S.List Aₛ S.𝕢 ω) S., Pₛ S.𝕢 ω) (3 + i) (s≤s (s≤s (s≤s p))) Bₛ ∷bComps 
                = 
                -- Another bug somwhere, shifts dont align in the context (the expected one is wrong I think). Maybe bug in insertType or more likely shiftindices 
                    {!  S.insertType (((cΓₛ S., Aₛ S.𝕢 ω) S., S.List Aₛ S.𝕢 ω) S., Pₛ S.𝕢 ω) (3 + i) (s≤s (s≤s (s≤s p))) Bₛ 𝟘  !}
    lemmaWeakenTerm (S.elimv aₛ 𝕢 𝟘 ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ []bₛ in []bComps | compileTerm (((((cΓₛ S., S.Nat 𝕢 𝟘) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 𝟘) 𝕢 ω) S., Pₛ 𝕢 ω)) ∷bₛ in ∷bComps
    ... | just aₜ | just []bₜ | just ∷bₜ
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
                | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps 
                -- same problem as with previous, is there a bug in the compiler? in shiftindices?
                | lemmaWeakenTerm ∷bₛ (((((cΓₛ S., S.Nat 𝕢 𝟘) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 𝟘) 𝕢 ω) S., Pₛ 𝕢 ω)) (4 + i) (s≤s (s≤s (s≤s (s≤s p)))) Bₛ ∷bComps
                = 
                    {!  lemmaWeakenTerm ∷bₛ (((((cΓₛ S., S.Nat 𝕢 𝟘) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 𝟘) 𝕢 ω) S., Pₛ 𝕢 ω)) (4 + i) (s≤s (s≤s (s≤s (s≤s p)))) Bₛ ∷bComps  !}
    lemmaWeakenTerm (S.elimv aₛ 𝕢 ω ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ) cΓₛ i p Bₛ lComps
        with compileTerm cΓₛ aₛ in aComps | compileTerm cΓₛ []bₛ in []bComps | compileTerm (((((cΓₛ S., S.Nat 𝕢 ω) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 ω) 𝕢 ω) S., Pₛ 𝕢 ω)) ∷bₛ in ∷bComps
    ... | just aₜ | just []bₜ | just ∷bₜ
            rewrite lemmaWeakenTerm aₛ cΓₛ i p Bₛ aComps
                | lemmaWeakenTerm []bₛ cΓₛ i p Bₛ []bComps
                | lemmaWeakenTerm ∷bₛ (((((cΓₛ S., S.Nat 𝕢 ω) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 ω) 𝕢 ω) S., Pₛ 𝕢 ω)) (4 + i) (s≤s (s≤s (s≤s (s≤s p)))) Bₛ ∷bComps  
                = 
                    {! lemmaWeakenTerm ∷bₛ (((((cΓₛ S., S.Nat 𝕢 ω) S., Aₛ 𝕢 ω) S., S.Vec Aₛ (S.var 1 𝕢 ω) 𝕢 ω) S., Pₛ 𝕢 ω)) (4 + i) (s≤s (s≤s (s≤s (s≤s p)))) Bₛ ∷bComps  !} 
    ---- Base cases
    lemmaWeakenTerm S.nill cΓₛ i p Bₛ lComps = lComps
    lemmaWeakenTerm (S.nilv𝕢 𝟘) cΓₛ i p Bₛ lComps = lComps
    lemmaWeakenTerm (S.nilv𝕢 ω) cΓₛ i p Bₛ lComps = lComps
    lemmaWeakenTerm S.z cΓₛ i p Bₛ lComps = lComps

    lemmaWeakenType :
        (Cₛ : S.Type) →
        (i : ℕ) →
        (l : ℕ) →
        Cₛ ⇒ Cₜ →
        S.shiftindices Cₛ i l ⇒ Cₜ
    lemmaWeakenType S.Nat i l Comps = {!   !}
    lemmaWeakenType (S.List Aₛ) i l Comps 
        with compileType Aₛ in AComps
    ... | just Aₜ 
            rewrite lemmaWeakenType Aₛ i l AComps = 
                Comps
    lemmaWeakenType (S.Vec Aₛ (nₛ 𝕢 𝟘)) i l Comps 
        with compileType Aₛ in AComps
    ... | just Aₜ 
            rewrite lemmaWeakenType Aₛ i l AComps = 
                Comps  
    lemmaWeakenType (S.Vec Aₛ (nₛ 𝕢 ω)) i l Comps 
        with compileType Aₛ in AComps
    ... | just Aₜ 
            rewrite lemmaWeakenType Aₛ i l AComps = Comps
    lemmaWeakenType (S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ) i l Comps = {!   !}
    lemmaWeakenType (S.∶ Aₛ 𝕢 ω ⟶ Bₛ) i l Comps = {!   !}
    lemmaWeakenType (S.r∶ Aₛ ⟶ Bₛ) i l Comps = {!   !}

open Weakening

module ElimExt where
    open import Data.Product
    private variable
        []bₛ ∷bₛ Pₛ : S.Term

    
    lemmaElimL[] : 
        (cₛ : S.Term) →
        compileRemap cΓₛ ≡ just rΓ → 
        remapIndex i rΓ ≡ just l →
        cΓₛ ⊢ cₛ ⇒ cₜ →
        cΓₛ ⊢ cₛ S.[ i / S.nill ] ⇒ (cₜ T.[ l / T.nill ])


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
~ᵣtermproof {aₛ = S.eliml .(S.var i) ty∶ Aₛ P∶ Pₛ nb∶ []bₛ cb∶ ∷bₛ} {cₛ} cΓₛ (S.~ᵣηlist {i = i} ~[] ~∷) lComps rComps
-- varComps needs to be done manually, get rΓ then get reindex 
    with compileRemap cΓₛ in cΓComps
... | just rΓ 
        with remapIndex i rΓ in remapEq
...     | just n
            with compileTerm cΓₛ []bₛ in []bComps
...         | just []bₜ 
                with compileTerm (((cΓₛ S., Aₛ 𝕢 ω) S., S.List Aₛ 𝕢 ω) S., Pₛ 𝕢 ω) ∷bₛ in ∷bComps
...             | just ∷bₜ  
-- Probably need some extensionality principle, 
-- how to deal differing contexts and 
                    rewrite sym (just-injective lComps) = {!   !}
                    where
                        tmp[] = ~ᵣtermproof cΓₛ ~[] []bComps (lemmaElimL[] cₛ cΓComps remapEq rComps)
                        -- what is implied context on either side of this?
                        tmp∷ = ~ᵣtermproof {!   !} ~∷ {!   !} {!   !}
~ᵣtermproof {aₛ = S.elimv x ty∶ innerty P∶ aₛ nb∶ aₛ₁ cb∶ aₛ₂} cΓₛ (S.~ᵣηvec ~ ~₁) lComps rComps = {!   !}


~ᵣtypeproof :
    Aₛ ~ᵣ Cₛ → 
    Aₛ ⇒ Aₜ →
    Cₛ ⇒ Cₜ → 
    Aₜ ↔ty Cₜ
~ᵣtypeproof S.~ᵣrefl lComps rComps 
    rewrite lComps | just-injective rComps = Ty.lemmaRefl
~ᵣtypeproof (S.~ᵣsym ~) lComps rComps = {!   !}
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
~ᵣtypeproof {S.∶ Aₛ 𝕢 ω ⟶ Bₛ} (S.~ᵣpiω ~ ~₁) lComps rComps = {!   !}
~ᵣtypeproof {S.r∶ Aₛ ⟶ Bₛ} (S.~ᵣpir ~) lComps rComps = {!   !}