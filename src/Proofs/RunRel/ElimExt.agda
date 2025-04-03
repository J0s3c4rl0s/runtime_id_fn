module Proofs.RunRel.ElimExt where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_;
    _↑_≥_)

open import Data.Nat
open import Data.Bool hiding (_≤_)

open import Data.Sum
open import Data.Product

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

    []bₛ ∷bₛ Pₛ : S.Term
    []bₜ ∷bₜ Pₜ : T.Term

_⊢⇒_ : 
    (cΓₛ : S.Context Γₛ) → 
    ContextRemap cΓₛ → Set
cΓₛ ⊢⇒ rΓ = compileRemap cΓₛ ≡ just rΓ

_⊢_↦_ : 
    (cΓₛ : S.Context Γₛ) → 
    ℕ → 
    ℕ →
    Set
-- Not sure if sigmas are annoying
cΓₛ ⊢ i ↦ j = 
    Σ[ rΓ ∈ ContextRemap cΓₛ ] 
        ((compileRemap cΓₛ ≡ just rΓ) × 
        remapIndex i rΓ ≡ just j)

_⊢_[_/_]⇒_[_/_] : 
    S.Context Γₛ → S.Term → ℕ → S.Term → 
    T.Term → ℕ → T.Term →
    Set
cΓₛ ⊢ aₛ [ i / bₛ ]⇒ aₜ [ j / bₜ ] = 
    (cΓₛ ⊢ aₛ ⇒ aₜ) × 
    (cΓₛ ⊢ bₛ ⇒ bₜ) × 
    -- Should I have a special rule for reindexing?
    (cΓₛ ⊢ i ↦ j) × 
    (cΓₛ ⊢ aₛ S.[ i / bₛ ] ⇒ (aₜ T.[ j / bₜ ]))

_⊢_[_/_]⇒ : S.Context Γₛ → S.Term → ℕ → S.Term → Set
cΓₛ ⊢ aₛ [ i / bₛ ]⇒ = 
    Σ[ aₜ ∈ T.Term ] 
        Σ[ j ∈ ℕ ] 
            Σ[ rΓ ∈ ContextRemap cΓₛ ] 
                Σ[ bₜ ∈ T.Term ] 
                    (cΓₛ ⊢ (aₛ S.[ i / bₛ ]) ⇒ (aₜ T.[ j / bₜ ]))   

substComp : 
    (aₛ : S.Term) →
    compileRemap cΓₛ ≡ just rΓ → 
    remapIndex i rΓ ≡ just l →
    cΓₛ ⊢ aₛ ⇒ aₜ →
    cΓₛ ⊢ bₛ ⇒ bₜ →
    cΓₛ ⊢ (aₛ S.[ i / bₛ ]) ⇒ (aₜ T.[ j / bₜ ])
substComp (S.var x) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.ƛ∶ x ♭ aₛ) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.ƛr∶ x ♭ aₛ) cΓₛComps remapEq aComps bComps = {!   !}
substComp (aₛ S.· aₛ₁ 𝕢 x) cΓₛComps remapEq aComps bComps = {!   !}
substComp (aₛ S.·ᵣ aₛ₁) cΓₛComps remapEq aComps bComps = {!   !}
substComp S.z cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.s aₛ) cΓₛComps remapEq aComps bComps = {!   !}
substComp S.nill cΓₛComps remapEq aComps bComps = {!   !}
substComp (aₛ S.∷l aₛ₁) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.nilv𝕢 x) cΓₛComps remapEq aComps bComps = {!   !}
substComp (aₛ S.∷v aₛ₁ 𝕟 aₛ₂ 𝕢 x) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.elimnat aₛ P∶ aₛ₁ zb∶ aₛ₂ sb∶ aₛ₃) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.eliml aₛ ty∶ innerty P∶ aₛ₁ nb∶ aₛ₂ cb∶ aₛ₃) cΓₛComps remapEq aComps bComps = {!   !}
substComp (S.elimv x ty∶ innerty P∶ aₛ nb∶ aₛ₁ cb∶ aₛ₂) cΓₛComps remapEq aComps bComps = {!   !}




list[]Comp : 
    (cₛ : S.Term) →
    compileRemap cΓₛ ≡ just rΓ → 
    remapIndex i rΓ ≡ just l →
    cΓₛ ⊢ cₛ ⇒ cₜ →
    cΓₛ ⊢ cₛ S.[ i / S.nill ] ⇒ (cₜ T.[ l / T.nill ])
list[]Comp {cΓₛ = cΓₛ} {rΓ} {i = i} {l} {cₜ = cₜ} cₛ cΓₛComps remapEq cₛComps = {!   !}
    where
        rel : cΓₛ ⊢ cₛ [ i / S.nill ]⇒ cₜ [ l / T.nill ]
        rel = 
            cₛComps , 
            (refl , 
            ((rΓ , cΓₛComps , remapEq) , 
            {!   !}))
-- 
listConsComp : 
    (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ ∷bₛ ⇒ ∷bₜ →
    -- What should result be? Perhaps give substitution with updated index?
    (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ ∷bₛ S.[ 0 / S.var 1 ] ⇒ (∷bₜ T.[ 0 / (T.var 1) ])
listConsComp = {!   !}

tmp : 
    (cΓₛ S., Aₛ 𝕢 ω S., S.List (Aₛ ↑ 1 ≥ 0) 𝕢 ω S., (Pₛ ↑ 1 ≥ 1) 𝕢 ω) ⊢ 
        (cₛ ↑ 3 ≥ 0) S.[ (3 + i) / S.var 2 S.∷l S.var 1 ] ⇒ ((cₜ T.↑ 3 ≥ 0) T.[ (3 + n) / T.var 2 T.∷l T.var 1 ])
tmp = {!   !} 