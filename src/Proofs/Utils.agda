module Proofs.Utils where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

open import Data.Nat


private variable
    sΓ sΔ : S.PreContext
    scΓ : S.Context sΓ
    scΔ : S.Context sΔ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term

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