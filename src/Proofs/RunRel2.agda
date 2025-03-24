module Proofs.RunRel2 where

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
open import Data.Product
open import Data.Maybe -- using (Maybe; just; nothing; _>>=_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Equality.Rewrite


~ᵣtermproof : ∀ {sΓ sa sc ta tc} →
    (scΓ : S.Context sΓ) →
    sa ~ᵣ sc →
    (scΓ ⊢ sa ⇒te ta) →  
    (scΓ ⊢ sc ⇒te tc) → 
    ta ↔te tc
~ᵣtermproof {sa = sa} scΓ S.~ᵣrefl aComps cComps = Te.TeDeterministic scΓ sa aComps cComps 
~ᵣtermproof scΓ (S.~ᵣsym ~) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣtrans ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣs ~) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣ∷l ~ ~₁) aComps cComps = {!   !}
~ᵣtermproof scΓ (S.~ᵣlamω ~) aComps cComps = {!   !}
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