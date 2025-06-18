module Proofs.RunRel.Weakening where

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)


open import Data.Bool using (if_then_else_; Bool)

open import Data.Nat
open import Data.Nat.Properties using (+-comm)

open import Data.Maybe
open import Relation.Binary.PropositionalEquality

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

abstract
