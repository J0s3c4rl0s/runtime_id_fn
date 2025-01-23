module ListCalc.STLC.Examples where

open import ListCalc.STLC.Syntax
open import ListCalc.STLC.TypeRules

idNatTy : Type
idNatTy = Nat ⟶ Nat

idNatDef : Term
idNatDef = ƛ var 0

idNatTyped : [] ⊢ idNatDef ∶ idNatTy
idNatTyped = ⊢lam (⊢var Z)