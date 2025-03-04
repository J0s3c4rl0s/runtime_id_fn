module STLC.Examples where

open import STLC.Syntax
open import STLC.TypeRules

idNatTy : Type
idNatTy = Nat ⟶ Nat

idNatDef : Term
idNatDef = ƛ var 0

idNatTyped : [] ⊢ idNatDef ∶ idNatTy
idNatTyped = ⊢lam (⊢var Z)