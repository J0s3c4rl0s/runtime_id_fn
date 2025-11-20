module Test where

open import Data.Nat
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Data.Product renaming (_,_ to _,p_)

open import Language
open import Semantics


private variable
    Γ : Context
    a a' : Term

    γ γ' : Env

    i : ℕ

proof : ∀ {Aᵣ} →
    -- Γ ⊨ a ∶ Aᵣ at i → 
    -- Γ ⊨ a' ∶ Aᵣ at i →
    a ~ᵣ a' → 
    γ ≅ γ' ∶⟦C Γ ⟧ → 
    -- (⟦ a ⟧ γ) ≅ ⟦ a' ⟧ γ' ∶ (⟦ Aᵣ ⟧T γ)
    ? 