module Gtt where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)

open import Graded.Modality.Instances.Erasure using (Erasure)
open import Graded.Modality Erasure using (Modality)
open import Graded.Modality.Instances.Erasure.Modality using (ErasureModality)

𝕄 : Modality
-- Dont I _need_ to allow 0? Not sure what 0m allowed means
-- Also erasure literally comes with a nr function sooo?
𝕄 = ErasureModality (record { 𝟘ᵐ-allowed = true ; nr-available = true })

open import Definition.Untyped Erasure using (Term)
open import Definition.Typed.Restrictions 𝕄 using (Type-restrictions)

instance
  tr : Type-restrictions
  tr = record { 
    -- Eta expansion for weak unit type 
    type-variant = record { η-for-Unitʷ = false }
    -- ALlowing both strong and weak unit types, again idk the diff or if it even matters in erasure
    ; Unit-allowed = λ x → ⊤
    -- No restrictions on sigma or pi types
    ; ΠΣ-allowed = λ x p q → ⊤
    -- just spam yes to everything and double check
    ; K-allowed = ⊤
    ; []-cong-allowed = λ x → ⊤
    ; []-cong→Erased = λ x → tt , tt
    ; []-cong→¬Trivial = {!   !}
    ; Equality-reflection = {!   !}
    ; Equality-reflection? = {!   !}
    }

-- Takes some type Restriction
open import Definition.Typed {!   !} using (_⊢_∷_; _⊢_; ⊢_)


record RuntimeRepGTT (T : {!   !} ⊢ {!   !}) : Set {!   !} where
    field

