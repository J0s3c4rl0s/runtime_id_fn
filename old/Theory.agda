module Theory where

open import Data.Product using (_×_)

-- Necessary componens to define the annotation and reason about it

-- Universe of types
open import Reflection using (Type; Definition)

-- Context mapping var names to data type declarations 
data decContext : Set where

-- Some function which computes erased type
erase : Type → Type 
erase t = {!  t  !}

-- Relation stating that modulo erased constructors they are equal, add hoc creating erased types/cons (may be worthwhile to store erased mappings somewhere)
_⊢_≅_ : decContext → Type → Type → Set
Γ ⊢ Reflection.var x args ≅ tᵣ = {!   !}
Γ ⊢ Reflection.con c args ≅ tᵣ = {!   !}
Γ ⊢ Reflection.def f args ≅ tᵣ = {!   !}
Γ ⊢ Reflection.lam v t ≅ tᵣ = {!   !}
Γ ⊢ Reflection.pat-lam cs args ≅ tᵣ = {!   !}
Γ ⊢ Reflection.pi (Reflection.arg i x) b ≅ tᵣ = {!   !}
Γ ⊢ Reflection.agda-sort s ≅ tᵣ = {!   !}
Γ ⊢ Reflection.lit l ≅ tᵣ = {!   !}
Γ ⊢ Reflection.meta x x₁ ≅ tᵣ = {!   !}
Γ ⊢ Reflection.unknown ≅ tᵣ = {!   !}

-- Some relation on types, saying that they will be erased to the same type (or isomorphic with ad-hoc erasure)
_⊢_=ₜ_ : decContext → Type → Type → Set 
Γ ⊢ t1 =ₜ t2 = {!   !}

{-
From here can state the inference rule, I think it matters to have a few rules 

formation rule :
    default QTT conditions 
    0Γ ⊢ A =ₜ B a, verify that post erasure (in the context) argument type matches return type. unsure if I need to add a to env or no 
    ----------Pi_Id
    0Γ ⊢ (a :^ω A) →ᵢ B a -- Cant have a runtime id fn with erased arg 

introduction rule (for lam) :
    default QTT conditions
    Γ ⊢ a =ₜ M, verify that erased body matches argument (shouldnt need to substitute or eval right?)
    --------Lam_Id
    Γ ⊢ (λᵢ a :^ω A.M) : (a : A) →ᵢ B a

introduction rule (for pat) :
    default QTT conditions
    ∀n, Γ ⊢ aₙ =ₜ Mₙ, verify that erased body matches argument for each branch (shouldnt need to substitute or eval right?)
    --------Pat_Id
    Γ ⊢ List (pᵢ aₙ :^ω A.Mₙ) : (a : A) →ᵢ B

elimination rule 
    default QTT conditions but with id slapped in annotation
    --------App_Id
    Γ ⊢  f a : B a

-}