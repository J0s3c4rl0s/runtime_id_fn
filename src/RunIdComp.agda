module RunIdComp where

import RunId as S 
import STLC as T

---- Directly import synaₜx only used in S 
open S using (
    -- Quantities 
    𝟘; ω; 
    -- Annoaₜtions
    _𝕢_)

open import Data.Unit using (⊤; tt)
open import Data.List
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)

-- For some reason not included in the stdlib
infixl 1 _>>_
_>>_ : {A B : Set} → Maybe A → Maybe B → Maybe B
m >> n = m >>= λ _ → n

private variable
    Γₛ : S.PreContext
    cΓₛ : S.Context Γₛ

-- Figure out how it actually makes sense to keep track of indices 
data ContextRemap : S.Context Γₛ  → Set where
    []ᵣ : ContextRemap S.[]
    _,ᵣ_skip : ContextRemap cΓₛ → (Aₛ : S.Term) → ContextRemap (cΓₛ S., Aₛ S.𝕢 𝟘)  
    _,ᵣ_↦_ : ContextRemap cΓₛ → (Aₛ : S.Term) → (Aₜ : T.Type) → ContextRemap (cΓₛ S., Aₛ S.𝕢 ω)

compileType : S.Type → Maybe T.Type

compileRemap : (cΓₛ : S.Context Γₛ) → Maybe (ContextRemap cΓₛ) 
compileRemap S.[] = just []ᵣ 
compileRemap (cΓₛ S., Aₛ S.𝕢 𝟘) = do 
    rΓ ← compileRemap cΓₛ
    just (rΓ ,ᵣ Aₛ skip)
compileRemap (cΓₛ S., Aₛ S.𝕢 ω) = do 
    rΓ ← compileRemap cΓₛ
    Aₜ ← compileType Aₛ
    just (rΓ ,ᵣ Aₛ ↦ Aₜ) 

-- ousₜide of FP this could be a collection of insₜ to skip over and do maths instead
remapIndex : ℕ → ContextRemap cΓₛ → Maybe ℕ
remapIndex i []ᵣ = nothing
remapIndex zero (cΓₛ ,ᵣ Aₛ skip) = nothing
-- this entry wont exist so decrement index
remapIndex (suc i) (cΓₛ ,ᵣ Aₛ skip) = remapIndex i cΓₛ
remapIndex zero (cΓₛ ,ᵣ Aₛ ↦ Aₜ) = just zero
remapIndex (suc i) (cΓₛ ,ᵣ Aₛ ↦ Aₜ) = do 
    n ← remapIndex i cΓₛ 
    just (suc n)


compileType S.Nat = just T.Nat
compileType (S.List Aₛ) = do 
    Aₜ ← compileType Aₛ 
    just (T.List Aₜ) 
compileType (S.Vec Aₛ (_ S.𝕢 𝟘)) = do 
    Aₜ ← compileType Aₛ
    just (T.List Aₜ) 
compileType (S.Vec Aₛ (_ S.𝕢 ω)) = do 
    Aₜ ← compileType Aₛ
    just (T.Vec Aₜ)
compileType (S.∶ Aₛ 𝕢 𝟘 ⟶ Bₛ) = compileType Bₛ
compileType (S.∶ Aₛ 𝕢 ω ⟶ Bₛ) = do 
    Aₜ ← compileType Aₛ 
    Bₜ ← compileType Bₛ
    just (Aₜ T.⟶ Bₜ)
-- Force into id? Or compile normally?
compileType (S.r∶ Aₛ ⟶ Bₛ) = do 
    Aₜ ← compileType Aₛ 
    Bₜ ← compileType Bₛ
    just (Aₜ T.⟶ Bₜ)
-- Not sure what to do here... reject?
compileType (S.Sett l) = nothing
-- Reject terms in type positon.
compileType Aₛ = nothing

compileTerm : (cΓₛ : S.Context Γₛ) → S.Term → Maybe T.Term
compileTerm cΓₛ (S.var x) = do 
    -- Compute remap
    remap ← compileRemap cΓₛ
    -- Recompute index (how)?
    n ← remapIndex x remap 
    just (T.var n)
-- shift indices tbody ? Wont it automatically be shifted down?
compileTerm cΓₛ (S.ƛ∶ Aₛ S.𝕢 𝟘 ♭ sbody) = compileTerm (cΓₛ S., Aₛ S.𝕢 𝟘) sbody
-- what abt (lambda (f : a runid-> b). f 42) (lambda. 6)
-- Options: 
---- 1. Remove beaₜ reduction 
---- 2. Require well typed for beaₜ reduction 
compileTerm cΓₛ (S.ƛ∶ Aₛ S.𝕢 ω ♭ sbody) = do 
    tbody ← compileTerm (cΓₛ S., Aₛ S.𝕢 ω) sbody
    just (T.ƛ tbody) 
-- reject when erased? 
-- builtin id function?
compileTerm cΓₛ (S.ƛr∶ Aₛ ♭ aₛ) = do 
    -- should I try compiling Aₛ just in case?
    just (T.ƛ (T.var 0)) 
compileTerm cΓₛ (fₛ S.· aₛ 𝕢 𝟘) = compileTerm cΓₛ fₛ
compileTerm cΓₛ (fₛ S.· aₛ 𝕢 ω) = do 
    fₜ ← compileTerm cΓₛ fₛ 
    aₜ ← compileTerm cΓₛ aₛ 
    just (fₜ T.· aₜ) 
-- Replace by arg
compileTerm cΓₛ (fₛ S.·ᵣ aₛ) = compileTerm cΓₛ aₛ
compileTerm cΓₛ S.z = just T.z
compileTerm cΓₛ (S.s aₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    just (T.s aₜ) 
compileTerm cΓₛ S.nill = just T.nill
compileTerm cΓₛ (aₛ S.∷l asₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    asₜ ← compileTerm cΓₛ asₛ 
    just (aₜ T.∷l asₜ) 
compileTerm cΓₛ (S.nilv𝕢 𝟘) = just T.nill
compileTerm cΓₛ (S.nilv𝕢 ω) = just T.nilv
compileTerm cΓₛ (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 𝟘) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    asₜ ← compileTerm cΓₛ asₛ 
    just (aₜ T.∷l asₜ) 
compileTerm cΓₛ (aₛ S.∷v asₛ 𝕟 nₛ 𝕢 ω) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    asₜ ← compileTerm cΓₛ asₛ 
    nₜ ← compileTerm cΓₛ nₛ 
    just (aₜ T.∷v asₜ 𝕟 nₜ)
{-
---- Attempt building basic reduction optimization into compiler
-- Asₛume must be an unerased nat
compileTerm cΓₛ (S.elimnat aₛ P∶ Pₛ zb∶ zₛ sb∶ sₛ) = do 
    zₜ ← compileTerm cΓₛ zₛ 
    sₜ ← compileTerm (cΓₛ S., S.Nat S.𝕢 ω) sₛ 
    T.z ← compileTerm cΓₛ aₛ where
        -- substitute into sₜ?
        T.s aₜ → just ({! sₜ   !})
        aₜ → just (T.elimnat aₜ zb∶ zₜ sb∶ sₜ)  
    just {!   !}
-}
---- dont optimize variant
compileTerm cΓₛ (S.elimnat aₛ P∶ Pₛ zb∶ zₛ sb∶ sₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    zₜ ← compileTerm cΓₛ zₛ 
    sₜ ← compileTerm 
        ((cΓₛ S., 
            S.Nat S.𝕢 ω) S., 
            Pₛ S.𝕢 ω) 
        sₛ 
    just (T.elimnat aₜ zb∶ zₜ sb∶ sₜ)
compileTerm cΓₛ (S.eliml aₛ ty∶ Aₛ P∶ Pₛ nb∶ nₛ cb∶ cₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    nₜ ← compileTerm cΓₛ nₛ 
    -- How will compilation change the presence of the P entry? What should the uaₛge of P be?
    -- What about e.g. f x = Int? I literally _have to_ reduce this application... 
    tc ← compileTerm 
        (((cΓₛ S., 
            Aₛ S.𝕢 ω) S., 
            S.List Aₛ S.𝕢 ω) S., 
            Pₛ S.𝕢 ω) 
        cₛ 
    just (T.eliml aₜ nb∶ nₜ cb∶ tc)
compileTerm cΓₛ (S.elimv aₛ 𝕢 𝟘 ty∶ Aₛ P∶ Pₛ nb∶ nₛ cb∶ cₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    nₜ ← compileTerm cΓₛ nₛ 
    tc ← compileTerm 
        ((((cΓₛ S., 
            S.Nat 𝕢 𝟘) S., 
            Aₛ 𝕢 ω) S., 
            S.Vec Aₛ (S.var 1 𝕢 𝟘) 𝕢 ω) S.,
            Pₛ 𝕢 ω) 
        cₛ 
    just (T.eliml aₜ nb∶ nₜ cb∶ tc)
compileTerm cΓₛ (S.elimv aₛ 𝕢 ω ty∶ A P∶ Pₛ nb∶ nₛ cb∶ cₛ) = do 
    aₜ ← compileTerm cΓₛ aₛ 
    nₜ ← compileTerm cΓₛ nₛ 
    tc ← compileTerm  
        ((((cΓₛ S., 
            S.Nat 𝕢 ω) S., 
            A 𝕢 ω) S., 
            S.Vec A (S.var 1 𝕢 ω) 𝕢 ω) S., 
            Pₛ 𝕢 ω) 
        cₛ 
    just (T.elimv aₜ nb∶ nₜ cb∶ tc)
-- Reject types in term position
compileTerm cΓₛ Aₛ = nothing


-- I dont actually use this rn
compileContext : (cΓₛ : S.Context Γₛ) → Maybe T.Context
compileContext S.[] = just T.[]
compileContext (cΓₛ S., Aₛ S.𝕢 𝟘) = compileContext cΓₛ
compileContext (cΓₛ S., Aₛ S.𝕢 ω) = do 
    Γₜ ← compileContext cΓₛ 
    Aₜ ← compileType Aₛ
    just (Γₜ T., Aₜ) 

-- Would a compiler monad make sense? 
-- Top level asₛumes empty context
compile : S.Term → S.Type → Maybe (T.Term × T.Type) 
compile aₛ Aₛ = do
    aₜ ← compileTerm S.[] aₛ
    Aₜ ← compileType Aₛ 
    just (aₜ , Aₜ)