module RunIdComp where

import RunId as S 
import STLC as T

---- Directly import syntax only used in S 
open S using (
    -- Quantities 
    𝟘; ω; 
    -- Annotations
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
    sΓ : S.PreContext
    scΓ : S.Context sΓ
    tΓ : T.Context

-- Figure out how it actually makes sense to keep track of indices 
data ContextRemap : S.Context sΓ  → Set where
    []ᵣ : ContextRemap S.[]
    _,ᵣ_skip : ContextRemap scΓ → (sA : S.Term) → ContextRemap (scΓ S., sA S.𝕢 S.𝟘)  
    _,ᵣ_↦_ : ContextRemap scΓ → (sA : S.Term) → (tA : T.Type) → ContextRemap (scΓ S., sA S.𝕢 S.ω)

computeRemap : (scΓ : S.Context sΓ) → ContextRemap scΓ 
computeRemap S.[] = []ᵣ 
computeRemap (scΓ S., A S.𝕢 S.𝟘) = computeRemap scΓ ,ᵣ A skip 
computeRemap (scΓ S., A S.𝕢 S.ω) = computeRemap scΓ ,ᵣ A ↦ T.Nat 

-- outside of FP this could be a collection of ints to skip over and do maths instead
remapIndex : ℕ → ContextRemap scΓ → Maybe ℕ
remapIndex i []ᵣ = nothing
remapIndex zero (scΓ ,ᵣ sA skip) = nothing
-- this entry wont exist so decrement index
remapIndex (suc i) (scΓ ,ᵣ sA skip) = remapIndex i scΓ
remapIndex zero (scΓ ,ᵣ sA ↦ tA) = just zero
remapIndex (suc i) (scΓ ,ᵣ sA ↦ tA) = do 
    n ← remapIndex i scΓ 
    just (suc n)

lookupType : S.Context sΓ → ℕ → Maybe (S.Type × S.Quantity) 
lookupType S.[] i = nothing
lookupType (scon S., A S.𝕢 σ) zero = just (A , σ) 
lookupType (scon S., A S.𝕢 σ) (suc i) = lookupType scon i


compileType : S.Type → Maybe T.Type
compileType S.Nat = just T.Nat
compileType (S.List sA) = do 
    tA ← compileType sA 
    just (T.List tA) 
compileType (S.Vec sA (_ S.𝕢 S.𝟘)) = do 
    tA ← compileType sA
    just (T.List tA) 
compileType (S.Vec sA (_ S.𝕢 S.ω)) = do 
    tA ← compileType sA
    just (T.Vec tA)
compileType (S.∶ sA S.𝕢 σ ⟶ sB) = do 
    tA ← compileType sA 
    tB ← compileType sB
    just (tA T.⟶ tB) 
-- Force into id? Or compile normally?
compileType (S.r∶ sA ⟶ sB) = do 
    tA ← compileType sA 
    tB ← compileType sB
    just (tA T.⟶ tB)
-- Not sure what to do here... reject?
compileType (S.Sett l) = nothing
-- Reject terms in type positon.
compileType sA = nothing

compileTerm : (scΓ : S.Context sΓ) → S.Term → Maybe T.Term
compileTerm scon (S.var x) = do 
    -- Compute remap
    let remap = computeRemap scon
    -- Recompute index (how)?
    n ← remapIndex x remap
    just (T.var n)
compileTerm scon (S.ƛ∶ sA S.𝕢 S.𝟘 ♭ sbody) = do 
    tbody ← compileTerm (scon S., sA S.𝕢 S.𝟘) sbody
    -- shift indices tbody
    just (T.shiftindices tbody 1 0)
-- what abt (lambda (f : a runid-> b). f 42) (lambda. 6)
-- Options: 
---- 1. Remove beta reduction 
---- 2. Require well typed for beta reduction 
compileTerm scon (S.ƛ∶ sA S.𝕢 S.ω ♭ sbody) = do 
    tbody ← compileTerm (scon S., sA S.𝕢 S.ω) sbody
    just (T.ƛ tbody) 
-- reject when erased? 
-- builtin id function?
compileTerm scon (S.ƛr∶ sA ♭ sterm) = do 
    -- should I try compiling sA just in case?
    just (T.ƛ (T.var 0))
compileTerm scon (sf S.· sa 𝕢 S.𝟘) = compileTerm scon sf
compileTerm scon (sf S.· sa 𝕢 S.ω) = do 
    tf ← compileTerm scon sf 
    ta ← compileTerm scon sa 
    just (tf T.· ta) 
-- Replace by arg
compileTerm scon (sf S.·ᵣ sa) = compileTerm scon sa
compileTerm scon S.z = just T.z
compileTerm scon (S.s sa) = do 
    ta ← compileTerm scon sa 
    just (T.s ta) 
compileTerm scon S.nill = just T.nill
compileTerm scon (sa S.∷l sas) = do 
    ta ← compileTerm scon sa 
    tas ← compileTerm scon sas 
    just (ta T.∷l tas) 
compileTerm scon (S.nilv𝕢 S.𝟘) = just T.nill
compileTerm scon (S.nilv𝕢 S.ω) = just T.nilv
compileTerm scon (sa S.∷v sas 𝕟 sn 𝕢 S.𝟘) = do 
    ta ← compileTerm scon sa 
    tas ← compileTerm scon sas 
    just (ta T.∷l tas) 
compileTerm scon (sa S.∷v sas 𝕟 sn 𝕢 S.ω) = do 
    ta ← compileTerm scon sa 
    tas ← compileTerm scon sas 
    tn ← compileTerm scon sn 
    just (ta T.∷v tas 𝕟 tn)
{-
---- Attempt building basic reduction optimization into compiler
-- Assume must be an unerased nat
compileTerm scon (S.elimnat sa P∶ sP zb∶ sz sb∶ ss) = do 
    tz ← compileTerm scon sz 
    ts ← compileTerm (scon S., S.Nat S.𝕢 S.ω) ss 
    T.z ← compileTerm scon sa where
        -- substitute into ts?
        T.s ta → just ({! ts   !})
        ta → just (T.elimnat ta zb∶ tz sb∶ ts)  
    just {!   !}
-}
---- dont optimize variant
compileTerm scon (S.elimnat sa P∶ sP zb∶ sz sb∶ ss) = do 
    ta ← compileTerm scon sa 
    tz ← compileTerm scon sz 
    -- Assume nat is unerased?
    -- Usage of P's arg? Usage of P?
    ts ← compileTerm ((scon S., S.Nat S.𝕢 ω) S., (sP S.· S.var 0 𝕢 {!   !}) S.𝕢 {!   !}) ss 
    just (T.elimnat ta zb∶ tz sb∶ ts)
compileTerm scon (S.eliml sa P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sc 
    -- How will compilation change the presence of the P entry? What should the usage of P be?
    -- What about e.g. f x = Int? I literally _have to_ reduce this application... 
    tc ← compileTerm 
        (((scon S., {! A  !} S.𝕢 ω) S., 
            S.List {!  A !} S.𝕢 ω) S., 
            (sP S.· S.var 0 𝕢 {!   !}) S.𝕢 {!   !}) 
        sn 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm scon (S.elimv sa S.𝕢 S.𝟘 P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sn 
    tc ← compileTerm 
        ((((scon S., 
            S.Nat 𝕢 𝟘) S., 
            {!  A !} 𝕢 ω) S., 
            S.Vec {!  A  !} (S.var 1 𝕢 𝟘) 𝕢 ω) S., 
            (sP S.· S.var 0 𝕢 {!   !}) 𝕢 {!   !}) 
        sc 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm scon (S.elimv sa S.𝕢 S.ω P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sn 
    tc ← compileTerm  
        ((((scon S., 
            S.Nat 𝕢 ω) S., 
            {!  A  !} 𝕢 ω) S., 
            S.Vec {!  A  !} (S.var 1 𝕢 ω) 𝕢 ω) S., 
            (sP S.· S.var 0 𝕢 {!   !}) 𝕢 {!   !}) 
        sc 
    just (T.elimv ta nb∶ tn cb∶ tc)
-- Reject types in term position
compileTerm scon stype = nothing


-- I dont actually use this rn
compileContext : (scΓ : S.Context sΓ) → Maybe T.Context
compileContext S.[] = just T.[]
compileContext (scon S., A S.𝕢 S.𝟘) = compileContext scon
compileContext (scon S., A S.𝕢 S.ω) = do 
    tcon ← compileContext scon 
    tty ← compileType A
    just (tcon T., tty) 

-- Would a compiler monad make sense? 
-- Top level assumes empty context
compile : S.Term → S.Type → Maybe (T.Term × T.Type) 
compile sterm stype = do
    tterm ← compileTerm S.[] sterm
    ttype ← compileType stype 
    just (tterm , ttype)