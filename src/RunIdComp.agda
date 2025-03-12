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
compileType (S.∶ sA 𝕢 𝟘 ⟶ sB) = compileType sB
compileType (S.∶ sA 𝕢 ω ⟶ sB) = do 
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

data ContextRemap : S.Context sΓ  → Set where
    []ᵣ : ContextRemap S.[]
    _,ᵣ_skip : ContextRemap scΓ → (sA : S.Term) → ContextRemap (scΓ S., sA S.𝕢 S.𝟘)  
    _,ᵣ_↦_ : ContextRemap scΓ → (sA : S.Term) → (tA : T.Type) → ContextRemap (scΓ S., sA S.𝕢 S.ω)

compileRemap : (scΓ : S.Context sΓ) → Maybe (ContextRemap scΓ) 
compileRemap S.[] = just []ᵣ 
compileRemap (scΓ S., sA S.𝕢 S.𝟘) = do 
    rΓ ← compileRemap scΓ
    just (rΓ ,ᵣ sA skip)
compileRemap (scΓ S., sA S.𝕢 S.ω) = do 
    rΓ ← compileRemap scΓ
    tA ← compileType sA
    just (rΓ ,ᵣ sA ↦ tA) 

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

compileTerm : ContextRemap scΓ →  S.Term → Maybe T.Term
compileTerm rΓ (S.var x) = do 
    n ← remapIndex x rΓ
    just (T.var n)
compileTerm rΓ (S.ƛ∶ sA 𝕢 𝟘 ♭ sa) = compileTerm (rΓ ,ᵣ sA skip) sa
compileTerm rΓ (S.ƛ∶ sA 𝕢 ω ♭ sa) = do
    tA ← compileType sA
    tbody ← compileTerm (rΓ ,ᵣ sA ↦ tA) sa
    just (T.ƛ tbody)
compileTerm rΓ (S.ƛr∶ sA ♭ sterm) =  
    -- should I try compiling sA just in case?
    just (T.ƛ (T.var 0)) 
compileTerm rΓ (sf S.· sa 𝕢 S.𝟘) = compileTerm rΓ sf
compileTerm rΓ (sf S.· sa 𝕢 S.ω) = do 
    tf ← compileTerm rΓ sf 
    ta ← compileTerm rΓ sa 
    just (tf T.· ta) 
-- Replace by arg
compileTerm rΓ (sf S.·ᵣ sa) = compileTerm rΓ sa
compileTerm rΓ S.z = just T.z
compileTerm rΓ (S.s sa) = do 
    ta ← compileTerm rΓ sa 
    just (T.s ta) 
compileTerm rΓ S.nill = just T.nill
compileTerm rΓ (sa S.∷l sas) = do 
    ta ← compileTerm rΓ sa 
    tas ← compileTerm rΓ sas 
    just (ta T.∷l tas) 
compileTerm rΓ (S.nilv𝕢 S.𝟘) = just T.nill
compileTerm rΓ (S.nilv𝕢 S.ω) = just T.nilv
compileTerm rΓ (sa S.∷v sas 𝕟 sn 𝕢 S.𝟘) = do 
    ta ← compileTerm rΓ sa 
    tas ← compileTerm rΓ sas 
    just (ta T.∷l tas) 
compileTerm rΓ (sa S.∷v sas 𝕟 sn 𝕢 S.ω) = do 
    ta ← compileTerm rΓ sa 
    tas ← compileTerm rΓ sas 
    tn ← compileTerm rΓ sn 
    just (ta T.∷v tas 𝕟 tn)
compileTerm rΓ (S.elimnat sa P∶ sP zb∶ sz sb∶ ss) = do 
    ta ← compileTerm rΓ sa 
    tz ← compileTerm rΓ sz 
    tP ← compileType sP
    ts ← compileTerm 
        ((rΓ ,ᵣ 
            S.Nat ↦ T.Nat) ,ᵣ
            -- Need to evaluate sP to a T type... 
            -- Assume no path sensitivity therefore P : @0 A -> B 
            sP ↦ tP) 
        ss 
    just (T.elimnat ta zb∶ tz sb∶ ts)
compileTerm rΓ (S.eliml sa ty∶ sA P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm rΓ sa 
    tn ← compileTerm rΓ sn 
    tA ← compileType sA
    tP ← compileType sP
    tc ← compileTerm 
        (((rΓ ,ᵣ 
            sA ↦ tA) ,ᵣ 
            S.List sA ↦ T.List tA) ,ᵣ 
            sP ↦ tP) 
        sc 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm rΓ (S.elimv sa 𝕢 𝟘 ty∶ sA P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm rΓ sa 
    tn ← compileTerm rΓ sn 
    tA ← compileType sA
    tP ← compileType sP
    tc ← compileTerm 
        ((((rΓ ,ᵣ
            S.Nat skip) ,ᵣ 
            sA ↦ tA) ,ᵣ 
            S.Vec sA (S.var 1 𝕢 𝟘) ↦ T.List tA) ,ᵣ 
            sP ↦ tP)
        sc 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm rΓ (S.elimv sa 𝕢 ω ty∶ sA P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm rΓ sa 
    tn ← compileTerm rΓ sn 
    tA ← compileType sA
    tP ← compileType sP
    tc ← compileTerm  
        ((((rΓ ,ᵣ 
            S.Nat skip) ,ᵣ
            sA ↦ tA) ,ᵣ 
            S.Vec sA (S.var 1 𝕢 ω) ↦ T.Vec tA) ,ᵣ 
            sP ↦ tP) 
        sc 
    just (T.elimv ta nb∶ tn cb∶ tc)
-- Reject types in term position
compileTerm rΓ stype = nothing

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
    rΓ ← compileRemap S.[]
    tterm ← compileTerm rΓ sterm
    ttype ← compileType stype 
    just (tterm , ttype)