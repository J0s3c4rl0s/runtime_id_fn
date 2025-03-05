module RunIdComp where

import RunId as S 
import STLC as T

open import Data.Unit using (⊤; tt)
open import Data.List
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
compileTerm scon (S.ƛ∶ sA S.𝕢 S.ω ♭ sbody) = do 
    tbody ← compileTerm (scon S., sA S.𝕢 S.ω) sbody
    just (T.ƛ tbody) 
-- reject when erased? 
-- builtin id function?
compileTerm scon (S.ƛr∶ sA ♭ sterm) = do 
    -- should I try compiling sA just in case?
    just (T.ƛ (T.var 0))
compileTerm scon (sf S.· sa 𝕢 S.𝟘) = do 
    -- should compile away sf to its body
    tf ← compileTerm scon sf
    just tf  
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
compileTerm scon (S.elimnat sa P∶ sP zb∶ sz sb∶ ss) = do 
    ta ← compileTerm scon sa 
    tz ← compileTerm scon sz 
    ts ← compileTerm scon ss 
    just (T.elimnat ta zb∶ tz sb∶ ts)
compileTerm scon (S.eliml sa P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sn 
    tc ← compileTerm scon sc 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm scon (S.elimv sa S.𝕢 S.𝟘 P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sn 
    tc ← compileTerm scon sc 
    just (T.eliml ta nb∶ tn cb∶ tc)
compileTerm scon (S.elimv sa S.𝕢 S.ω P∶ sP nb∶ sn cb∶ sc) = do 
    ta ← compileTerm scon sa 
    tn ← compileTerm scon sn 
    tc ← compileTerm scon sc 
    just (T.elimv ta nb∶ tn cb∶ tc)
-- Reject types in term position
compileTerm scon stype = nothing


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

private variable
    sA sB : S.Type
    sa sb sas sbs : S.Term
    σ π ρ : S.Quantity

    tA tB : T.Type
    ta tb : T.Term

-- Find a way to exclude : Set from input?
-- Define normal form of STLC for comparison?
~ᵣ⇒comp≡ : 
    S.[] S.⊢ sa S.𝕢 σ ∶ sA → 
    S.[] S.⊢ sb S.𝕢 σ ∶ sB → 
    sa S.~ᵣ sb → 
    sA S.~ᵣ sB → 
    compile sa sA ≡  compile sb sB
~ᵣ⇒comp≡ = {!   !}

~ᵣ⇒＝ : 
    S.[] S.⊢ sa S.𝕢 σ ∶ sA → 
    S.[] S.⊢ sb S.𝕢 σ ∶ sB → 
    sa S.~ᵣ sb → 
    sA S.~ᵣ sB → 
    {!   !} →
    {!   !}
~ᵣ⇒＝ = {!   !}