module ListCalc.RunIdComp where

import ListCalc.RunId as S 
import ListCalc.STLC as T

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
    

lookupType : S.Context sΓ → ℕ → Maybe (S.Type × S.Quantity) 
lookupType S.[] i = nothing
lookupType (scon S., A S.𝕢 σ) zero = just (A , σ) 
lookupType (scon S., A S.𝕢 σ) (suc i) = lookupType scon i

compareTypes : S.Context sΓ → S.Type → S.Type → Maybe ⊤ 
compareTypes scon A B = {!   !}

-- Perhaps only support basic options for now
typecheck : S.Context sΓ → S.Term → S.Type → Maybe ⊤
typecheck scon (S.var x) stype = do 
    (contype , _) ← lookupType scon x
    -- compare contype and stype
    {!   !}
typecheck scon (S.ƛ∶ At S.𝕢 σt ♭ sterm) stype = do 
    -- Need to type infer.... Maybe should just be annotated
    Bt ← {! typecheck  !} 
    compareTypes scon (S.∶ At S.𝕢 σt ⟶ Bt) stype 
    just tt
typecheck scon (S.ƛr∶ At S.𝕢 σt ♭ sterm) stype = do 
    -- Need to type infer.... Maybe should just be annotated
    Bt ← {! typecheck  !} 
    compareTypes scon (S.r∶ At S.𝕢 σt ⟶ Bt) stype 
    just tt 
typecheck scon (sterm S.· sterm₁ 𝕢 σ) stype = {!   !}
typecheck scon (sterm S.·ᵣ sterm₁) stype = {!   !}
typecheck scon S.z stype = {!   !}
typecheck scon (S.s sterm) stype = {!   !}
typecheck scon S.nill stype = {!   !}
typecheck scon (sterm S.∷l sterm₁) stype = {!   !}
typecheck scon (S.nilv𝕢 x) stype = {!   !}
typecheck scon (sterm S.∷v sterm₁ 𝕟 sterm₂ 𝕢 x) stype = {!   !}
typecheck scon (S.elimnat sterm P∶ sterm₁ zb∶ sterm₂ sb∶ sterm₃) stype = {!   !}
typecheck scon (S.eliml sterm P∶ sterm₁ nb∶ sterm₂ cb∶ sterm₃) stype = {!   !}
typecheck scon (S.elimv sterm P∶ sterm₁ nb∶ sterm₂ cb∶ sterm₃) stype = {!   !}
-- Reject types as terms 
typecheck scon S.Nat stype = nothing
typecheck scon (S.List x) stype = nothing
typecheck scon (S.Vec x sterm) stype = nothing
typecheck scon (S.∶ x ⟶ x₁) stype = nothing
typecheck scon (S.r∶ x ⟶ x₁) stype = nothing
typecheck scon (S.Sett x) stype = nothing


-- Compile term, context and maybe? context remap
compileTerm : (scΓ : S.Context sΓ) → S.Term → Maybe T.Term
compileTerm scon (S.var x) = do 
    -- (need to fucking shift indices again) 
    conty ← lookupType scon x
    -- Do I have to compare?
    -- not sure I can compare insofar as conty is expecting a different context 
    compareTypes scon {!   !} {!   !}
    -- Recompute index (how)?
    -- Maybe shift function takes SCon and TCon?
    {!   !}
compileTerm scon (S.ƛ∶ sA S.𝕢 S.𝟘 ♭ sbody) = do 
    tbody ← compileTerm (scon S., sA S.𝕢 S.𝟘) sbody
    -- shift indices in tbody?
    just {!   !}
compileTerm scon (S.ƛ∶ sA S.𝕢 S.ω ♭ sbody) = do 
    tbody ← compileTerm (scon S., sA S.𝕢 S.ω) sbody
    just (T.ƛ tbody) 
-- reject when erased? 
-- builtin id function?
compileTerm scon (S.ƛr∶ sA S.𝕢 σ ♭ sterm) = {!   !}
compileTerm scon (sf S.· sa 𝕢 S.𝟘) = do 
    -- should compile away sf to its body
    tf ← compileTerm scon sf
    just tf  
compileTerm scon (sf S.· sa 𝕢 S.ω) = do 
    tf ← {!   !} 
    ta ← {!   !} 
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
-- Syntax for differentiating vec0 and vecomega
compileTerm scon (S.elimv sa P∶ sP nb∶ sn cb∶ sb) = {!   !}
-- Reject types in term position
compileTerm scon stype = nothing

-- Do I even need context? Should I exclude anything here or rely on type checker?
compileType : S.Type → Maybe T.Type
compileType S.Nat = just T.Nat
compileType (S.List sA) = do 
    tA ← compileType sA 
    just (T.List tA) 
compileType (S.Vec (_ S.𝕢 S.𝟘) sA) = do 
    tA ← compileType sA
    just (T.List tA) 
compileType (S.Vec (_ S.𝕢 S.ω) sA) = do 
    tA ← compileType sA
    just (T.Vec tA)
compileType (S.∶ sA S.𝕢 σ ⟶ sB) = do 
    tA ← compileType sA 
    tB ← compileType sB
    just (tA T.⟶ tB) 
-- Force into id? Or compile normally?
compileType (S.r∶ sA S.𝕢 σ ⟶ sB) = {!   !}
-- Not sure what to do here... reject?
compileType (S.Sett l) = nothing
-- Reject terms in type positon.
compileType sA = nothing

-- Figure out how it actually makes sense to keep track of indices 
data ContextRemap : S.Context sΓ → T.Context → Set where
    []ᵣ : ContextRemap S.[] T.[]
    _,ᵣ_skip : ContextRemap scΓ tΓ → (sa : S.Term) → ContextRemap {!   !} {!   !}  
    _,ᵣ_↦_ : ContextRemap scΓ tΓ → (sa : S.Term) → (ta : T.Term) → ContextRemap {!   !} {!   !}
    {-
    []ᵣ : ContextRemap S.[]
    -- For now keep track of number that says how many things to skip
    -- using _∋_ but not sure if possible
    _,ᵣ_ : ContextRemap (scΓ) → {!   !} T.∋ {!   !} → ContextRemap (scΓ S., _ S.𝕢 _) 
    -}

compileContext : (scΓ : S.Context sΓ) → Maybe T.Context
compileContext S.[] = just T.[]
compileContext (scon S., A S.𝕢 S.𝟘) = compileContext scon
compileContext (scon S., A S.𝕢 S.ω) = do 
    tcon ← compileContext scon 
    tty ← compileType A
    just (tcon T., tty) 
    
computeRemap : (scΓ : S.Context sΓ) → Maybe (T.Context × List ℕ) 
computeRemap = {!   !}

-- Would a compiler monad make sense? 
-- Recursive Helper
compileH : S.Context sΓ → S.Term → S.Type → Maybe (T.Context × T.Term × T.Type)
compileH scon sterm stype = do
    -- Reject ill typed terms
    typecheck scon sterm stype
    ---- alternative approach 
    -- 1. compute remap (and thus new context?)
    -- 2. shift all variables 
    -- 3. Implement naive compilation (term to term?) 

    -- compile recursively...? 
    -- do I gotta pattern match anyways?
    -- maybe another compile function that does the recursion? 
    -- termination checker?
    tterm ← compileTerm {!   !} {!   !} 
    -- Consider creating a data type to keep track of context shifts
    c ← {!   !} 
    d ← {!   !}
    {!   !}

-- Top level assumes empty context and then helper function takes context 
compile : S.Term → S.Type → Maybe (T.Term × T.Type) 
compile sterm stype = do 
    (T.[] , tterm , ttype) ← compileH S.[] sterm stype where 
    -- If context is nonempty then there are free variables which is nono
        ((_ T., _) , _ , _) → nothing
    just (tterm , ttype)
   