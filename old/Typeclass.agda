{-# OPTIONS --rewriting #-}

module Typeclass where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; _≗_)
open import Function using (_∘_)
open import Data.Product using (Σ; Σ-syntax)

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Enforces that a type has some runtime representation
record RuntimeRep (A : Set) : Set₁  where
    field 
        -- Need some way to enforce that this "run time rep" has no erased args
        R : Set
        erase : A → R

open RuntimeRep {{...}} public

-- Have some relation to mean runtime equal (thats what this shit is for??)
RunTimeId : ∀ {A B} → (ra : RuntimeRep A) → (rb : RuntimeRep B) → {eq : RuntimeRep.R ra ≡ RuntimeRep.R rb} → (f : A → B) → Set
RunTimeId record { R = _ ; erase = eraseA } record { R = _ ; erase = eraseB } {refl} f = eraseA ≗ eraseB ∘ f

-- Is it strictly necessary to give A and B as args? Maybe they could be implicit at least?
-- f : A -> B s.t. A ~ B
record HasRun A B (f : A → B) : Set₁ where
    field
        repA : RuntimeRep A
        repB : RuntimeRep B
        -- Could be modified to be parametric on some erase function (equality is post erasure), would be better higher tho
        eqTargTy : RuntimeRep.R repA ≡ RuntimeRep.R repB
        -- need to use eqTargTy to simplify Rb to Ra 
        fRId : RunTimeId repA repB {eqTargTy} f

open HasRun {{...}} public


record Erase : Set₁ where
    -- Could make this a build your own erasure type deal like GRTT 
    field
        eraseTy : Set → Set
        eraseTerm : {A : Set} → A → eraseTy A
        -- properties on erase (?)
        -- Not sure this is good for dep functions
        funDist :
            ∀ {A B} → 
            eraseTy (A → B) ≡ (eraseTy A → eraseTy B)
        
    
        -- post erasure execution should be the same as post execution erasure 
        square : 
            ∀ {A B} {f : A → B} →
            -- Cant fill in hole because cant apply rewrite rule from funDist
            eraseTerm ∘ f ≗ {! eraseTerm f   !} ∘ eraseTerm
        {-
        tyEr=termEr :
            ∀ {A B} →
            -- eraseTerm f : eraseTy f
            {!   !}
        -}
         
{-# REWRITE Erase.funDist #-}
        
-- Generic function class for runtime 
record RunFun A B (f : A → B) : Set₁ where
    field
        repA : RuntimeRep A
        repB : RuntimeRep B
        

-- Random bullshit go 

-- Some sense of rep equal between types (type eq judgment?)
data ⊢_=ᵣ_ : Set _ → Set _ → Set _ where
    test : 
        ∀ {A B C D}  →
        {! ⊢ ? =ᵣ ?   !} → 
        ⊢  ((a : A)  → B a)    =ᵣ ( (c : C)   → D c)  
        -- ⊢ {! (a : A) →   !} =ᵣ {!   !} →
        -----------------------------------------------------------------------
        -- Pretend this shit says rn id
        -- ⊢ ((a : A) → B a) =ᵣ ( (c : C)  → D c)

-- Some sense of term rep eqaul judgment
_=ᵣ_ : ∀ {A B} → A → B → Set _
a =ᵣ b = {!   !}

-- rn this is just saying that there is a mapping from A to B s.t. they are rep eq
_→ᵣ_ : {A : Set _} {B : A → Set _} → (a : A) → B a → Set _ 
_→ᵣ_ {A} {B} a b = a =ᵣ b


