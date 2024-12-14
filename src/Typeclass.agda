module Typeclass where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; _≗_)
open import Function using (_∘_)

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
        eqTargTy : RuntimeRep.R repA ≡ RuntimeRep.R repB
        -- need to use eqTargTy to simplify Rb to Ra 
        fRId : RunTimeId repA repB {eqTargTy} f

open HasRun {{...}} public

