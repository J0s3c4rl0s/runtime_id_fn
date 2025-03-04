module Meta where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; _≗_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (_∘_)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List
open import Data.Nat

open import Agda.Builtin.Reflection 
open import Reflection using (_>>=_; _>>_)
open import Level using (Level)

variable 
  l : Level
  A : Set l

-- If using map instead of removing, need some relation that states 
-- _these_ types/terms are runtime equiv
-- Should not be too hard, construct an erased or consider only the non-top tyües

isErasable : Arg A → Set
-- Not sure that visibility matters
isErasable (arg (arg-info v (modality r quantity-0)) x) = ⊤
isErasable (arg (arg-info v (modality r quantity-ω)) x) = ⊥
-- This seems insultingly trivial, must be a smarter way to automatically do this
eraseDec : (a : Arg A) → Dec (isErasable a)
eraseDec (arg (arg-info v (modality r quantity-0)) x) = yes tt
eraseDec (arg (arg-info v (modality r quantity-ω)) x) = no Function.id 

eraseF : Arg Term → Arg Term
eraseF (arg i x) = {!   !}

-- Filter or replace with () as GHC wants? hmm
filterErasedArgs : List (Arg Term) → List (Arg Term)
filterErasedArgs args = filter eraseDec args


removeErasedTypes : Type → Type
-- Worth thinking about what x should be, why a list of args?
removeErasedTypes (var x args) = var {!   !} (filterErasedArgs args)
removeErasedTypes (con c args) = con c (filterErasedArgs args)
removeErasedTypes (def f args) = def f (filterErasedArgs args)
--  Probably need to update the indices in here.. hmm might need to fetch the vars and then adjust by the removed ones
removeErasedTypes (lam v t) = lam v {!   !}
removeErasedTypes (pat-lam cs args) = {!   !}
removeErasedTypes (pi a b) = {!   !}
removeErasedTypes (agda-sort s) = {!   !}
removeErasedTypes (lit l) = {!   !}
removeErasedTypes (meta x x₁) = {!   !}
removeErasedTypes unknown = {!   !}

macro 
  removeErasedTypesTC : Type → Term → TC ⊤
  removeErasedTypesTC compTy hole = workOnTypes 
    (do 
      deff ← getDefinition {!   !}
      -- I shouldnt have to infer the type, I already have it
      -- compTy ← inferType compTerm
      -- Where get name from?
      runTyName ← freshName {!   !}
      declareData {!   !} {!   !} (removeErasedTypes compTy)       
      {!   !})

tmpR : Set → Set
tmpR ty = removeErasedTypesTC (quoteTerm ty)

macro 
  -- This doesnt do what I want right? 
  -- Does it being in compile mode make the inferred type erased?
  removeErasedTypesSimpl : Type → Term → TC ⊤
  removeErasedTypesSimpl cTy hole = workOnTypes (do 
      rTy ← inferType cTy
      unify rTy hole)

-- Enforces that a type has some runtime representation
record RuntimeRepMS (A : Set) : Set₁  where
    field 
        -- Need some way to enforce that this "run time rep" has no erased args
        -- R : Set
        erase : A → removeErasedTypesSimpl (quoteTerm A) 
open RuntimeRepMS {{...}} public

-- Simple test

data Vec (A : Set) : @0 ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {@0 n} (x : A) (xs : Vec A n) → Vec A (suc n)

instance 
    VecRuntime : {n : ℕ} → RuntimeRepMS (Vec ℕ n)
    erase ⦃ VecRuntime ⦄ v = {!   !}  



-- Have some relation to mean runtime equal (thats what this shit is for??)
RunTimeIdMS : ∀ {A B} → (ra : RuntimeRepMS A) → (rb : RuntimeRepMS B) → (f : A → B) → Set
RunTimeIdMS record { erase = eraseA } record { erase = eraseB } f = {! eraseA  !} ≗ {!   !}


record HasRun A B (f : A → B) : Set₁ where
    field
        repA : RuntimeRepMS A
        repB : RuntimeRepMS B
        --eqTargTy  : RuntimeRepMS.R repA ≡ RuntimeRepMS.R repB
        -- need to use eqTargTy to simplify Rb to Ra 
        fRId : RunTimeIdMS repA repB f

open HasRun {{...}} public