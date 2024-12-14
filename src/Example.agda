module Example where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; _≗_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; ∃)
open import Data.Unit
open import Data.Empty using (⊥)
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Typeclass

-- Simple example for "ornamented" lists

data @0 Even : ℕ → Set where
  even-zero  : Even zero
  even-plus2 : {n : ℕ} → Even n → Even (suc (suc n))

data EvenList : Set where
    []ₑ : EvenList
    _,_∷ₑ_ :  (n : ℕ) → @0 Dec (Even n) → EvenList → EvenList  

@0 tmp : ∀ {n} → ¬ Even n  →  ¬ Even (suc (suc n))
tmp p (even-plus2 pss) = p pss

@0 isEven : (n : ℕ) → Dec (Even n)
isEven zero = yes even-zero
isEven (suc zero) = no λ ()
isEven (suc (suc n)) with isEven n
... | yes p = yes (even-plus2 p)
... | no p = no (tmp p)

data Vec (A : Set) : @0 ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {@0 n} (x : A) (xs : Vec A n) → Vec A (suc n)

f : ∀ {n} → Vec ℕ n → EvenList  
f [] = []ₑ
f (x ∷ v) = x , isEven x ∷ₑ f v

instance 
    VecRuntime : {n : ℕ} → RuntimeRep (Vec ℕ n)
    R {{VecRuntime}} = List ℕ
    erase ⦃ VecRuntime ⦄ [] = []
    erase ⦃ VecRuntime ⦄ (x ∷ v) = x ∷ erase v
    
    EvenListRuntime : RuntimeRep (EvenList)
    R {{EvenListRuntime}} = List ℕ
    erase ⦃ EvenListRuntime ⦄ []ₑ = []
    erase ⦃ EvenListRuntime ⦄ (n , x ∷ₑ v) = n ∷ erase v
    
    -- Should args be bundled or provided separately?
    fHasRun : {n : ℕ} → HasRun (Vec ℕ n) EvenList f
    repA {{fHasRun}} = VecRuntime
    repB {{fHasRun}} = EvenListRuntime
    eqTargTy {{fHasRun}} = refl
    fRId ⦃ fHasRun ⦄ [] = refl
    fRId ⦃ fHasRun ⦄ (x ∷ x₁) = cong (_∷_  x) (fRId x₁)

-- What if already a function? 
A : @0 ℕ → ℕ → Set
A = {!   !}