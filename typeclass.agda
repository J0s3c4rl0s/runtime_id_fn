import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; _≗_)
open import Data.Product using (_×_; ∃)
open import Data.Bool
open import Relation.Nullary
open import Data.Empty
open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
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

-- Simple example for "ornamented" lists

data @0 Even : ℕ → Set where
  even-zero  : Even zero
  even-plus2 : {n : ℕ} → Even n → Even (suc (suc n))

data EvenList : Set where
    []ₑ : EvenList
    _,_∷ₑ_ :  (n : ℕ) → @0 Dec (Even n) → EvenList → EvenList  

tmp : ∀ {n} → ¬ Even n  →  ¬ Even (suc (suc n))
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
