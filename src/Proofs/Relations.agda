{-# OPTIONS --allow-unsolved-metas #-}
module Proofs.Relations where

import STLC as T
open import RunIdComp

open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Unit
open import Data.Empty

private variable
    A : Set
    a b c d : A
    ma mb mc : Maybe A

    tA tB : T.Type
    ta tb tc : T.Term    


-- For only talking about succesful compilation 
abstract 
    _compilesTo_ : Maybe A → A → Set
    _compilesTo_ (just t1) t2 = t1 ≡ t2
    _compilesTo_ nothing t2 = ⊥

    compIsDeterministic : 
        ma compilesTo a  →
        ma compilesTo b →
        a ≡ b
    compIsDeterministic {ma = just x} refl refl = refl

    compAbsurd : nothing compilesTo a → A
    compAbsurd ()

    
    postulate
        funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
            → ((x : A) →  f x ≡ g x) → f ≡ g

    
    {- 
    tmp2 : ∀ {scΓ sa ta} →  (compileTerm scΓ sa >>= (λ ta₁ → just (T.s ta₁))) compilesTo ta →
        compileTerm scΓ sa compilesTo ta 
    -}

-- should I even differ between term and type?
module Ty where
    abstract

        -- equivalence of types
        -- Do I even need a relation or should this _always_ be syntactic?
        _↔ty_ : T.Type → T.Type → Set
        _↔ty_ = _≡_

        lemmaRefl : tA ↔ty tA 
        lemmaRefl = refl

open Ty using (_↔ty_) public

module Te where
    abstract
        -- obs equivalence of term
        _↔te_ : T.Term → T.Term → Set
        _↔te_ = _≡_

        lemmaRefl : ta ↔te ta
        lemmaRefl = refl

        lemmaSym : ta ↔te tb → tb ↔te ta 
        lemmaSym refl = refl

        lemmaTrans : ta ↔te tb → tb ↔te tc → ta ↔te tc  
        lemmaTrans refl refl = refl

        -- need funext for body?
        lemmaBind : ∀ {body1 body2} →
            (ma >>= body1) compilesTo a → 
            (mb >>= body2) compilesTo b → 
            (inpsEqv : ∀ {c d} → ma compilesTo c → 
                mb compilesTo d → 
                c ↔te d) → 
            (outsEqv : ∀ {c d res} → ma compilesTo res →
                body1 res compilesTo c → 
                body2 res compilesTo d → 
                c ↔te d) →
            a ↔te b
        lemmaBind {just resa} {mb = just resb} maComps mbComps indL indR
            rewrite indL {c = resa} {d = resb} refl refl = indR refl maComps mbComps


        lemmaBindL : ∀ {body} →
            (ma >>= body) compilesTo a → 
            (mb >>= body) compilesTo b → 
            (∀ {c d} → ma compilesTo c 
                → mb compilesTo d 
                → c ↔te d) →
            a ↔te b 
        lemmaBindL maComps mbComps indL = 
            lemmaBind maComps mbComps indL λ _ resCompsL resCompsR → compIsDeterministic resCompsL resCompsR

open Te using (_↔te_) public

