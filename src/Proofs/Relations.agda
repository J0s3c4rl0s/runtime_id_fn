{-# OPTIONS --allow-unsolved-metas #-}
module Proofs.Relations where

import RunId as S
import STLC as T
open import RunIdComp

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Unit
open import Data.Empty
   
 
-- For only talking about succesful compilation 
module Compiles {A : Set} (_↔_ : A → A → Set) where
    _compilesTo_ : Maybe A → A → Set
    _compilesTo_ (just t1) t2 = t1 ↔ t2
    _compilesTo_ nothing t2 = ⊥

    compAbsurd : ∀ {B : Set} {a} → nothing compilesTo a → B
    compAbsurd ()

-- should I even differ between term and type?
module Ty where
    abstract
        private variable
            A B C : T.Type

        -- equivalence of types
        -- Do I even need a relation or should this _always_ be syntactic?
        _↔ty_ : T.Type → T.Type → Set
        _↔ty_ = _≡_

        open Compiles _↔ty_ public

        lemmaRefl : A ↔ty A 
        lemmaRefl = refl

open Ty 
    using (_↔ty_)
    renaming (_compilesTo_ to _compilesTypeTo_) public

module Te where
    abstract
        private variable
            ma mb mc : Maybe T.Term
            a b c : T.Term
        
        -- obs equivalence of term
        _↔te_ : T.Term → T.Term → Set
        _↔te_ = _≡_

        open Compiles _↔te_ public
        
        lemmaRefl : a ↔te a
        lemmaRefl = refl

        lemmaSym : a ↔te b → b ↔te a 
        lemmaSym refl = refl

        lemmaTrans : a ↔te b → b ↔te c → a ↔te c  
        lemmaTrans refl refl = refl

        compIsDeterministic : 
            (ma : Maybe T.Term) →
            ma compilesTo a  →
            ma compilesTo b →
            a ↔te b
        compIsDeterministic (just x) lComps rComps = lemmaTrans (lemmaSym lComps) rComps


        lemmaBindSubstInd : 
            (ma : Maybe T.Term) →
            (mb : Maybe T.Term) →
            (body1 : T.Term → Maybe T.Term) →
            (body2 : T.Term → Maybe T.Term) →
            (ma >>= body1) compilesTo b →
            (∀ {a} → 
                ma compilesTo a →
                mb compilesTo a) → 
            (outsEqv : ∀ {c } → (res : T.Term) → {maComps : ma compilesTo res} →
                body1 res compilesTo c → 
                body2 res compilesTo c) → 
            (mb >>= body2) compilesTo b
        lemmaBindSubstInd (just resa) mb body1 body2 maBindComps base ind
            with base refl
        lemmaBindSubstInd (just resa) (just .resa) body1 body2 maBindComps base ind | refl = 
            ind resa {maComps = refl} maBindComps

        lemmaBindSubstBase : 
            (ma : Maybe T.Term) →
            (mb : Maybe T.Term) →
            (body : T.Term → Maybe T.Term) →
            (ma >>= body) compilesTo b →
            (∀ {a} → 
                ma compilesTo a →
                mb compilesTo a) → 
            (mb >>= body) compilesTo b
        lemmaBindSubstBase ma mb body maBComps base = 
            lemmaBindSubstInd 
                ma mb 
                body body 
                maBComps 
                base 
                λ res resComps → resComps

        -- need funext for body?
        lemmaBindInd :
            (ma : Maybe T.Term) →  
            (mb : Maybe T.Term) →  
            (body1 : T.Term → Maybe T.Term) →
            (body2 : T.Term → Maybe T.Term) →
            (ma >>= body1) compilesTo a → 
            (mb >>= body2) compilesTo b → 
            (inpsEqv : ∀ {c d} → ma compilesTo c → 
                mb compilesTo d → 
                c ↔te d) → 
            (outsEqv : ∀ {c d} → (res : T.Term) → {_ : ma compilesTo res} →
                body1 res compilesTo c → 
                body2 res compilesTo d → 
                c ↔te d) →
            a ↔te b
        lemmaBindInd (just resa) (just resb) body1 body2 maComps mbComps indL indR
            rewrite indL {c = resa} {d = resb} refl refl = indR resb {refl} maComps mbComps


        lemmaBindBase :
            (ma : Maybe T.Term) →  
            (mb : Maybe T.Term) →  
            (body : T.Term → Maybe T.Term) →  
            (ma >>= body) compilesTo a → 
            (mb >>= body) compilesTo b → 
            (∀ {c d} → ma compilesTo c 
                → mb compilesTo d 
                → c ↔te d) →
            a ↔te b 
        lemmaBindBase ma mb body maComps mbComps indL = 
            lemmaBindInd 
                ma mb 
                body body 
                maComps mbComps 
                indL 
                λ res resCompsL resCompsR → compIsDeterministic (body res) resCompsL resCompsR

open Te 
    using (_↔te_) 
    renaming (_compilesTo_ to _compilesTermTo_) public
