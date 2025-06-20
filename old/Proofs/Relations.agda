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
open import Data.Product -- using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Unit
open import Data.Empty
   

module Compiles2 (_↔te_ : T.Term → T.Term → Set) (_↔ty_ : T.Type → T.Type → Set) where
    private variable
        sΓ : S.PreContext
        scΓ : S.Context sΓ

        A : S.Type
        a : S.Term
        
    

    ⟦_⟧ : S.Type → Set
    ⟦ A ⟧ = Σ[ tA ∈ T.Type ] compileType A ≡ just tA

    _⇒ty_ : ⟦ A ⟧ → T.Type → Set
    (tA , snd) ⇒ty tB = tA ↔ty tB


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

        lemmaSym : A ↔ty B → B ↔ty A 
        lemmaSym refl = refl

        lemmaTrans : A ↔ty B → B ↔ty C → A ↔ty C  
        lemmaTrans refl refl = refl

        compIsDeterministic : 
            (mA : Maybe T.Type) →
            mA compilesTo A  →
            mA compilesTo B →
            A ↔ty B
        compIsDeterministic (just x) lComps rComps = lemmaTrans (lemmaSym lComps) rComps


        lemmaBindSubstInd : 
            (mA : Maybe T.Type) →
            (mB : Maybe T.Type) →
            (body1 : T.Type → Maybe T.Type) →
            (body2 : T.Type → Maybe T.Type) →
            (mA >>= body1) compilesTo B →
            (∀ {A} → 
                mA compilesTo A →
                mB compilesTo A) → 
            (outsEqv : ∀ {C} → (res : T.Type) → {mAComps : mA compilesTo res} →
                body1 res compilesTo C → 
                body2 res compilesTo C) → 
            (mB >>= body2) compilesTo B
        lemmaBindSubstInd (just resa) mB body1 body2 mABindComps base ind
            with base refl
        lemmaBindSubstInd (just resa) (just .resa) body1 body2 mABindComps base ind | refl = 
            ind resa {mAComps = refl} mABindComps

        lemmaBindSubstBase : 
            (mA : Maybe T.Type) →
            (mB : Maybe T.Type) →
            (body : T.Type → Maybe T.Type) →
            (mA >>= body) compilesTo B →
            (∀ {A} → 
                mA compilesTo A →
                mB compilesTo A) → 
            (mB >>= body) compilesTo B
        lemmaBindSubstBase mA mB body mABindComps base = 
            lemmaBindSubstInd 
                mA mB 
                body body 
                mABindComps 
                base 
                λ res resComps → resComps

        

        -- need funext for body?
        lemmaBindInd :
            (mA : Maybe T.Type) →
            (mB : Maybe T.Type) →
            (body1 : T.Type → Maybe T.Type) →
            (body2 : T.Type → Maybe T.Type) →
            (mA >>= body1) compilesTo A → 
            (mB >>= body2) compilesTo B → 
            (inpsEqv : ∀ {C D} → mA compilesTo C → 
                mB compilesTo D → 
                C ↔ty D) → 
            (outsEqv : ∀ {C D} → (res : T.Type) → {_ : mA compilesTo res} →
                body1 res compilesTo C → 
                body2 res compilesTo D → 
                C ↔ty D) →
            A ↔ty B
        lemmaBindInd (just resa) (just resb) body1 body2 maComps mbComps indL indR
            rewrite indL {C = resa} {D = resb} refl refl = indR resb {refl} maComps mbComps


        lemmaBindBase :
            (mA : Maybe T.Type) →
            (mB : Maybe T.Type) →
            (body : T.Type → Maybe T.Type) →
            (mA >>= body) compilesTo A → 
            (mB >>= body) compilesTo B → 
            (inpsEqv : ∀ {C D} → mA compilesTo C → 
                mB compilesTo D → 
                C ↔ty D) → 
            A ↔ty B
        lemmaBindBase ma mb body maComps mbComps indL = 
            lemmaBindInd 
                ma mb 
                body body 
                maComps mbComps 
                indL 
                λ res resCompsL resCompsR → compIsDeterministic (body res) resCompsL resCompsR

open Ty 
    using (_↔ty_)
    renaming (_compilesTo_ to _compilesTypeTo_) public

module TermComps (_↔te_ : T.Term → T.Term → Set) where
    private variable
                sΓ : S.PreContext
                scΓ : S.Context sΓ
                ma mb mc : Maybe T.Term
                a b c : T.Term

    ⟦_⊢_⟧ : S.Context sΓ → S.Term → Set
    ⟦ scΓ ⊢ a ⟧ = Σ[ ta ∈ T.Term ] compileTerm scΓ a ≡ just ta

    _⊢_⇒te_ : (scΓ : S.Context sΓ) → (a : S.Term) → T.Term → Set
    _⊢_⇒te_ scΓ a tb = Σ[ (ta , _) ∈ ⟦ scΓ ⊢ a ⟧ ] (ta ↔te tb)
    -- (ta , snd) ⇒te tb = ta ↔te tb

module Te where
    abstract
        private variable
            sΓ : S.PreContext
            scΓ : S.Context sΓ
            ma mb mc : Maybe T.Term
            a b c : T.Term
        
        -- obs equivalence of term
        _↔te_ : T.Term → T.Term → Set
        _↔te_ = _≡_

        open Compiles _↔te_ public
        open TermComps _↔te_ public
        
        lemmaRefl : a ↔te a
        lemmaRefl = refl

        lemmaSym : a ↔te b → b ↔te a 
        lemmaSym refl = refl

        lemmaTrans : a ↔te b → b ↔te c → a ↔te c  
        lemmaTrans refl refl = refl

        import Data.Maybe.Properties as MaybeProps

        TeDeterministic : 
            (scΓ : S.Context sΓ) →
            (sa : S.Term) → 
            (scΓ ⊢ sa ⇒te a) →  
            (scΓ ⊢ sa ⇒te b) →  
            a ↔te b   
        TeDeterministic _ _ ((ta , taComps) , ta↔a) ((tb , tbComps) , tb↔b)
            rewrite taComps | MaybeProps.just-injective tbComps = lemmaTrans (lemmaSym ta↔a) tb↔b

        compIsDeterministic : 
            (ma : Maybe T.Term) →
            ma compilesTo a  →
            ma compilesTo b →
            a ↔te b
        compIsDeterministic (just x) lComps rComps = lemmaTrans (lemmaSym lComps) rComps

        lemmaRewriteComp : 
            a ↔te b →
            ma compilesTo a →
            ma compilesTo b
        lemmaRewriteComp {ma = just resa} eq refl = eq


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

        -- lemmaElimLExt : ∀ {sΓ sA sP sb snb scb i ta tb} {scΓ : S.Context sΓ} →
        --     compileTerm scΓ 
        --         (S.eliml S.var i ty∶ sA P∶ sP 
        --             nb∶ snb 
        --             cb∶ scb) 
        --         compilesTo ta →
        --     compileTerm scΓ sb compilesTo tb →
        --     -- if lookup var i = [] then sc = nb, or sc comps to same as nb 
        --     (∀ {tc td} →
        --         compileTerm scΓ snb compilesTo tc → 
        --         compileTerm scΓ (sb S.[ i / S.nill ]) compilesTo td → 
        --         tc ↔te td ) →
        --     -- if lookup var i = x :: xs then sc = cb, or sc comps to same as cb 
        --     (∀ {tc td} →
        --         -- should I subst into cb here? mirroring the current rule?
        --         compileTerm ((((scΓ S., sA 𝕢 ω) S., S.List sA 𝕢 ω) S., sP 𝕢 ω)) (scb S.[ 0 / S.var 1 ]) compilesTo tc → 
        --         compileTerm scΓ (sb S.[ i / S.var 2 S.∷l S.var 1 ]) compilesTo td → 
        --         tc ↔te td ) →
        --     -- Both held so elimL = sc
        --     ta ↔te tb
        -- lemmaElimLExt elimComps sbComps ind[] ind:: = {!  ind[]   !} 
            

open Te 
    using (_↔te_; ⟦_⊢_⟧; _⊢_⇒te_) 
    renaming (_compilesTo_ to _compilesTermTo_) public
 
open Compiles2 _↔te_ _↔ty_ public 