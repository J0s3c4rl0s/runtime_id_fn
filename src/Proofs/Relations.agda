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
open import Data.Nat

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Unit
open import Data.Empty

-- should I even differ between term and type?
module Ty where

    _⇒_ : S.Type → T.Type → Set
    Aₛ ⇒ Aₜ = compileType Aₛ ≡ just Aₜ

    abstract
        private variable
            Aₜ Bₜ Cₜ Dₜ : T.Type
        
        -- equivalence of types
        -- Do I even need a relation or should this _always_ be syntactic?
        _↔ty_ : T.Type → T.Type → Set
        _↔ty_ = _≡_

        
        lemmaRefl : Aₜ ↔ty Aₜ
        lemmaRefl = refl

        lemmaSym : Aₜ ↔ty Bₜ → Bₜ ↔ty Aₜ 
        lemmaSym refl = refl

        lemmaTrans : Aₜ ↔ty Bₜ → Bₜ ↔ty Cₜ → Aₜ ↔ty Cₜ  
        lemmaTrans refl refl = refl

        ---- CONGRUENCE RULES 

        ⟶-cong : 
            Aₜ ↔ty Cₜ →
            Bₜ ↔ty Dₜ →
            (Aₜ T.⟶ Bₜ) ↔ty (Cₜ T.⟶ Dₜ)
        ⟶-cong refl refl = refl

        List-cong : 
            Aₜ ↔ty Bₜ →
            (T.List Aₜ) ↔ty (T.List Bₜ)
        List-cong refl = refl

        Vec-cong : 
            Aₜ ↔ty Bₜ →
            (T.Vec Aₜ) ↔ty (T.Vec Bₜ)
        Vec-cong refl = refl        
        
open Ty using (_↔ty_; _⇒_) public



module Te where
    private variable
        Γₛ : S.PreContext
        cΓₛ : S.Context Γₛ
        aₜ bₜ cₜ asₜ bsₜ fₜ gₜ nₜ mₜ []bₜ ∷bₜ : T.Term
        aₛ bₛ cₛ : S.Term

        n m : ℕ

    -- obs equivalence of term
    _↔te_ : T.Term → T.Term → Set

    _⊢_⇒_ : (cΓₛ : S.Context Γₛ) → (aₛ : S.Term) → T.Term → Set
    cΓₛ ⊢ aₛ ⇒ aₜ = compileTerm cΓₛ aₛ ≡ just aₜ
    
    abstract

        _↔te_ = _≡_

        lemmaRefl : aₜ ↔te aₜ
        lemmaRefl = refl

        lemmaSym : aₜ ↔te bₜ → bₜ ↔te aₜ 
        lemmaSym refl = refl

        lemmaTrans : aₜ ↔te bₜ → bₜ ↔te cₜ → aₜ ↔te cₜ  
        lemmaTrans refl refl = refl
   

        compIsDeterministic' : 
            (cΓₛ : S.Context Γₛ) →
            (aₛ : S.Term) →
            cΓₛ ⊢ aₛ ⇒ aₜ  →
            cΓₛ ⊢ aₛ ⇒ bₜ  →
            aₜ ↔te bₜ
        compIsDeterministic' cΓₛ aₛ compsl compsr with compileTerm cΓₛ aₛ
        compIsDeterministic' cΓₛ aₛ refl refl | just x = refl
        
        ----- CONGRUENCE RULES
        s-cong : 
            aₜ ↔te bₜ →
            T.s aₜ ↔te T.s bₜ        
        s-cong refl = refl

        ∷l-cong : 
            aₜ ↔te bₜ →
            asₜ ↔te bsₜ →
            (aₜ T.∷l asₜ) ↔te (bₜ T.∷l bsₜ)        
        ∷l-cong refl refl = refl

        ∷v-cong : 
            aₜ ↔te bₜ →
            asₜ ↔te bsₜ →
            nₜ ↔te mₜ →
            (aₜ T.∷v asₜ 𝕟 nₜ) ↔te (bₜ T.∷v bsₜ 𝕟 mₜ)        
        ∷v-cong refl refl refl = refl

        ƛ-cong : 
            aₜ ↔te bₜ →
            T.ƛ aₜ ↔te T.ƛ bₜ        
        ƛ-cong refl = refl

        ·-cong : 
            fₜ ↔te gₜ →
            aₜ ↔te bₜ →
            (fₜ T.· aₜ) ↔te (gₜ T.· bₜ)
        ·-cong refl refl = refl            

        -- Eta exensionality 
        elimlη : 
            []bₜ ↔te (cₜ T.[ n / T.nill ])  → 
            (∷bₜ T.[ 0 / T.var 1 ]) ↔te ((cₜ T.↑ 3 ≥ 0) T.[ (3 + n) / T.var 2 T.∷l T.var 1 ]) →
            (T.eliml T.var n nb∶ []bₜ cb∶ ∷bₜ) ↔te cₜ
        elimlη []↔ ∷↔ = {!    !}

open Te using (_↔te_; _⊢_⇒_) public
  