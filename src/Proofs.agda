module Proofs where

import RunId as S 
import STLC as T
open import RunIdComp

-- I think this fucks up pattern match, make issue
open S using (_~ᵣ_)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym)

private variable
    sΓ : S.PreContext
    scΓ : S.Context sΓ
    sA sB : S.Type
    sa sb sc sas sbs sf sg : S.Term
    σ π ρ : S.Quantity

    tA tB : T.Type
    ta tb : T.Term

-- Maybe a lemma or relation to from a derivation get its subterm proof
-- mark as inline ? so termination checker dont struggle w opacity
lemmabind : ∀ {l} {A B : Set l} {a b : Maybe A} {body : A → Maybe B} → a ≡ b → (a >>= body) ≡ (b >>= body) 
lemmabind {body = body} eq = cong (λ x → x >>= body) eq
-- seems to push weird proofs through with implicits
-- {-# INLINE lemmabind #-}

lemmabind2 : ∀ {l} {A B : Set l} {a b : Maybe A} {body1 body2 : A → Maybe B} → a ≡ b → body1 ≡ body2 → (a >>= body1) ≡ (b >>= body2) 
lemmabind2 a≡b refl = lemmabind a≡b

~ᵣtermproof :
    sa ~ᵣ sc → 
    compileTerm scΓ sa ≡ compileTerm scΓ sc
~ᵣtermproof {scΓ = scΓ} S.~ᵣrefl = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣsym a~b) rewrite ~ᵣtermproof {scΓ = scΓ} a~b = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣtrans a~B B~b) = trans (~ᵣtermproof a~B) (~ᵣtermproof B~b)
-- These rules engage in some reduction, either 
---- 1. Optimize in the compiler 
---- 2. Remove reduction rules 
---- 3. Instead create observational equivalence between terms
-- Tried moving m ~ z style inversions into rule and also add a cong rule
~ᵣtermproof {scΓ = scΓ} (S.~ᵣnatelz a~c) rewrite sym (~ᵣtermproof {scΓ = scΓ} a~c) = {! ~ᵣtermproof {scΓ = scΓ} a~c  !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣnatels a~b a~b₁) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlisteln cs~nill) rewrite ~ᵣtermproof {scΓ = scΓ} cs~nill = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlistelc a~b a~b₁) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣveceln a~b) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣvecelc a~b a~b₁) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣs n~m) rewrite ~ᵣtermproof {scΓ = scΓ} n~m  = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlist a~b) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷l a~c as~cs) 
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpiω a~b a~b₁) = refl
-- stuck why? Cant tell B is a type...
-- probably need some lemma on shifting
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpi𝟘 {B} a~b) = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣpir a~b) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlamω {A = A} b~c) 
    rewrite ~ᵣtermproof {scΓ = scΓ S., A S.𝕢 S.ω} b~c = refl
-- Different contexts in both options....
~ᵣtermproof {scΓ = scΓ} (S.~ᵣlam𝟘 b~sbs) rewrite ~ᵣtermproof {scΓ = {!   !}} b~sbs = {!   !}
~ᵣtermproof {scΓ = scΓ} S.~ᵣlamr = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣappω b~d a~c)
    rewrite ~ᵣtermproof {scΓ = scΓ} b~d | ~ᵣtermproof {scΓ = scΓ} a~c = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣapp𝟘 b~sb) rewrite ~ᵣtermproof {scΓ = scΓ} b~sb = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣappr = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣbetaω = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣvecω _ _) = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣvec𝟘 _) = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣnilvω = refl
~ᵣtermproof {scΓ = scΓ} S.~ᵣnilv𝟘 = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷vω a~c as~cs n~m) 
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs | ~ᵣtermproof {scΓ = scΓ} n~m = refl
~ᵣtermproof {scΓ = scΓ} (S.~ᵣ∷v𝟘 a~c as~cs)
    rewrite ~ᵣtermproof {scΓ = scΓ} a~c | ~ᵣtermproof {scΓ = scΓ} as~cs = refl
-- probably need lemma here, not sure if rewrite does any work
~ᵣtermproof {scΓ = scΓ} (S.~ᵣηlist nb~sbn cb~sbc)
    rewrite ~ᵣtermproof {scΓ = scΓ} nb~sbn | ~ᵣtermproof {scΓ = scΓ} cb~sbc = {!   !}
~ᵣtermproof {scΓ = scΓ} (S.~ᵣηvec a~b a~b₁) = {!   !}

~ᵣ⇒comptype＝ :
    sa ~ᵣ sb → 
    compileType sa ≡ compileType sb
~ᵣ⇒comptype＝ = {!   !}

-- Add proof for type preservation  