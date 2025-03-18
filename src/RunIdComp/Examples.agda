module RunIdComp.Examples where 

import RunId as S
import STLC as T
open import RunIdComp
open import Proofs.Relations
open import Proofs.Utils

open import Data.Nat
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open S using (
    𝟘; ω;
    _𝕢_;
    _~ᵣ_)

elimnatExPre : S.PreContext
elimnatExPre = {!   !}

elimnatExCont : S.Context elimnatExPre
elimnatExCont = {!   !}

elimnatExTe : S.Term
elimnatExTe = (S.elimnat S.z P∶ S.Nat 
            zb∶ S.z 
            sb∶ S.s (S.var 0))

testElimNat : 
    compileTerm 
        S.[] 
        elimnatExTe
        compilesTermTo 
    (T.elimnat T.z 
        zb∶ T.z 
        sb∶ T.s (T.var 0))
testElimNat = Te.lemmaRefl

testElimNat↑ : 
    compileTerm 
        (insertType S.[] zero z≤n S.Nat 𝟘) 
        (S.shiftindices 
            elimnatExTe 
            1 
            zero) 
        compilesTermTo 
    (T.elimnat T.z 
        zb∶ T.z 
        sb∶ T.s (T.var 0))
testElimNat↑ = {!   !}