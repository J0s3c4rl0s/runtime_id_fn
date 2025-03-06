{-# OPTIONS --erasure #-}

module compiletest where

data ⊤ : Set where
    tt : ⊤

data A : Set where
    a : A

data B : A → Set where 
    b : (a : A) → B a

test : (@0 a : A) → B a
test a = b a


