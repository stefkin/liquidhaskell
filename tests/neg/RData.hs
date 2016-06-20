module RData where


data Foo = F {ff::Int} 
{-@ data Foo = F Nat @-}


foo = F {ff = -1}