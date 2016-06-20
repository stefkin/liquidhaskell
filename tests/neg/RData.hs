module RData where


data Foo = F Int 
{-@ data Foo = F Nat @-}


foo = F (-1)