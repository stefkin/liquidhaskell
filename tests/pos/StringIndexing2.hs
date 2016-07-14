{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--stringtheory"      @-}

module StringIndexing where

import Prelude hiding (concat)

import Language.Haskell.Liquid.Prelude ((==>), liquidAssert)

import GHC.TypeLits
import Data.String 
import GHC.CString

import Data.Proxy 
-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) s where 
  MI :: IsString s => s        -- input string
                   -> [Int]    -- valid indeces of target in input
                   -> MI target s

{-@ MI :: input:s 
       -> [{i:Nat | subString input i (stringLen target)  == target && i < stringLen input }]
       -> MI s @-}




-- STEP 2: Verify that mempty and mappend satisfy the invariants 
mempty :: forall (target :: Symbol). MI target String
mempty = MI "" []


mappend :: forall (target :: Symbol). (KnownSymbol target) => 
           MI target String -> MI target String -> MI target String
mappend (MI i1 is1) (MI i2 is2)
  = MI i12 (is1 ++ (map (+l1) is2) ++ is12)
  where 
  	is12   = makeIndeces target l1 i12
  	i12    = i1 `concat` i2 
  	l1     = length i1 
  	target = symbolVal (Proxy :: Proxy target)



{-@ predicate PlusMinus V X Y = X - Y <= V  && V <= X + Y @-}

makeIndeces :: String -> Int -> String -> [Int]
{-@ makeIndeces :: tg:String  
                -> bk:Nat 
                -> input:String 
                -> [{i:Nat | subString input i (len tg)  == tg && i < len input && PlusMinus i bk (len tg) }] @-}
makeIndeces tg bk input 
  = go $ rangeFromTo (max 0 (bk - length tg)) (bk + length tg)
  where
    go :: [Int] -> [Int]
    {-@ go :: [{v:Nat | PlusMinus v bk (len tg)}] -> [{i:Nat | subString input i (len tg)  == tg && i < len input  && PlusMinus i bk (len tg)}] @-}
    go (i:is) 
      | substr input i (length tg) == tg && i < length input 
      = i:go is 
      | otherwise
      = go is 
    go [] = []  


{-@ rangeFromTo :: lo:Nat -> hi:{ Nat | lo <= hi } -> [{v: Nat | lo <= v && v <= hi}] / [hi - lo] @-}
rangeFromTo :: Int -> Int -> [Int]
rangeFromTo i j 
  | i < j    = i:rangeFromTo (i+1) j
  | otherwise = [j]

{-@ assume symbolVal :: forall n proxy. KnownSymbol n => proxy n -> {v:String | v == n } @-}


{-@ assume concat :: IsString s => x:s -> y:s -> {v:s | v = concatString x y } @-}
concat :: IsString s => s -> s -> s 
concat = undefined


{-@ assume substr :: IsString s => x:s -> i:Nat -> j:Nat -> {o:s | o = subString x i j}  @-}
substr :: IsString s => s -> Int -> Int -> s 
substr = undefined 

