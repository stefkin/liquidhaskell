{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--stringtheory"      @-}
{-@ LIQUID "--exact-data-cons"     @-}
{-@ LIQUID "--higherorder"        @-}

module StringIndexing where

import Prelude hiding (concat, mempty, map, mappend, max)

import Language.Haskell.Liquid.Prelude ((==>), liquidAssert)

import GHC.TypeLits
import Data.String 
import GHC.CString

import Data.Proxy 
-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) s where 
  MI :: IsString s => s        -- input string
                   -> L Int    -- valid indeces of target in input
                   -> MI target s

{-@ MI :: input:s 
       -> L {i:Nat | subString input i (stringLen target)  == target && i < stringLen input }
       -> MI s @-}



-- STEP 2: Verify that mempty and mappend satisfy the invariants 
{-@ reflect mempty @-}
mempty :: forall (target :: Symbol). MI target String
mempty = MI "" N


{-@ measure select_MI_2 @-}
select_MI_2 :: IsString s => MI target s -> s 
select_MI_2 (MI x y) = x

{-@ measure select_MI_3 @-}
select_MI_3 :: MI target s -> L Int 
select_MI_3 (MI x y) = y


 
{-@ axiomatize mappend @-}
mappend :: forall (target :: Symbol). (KnownSymbol target) => 
           MI target String -> MI target String -> MI target String
mappend (MI i1 is1) (MI i2 is2)
  = MI i12 (is1 `append` (map (+l1) is2) `append` is12)
  where 
  	is12   = makeIndeces target l1 i12
  	i12    = i1 `concatString` i2 
  	l1     = stringLen i1 
  	target = symbolVal (Proxy :: Proxy target)

{-@ reflect makeIndeces @-}
{-@ predicate PlusMinus V X Y = X - Y <= V  && V <= X + Y @-}

makeIndeces :: String -> Int -> String -> L Int
{-@ makeIndeces :: tg:String  
                -> bk:Nat 
                -> input:String 
                -> L {i:Nat | subString input i (len tg)  == tg && i < len input && PlusMinus i bk (len tg) } @-}
makeIndeces tg bk input 
  = go tg bk input (rangeFromTo (max 0 (bk - stringLen tg)) (bk + stringLen tg))

{-@ reflect go @-}    
go :: String -> Int -> String -> L Int -> L Int

{-@ go :: tg:String -> bk:Nat -> input:String -> is:L {v:Nat | PlusMinus v bk (len tg)} 
      -> L {i:Nat | subString input i (stringLen tg)  == tg && i < stringLen input  && PlusMinus i bk (stringLen tg)} / [llen is] @-}
go tg bk input (C i is) 
      | subString input i (stringLen tg) == tg && i < stringLen input 
      = C i (go tg bk input is) 
      | otherwise
      = go tg bk input is 
go _ _ _ N = N  



{-@ reflect max @-}
max :: Int -> Int -> Int 
max x y = if x <= y then y else x 

{-@ reflect rangeFromTo @-}
{-@ rangeFromTo :: lo:Nat -> hi:{ Nat | lo <= hi } -> L {v: Nat | lo <= v && v <= hi} / [hi - lo] @-}
rangeFromTo :: Int -> Int -> L Int
rangeFromTo i j 
  | i < j     = C i (rangeFromTo (i+1) j)
  | otherwise = C j N 



-- Proofs 

-- mempty left 

mempty_left :: forall (target :: Symbol). KnownSymbol target =>  MI target String -> ()
{-@ mempty_left :: forall (target :: Symbol). x:MI target String 
                 -> {mappend x mempty  = x} @-}
mempty_left x = (\_ -> ()) $ mappend x mempty


{-@ reflect map @-}
map :: (a -> b) -> L a -> L b 
map f N = N 
map f (C x xs) = f x `C` map f xs

{-@ reflect append @-}
append :: L a -> L a -> L a 
append N        ys = ys 
append (C x xs) ys = x `C` append xs ys 






data L a = N | C a (L a)
{-@ data L [llen] a = N | C {lhd :: a, ltl :: L a} @-}


llen :: L a -> Int 
{-@ llen :: L a -> Nat @-}
{-@ measure llen @-}
llen N = 0 
llen (C x xs) = 1 + llen xs 


{-@ assume symbolVal :: forall n proxy. x:proxy n -> {v:String | v == n && v == symbolVal x} @-}
{-@ measure symbolVal :: forall n proxy. proxy n -> String @-}

{-@ stringLen :: s:String -> {v:Int | v = stringLen s}  @-}
stringLen :: String -> Int 
stringLen = undefined

{-@ assume concatString :: IsString s => x:s -> y:s -> {v:s | v = concatString x y } @-}
concatString :: IsString s => s -> s -> s 
concatString = undefined


{-@ assume subString :: IsString s => x:s -> i:Nat -> j:Nat -> {o:s | o = subString x i j}  @-}
subString :: IsString s => s -> Int -> Int -> s 
subString = undefined 

