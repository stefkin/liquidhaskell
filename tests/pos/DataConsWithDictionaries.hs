{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}

{-@ LIQUID "--totality"          @-}
{-@ LIQUID "--stringtheory"      @-}

module StringIndexing where


import GHC.TypeLits
import Data.String 
import GHC.CString

data MI (tagret :: Symbol) s where 
  MI :: IsString s => s        -- input string
                   -> [Int]    -- valid indeces of target in input
                   -> MI target s

{-@ MI :: input:s 
       -> [{i:Int | subString input i (stringLen target)  == target }]
       -> MI s @-}


tmp :: forall (target :: Symbol). (KnownSymbol target) => MI target String -> MI target String 
tmp (MI s is) = MI s is 
