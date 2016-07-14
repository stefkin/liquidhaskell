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

import Language.Haskell.Liquid.Prelude ((==>))

import GHC.TypeLits
import Data.String 
import GHC.CString

import Data.Proxy 
-- Structure that defines valid indeces of a type level target 
-- symbol in a value level string

data MI (tagret :: Symbol) 



{-@ tid :: forall (target :: Symbol). (KnownSymbol target) => MI target  -> {v:String | v == target} @-}
tid :: forall (target :: Symbol). (KnownSymbol target) => MI target -> String
tid _
  = symbolVal (Proxy :: Proxy target)


{-@ assume symbolVal :: forall n proxy. KnownSymbol n => proxy n -> {v:String | v == n } @-}

