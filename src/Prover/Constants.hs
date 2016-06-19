module Prover.Constants where

import Control.Monad (when)

-------------------------------------------------------------------------------
----------------------------   Debugging  -------------------------------------
-------------------------------------------------------------------------------

debug :: Bool
debug = True

whenLoud :: (Monad m) => m () -> m ()
whenLoud = when debug

-------------------------------------------------------------------------------
------------------------   Constant Numbers   ---------------------------------
-------------------------------------------------------------------------------

delta, epsilon, default_depth :: Int
delta   = 5
epsilon = 10
default_depth = 2


-------------------------------------------------------------------------------
------------------------   Files  ---------------------------------------------
-------------------------------------------------------------------------------


smtFile :: FilePath -> FilePath
smtFile fn = fn ++ smtFileExtension
  where
    smtFileExtension = ".smt"