module AocIO where
open import IO.Primitive public
open import Data.String as String
open import Data.List as List

postulate
  getLine : IO Costring
  getArgs : IO (List String)
  getProgName : IO String

{-# COMPILE GHC getLine = getLine #-}
{-# FOREIGN GHC import qualified Data.Text    as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import System.Environment (getArgs, getProgName) #-}
{-# COMPILE GHC getArgs = fmap (map Text.pack) getArgs #-}
{-# COMPILE GHC getProgName = fmap Text.pack getProgName   #-}
