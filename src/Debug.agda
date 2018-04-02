module Debug where
open import Data.String using (String) public
open import Level public

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Debug.Trace as Trace #-}

{-# FOREIGN GHC
debug' :: Data.Text.Text -> c -> c
debug' txt c = Trace.trace (Data.Text.unpack txt) c
#-}

postulate debug : {a : Level} {A : Set a} → String → A → A
{-# COMPILE GHC debug = (\x -> (\y -> debug')) #-}
