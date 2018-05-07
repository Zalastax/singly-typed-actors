module Selective.Runtime where
open import Selective.Simulate
open import Selective.SimulationEnvironment

open import Data.List using (List ; _∷_ ; [] ; map ; length)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String ; _++_)
open import Data.Unit using (⊤ ; tt)

open import Coinduction using ( ♯_ ; ♭)
open import Size using (∞)
import IO
open ∞Trace

record BlockedCount : Set₂ where
  field
    return-count : ℕ
    receive-count : ℕ
    selective-count : ℕ

count-blocked : (env : Env) → BlockedCount
count-blocked env = loop (Env.blocked-no-progress env)
  where
    open BlockedCount
    loop : ∀ {store inbs bl} → All (IsBlocked store inbs) bl → BlockedCount
    loop [] = record { return-count = 0 ; receive-count = 0 ; selective-count = 0 }
    loop (BlockedReturn _ _ ∷ xs) =
      let rec = loop xs
      in record { return-count = suc (rec .return-count) ; receive-count = rec .receive-count ; selective-count = rec .selective-count }
    loop (BlockedReceive _ _ _ ∷ xs) =
      let rec = loop xs
      in record { return-count = rec .return-count ; receive-count = suc (rec .receive-count) ; selective-count = rec .selective-count }
    loop (BlockedSelective _ _ _ _ _ ∷ xs) =
      let rec = loop xs
      in record { return-count = rec .return-count ; receive-count = rec .receive-count ; selective-count = suc (rec .selective-count) }

show-env : Env → String
show-env env =
  let count = count-blocked env
      open BlockedCount
  in "There are " ++ show (count .return-count) ++ " finished actors, " ++ show (count .receive-count) ++ " receiving actors, and " ++ show (count .selective-count) ++ " selecting actors"

show-final-step : ℕ → String
show-final-step n = "Done after " ++ (show n) ++ " steps."

-- run-env continously runs the simulation of an environment
-- and transforms the steps taken into output to the console.
run-env : Env → IO.IO ⊤
run-env env = loop 1 ((simulate env) .force)
  where
    loop : ℕ → Trace ∞ → IO.IO ⊤
    loop n (TraceStop env _) = ♯ IO.putStrLn (show-final-step n) IO.>> ♯ IO.putStrLn (show-env env)
    loop n (x ∷ xs) = ♯ IO.putStrLn ("Step " ++ show n ) IO.>> ♯ loop (suc n) (xs .force)

run-env-silent : Env → IO.IO ⊤
run-env-silent env = loop 1 ((simulate env) .force)
  where
    loop : ℕ → Trace ∞ → IO.IO ⊤
    loop n (TraceStop env _) = IO.putStrLn (show-final-step n)
    loop n (x ∷ xs) = ♯ IO.return tt IO.>> ♯ loop (suc n) (xs .force)

run-env-end : Env → IO.IO Env
run-env-end env = loop ((simulate env) .force)
  where
    loop : Trace ∞ → IO.IO Env
    loop (TraceStop env _) = IO.return env
    loop (x ∷ xs) = ♯ IO.return x IO.>> ♯ loop (xs .force)
