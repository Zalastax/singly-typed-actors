module Runtime where
open import Simulate
open import SimulationEnvironment
open import Prelude

open import Data.Nat.Show using (show)
open import Codata.Musical.Notation using ( ♯_ ; ♭)
import IO
open ∞Trace

record BlockedCount : Set₂ where
  field
    return-count : ℕ
    receive-count : ℕ

count-blocked : (env : Env) → BlockedCount
count-blocked env = loop (Env.blocked-no-progress env)
  where
    open BlockedCount
    loop : ∀ {store inbs bl} → All (IsBlocked store inbs) bl → BlockedCount
    loop [] = record { return-count = 0 ; receive-count = 0 }
    loop (BlockedReturn _ _ ∷ xs) =
      let rec = loop xs
      in record { return-count = suc (rec .return-count) ; receive-count = rec .receive-count }
    loop (BlockedReceive _ _ _ ∷ xs) =
      let rec = loop xs
      in record { return-count = rec .return-count ; receive-count = suc (rec .receive-count) }

show-env : Env → String
show-env env =
  let count = count-blocked env
      open BlockedCount
  in "There are " || show (count .return-count) || " finished actors and " || show (count .receive-count) || " blocked actors"

show-final-step : ℕ → String
show-final-step n = "Done after " || (show n) || " steps."

-- run-env continously runs the simulation of an environment
-- and transforms the steps taken into output to the console.
run-env : Env → IO.IO ⊤
run-env env = loop 1 ((simulate env) .force)
  where
    loop : ℕ → Trace ∞ → IO.IO ⊤
    loop n (TraceStop env _) = ♯ IO.putStrLn (show-final-step n) IO.>> ♯ IO.putStrLn (show-env env)
    loop n (x ∷ xs) = ♯ IO.putStrLn ("Step " || show n ) IO.>> ♯ loop (suc n) (xs .force)

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
