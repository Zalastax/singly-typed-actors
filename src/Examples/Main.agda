module Examples.Main where
import Examples.PingPong as PingPong
import Examples.InfiniteBind as InfiniteBind
import Examples.SelectiveReceive as SelectiveReceive
import Examples.Call as Call
open import Runtime
open import SimulationEnvironment
open import ActorMonad
import IO
open ∞ActorM

pingpongEntry = singleton-env (PingPong.spawner .force)
infinitebindEntry = singleton-env (InfiniteBind.binder .force)
selectiveReceiveEntry = singleton-env SelectiveReceive.spawner
callEntry = singleton-env (Call.calltestActor .force)

main = IO.run (run-env trace+actors-logger pingpongEntry)
