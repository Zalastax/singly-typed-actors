module Selective.Examples.Main-generated where
import Selective.Examples.PingPong as PingPong
import Selective.Examples.Call as Call
open import Selective.Runtime
open import Selective.SimulationEnvironment
open import Selective.ActorMonad
import IO
open ∞ActorM

pingpongEntry = singleton-env (PingPong.spawner .force)
callEntry = singleton-env (Call.calltestActor .force)

main = IO.run (run-env trace+actors-logger __ENTRY__)
