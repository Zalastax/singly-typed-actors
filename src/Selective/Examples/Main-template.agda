module Selective.Examples.Main-generated where
import Selective.Examples.PingPong as PingPong
import Selective.Examples.Call as Call
import Selective.Examples.Fibonacci as Fib
import Selective.Examples.Chat as Chat

open import Selective.Runtime
open import Selective.SimulationEnvironment
open import Selective.ActorMonad
import IO
open ∞ActorM

pingpongEntry = singleton-env (PingPong.spawner .force)
callEntry = singleton-env (Call.calltestActor .force)
fibEntry = singleton-env (Fib.spawner .force)
chatEntry = singleton-env (Chat.chat-supervisor .force)

main = IO.run (run-env trace+actors-logger __ENTRY__)
