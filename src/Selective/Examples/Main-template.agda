module Selective.Examples.Main-generated where
import Selective.Examples.PingPong as PingPong
import Selective.Examples.Call as Call
import Selective.Examples.Fibonacci as Fib
import Selective.Examples.Chat as Chat
import Selective.Examples.Bookstore as Bookstore

open import Selective.Runtime
open import Selective.SimulationEnvironment
open import Selective.ActorMonad
import IO
open ∞ActorM

pingpongEntry = singleton-env (PingPong.spawner .force)
callEntry = singleton-env (Call.calltestActor .force)
fibEntry = singleton-env (Fib.spawner .force)
chatEntry = singleton-env (Chat.chat-supervisor .force)
bookstoreEntry = singleton-env (Bookstore.bookstore-supervisor .force)

main = IO.run (run-env __ENTRY__)
