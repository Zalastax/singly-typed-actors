module Selective.Examples.Main-generated where
import Selective.Examples.PingPong as PingPong
import Selective.Examples.TestCall as Call
import Selective.Examples.TestCall2 as Call2
import Selective.Examples.Fibonacci as Fib
import Selective.Examples.Chat as Chat
import Selective.Examples.Bookstore as Bookstore
import Selective.Examples.TestAO as TestAO
import Selective.Examples.TestSelectiveReceive as SelectiveReceive
import Selective.Examples.TestSelectiveReceive-calc as SelectiveReceive-calc

open import Selective.Runtime
open import Selective.SimulationEnvironment
open import Selective.ActorMonad
import IO
open ∞ActorM

pingpongEntry = singleton-env (PingPong.spawner .force)
callEntry = singleton-env (Call.calltestActor .force)
call2Entry = singleton-env (Call2.calculator-test-actor .force)
fibEntry = singleton-env (Fib.spawner .force)
chatEntry = singleton-env (Chat.chat-supervisor .force)
bookstoreEntry = singleton-env (Bookstore.bookstore-supervisor .force)
testaoEntry = singleton-env (TestAO.calculator-test-actor .force)
testsrcalcEntry = singleton-env (SelectiveReceive-calc.calculator-test-actor .force)
testsrEntry = singleton-env (SelectiveReceive.receive-42-with-reference)

main = IO.run (run-env __ENTRY__)
