module Selective.Examples.Main-generated where
import Selective.Examples.PingPong as PingPong
open import Selective.Runtime
open import Selective.SimulationEnvironment
import IO

pingpongEntry = singleton-env PingPong.spawner

main = IO.run (run-env trace+actors-logger __ENTRY__)
