module Examples.Main where
import Examples.PingPong as PingPong
import Examples.InfiniteBind as InfiniteBind
import Examples.SelectiveReceive as SelectiveReceive
import Examples.Call as Call
open import Runtime
open import SimulationEnvironment
import IO

pingpongEntry = singleton-env PingPong.spawner
infinitebindEntry = singleton-env InfiniteBind.binder
selectiveReceiveEntry = singleton-env SelectiveReceive.spawner
callEntry = singleton-env Call.calltestActor

main = IO.run (run-env trace+actors-logger pingpongEntry)
